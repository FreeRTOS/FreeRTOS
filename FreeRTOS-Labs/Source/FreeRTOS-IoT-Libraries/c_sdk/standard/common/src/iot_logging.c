/*
 * IoT Common V1.1.0
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/**
 * @file iot_logging.c
 * @brief Implementation of logging functions from iot_logging.h
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <stdarg.h>
#include <stdio.h>
#include <string.h>

/* Platform clock include. */
#include "platform/iot_clock.h"

/* Logging includes. */
#include "iot_logging.h"

/*-----------------------------------------------------------*/

/* This implementation assumes the following values for the log level constants.
 * Ensure that the values have not been modified. */
#if IOT_LOG_NONE != 0
    #error "IOT_LOG_NONE must be 0."
#endif
#if IOT_LOG_ERROR != 1
    #error "IOT_LOG_ERROR must be 1."
#endif
#if IOT_LOG_WARN != 2
    #error "IOT_LOG_WARN must be 2."
#endif
#if IOT_LOG_INFO != 3
    #error "IOT_LOG_INFO must be 3."
#endif
#if IOT_LOG_DEBUG != 4
    #error "IOT_LOG_DEBUG must be 4."
#endif

/**
 * @def IotLogging_Puts( message )
 * @brief Function the logging library uses to print a line.
 *
 * This function can be set by using a define. By default, the standard library
 * [puts](http://pubs.opengroup.org/onlinepubs/9699919799/functions/puts.html)
 * function is used.
 */
#ifndef IotLogging_Puts
    #define IotLogging_Puts    puts
#endif

/*
 * Provide default values for undefined memory allocation functions based on
 * the usage of dynamic memory allocation.
 */
#if IOT_STATIC_MEMORY_ONLY == 1
    /* Static memory allocation header. */
    #include "iot_static_memory.h"

/**
 * @brief Allocate a new logging buffer. This function must have the same
 * signature as [malloc](http://pubs.opengroup.org/onlinepubs/9699919799/functions/malloc.html).
 */
    #ifndef IotLogging_Malloc
        #define IotLogging_Malloc    Iot_MallocMessageBuffer
    #endif

/**
 * @brief Free a logging buffer. This function must have the same signature
 * as [free](http://pubs.opengroup.org/onlinepubs/9699919799/functions/free.html).
 */
    #ifndef IotLogging_Free
        #define IotLogging_Free    Iot_FreeMessageBuffer
    #endif

/**
 * @brief Get the size of a logging buffer. Statically-allocated buffers
 * should all have the same size.
 */
    #ifndef IotLogging_StaticBufferSize
        #define IotLogging_StaticBufferSize    Iot_MessageBufferSize
    #endif
#else /* if IOT_STATIC_MEMORY_ONLY == 1 */
    #ifndef IotLogging_Malloc
        #include <stdlib.h>
        #define IotLogging_Malloc    malloc
    #endif

    #ifndef IotLogging_Free
        #include <stdlib.h>
        #define IotLogging_Free    free
    #endif
#endif /* if IOT_STATIC_MEMORY_ONLY == 1 */

/**
 * @brief A guess of the maximum length of a timestring.
 *
 * There's no way for this logging library to know the length of a timestring
 * before it's generated. Therefore, the logging library will assume a maximum
 * length of any timestring it may get. This value should be generous enough
 * to accommodate the vast majority of timestrings.
 *
 * @see @ref platform_clock_function_gettimestring
 */
#define MAX_TIMESTRING_LENGTH    ( 64 )

/**
 * @brief The longest string in #_pLogLevelStrings (below), plus 3 to accommodate
 * `[]` and a null-terminator.
 */
#define MAX_LOG_LEVEL_LENGTH     ( 8 )

/**
 * @brief How many bytes @ref logging_function_genericprintbuffer should output on
 * each line.
 */
#define BYTES_PER_LINE           ( 16 )

/*-----------------------------------------------------------*/

/**
 * @brief Lookup table for log levels.
 *
 * Converts one of the @ref logging_constants_levels to a string.
 */
static const char * const _pLogLevelStrings[ 5 ] =
{
    "",      /* IOT_LOG_NONE */
    "ERROR", /* IOT_LOG_ERROR */
    "WARN ", /* IOT_LOG_WARN */
    "INFO ", /* IOT_LOG_INFO */
    "DEBUG"  /* IOT_LOG_DEBUG */
};

/*-----------------------------------------------------------*/

#if !defined( IOT_STATIC_MEMORY_ONLY ) || ( IOT_STATIC_MEMORY_ONLY == 0 )
    static bool _reallocLoggingBuffer( void ** pOldBuffer,
                                       size_t newSize,
                                       size_t oldSize )
    {
        bool status = false;

        /* Allocate a new, larger buffer. */
        void * pNewBuffer = IotLogging_Malloc( newSize );

        /* Ensure that memory allocation succeeded. */
        if( pNewBuffer != NULL )
        {
            /* Copy the data from the old buffer to the new buffer. */
            ( void ) memcpy( pNewBuffer, *pOldBuffer, oldSize );

            /* Free the old buffer and update the pointer. */
            IotLogging_Free( *pOldBuffer );
            *pOldBuffer = pNewBuffer;

            status = true;
        }

        return status;
    }
#endif /* if !defined( IOT_STATIC_MEMORY_ONLY ) || ( IOT_STATIC_MEMORY_ONLY == 0 ) */

/*-----------------------------------------------------------*/

void IotLog_Generic( int libraryLogSetting,
                     const char * const pLibraryName,
                     int messageLevel,
                     const IotLogConfig_t * const pLogConfig,
                     const char * const pFormat,
                     ... )
{
    int requiredMessageSize = 0;
    size_t bufferSize = 0,
           bufferPosition = 0, timestringLength = 0;
    char * pLoggingBuffer = NULL;
    va_list args;

    /* If the library's log level setting is lower than the message level,
     * return without doing anything. */
    if( ( messageLevel == 0 ) || ( messageLevel > libraryLogSetting ) )
    {
        return;
    }

    if( ( pLogConfig == NULL ) || ( pLogConfig->hideLogLevel == false ) )
    {
        /* Add length of log level if requested. */
        bufferSize += MAX_LOG_LEVEL_LENGTH;
    }

    /* Estimate the amount of buffer needed for this log message. */
    if( ( pLogConfig == NULL ) || ( pLogConfig->hideLibraryName == false ) )
    {
        /* Add size of library name if requested. Add 2 to accommodate "[]". */
        bufferSize += strlen( pLibraryName ) + 2;
    }

    if( ( pLogConfig == NULL ) || ( pLogConfig->hideTimestring == false ) )
    {
        /* Add length of timestring if requested. */
        bufferSize += MAX_TIMESTRING_LENGTH;
    }

    /* Add 64 as an initial (arbitrary) guess for the length of the message. */
    bufferSize += 64;

    /* In static memory mode, check that the log message will fit in the a
     * static buffer. */
    #if IOT_STATIC_MEMORY_ONLY == 1
        if( bufferSize >= IotLogging_StaticBufferSize() )
        {
            /* If the static buffers are likely too small to fit the log message,
             * return. */
            return;
        }

        /* Otherwise, update the buffer size to the size of a static buffer. */
        bufferSize = IotLogging_StaticBufferSize();
    #endif

    /* Allocate memory for the logging buffer. */
    pLoggingBuffer = ( char * ) IotLogging_Malloc( bufferSize );

    if( pLoggingBuffer == NULL )
    {
        return;
    }

    /* Print the message log level if requested. */
    if( ( pLogConfig == NULL ) || ( pLogConfig->hideLogLevel == false ) )
    {
        /* Ensure that message level is valid. */
        if( ( messageLevel >= IOT_LOG_NONE ) && ( messageLevel <= IOT_LOG_DEBUG ) )
        {
            /* Add the log level string to the logging buffer. */
            requiredMessageSize = snprintf( pLoggingBuffer + bufferPosition,
                                            bufferSize - bufferPosition,
                                            "[%s]",
                                            _pLogLevelStrings[ messageLevel ] );

            /* Check for encoding errors. */
            if( requiredMessageSize <= 0 )
            {
                IotLogging_Free( pLoggingBuffer );

                return;
            }

            /* Update the buffer position. */
            bufferPosition += ( size_t ) requiredMessageSize;
        }
    }

    /* Print the library name if requested. */
    if( ( pLogConfig == NULL ) || ( pLogConfig->hideLibraryName == false ) )
    {
        /* Add the library name to the logging buffer. */
        requiredMessageSize = snprintf( pLoggingBuffer + bufferPosition,
                                        bufferSize - bufferPosition,
                                        "[%s]",
                                        pLibraryName );

        /* Check for encoding errors. */
        if( requiredMessageSize <= 0 )
        {
            IotLogging_Free( pLoggingBuffer );

            return;
        }

        /* Update the buffer position. */
        bufferPosition += ( size_t ) requiredMessageSize;
    }

    /* Print the timestring if requested. */
    if( ( pLogConfig == NULL ) || ( pLogConfig->hideTimestring == false ) )
    {
        /* Add the opening '[' enclosing the timestring. */
        pLoggingBuffer[ bufferPosition ] = '[';
        bufferPosition++;

        /* Generate the timestring and add it to the buffer. */
        if( IotClock_GetTimestring( pLoggingBuffer + bufferPosition,
                                    bufferSize - bufferPosition,
                                    &timestringLength ) == true )
        {
            /* If the timestring was successfully generated, add the closing "]". */
            bufferPosition += timestringLength;
            pLoggingBuffer[ bufferPosition ] = ']';
            bufferPosition++;
        }
        else
        {
            /* Sufficient memory for a timestring should have been allocated. A timestring
             * probably failed to generate due to a clock read error; remove the opening '['
             * from the logging buffer. */
            bufferPosition--;
            pLoggingBuffer[ bufferPosition ] = '\0';
        }
    }

    /* Add a padding space between the last closing ']' and the message, unless
     * the logging buffer is empty. */
    if( bufferPosition > 0 )
    {
        pLoggingBuffer[ bufferPosition ] = ' ';
        bufferPosition++;
    }

    va_start( args, pFormat );

    /* Add the log message to the logging buffer. */
    requiredMessageSize = vsnprintf( pLoggingBuffer + bufferPosition,
                                     bufferSize - bufferPosition,
                                     pFormat,
                                     args );

    va_end( args );

    /* If the logging buffer was too small to fit the log message, reallocate
     * a larger logging buffer. */
    if( ( size_t ) requiredMessageSize >= bufferSize - bufferPosition )
    {
        #if IOT_STATIC_MEMORY_ONLY == 1

            /* There's no point trying to allocate a larger static buffer. Return
             * immediately. */
            IotLogging_Free( pLoggingBuffer );

            return;
        #else
            if( _reallocLoggingBuffer( ( void ** ) &pLoggingBuffer,
                                       ( size_t ) requiredMessageSize + bufferPosition + 1,
                                       bufferSize ) == false )
            {
                /* If buffer reallocation failed, return. */
                IotLogging_Free( pLoggingBuffer );

                return;
            }

            /* Reallocation successful, update buffer size. */
            bufferSize = ( size_t ) requiredMessageSize + bufferPosition + 1;

            /* Add the log message to the buffer. Now that the buffer has been
             * reallocated, this should succeed. */
            va_start( args, pFormat );
            requiredMessageSize = vsnprintf( pLoggingBuffer + bufferPosition,
                                             bufferSize - bufferPosition,
                                             pFormat,
                                             args );
            va_end( args );
        #endif /* if IOT_STATIC_MEMORY_ONLY == 1 */
    }

    /* Check for encoding errors. */
    if( requiredMessageSize <= 0 )
    {
        IotLogging_Free( pLoggingBuffer );

        return;
    }

    /* Print the logging buffer to stdout. */
    IotLogging_Puts( pLoggingBuffer );

    /* Free the logging buffer. */
    IotLogging_Free( pLoggingBuffer );
}

/*-----------------------------------------------------------*/

void IotLog_GenericPrintBuffer( const char * const pLibraryName,
                                const char * const pHeader,
                                const uint8_t * const pBuffer,
                                size_t bufferSize )
{
    size_t i = 0, offset = 0;

    /* Allocate memory to hold each line of the log message. Since each byte
     * of pBuffer is printed in 4 characters (2 digits, a space, and a null-
     * terminator), the size of each line is 4 * BYTES_PER_LINE. */
    char * pMessageBuffer = IotLogging_Malloc( 4 * BYTES_PER_LINE );

    /* Exit if no memory is available. */
    if( pMessageBuffer == NULL )
    {
        return;
    }

    /* Print pHeader before printing pBuffer. */
    if( pHeader != NULL )
    {
        IotLog_Generic( IOT_LOG_DEBUG,
                        pLibraryName,
                        IOT_LOG_DEBUG,
                        NULL,
                        pHeader );
    }

    /* Print each byte in pBuffer. */
    for( i = 0; i < bufferSize; i++ )
    {
        /* Print a line if BYTES_PER_LINE is reached. But don't print a line
         * at the beginning (when i=0). */
        if( ( i % BYTES_PER_LINE == 0 ) && ( i != 0 ) )
        {
            IotLogging_Puts( pMessageBuffer );

            /* Reset offset so that pMessageBuffer is filled from the beginning. */
            offset = 0;
        }

        /* Print a single byte into pMessageBuffer. */
        ( void ) snprintf( pMessageBuffer + offset, 4, "%02x ", pBuffer[ i ] );

        /* Move the offset where the next character is printed. */
        offset += 3;
    }

    /* Print the final line of bytes. This line isn't printed by the for-loop above. */
    IotLogging_Puts( pMessageBuffer );

    /* Free memory used by this function. */
    IotLogging_Free( pMessageBuffer );
}

/*-----------------------------------------------------------*/
