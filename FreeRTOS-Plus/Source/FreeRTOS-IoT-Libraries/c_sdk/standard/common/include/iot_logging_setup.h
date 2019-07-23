/*
 * Amazon FreeRTOS Common V1.0.0
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
 *
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

/**
 * @file iot_logging_setup.h
 * @brief Defines the logging macro #IotLog.
 */

#ifndef IOT_LOGGING_SETUP_H_
#define IOT_LOGGING_SETUP_H_

/* The config header is always included first. */
#include "iot_config.h"

/* Logging include. Because it's included here, iot_logging.h never needs
 * to be included in source. */
#include "private/iot_logging.h"

/**
 * @functionpage{IotLog,logging,log}
 * @functionpage{IotLog_PrintBuffer,logging,printbuffer}
 */

/**
 * @def IotLog( messageLevel, pLogConfig, ... )
 * @brief Logging function for a specific library. In most cases, this is the
 * logging function to call.
 *
 * This function prints a single log message. It is available when @ref
 * LIBRARY_LOG_LEVEL is not #IOT_LOG_NONE. Log messages automatically
 * include the [log level](@ref logging_constants_levels), [library name]
 * (@ref LIBRARY_LOG_NAME), and time. An optional @ref IotLogConfig_t may
 * be passed to this function to hide information for a single log message.
 *
 * The logging library must be set up before this function may be called. See
 * @ref logging_setup_use for more information.
 *
 * This logging function also has the following abbreviated forms that can be used
 * when an #IotLogConfig_t isn't needed.
 *
 * Name         | Equivalent to
 * ----         | -------------
 * #IotLogError | @code{c} IotLog( IOT_LOG_ERROR, NULL, ... ) @endcode
 * #IotLogWarn  | @code{c} IotLog( IOT_LOG_WARN, NULL, ... ) @endcode
 * #IotLogInfo  | @code{c} IotLog( IOT_LOG_INFO, NULL, ... ) @endcode
 * #IotLogDebug | @code{c} IotLog( IOT_LOG_DEBUG, NULL, ... ) @endcode
 *
 * @param[in] messageLevel Log level of this message. Must be one of the
 * @ref logging_constants_levels.
 * @param[in] pLogConfig Pointer to an #IotLogConfig_t. Optional; pass `NULL`
 * to ignore.
 * @param[in] ... Message and format specification.
 *
 * @return No return value. On errors, it prints nothing.
 *
 * @note This function may be implemented as a macro.
 * @see @ref logging_function_generic for the generic (not library-specific)
 * logging function.
 */

/**
 * @def IotLog_PrintBuffer( pHeader, pBuffer, bufferSize )
 * @brief Log the contents of buffer as bytes. Only available when @ref
 * LIBRARY_LOG_LEVEL is #IOT_LOG_DEBUG.
 *
 * This function prints the bytes located at a given memory address. It is
 * intended for debugging only, and is therefore only available when @ref
 * LIBRARY_LOG_LEVEL is #IOT_LOG_DEBUG.
 *
 * Log messages printed by this function <b>always</b> include the [log level]
 * (@ref logging_constants_levels), [library name](@ref LIBRARY_LOG_NAME),
 * and time.  In addition, this function may print an optional header `pHeader`
 * before it prints the contents of the buffer. This function does not have an
 * #IotLogConfig_t parameter.
 *
 * The logging library must be set up before this function may be called. See
 * @ref logging_setup_use for more information.
 *
 * @param[in] pHeader A message to log before the buffer. Optional; pass `NULL`
 * to ignore.
 * @param[in] pBuffer Pointer to start of buffer.
 * @param[in] bufferSize Size of `pBuffer`.
 *
 * @return No return value. On errors, it prints nothing.
 *
 * @note This function may be implemented as a macro.
 * @note To conserve memory, @ref logging_function_genericprintbuffer (the underlying
 * implementation) only allocates enough memory for a single line of output. Therefore,
 * in multithreaded systems, its output may appear "fragmented" if other threads are
 * logging simultaneously.
 * @see @ref logging_function_genericprintbuffer for the generic (not library-specific)
 * buffer logging function.
 *
 * <b>Example</b>
 * @code{c}
 * const uint8_t pBuffer[] = { 0x00, 0x01, 0x02, 0x03 };
 *
 * IotLog_PrintBuffer( "This buffer contains:",
 *                     pBuffer,
 *                     4 );
 * @endcode
 * The code above prints something like the following:
 * @code{c}
 * [DEBUG][LIB_NAME][2018-01-01 12:00:00] This buffer contains:
 * 00 01 02 03
 * @endcode
 */

/**
 * @def IotLogError( ...  )
 * @brief Abbreviated logging macro for level #IOT_LOG_ERROR.
 *
 * Equivalent to:
 * @code{c}
 * IotLog( IOT_LOG_ERROR, NULL, ... )
 * @endcode
 */

/**
 * @def IotLogWarn( ...  )
 * @brief Abbreviated logging macro for level #IOT_LOG_WARN.
 *
 * Equivalent to:
 * @code{c}
 * IotLog( IOT_LOG_WARN, NULL, ... )
 * @endcode
 */

/**
 * @def IotLogInfo( ...  )
 * @brief Abbreviated logging macro for level #IOT_LOG_INFO.
 *
 * Equivalent to:
 * @code{c}
 * IotLog( IOT_LOG_INFO, NULL, ... )
 * @endcode
 */

/**
 * @def IotLogDebug( ...  )
 * @brief Abbreviated logging macro for level #IOT_LOG_DEBUG.
 *
 * Equivalent to:
 * @code{c}
 * IotLog( IOT_LOG_DEBUG, NULL, ... )
 * @endcode
 */

/* Check that LIBRARY_LOG_LEVEL is defined and has a valid value. */
#if !defined( LIBRARY_LOG_LEVEL ) ||            \
    ( LIBRARY_LOG_LEVEL != IOT_LOG_NONE &&  \
      LIBRARY_LOG_LEVEL != IOT_LOG_ERROR && \
      LIBRARY_LOG_LEVEL != IOT_LOG_WARN &&  \
      LIBRARY_LOG_LEVEL != IOT_LOG_INFO &&  \
      LIBRARY_LOG_LEVEL != IOT_LOG_DEBUG )
    #error "Please define LIBRARY_LOG_LEVEL as either IOT_LOG_NONE, IOT_LOG_ERROR, IOT_LOG_WARN, IOT_LOG_INFO, or IOT_LOG_DEBUG."
/* Check that LIBRARY_LOG_NAME is defined and has a valid value. */
#elif !defined( LIBRARY_LOG_NAME )
    #error "Please define LIBRARY_LOG_NAME."
#else
    /* Define IotLog if the log level is greater than "none". */
    #if LIBRARY_LOG_LEVEL > IOT_LOG_NONE
        #define IotLog( messageLevel, pLogConfig, ... )   \
                IotLog_Generic( LIBRARY_LOG_LEVEL,        \
                                LIBRARY_LOG_NAME,        \
                                messageLevel,             \
                                pLogConfig,               \
                                __VA_ARGS__ )

        /* Define the abbreviated logging macros. */
        #define IotLogError( ...  )    IotLog( IOT_LOG_ERROR, NULL, __VA_ARGS__ )
        #define IotLogWarn( ... )      IotLog( IOT_LOG_WARN, NULL, __VA_ARGS__ )
        #define IotLogInfo( ... )      IotLog( IOT_LOG_INFO, NULL, __VA_ARGS__ )
        #define IotLogDebug( ... )     IotLog( IOT_LOG_DEBUG, NULL, __VA_ARGS__ )

        /* If log level is DEBUG, enable the function to print buffers. */
        #if LIBRARY_LOG_LEVEL >= IOT_LOG_DEBUG
        #define IotLog_PrintBuffer( pHeader, pBuffer, bufferSize )    \
                IotLog_GenericPrintBuffer( LIBRARY_LOG_NAME,         \
                                           pHeader,                   \
                                           pBuffer,                   \
                                           bufferSize )
        #else
        #define IotLog_PrintBuffer( pHeader, pBuffer, bufferSize )
        #endif
    /* Remove references to IotLog from the source code if logging is disabled. */
    #else
        /* @[declare_logging_log] */
        #define IotLog( messageLevel, pLogConfig, ... )
        /* @[declare_logging_log] */
        /* @[declare_logging_printbuffer] */
        #define IotLog_PrintBuffer( pHeader, pBuffer, bufferSize )
        /* @[declare_logging_printbuffer] */
        #define IotLogError( ...  )
        #define IotLogWarn( ... )
        #define IotLogInfo( ... )
        #define IotLogDebug( ... )
    #endif
#endif

#endif /* ifndef IOT_LOGGING_SETUP_H_ */
