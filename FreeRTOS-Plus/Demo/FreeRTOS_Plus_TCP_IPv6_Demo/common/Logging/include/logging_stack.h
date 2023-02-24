/*
 * FreeRTOS V202012.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

/**
 * @file logging_stack.h
 * @brief Utility header file that exposes macros for configuring logging implementation of logging macros (LogError, LogWarn, LogInfo, LogDebug).
 */

#ifndef LOGGING_STACK_H
#define LOGGING_STACK_H

/* Include header for logging level macros. */
#include "logging_levels.h"

/* Standard Include. */
#include <stdio.h>
#include <stdint.h>

/**
 * @brief The name of the library or demo to add as metadata in log messages
 * from the library or demo.
 *
 * This metadata aids in identifying the module source of log messages.
 * The metadata is logged in the format `[ <LIBRARY-NAME> ]` as a prefix to the
 * log messages.
 * Refer to #LOG_METADATA_FORMAT for the complete format of the metadata prefix in
 * log messages.
 */
/* Check if LIBRARY_LOG_NAME macro has been defined. */
#if !defined( LIBRARY_LOG_NAME )
    #error "Please define LIBRARY_LOG_NAME for the library."
#endif

/* Metadata information to prepend to every log message. */
#ifndef LOG_METADATA_FORMAT
    #define LOG_METADATA_FORMAT    "[%s:%d] "                  /**< @brief Format of metadata prefix in log messages. */
#endif

#ifndef LOG_METADATA_ARGS
    #define LOG_METADATA_ARGS    __FUNCTION__, __LINE__  /**< @brief Arguments into the metadata logging prefix format. */
#endif

/**
 * @brief Common macro that maps all the logging interfaces,
 * (#LogDebug, #LogInfo, #LogWarn, #LogError) to the platform-specific logging
 * function.
 *
 * @note The default definition of the macro is an empty definition that does not
 * generate any logging.
 */
#ifndef SdkLog
    #define SdkLog( string )
#endif

/**
 * Disable definition of logging interface macros when generating doxygen output,
 * to avoid conflict with documentation of macros at the end of the file.
 */
/* Check that LIBRARY_LOG_LEVEL is defined and has a valid value. */
#if !defined( LIBRARY_LOG_LEVEL ) ||       \
    ( ( LIBRARY_LOG_LEVEL != LOG_NONE ) && \
    ( LIBRARY_LOG_LEVEL != LOG_ERROR ) &&  \
    ( LIBRARY_LOG_LEVEL != LOG_WARN ) &&   \
    ( LIBRARY_LOG_LEVEL != LOG_INFO ) &&   \
    ( LIBRARY_LOG_LEVEL != LOG_DEBUG ) )
    #error "Please define LIBRARY_LOG_LEVEL as either LOG_NONE, LOG_ERROR, LOG_WARN, LOG_INFO, or LOG_DEBUG."
#else
    #if LIBRARY_LOG_LEVEL == LOG_DEBUG
        /* All log level messages will logged. */
        #define LogError( message )    SdkLog( ( "[ERROR] [%s] "LOG_METADATA_FORMAT, LIBRARY_LOG_NAME, LOG_METADATA_ARGS ) ); SdkLog( message ); SdkLog( ( "\r\n" ) )
        #define LogWarn( message )     SdkLog( ( "[WARN] [%s] "LOG_METADATA_FORMAT, LIBRARY_LOG_NAME, LOG_METADATA_ARGS ) ); SdkLog( message ); SdkLog( ( "\r\n" ) )
        #define LogInfo( message )     SdkLog( ( "[INFO] [%s] "LOG_METADATA_FORMAT, LIBRARY_LOG_NAME, LOG_METADATA_ARGS ) ); SdkLog( message ); SdkLog( ( "\r\n" ) )
        #define LogDebug( message )    SdkLog( ( "[DEBUG] [%s] "LOG_METADATA_FORMAT, LIBRARY_LOG_NAME, LOG_METADATA_ARGS ) ); SdkLog( message ); SdkLog( ( "\r\n" ) )

    #elif LIBRARY_LOG_LEVEL == LOG_INFO
        /* Only INFO, WARNING and ERROR messages will be logged. */
        #define LogError( message )    SdkLog( ( "[ERROR] [%s] "LOG_METADATA_FORMAT, LIBRARY_LOG_NAME, LOG_METADATA_ARGS ) ); SdkLog( message ); SdkLog( ( "\r\n" ) )
        #define LogWarn( message )     SdkLog( ( "[WARN] [%s] "LOG_METADATA_FORMAT, LIBRARY_LOG_NAME, LOG_METADATA_ARGS ) ); SdkLog( message ); SdkLog( ( "\r\n" ) )
        #define LogInfo( message )     SdkLog( ( "[INFO] [%s] "LOG_METADATA_FORMAT, LIBRARY_LOG_NAME, LOG_METADATA_ARGS ) ); SdkLog( message ); SdkLog( ( "\r\n" ) )
        #define LogDebug( message )

    #elif LIBRARY_LOG_LEVEL == LOG_WARN
        /* Only WARNING and ERROR messages will be logged.*/
        #define LogError( message )    SdkLog( ( "[ERROR] [%s] "LOG_METADATA_FORMAT, LIBRARY_LOG_NAME, LOG_METADATA_ARGS ) ); SdkLog( message ); SdkLog( ( "\r\n" ) )
        #define LogWarn( message )     SdkLog( ( "[WARN] [%s] "LOG_METADATA_FORMAT, LIBRARY_LOG_NAME, LOG_METADATA_ARGS ) ); SdkLog( message ); SdkLog( ( "\r\n" ) )
        #define LogInfo( message )
        #define LogDebug( message )

    #elif LIBRARY_LOG_LEVEL == LOG_ERROR
        /* Only ERROR messages will be logged. */
        #define LogError( message )    SdkLog( ( "[ERROR] [%s] "LOG_METADATA_FORMAT, LIBRARY_LOG_NAME, LOG_METADATA_ARGS ) ); SdkLog( message ); SdkLog( ( "\r\n" ) )
        #define LogWarn( message )
        #define LogInfo( message )
        #define LogDebug( message )

    #else /* if LIBRARY_LOG_LEVEL == LOG_ERROR */

        #define LogError( message )
        #define LogWarn( message )
        #define LogInfo( message )
        #define LogDebug( message )

    #endif /* if LIBRARY_LOG_LEVEL == LOG_ERROR */
#endif /* if !defined( LIBRARY_LOG_LEVEL ) || ( ( LIBRARY_LOG_LEVEL != LOG_NONE ) && ( LIBRARY_LOG_LEVEL != LOG_ERROR ) && ( LIBRARY_LOG_LEVEL != LOG_WARN ) && ( LIBRARY_LOG_LEVEL != LOG_INFO ) && ( LIBRARY_LOG_LEVEL != LOG_DEBUG ) ) */

#endif /* ifndef LOGGING_STACK_H */
