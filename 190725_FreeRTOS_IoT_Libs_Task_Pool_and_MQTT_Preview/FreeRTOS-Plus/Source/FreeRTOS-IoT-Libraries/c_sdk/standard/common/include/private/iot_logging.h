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
 * @file iot_logging.h
 * @brief Generic logging function header file.
 *
 * Declares the generic logging function and the log levels. This file never
 * needs to be included in source code. The header iot_logging_setup.h should
 * be included instead.
 *
 * @see iot_logging_setup.h
 */

#ifndef IOT_LOGGING_H_
#define IOT_LOGGING_H_

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

/**
 * @constantspage{logging,logging library}
 *
 * @section logging_constants_levels Log levels
 * @brief Log levels for the libraries in this SDK.
 *
 * Each library should specify a log level by setting @ref LIBRARY_LOG_LEVEL.
 * All log messages with a level at or below the specified level will be printed
 * for that library.
 *
 * Currently, there are 4 log levels. In the order of lowest to highest, they are:
 * - #IOT_LOG_NONE <br>
 *   @copybrief IOT_LOG_NONE
 * - #IOT_LOG_ERROR <br>
 *   @copybrief IOT_LOG_ERROR
 * - #IOT_LOG_WARN <br>
 *   @copybrief IOT_LOG_WARN
 * - #IOT_LOG_INFO <br>
 *   @copybrief IOT_LOG_INFO
 * - #IOT_LOG_DEBUG <br>
 *   @copybrief IOT_LOG_DEBUG
 */

/**
 * @brief No log messages.
 *
 * Log messages with this level will be silently discarded. When @ref
 * LIBRARY_LOG_LEVEL is #IOT_LOG_NONE, logging is disabled and no [logging functions]
 * (@ref logging_functions) can be called.
 */
#define IOT_LOG_NONE     0

/**
 * @brief Only critical, unrecoverable errors.
 *
 * Log messages with this level will be printed when a library encounters an
 * error from which it cannot easily recover.
 */
#define IOT_LOG_ERROR    1

/**
 * @brief Message about an abnormal but recoverable event.
 *
 * Log messages with this level will be printed when a library encounters an
 * abnormal event that may be indicative of an error. Libraries should continue
 * execution after logging a warning.
 */
#define IOT_LOG_WARN     2

/**
 * @brief A helpful, informational message.
 *
 * Log messages with this level may indicate the normal status of a library
 * function. They should be used to track how far a program has executed.
 */
#define IOT_LOG_INFO     3

/**
 * @brief Detailed and excessive debug information.
 *
 * Log messages with this level are intended for developers. They may contain
 * excessive information such as internal variables, buffers, or other specific
 * information.
 */
#define IOT_LOG_DEBUG    4

/**
 * @paramstructs{logging,logging}
 */

/**
 * @ingroup logging_datatypes_paramstructs
 * @brief Log message configuration struct.
 *
 * @paramfor @ref logging_function_log, @ref logging_function_generic
 *
 * By default, log messages print the library name, log level, and a timestring.
 * This struct can be passed to @ref logging_function_generic to disable one of
 * the above components in the log message.
 *
 * <b>Example:</b>
 *
 * @code{c}
 * IotLog_Generic( IOT_LOG_DEBUG, "SAMPLE", IOT_LOG_DEBUG, NULL, "Hello world!" );
 * @endcode
 * The code above prints the following message:
 * @code
 * [DEBUG][SAMPLE][2018-01-01 12:00:00] Hello world!
 * @endcode
 *
 * The timestring can be disabled as follows:
 * @code
 * IotLogConfig_t logConfig = { .hideLogLevel = false, .hideLibraryName = false, .hideTimestring = true};
 * IotLog_Generic( IOT_LOG_DEBUG, "SAMPLE", IOT_LOG_DEBUG, &logConfig, "Hello world!" );
 * @endcode
 * The resulting log message will be:
 * @code
 * [DEBUG][SAMPLE] Hello world!
 * @endcode
 */
typedef struct IotLogConfig
{
    bool hideLogLevel;    /**< @brief Don't print the log level string for this message. */
    bool hideLibraryName; /**< @brief Don't print the library name for this message. */
    bool hideTimestring;  /**< @brief Don't print the timestring for this message. */
} IotLogConfig_t;

/**
 * @functionspage{logging,logging library}
 *
 * - @functionname{logging_function_log}
 * - @functionname{logging_function_printbuffer}
 * - @functionname{logging_function_generic}
 * - @functionname{logging_function_genericprintbuffer}
 */

/**
 * @functionpage{IotLog_Generic,logging,generic}
 * @functionpage{IotLog_PrintBuffer,logging,genericprintbuffer}
 */

/**
 * @brief Generic logging function that prints a single message.
 *
 * This function is the generic logging function shared across all libraries.
 * The library-specific logging function @ref logging_function_log is implemented
 * using this function. Like @ref logging_function_log, this function is only
 * available when @ref LIBRARY_LOG_LEVEL is #IOT_LOG_NONE.
 *
 * In most cases, the library-specific logging function @ref logging_function_log
 * should be called instead of this function.
 *
 * @param[in] libraryLogSetting The log level setting of the library, used to
 * determine if the log message should be printed. Must be one of the @ref
 * logging_constants_levels.
 * @param[in] pLibraryName The library name to print. See @ref LIBRARY_LOG_NAME.
 * @param[in] messageLevel The log level of the this message. See @ref LIBRARY_LOG_LEVEL.
 * @param[in] pLogConfig Pointer to a #IotLogConfig_t. Optional; pass `NULL` to ignore.
 * @param[in] pFormat Format string for the log message.
 * @param[in] ... Arguments for format specification.
 *
 * @return No return value. On errors, it prints nothing.
 */
/* @[declare_logging_generic] */
void IotLog_Generic( int libraryLogSetting,
                     const char * const pLibraryName,
                     int messageLevel,
                     const IotLogConfig_t * const pLogConfig,
                     const char * const pFormat,
                     ... );
/* @[declare_logging_generic] */

/**
 * @brief Generic function to log the contents of a buffer as bytes.
 *
 * This function is the generic buffer logging function shared across all libraries.
 * The library-specific buffer logging function @ref logging_function_printbuffer is
 * implemented using this function. Like @ref logging_function_printbuffer, this
 * function is only available when @ref LIBRARY_LOG_LEVEL is #IOT_LOG_DEBUG.
 *
 * In most cases, the library-specific buffer logging function @ref
 * logging_function_printbuffer should be called instead of this function.
 *
 * @param[in] pLibraryName The library name to print with the log. See @ref LIBRARY_LOG_NAME.
 * @param[in] pHeader A message to print before printing the buffer.
 * @param[in] pBuffer The buffer to print.
 * @param[in] bufferSize The number of bytes in `pBuffer` to print.
 *
 * @return No return value. On errors, it prints nothing.
 *
 * @note To conserve memory, this function only allocates enough memory for a
 * single line of output. Therefore, in multithreaded systems, its output may
 * appear "fragmented" if other threads are logging simultaneously.
 */
/* @[declare_logging_genericprintbuffer] */
void IotLog_GenericPrintBuffer( const char * const pLibraryName,
                                const char * const pHeader,
                                const uint8_t * const pBuffer,
                                size_t bufferSize );
/* @[declare_logging_genericprintbuffer] */

#endif /* ifndef IOT_LOGGING_H_ */
