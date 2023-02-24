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
 * @file logging_levels.h
 * @brief Defines the configuration constants for all logging verbosity levels.
 */

#ifndef LOGGING_LEVELS_H
#define LOGGING_LEVELS_H

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
 * - #LOG_NONE <br>
 *   @copybrief LOG_NONE
 * - #LOG_ERROR <br>
 *   @copybrief LOG_ERROR
 * - #LOG_WARN <br>
 *   @copybrief LOG_WARN
 * - #LOG_INFO <br>
 *   @copybrief LOG_INFO
 * - #LOG_DEBUG <br>
 *   @copybrief LOG_DEBUG
 */

/**
 * @brief No log messages.
 *
 * When @ref LIBRARY_LOG_LEVEL is #LOG_NONE, logging is disabled and no
 * logging messages are printed.
 */
#define LOG_NONE     0

/**
 * @brief Represents erroneous application state or event.
 *
 * These messages describe the situations when a library encounters an error from
 * which it cannot recover.
 *
 * These messages are printed when @ref LIBRARY_LOG_LEVEL is defined as either
 * of #LOG_ERROR, #LOG_WARN, #LOG_INFO or #LOG_DEBUG.
 */
#define LOG_ERROR    1

/**
 * @brief Message about an abnormal event.
 *
 * These messages describe the situations when a library encounters
 * abnormal event that may be indicative of an error. Libraries continue
 * execution after logging a warning.
 *
 * These messages are printed when @ref LIBRARY_LOG_LEVEL is defined as either
 * of #LOG_WARN, #LOG_INFO or #LOG_DEBUG.
 */
#define LOG_WARN     2

/**
 * @brief A helpful, informational message.
 *
 * These messages describe normal execution of a library. They provide
 * the progress of the program at a coarse-grained level.
 *
 * These messages are printed when @ref LIBRARY_LOG_LEVEL is defined as either
 * of #LOG_INFO or #LOG_DEBUG.
 */
#define LOG_INFO     3

/**
 * @brief Detailed and excessive debug information.
 *
 * Debug log messages are used to provide the
 * progress of the program at a fine-grained level. These are mostly used
 * for debugging and may contain excessive information such as internal
 * variables, buffers, or other specific information.
 *
 * These messages are only printed when @ref LIBRARY_LOG_LEVEL is defined as
 * #LOG_DEBUG.
 */
#define LOG_DEBUG    4

#endif /* ifndef LOGGING_LEVELS_H */
