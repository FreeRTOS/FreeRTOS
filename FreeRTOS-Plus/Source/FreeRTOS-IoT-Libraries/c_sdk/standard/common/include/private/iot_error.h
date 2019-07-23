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
 * @file iot_error.h
 * @brief Provides macros for error checking and function cleanup.
 *
 * The macros in this file are generic. They may be customized by each library
 * by setting the library prefix.
 */

#ifndef IOT_ERROR_H_
#define IOT_ERROR_H_

/* The config header is always included first. */
#include "iot_config.h"

/**
 * @brief Declare the status variable and an initial value.
 *
 * This macro should be at the beginning of any functions that use cleanup sections.
 *
 * @param[in] statusType The type of the status variable for this function.
 * @param[in] initialValue The initial value to assign to the status variable.
 */
#define IOT_FUNCTION_ENTRY( statusType, initialValue )    statusType status = initialValue

/**
 * @brief Declares the label that begins a cleanup section.
 *
 * This macro should be placed at the end of a function and followed by
 * #IOT_FUNCTION_CLEANUP_END.
 */
#define IOT_FUNCTION_CLEANUP_BEGIN()                      iotCleanup:

/**
 * @brief Declares the end of a cleanup section.
 *
 * This macro should be placed at the end of a function and preceded by
 * #IOT_FUNCTION_CLEANUP_BEGIN.
 */
#define IOT_FUNCTION_CLEANUP_END()                        return status

/**
 * @brief Declares an empty cleanup section.
 *
 * This macro should be placed at the end of a function to exit on error if no
 * cleanup is required.
 */
#define IOT_FUNCTION_EXIT_NO_CLEANUP()                    IOT_FUNCTION_CLEANUP_BEGIN(); IOT_FUNCTION_CLEANUP_END()

/**
 * @brief Jump to the cleanup section.
 */
#define IOT_GOTO_CLEANUP()                                goto iotCleanup

/**
 * @brief Assign a value to the status variable and jump to the cleanup section.
 *
 * @param[in] statusValue The value to assign to the status variable.
 */
#define IOT_SET_AND_GOTO_CLEANUP( statusValue )           { status = ( statusValue ); IOT_GOTO_CLEANUP(); }

/**
 * @brief Jump to the cleanup section if a condition is `false`.
 *
 * This macro may be used in place of `assert` to exit a function is a condition
 * is `false`.
 *
 * @param[in] condition The condition to check.
 */
#define IOT_GOTO_CLEANUP_IF_FALSE( condition )            { if( ( condition ) == false ) { IOT_GOTO_CLEANUP(); } }

/**
 * @brief Assign a value to the status variable and jump to the cleanup section
 * if a condition is `false`.
 *
 * @param[in] statusValue The value to assign to the status variable.
 * @param[in] condition The condition to check.
 */
#define IOT_SET_AND_GOTO_CLEANUP_IF_FALSE( statusValue, condition ) \
    if( ( condition ) == false )                                    \
        IOT_SET_AND_GOTO_CLEANUP( statusValue )

/**
 * @brief Check a condition; if `false`, assign the "Bad parameter" status value
 * and jump to the cleanup section.
 *
 * @param[in] libraryPrefix The library prefix of the status variable.
 * @param[in] condition The condition to check.
 */
#define IOT_VALIDATE_PARAMETER( libraryPrefix, condition ) \
    IOT_SET_AND_GOTO_CLEANUP_IF_FALSE( libraryPrefix ## _BAD_PARAMETER, condition )

#endif /* ifndef IOT_ERROR_H_ */
