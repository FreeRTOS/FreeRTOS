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
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

/**
 * @file mbedtls_error.h
 * @brief Stringification utilities for high-level and low-level codes of mbed TLS.
 */

#ifndef MBEDTLS_ERROR_H_
    #define MBEDTLS_ERROR_H_

    #include <stdint.h>

    #ifdef __cplusplus
        extern "C" {
    #endif

/**
 * @brief Translate an mbed TLS high level code into its string representation.
 *        Result includes a terminating null byte.
 *
 * @param errnum The error code containing the high-level code.
 * @return The string representation if high-level code is present; otherwise NULL.
 *
 * @warning The string returned by this function must never be modified.
 */
    const char * mbedtls_strerror_highlevel( int32_t errnum );

/**
 * @brief Translate an mbed TLS low level code into its string representation,
 *        Result includes a terminating null byte.
 *
 * @param errnum The error code containing the low-level code.
 * @return The string representation if low-level code is present; otherwise NULL.
 *
 * @warning The string returned by this function must never be modified.
 */
    const char * mbedtls_strerror_lowlevel( int32_t errnum );

    #ifdef __cplusplus
}
    #endif

#endif /* ifndef MBEDTLS_ERROR_H_ */
