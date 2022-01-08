/*
 * FreeRTOS V202112.00
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

#ifndef TEST_CONFIG_H
#define TEST_CONFIG_H

/**
 * @brief test cellular APIs.
 */
#define testCELLULAR_API                                       ( 1 )

/**
 * DNS server address.
 * #define testCELLULAR_DNS_SERVER_ADDRESS  "...insert here..."
 */

/**
 * Host name to resolve. The host name should only has one IP address.
 * #define testCELLULAR_HOST_NAME  "...insert here..."
 */

/**
 * Host name resolved address. The resolved address should be the IP address of
 * testCELLULAR_HOST_NAME.
 * #define testCELLULAR_HOST_NAME_ADDRESS  "...insert here..."
 */

/**
 * Echo server address for tcp connection test.
 * #define testCELLULAR_ECHO_SERVER_ADDRESS  "...insert here..."
 */

/**
 * Echo server port for tcp connection test.
 * #define testCELLULAR_ECHO_SERVER_PORT  ( ...insert here... )
 */

/**
 * Repeat echo server address for EDRX echo times test.
 * #define testCELLULAR_EDRX_ECHO_SERVER_ADDRESS  "...insert here..."
 */

/**
 * Repeat echo server port for EDRX echo times test.
 * #define testCELLULAR_EDRX_ECHO_SERVER_PORT  ( ...insert here... )
 */

/**
 * Repeat echo server send interfal for EDRX echo times test.
 * This settings should align with your repeat echo server settings.
 * #define testCELLULAR_EDRX_ECHO_SERVER_DATA_SEND_INTERVAL_MS  ( ...insert here... )
 */


#define testconfigTEST_STACKSIZE                               ( 1024 )

#define testconfigTEST_PRIORITY                                ( tskIDLE_PRIORITY + 1 )

/* UNITY test config. */
#define UNITY_EXCLUDE_SETJMP_H

#endif /* TEST_CONFIG_H */
