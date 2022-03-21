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

#ifndef HTTP_DEMO_UTILS_H
#define HTTP_DEMO_UTILS_H

/* Standard includes. */
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* HTTP API header. */
#include "core_http_client.h"

/**
 * @brief Function pointer for establishing connection to a server.
 *
 * @param[out] pxNetworkContext Implementation-defined network context.
 *
 * @return pdFAIL on failure; pdPASS on successful connection.
 */
typedef BaseType_t ( * TransportConnect_t )( NetworkContext_t * pxNetworkContext );

/**
 * @brief Connect to a server with reconnection retries.
 *
 * If connection fails, retry is attempted after a timeout. The timeout value
 * will exponentially increase until either the maximum timeout value is reached
 * or the set number of attempts are exhausted.
 *
 * @param[in] connectFunction Function pointer for establishing connection to a
 * server.
 * @param[out] pxNetworkContext Implementation-defined network context.
 *
 * @return pdFAIL on failure; pdPASS on successful connection.
 */
BaseType_t connectToServerWithBackoffRetries( TransportConnect_t connectFunction,
                                              NetworkContext_t * pxNetworkContext );

/**
 * @brief Retrieve the path from the input URL.
 *
 * This function retrieves the location and length of the path from within the
 * input the URL. The query is not included in the length returned.
 *
 * The URL MUST start with "http://" or "https://" to find the path.
 *
 * For example, if pcUrl is:
 * "https://www.somewebsite.com/path/to/item.txt?optionalquery=stuff"
 *
 * Then pcPath and pxPathLen will be the following:
 * *pcPath = "/path/to/item.txt?optionalquery=stuff"
 * *pxPathLen = 17
 *
 * @param[in] pcUrl URL string to parse.
 * @param[in] xUrlLen The length of the URL string input.
 * @param[out] pcPath pointer within input url that the path starts at.
 * @param[out] pxPathLen Length of the path.
 *
 * @return The status of the parsing attempt:
 * HTTPSuccess if the path was successfully parsed,
 * HTTPParserInternalError if there was an error parsing the URL,
 * or HTTPNoResponse if the path was not found.
 */
HTTPStatus_t getUrlPath( const char * pcUrl,
                         size_t xUrlLen,
                         const char ** pcPath,
                         size_t * pxPathLen );

/**
 * @brief Retrieve the Address from the input URL.
 *
 * This function retrieves the location and length of the address from within
 * the input URL. The path and query are not included in the length returned.
 *
 * The URL MUST start with "http://" or "https://" to find the address.
 *
 * For example, if pcUrl is:
 * "https://www.somewebsite.com/path/to/item.txt?optionalquery=stuff"
 *
 * Then pcAddress and pxAddressLen will be the following:
 * *pcAddress = "www.somewebsite.com/path/to/item.txt?optionalquery=stuff"
 * *pxAddressLen = 19
 *
 * @param[in] pcUrl URL string to parse.
 * @param[in] xUrlLen The length of the URL string input.
 * @param[out] pcAddress pointer within input url that the address starts at.
 * @param[out] pxAddressLen Length of the address.
 *
 * @return The status of the parsing attempt:
 * HTTPSuccess if the path was successfully parsed,
 * HTTPParserInternalError if there was an error parsing the URL,
 * or HTTPNoResponse if the path was not found.
 */
HTTPStatus_t getUrlAddress( const char * pcUrl,
                            size_t xUrlLen,
                            const char ** pcAddress,
                            size_t * pxAddressLen );

#endif /* ifndef HTTP_DEMO_UTILS_H */
