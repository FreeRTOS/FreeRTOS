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

/* Standard includes. */
#include <assert.h>

#include "http_demo_utils.h"

/* Exponential backoff retry include. */
#include "backoff_algorithm.h"

/* Parser utilities. */
#include "http_parser.h"

/*-----------------------------------------------------------*/

/**
 * @brief The maximum number of retries for network operation with server.
 */
#define RETRY_MAX_ATTEMPTS            ( 5U )

/**
 * @brief The maximum back-off delay (in milliseconds) for retrying failed
 * operation with server.
 */
#define RETRY_MAX_BACKOFF_DELAY_MS    ( 5000U )

/**
 * @brief The base back-off delay (in milliseconds) to use for network operation
 * retry attempts.
 */
#define RETRY_BACKOFF_BASE_MS         ( 500U )

/*-----------------------------------------------------------*/

/** 
 * @brief Each compilation unit that consumes the NetworkContext must define it. 
 * It should contain a single pointer to the type of your desired transport.
 * This utility is used by both TLS and plaintext HTTP demos, so define this pointer as void *.
 *
 * @note Transport stacks are defined in FreeRTOS-Plus/Source/Application-Protocols/network_transport.
 */
struct NetworkContext
{
    void * pParams;
};

/*-----------------------------------------------------------*/

extern UBaseType_t uxRand();

/*-----------------------------------------------------------*/
BaseType_t connectToServerWithBackoffRetries( TransportConnect_t connectFunction,
                                              NetworkContext_t * pxNetworkContext )
{
    BaseType_t xReturn = pdFAIL;
    /* Status returned by the retry utilities. */
    BackoffAlgorithmStatus_t xBackoffAlgStatus = BackoffAlgorithmSuccess;
    /* Struct containing the next backoff time. */
    BackoffAlgorithmContext_t xReconnectParams;
    uint16_t usNextBackoff = 0U;

    assert( connectFunction != NULL );

    /* Initialize reconnect attempts and interval */
    BackoffAlgorithm_InitializeParams( &xReconnectParams,
                                       RETRY_BACKOFF_BASE_MS,
                                       RETRY_MAX_BACKOFF_DELAY_MS,
                                       RETRY_MAX_ATTEMPTS );

    /* Attempt to connect to the HTTP server. If connection fails, retry after a
     * timeout. The timeout value will exponentially increase until either the
     * maximum timeout value is reached or the set number of attempts are
     * exhausted.*/
    do
    {
        xReturn = connectFunction( pxNetworkContext );

        if( xReturn != pdPASS )
        {
            /* Generate a random number and calculate backoff value (in milliseconds) for
             * the next connection retry.
             * Note: It is recommended to seed the random number generator with a device-specific
             * entropy source so that possibility of multiple devices retrying failed network operations
             * at similar intervals can be avoided. */
            xBackoffAlgStatus = BackoffAlgorithm_GetNextBackoff( &xReconnectParams, uxRand(), &usNextBackoff );

            if( xBackoffAlgStatus == BackoffAlgorithmSuccess )
            {
                LogWarn( ( "Connection to the HTTP server failed. "
                           "Retrying connection with backoff and jitter." ) );
                LogInfo( ( "Retry attempt %lu out of maximum retry attempts %lu.",
                           xReconnectParams.attemptsDone,
                           RETRY_MAX_ATTEMPTS ) );
            }
        }
    } while( ( xReturn == pdFAIL ) && ( xBackoffAlgStatus == BackoffAlgorithmSuccess ) );

    if( xReturn == pdFAIL )
    {
        LogError( ( "Connection to the server failed, all attempts exhausted." ) );
    }

    return xReturn;
}

/*-----------------------------------------------------------*/

HTTPStatus_t getUrlPath( const char * pcUrl,
                         size_t xUrlLen,
                         const char ** pcPath,
                         size_t * pxPathLen )
{
    /* http-parser status. Initialized to 1 to signify failure. */
    int lParserStatus = 1;
    struct http_parser_url xUrlParser;
    HTTPStatus_t xHTTPStatus = HTTPSuccess;

    /* Sets all members in xUrlParser to 0. */
    http_parser_url_init( &xUrlParser );

    if( ( pcUrl == NULL ) || ( pcPath == NULL ) || ( pxPathLen == NULL ) )
    {
        LogError( ( "NULL parameter passed to getUrlPath()." ) );
        xHTTPStatus = HTTPInvalidParameter;
    }

    if( xHTTPStatus == HTTPSuccess )
    {
        lParserStatus = http_parser_parse_url( pcUrl, xUrlLen, 0, &xUrlParser );

        if( lParserStatus != 0 )
        {
            LogError( ( "Error parsing the input URL %.*s. Error code: %d.",
                        ( int32_t ) xUrlLen,
                        pcUrl,
                        lParserStatus ) );
            xHTTPStatus = HTTPParserInternalError;
        }
    }

    if( xHTTPStatus == HTTPSuccess )
    {
        *pxPathLen = ( size_t ) ( xUrlParser.field_data[ UF_PATH ].len );

        if( *pxPathLen == 0 )
        {
            xHTTPStatus = HTTPNoResponse;
            *pcPath = NULL;
        }
        else
        {
            *pcPath = &pcUrl[ xUrlParser.field_data[ UF_PATH ].off ];
        }
    }

    if( xHTTPStatus != HTTPSuccess )
    {
        LogError( ( "Error parsing the path from URL %s. Error code: %d",
                    pcUrl,
                    xHTTPStatus ) );
    }

    return xHTTPStatus;
}

/*-----------------------------------------------------------*/

HTTPStatus_t getUrlAddress( const char * pcUrl,
                            size_t xUrlLen,
                            const char ** pcAddress,
                            size_t * pxAddressLen )
{
    /* http-parser status. Initialized to 1 to signify failure. */
    int lParserStatus = 1;
    struct http_parser_url xUrlParser;
    HTTPStatus_t xHTTPStatus = HTTPSuccess;

    /* Sets all members in xUrlParser to 0. */
    http_parser_url_init( &xUrlParser );

    if( ( pcUrl == NULL ) || ( pcAddress == NULL ) || ( pxAddressLen == NULL ) )
    {
        LogError( ( "NULL parameter passed to getUrlAddress()." ) );
        xHTTPStatus = HTTPInvalidParameter;
    }

    if( xHTTPStatus == HTTPSuccess )
    {
        lParserStatus = http_parser_parse_url( pcUrl, xUrlLen, 0, &xUrlParser );

        if( lParserStatus != 0 )
        {
            LogError( ( "Error parsing the input URL %.*s. Error code: %d.",
                        ( int32_t ) xUrlLen,
                        pcUrl,
                        lParserStatus ) );
            xHTTPStatus = HTTPParserInternalError;
        }
    }

    if( xHTTPStatus == HTTPSuccess )
    {
        *pxAddressLen = ( size_t ) ( xUrlParser.field_data[ UF_HOST ].len );

        if( *pxAddressLen == 0 )
        {
            xHTTPStatus = HTTPNoResponse;
            *pcAddress = NULL;
        }
        else
        {
            *pcAddress = &pcUrl[ xUrlParser.field_data[ UF_HOST ].off ];
        }
    }

    if( xHTTPStatus != HTTPSuccess )
    {
        LogError( ( "Error parsing the address from URL %s. Error code %d",
                    pcUrl,
                    xHTTPStatus ) );
    }

    return xHTTPStatus;
}
