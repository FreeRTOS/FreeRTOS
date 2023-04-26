/*
 * FreeRTOS V202212.00
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

/**
 * @brief The separator between the "https" scheme and the host in a URL.
 */
#define SCHEME_SEPARATOR              "://"

/**
 * @brief The length of the "://" separator.
 */
#define SCHEME_SEPARATOR_LEN          ( sizeof( SCHEME_SEPARATOR ) - 1 )

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
    HTTPStatus_t xHttpStatus = HTTPSuccess;
    const char * pcHostStart = NULL;
    const char * pcPathStart = NULL;
    size_t xHostLen = 0, i = 0, xPathStartIndex = 0, xPathLen = 0;

    if( ( pcUrl == NULL ) || ( pcPath == NULL ) || ( pxPathLen == NULL ) )
    {
        LogError( ( "NULL parameter passed to getUrlPath()." ) );
        xHttpStatus = HTTPInvalidParameter;
    }

    if( xHttpStatus == HTTPSuccess )
    {
        xHttpStatus = getUrlAddress( pcUrl, xUrlLen, &pcHostStart, &xHostLen );
    }

    if( xHttpStatus == HTTPSuccess )
    {
        /* Search for the start of the path. */
        for( i = ( pcHostStart - pcUrl ) + xHostLen; i < xUrlLen; i++ )
        {
            if( pcUrl[ i ] == '/' )
            {
                pcPathStart = &pcUrl[ i ];
                xPathStartIndex = i;
                break;
            }
        }

        if( pcPathStart != NULL )
        {
            /* The end of the path will be either the start of the query,
             * start of the fragment, or end of the URL. If this is an S3
             * presigned URL, then there must be a query. */
            for( i = xPathStartIndex; i < xUrlLen; i++ )
            {
                if( pcUrl[ i ] == '?' )
                {
                    break;
                }
            }

            xPathLen = i - xPathStartIndex;
        }

        if( xPathLen == 0 )
        {
            LogError( ( "Could not parse path from input URL %.*s",
                        ( int32_t ) xUrlLen,
                        pcUrl ) );
            xHttpStatus = HTTPNoResponse;
        }
    }

    if( xHttpStatus == HTTPSuccess )
    {
        *pxPathLen = xPathLen;
        *pcPath = pcPathStart;
    }

    if( xHttpStatus != HTTPSuccess )
    {
        LogError( ( "Error parsing the path from URL %s. Error code: %d",
                    pcUrl,
                    xHttpStatus ) );
    }

    return xHttpStatus;
}

/*-----------------------------------------------------------*/

HTTPStatus_t getUrlAddress( const char * pcUrl,
                            size_t xUrlLen,
                            const char ** pcAddress,
                            size_t * pxAddressLen )
{
    HTTPStatus_t xHttpStatus = HTTPSuccess;
    const char * pcHostStart = NULL;
    const char * pcHostEnd = NULL;
    size_t i = 0, xHostLen = 0;

    if( ( pcUrl == NULL ) || ( pcAddress == NULL ) || ( pxAddressLen == NULL ) )
    {
        LogError( ( "NULL parameter passed to getUrlAddress()." ) );
        xHttpStatus = HTTPInvalidParameter;
    }

    if( xHttpStatus == HTTPSuccess )
    {
        /* Search for the start of the hostname using the "://" separator. */
        for( i = 0; i < ( xUrlLen - SCHEME_SEPARATOR_LEN ); i++ )
        {
            if( strncmp( &( pcUrl[ i ] ), SCHEME_SEPARATOR, SCHEME_SEPARATOR_LEN ) == 0 )
            {
                pcHostStart = pcUrl + i + SCHEME_SEPARATOR_LEN;
                break;
            }
        }

        if( pcHostStart == NULL )
        {
            LogError( ( "Could not find \"://\" scheme separator in input URL %.*s",
                        ( int32_t ) xUrlLen,
                        pcUrl ) );
            xHttpStatus = HTTPParserInternalError;
        }
        else
        {
            /* Search for the end of the hostname assuming that the object path
             * is next. Assume that there is no port number as this is used for
             * S3 presigned URLs. */
            for( pcHostEnd = pcHostStart; pcHostEnd < ( pcUrl + xUrlLen ); pcHostEnd++ )
            {
                if( *pcHostEnd == '/' )
                {
                    xHostLen = ( size_t ) ( pcHostEnd - pcHostStart );
                    break;
                }
            }
        }
    }

    if( xHttpStatus == HTTPSuccess )
    {
        *pxAddressLen = xHostLen;

        if( xHostLen == 0 )
        {
            LogError( ( "Could not find end of host in input URL %.*s",
                        ( int32_t ) xUrlLen,
                        pcUrl ) );
            xHttpStatus = HTTPNoResponse;
            *pcAddress = NULL;
        }
        else
        {
            *pcAddress = pcHostStart;
        }
    }

    if( xHttpStatus != HTTPSuccess )
    {
        LogError( ( "Error parsing the address from URL %s. Error code %d",
                    pcUrl,
                    xHttpStatus ) );
    }

    return xHttpStatus;
}
