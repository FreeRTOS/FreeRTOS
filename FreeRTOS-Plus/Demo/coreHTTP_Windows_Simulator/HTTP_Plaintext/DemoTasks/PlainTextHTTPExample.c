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

/*
 * Demo for showing use of the HTTP API using a plaintext network connection.
 *
 * This example resolves a domain, then establishes a TCP connection with an
 * HTTP server to demonstrate HTTP request/response communication without using
 * an encrypted channel (i.e. without TLS). After which, HTTP Client library API
 * is used to send a GET, HEAD, PUT, and POST request in that order. For each
 * request, the HTTP response from the server (or an error code) is logged.
 *
 * This example uses a single task.
 */

/**
 * @file PlainTextHTTPExample.c
 * @brief Demonstrates usage of the HTTP library.
 */

/* Standard includes. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo Specific configs. */
#include "demo_config.h"

/* HTTP library includes. */
#include "core_http_client.h"

/* Transport interface implementation include for plaintext communication. */
#include "using_plaintext.h"

/* Common HTTP demo utilities. */
#include "http_demo_utils.h"

/*------------- Demo configurations -------------------------*/

/* Check that the hostname of the server is defined. */
#ifndef democonfigSERVER_HOSTNAME
    #error "Please define democonfigSERVER_HOSTNAME in demo_config.h."
#endif

/* Check that the hostname of the server is defined. */
#ifndef democonfigHTTP_PORT
    #error "Please define democonfigHTTP_PORT in demo_config.h."
#endif

/* Check that a path for HTTP Method GET is defined. */
#ifndef democonfigGET_PATH
    #error "Please define democonfigGET_PATH in demo_config.h."
#endif

/* Check that a path for HTTP Method HEAD is defined. */
#ifndef democonfigHEAD_PATH
    #error "Please define democonfigHEAD_PATH in demo_config.h."
#endif

/* Check that a path for HTTP Method PUT is defined. */
#ifndef democonfigPUT_PATH
    #error "Please define democonfigPUT_PATH in demo_config.h."
#endif

/* Check that a path for HTTP Method POST is defined. */
#ifndef democonfigPOST_PATH
    #error "Please define democonfigPOST_PATH in demo_config.h."
#endif

/* Check that a request body to send for the POST request is defined. */
#ifndef democonfigREQUEST_BODY
    #error "Please define a democonfigREQUEST_BODY in demo_config.h."
#endif

/* Check that a transport timeout for transport send and receive is defined. */
#ifndef democonfigTRANSPORT_SEND_RECV_TIMEOUT_MS
    #define democonfigTRANSPORT_SEND_RECV_TIMEOUT_MS    ( 1000 )
#endif

/* Check that a size for the user buffer is defined. */
#ifndef democonfigUSER_BUFFER_LENGTH
    #define democonfigUSER_BUFFER_LENGTH    ( 2048 )
#endif

/**
 * @brief The length of the server's hostname.
 */
#define httpexampleSERVER_HOSTNAME_LENGTH     ( sizeof( democonfigSERVER_HOSTNAME ) - 1 )

/**
 * @brief The length of the HTTP GET method.
 */
#define httpexampleHTTP_METHOD_GET_LENGTH     ( sizeof( HTTP_METHOD_GET ) - 1 )

/**
 * @brief The length of the HTTP HEAD method.
 */
#define httpexampleHTTP_METHOD_HEAD_LENGTH    ( sizeof( HTTP_METHOD_HEAD ) - 1 )

/**
 * @brief The length of the HTTP PUT method.
 */
#define httpexampleHTTP_METHOD_PUT_LENGTH     ( sizeof( HTTP_METHOD_PUT ) - 1 )

/**
 * @brief The length of the HTTP POST method.
 */
#define httpexampleHTTP_METHOD_POST_LENGTH    ( sizeof( HTTP_METHOD_POST ) - 1 )

/**
 * @brief The length of the HTTP GET path.
 */
#define httpexampleGET_PATH_LENGTH            ( sizeof( democonfigGET_PATH ) - 1 )

/**
 * @brief The length of the HTTP HEAD path.
 */
#define httpexampleHEAD_PATH_LENGTH           ( sizeof( democonfigHEAD_PATH ) - 1 )

/**
 * @brief The length of the HTTP PUT path.
 */
#define httpexamplePUT_PATH_LENGTH            ( sizeof( democonfigPUT_PATH ) - 1 )

/**
 * @brief The length of the HTTP POST path.
 */
#define httpexamplePOST_PATH_LENGTH           ( sizeof( democonfigPOST_PATH ) - 1 )

/**
 * @brief Length of the request body.
 */
#define httpexampleREQUEST_BODY_LENGTH        ( sizeof( democonfigREQUEST_BODY ) - 1 )

/**
 * @brief Number of HTTP paths to request.
 */
#define httpexampleNUMBER_HTTP_PATHS          ( 4 )

/** 
 * @brief Each compilation unit that consumes the NetworkContext must define it. 
 * It should contain a single pointer to the type of your desired transport.
 * When using multiple transports in the same compilation unit, define this pointer as void *.
 *
 * @note Transport stacks are defined in FreeRTOS-Plus/Source/Application-Protocols/network_transport.
 */
struct NetworkContext
{
    PlaintextTransportParams_t * pParams;
};

/**
 * @brief The maximum number of times to run the loop in this demo.
 *
 * @note The demo loop is attempted to re-run only if it fails in an iteration.
 * Once the demo loop succeeds in an iteration, the demo exits successfully.
 */
#ifndef HTTP_MAX_DEMO_LOOP_COUNT
    #define HTTP_MAX_DEMO_LOOP_COUNT    ( 3 )
#endif

/**
 * @brief Time in ticks to wait between retries of the demo loop if
 * demo loop fails.
 */
#define DELAY_BETWEEN_DEMO_RETRY_ITERATIONS_TICKS    ( pdMS_TO_TICKS( 5000U ) )

/**
 * @brief A pair containing a path string of the URI and its length.
 */
typedef struct httpPathStrings
{
    const char * pcHttpPath;
    size_t ulHttpPathLength;
} httpPathStrings_t;

/**
 * @brief A pair containing an HTTP method string and its length.
 */
typedef struct httpMethodStrings
{
    const char * pcHttpMethod;
    size_t ulHttpMethodLength;
} httpMethodStrings_t;

/**
 * @brief A buffer used in the demo for storing HTTP request headers and
 * HTTP response headers and body.
 *
 * @note This demo shows how the same buffer can be re-used for storing the HTTP
 * response after the HTTP request is sent out. However, the user can also
 * decide to use separate buffers for storing the HTTP request and response.
 */
static uint8_t ucUserBuffer[ democonfigUSER_BUFFER_LENGTH ];

/*-----------------------------------------------------------*/

/**
 * @brief The task used to demonstrate the HTTP API.
 *
 * @param[in] pvParameters Parameters as passed at the time of task creation. Not
 * used in this example.
 */
static void prvHTTPDemoTask( void * pvParameters );


/**
 * @brief Connect to HTTP server with reconnection retries.
 *
 * @param[out] pxNetworkContext The output parameter to return the created network context.
 *
 * @return pdPASS on successful connection, pdFAIL otherwise.
 */
static BaseType_t prvConnectToServer( NetworkContext_t * pxNetworkContext );

/**
 * @brief Send an HTTP request based on a specified method and path, then
 * print the response received from the server.
 *
 * @param[in] pxTransportInterface The transport interface for making network calls.
 * @param[in] pcMethod The HTTP request method.
 * @param[in] xMethodLen The length of the HTTP request method.
 * @param[in] pcPath The Request-URI to the objects of interest.
 * @param[in] xPathLen The length of the Request-URI.
 *
 * @return pdFAIL on failure; pdPASS on success.
 */
static BaseType_t prvSendHttpRequest( const TransportInterface_t * pxTransportInterface,
                                      const char * pcMethod,
                                      size_t xMethodLen,
                                      const char * pcPath,
                                      size_t xPathLen );

/*-----------------------------------------------------------*/

/*
 * @brief Create the task that demonstrates the HTTP API Demo over a
 * mutually-authenticated network connection with an HTTP server.
 */
void vStartSimpleHTTPDemo( void )
{
    /* This example uses a single application task, which in turn is used to
     * connect, send requests, receive responses, and disconnect from the HTTP
     * server */
    xTaskCreate( prvHTTPDemoTask,          /* Function that implements the task. */
                 "DemoTask",               /* Text name for the task - only used for debugging. */
                 democonfigDEMO_STACKSIZE, /* Size of stack (in words, not bytes) to allocate for the task. */
                 NULL,                     /* Task parameter - not used in this case. */
                 tskIDLE_PRIORITY,         /* Task priority, must be between 0 and configMAX_PRIORITIES - 1. */
                 NULL );                   /* Used to pass out a handle to the created task - not used in this case. */
}

/*-----------------------------------------------------------*/

/**
 * @brief Entry point of the demo.
 *
 * This example resolves a domain, then establishes a TCP connection with an
 * HTTP server to demonstrate HTTP request/response communication without using
 * an encrypted channel (i.e. without TLS). After which, HTTP Client library API
 * is used to send a GET, HEAD, PUT, and POST request in that order. For each
 * request, the HTTP response from the server (or an error code) is logged.
 *
 * @note This example uses a single task.
 *
 */
static void prvHTTPDemoTask( void * pvParameters )
{
    /* The transport layer interface used by the HTTP Client library. */
    TransportInterface_t xTransportInterface;
    /* The network context for the transport layer interface. */
    NetworkContext_t xNetworkContext = { 0 };
    PlaintextTransportParams_t xPlaintextTransportParams = { 0 };
    /* An array of HTTP paths to request. */
    const httpPathStrings_t xHttpMethodPaths[] =
    {
        { democonfigGET_PATH,  httpexampleGET_PATH_LENGTH  },
        { democonfigHEAD_PATH, httpexampleHEAD_PATH_LENGTH },
        { democonfigPUT_PATH,  httpexamplePUT_PATH_LENGTH  },
        { democonfigPOST_PATH, httpexamplePOST_PATH_LENGTH }
    };
    /* The respective method for the HTTP paths listed in #httpMethodPaths. */
    const httpMethodStrings_t xHttpMethods[] =
    {
        { HTTP_METHOD_GET,  httpexampleHTTP_METHOD_GET_LENGTH  },
        { HTTP_METHOD_HEAD, httpexampleHTTP_METHOD_HEAD_LENGTH },
        { HTTP_METHOD_PUT,  httpexampleHTTP_METHOD_PUT_LENGTH  },
        { HTTP_METHOD_POST, httpexampleHTTP_METHOD_POST_LENGTH }
    };
    BaseType_t xIsConnectionEstablished = pdFALSE;
    UBaseType_t uxHttpPathCount = 0U;
    UBaseType_t uxDemoRunCount = 0UL;

    /* The user of this demo must check the logs for any failure codes. */
    BaseType_t xDemoStatus = pdPASS;

    /* Remove compiler warnings about unused parameters. */
    ( void ) pvParameters;

    /* Set the pParams member of the network context with desired transport. */
    xNetworkContext.pParams = &xPlaintextTransportParams;

    /* This demo runs a single loop unless there are failures in the demo execution.
     * In case of failures in the demo execution, demo loop will be retried for up to
     * HTTP_MAX_DEMO_LOOP_COUNT times. */
    do
    {
        /**************************** Connect. ******************************/

        /* Attempt to connect to the HTTP server. If connection fails, retry after a
         * timeout. The timeout value will be exponentially increased until either the
         * maximum number of attempts or the maximum timeout value is reached. The
         * function returns pdFAIL if the TCP connection cannot be established with
         * the server after the number of attempts. */
        xDemoStatus = connectToServerWithBackoffRetries( prvConnectToServer,
                                                         &xNetworkContext );

        if( xDemoStatus == pdPASS )
        {
            /* Set a flag indicating that a TCP connection has been established. */
            xIsConnectionEstablished = pdTRUE;

            /* Define the transport interface. */
            xTransportInterface.pNetworkContext = &xNetworkContext;
            xTransportInterface.send = Plaintext_FreeRTOS_send;
            xTransportInterface.recv = Plaintext_FreeRTOS_recv;
        }
        else
        {
            /* Log error to indicate connection failure after all
             * reconnect attempts are over. */
            LogError( ( "Failed to connect to HTTP server %.*s.",
                        ( int32_t ) httpexampleSERVER_HOSTNAME_LENGTH,
                        democonfigSERVER_HOSTNAME ) );
        }

        /*********************** Send HTTP request.************************/

        for( uxHttpPathCount = 0; uxHttpPathCount < httpexampleNUMBER_HTTP_PATHS; ++uxHttpPathCount )
        {
            if( xDemoStatus == pdPASS )
            {
                xDemoStatus = prvSendHttpRequest( &xTransportInterface,
                                                  xHttpMethods[ uxHttpPathCount ].pcHttpMethod,
                                                  xHttpMethods[ uxHttpPathCount ].ulHttpMethodLength,
                                                  xHttpMethodPaths[ uxHttpPathCount ].pcHttpPath,
                                                  xHttpMethodPaths[ uxHttpPathCount ].ulHttpPathLength );
            }
            else
            {
                break;
            }
        }

        /**************************** Disconnect. ******************************/

        /* Close the network connection to clean up any system resources that the
         * demo may have consumed. */
        if( xIsConnectionEstablished == pdTRUE )
        {
            /* Close the network connection.  */
            Plaintext_FreeRTOS_Disconnect( &xNetworkContext );
        }

        /*********************** Retry in case of failure. ************************/

        /* Increment the demo run count. */
        uxDemoRunCount++;

        if( xDemoStatus == pdPASS )
        {
            LogInfo( ( "Demo iteration %lu was successful.", uxDemoRunCount ) );
        }
        /* Attempt to retry a failed demo iteration for up to #HTTP_MAX_DEMO_LOOP_COUNT times. */
        else if( uxDemoRunCount < HTTP_MAX_DEMO_LOOP_COUNT )
        {
            LogWarn( ( "Demo iteration %lu failed. Retrying...", uxDemoRunCount ) );
            vTaskDelay( DELAY_BETWEEN_DEMO_RETRY_ITERATIONS_TICKS );
        }
        /* Failed all #HTTP_MAX_DEMO_LOOP_COUNT demo iterations. */
        else
        {
            LogError( ( "All %d demo iterations failed.", HTTP_MAX_DEMO_LOOP_COUNT ) );
            break;
        }
    } while( xDemoStatus != pdPASS );

    if( xDemoStatus == pdPASS )
    {
        LogInfo( ( "prvHTTPDemoTask() completed successfully. "
                   "Total free heap is %u.\r\n",
                   xPortGetFreeHeapSize() ) );
        LogInfo( ( "Demo completed successfully.\r\n" ) );
        vTaskDelete( NULL );
    }
}

/*-----------------------------------------------------------*/

static BaseType_t prvConnectToServer( NetworkContext_t * pxNetworkContext )
{
    BaseType_t xStatus = pdPASS;

    PlaintextTransportStatus_t xNetworkStatus;

    configASSERT( pxNetworkContext != NULL );

    /* Establish a TCP connection with the HTTP server. This example connects to
     * the HTTP server as specified in democonfigSERVER_HOSTNAME and
     * democonfigHTTP_PORT in demo_config.h. */
    LogInfo( ( "Establishing a TCP connection to %.*s:%d.",
               ( int32_t ) httpexampleSERVER_HOSTNAME_LENGTH,
               democonfigSERVER_HOSTNAME,
               democonfigHTTP_PORT ) );
    xNetworkStatus = Plaintext_FreeRTOS_Connect( pxNetworkContext,
                                                 democonfigSERVER_HOSTNAME,
                                                 democonfigHTTP_PORT,
                                                 democonfigTRANSPORT_SEND_RECV_TIMEOUT_MS,
                                                 democonfigTRANSPORT_SEND_RECV_TIMEOUT_MS );

    if( xNetworkStatus != PLAINTEXT_TRANSPORT_SUCCESS )
    {
        xStatus = pdFAIL;
    }

    return xStatus;
}

/*-----------------------------------------------------------*/

static BaseType_t prvSendHttpRequest( const TransportInterface_t * pxTransportInterface,
                                      const char * pcMethod,
                                      size_t xMethodLen,
                                      const char * pcPath,
                                      size_t xPathLen )
{
    /* Return value of this method. */
    BaseType_t xStatus = pdPASS;

    /* Configurations of the initial request headers that are passed to
     * #HTTPClient_InitializeRequestHeaders. */
    HTTPRequestInfo_t xRequestInfo;
    /* Represents a response returned from an HTTP server. */
    HTTPResponse_t xResponse;
    /* Represents header data that will be sent in an HTTP request. */
    HTTPRequestHeaders_t xRequestHeaders;

    /* Return value of all methods from the HTTP Client library API. */
    HTTPStatus_t xHTTPStatus = HTTPSuccess;

    configASSERT( pcMethod != NULL );
    configASSERT( pcPath != NULL );

    /* Initialize all HTTP Client library API structs to 0. */
    ( void ) memset( &xRequestInfo, 0, sizeof( xRequestInfo ) );
    ( void ) memset( &xResponse, 0, sizeof( xResponse ) );
    ( void ) memset( &xRequestHeaders, 0, sizeof( xRequestHeaders ) );

    /* Initialize the request object. */
    xRequestInfo.pHost = democonfigSERVER_HOSTNAME;
    xRequestInfo.hostLen = httpexampleSERVER_HOSTNAME_LENGTH;
    xRequestInfo.pMethod = pcMethod;
    xRequestInfo.methodLen = xMethodLen;
    xRequestInfo.pPath = pcPath;
    xRequestInfo.pathLen = xPathLen;

    /* Set "Connection" HTTP header to "keep-alive" so that multiple requests
     * can be sent over the same established TCP connection. */
    xRequestInfo.reqFlags = HTTP_REQUEST_KEEP_ALIVE_FLAG;

    /* Set the buffer used for storing request headers. */
    xRequestHeaders.pBuffer = ucUserBuffer;
    xRequestHeaders.bufferLen = democonfigUSER_BUFFER_LENGTH;

    xHTTPStatus = HTTPClient_InitializeRequestHeaders( &xRequestHeaders,
                                                       &xRequestInfo );

    if( xHTTPStatus == HTTPSuccess )
    {
        /* Initialize the response object. The same buffer used for storing
         * request headers is reused here. */
        xResponse.pBuffer = ucUserBuffer;
        xResponse.bufferLen = democonfigUSER_BUFFER_LENGTH;

        LogInfo( ( "Sending HTTP %.*s request to %.*s%.*s...",
                   ( int32_t ) xRequestInfo.methodLen, xRequestInfo.pMethod,
                   ( int32_t ) httpexampleSERVER_HOSTNAME_LENGTH, democonfigSERVER_HOSTNAME,
                   ( int32_t ) xRequestInfo.pathLen, xRequestInfo.pPath ) );
        LogInfo( ( "Request Headers:\n%.*s\n"
                   "Request Body:\n%.*s\n",
                   ( int32_t ) xRequestHeaders.headersLen,
                   ( char * ) xRequestHeaders.pBuffer,
                   ( int32_t ) httpexampleREQUEST_BODY_LENGTH, democonfigREQUEST_BODY ) );

        /* Send the request and receive the response. */
        xHTTPStatus = HTTPClient_Send( pxTransportInterface,
                                       &xRequestHeaders,
                                       ( uint8_t * ) democonfigREQUEST_BODY,
                                       httpexampleREQUEST_BODY_LENGTH,
                                       &xResponse,
                                       0 );
    }
    else
    {
        LogError( ( "Failed to initialize HTTP request headers: Error=%s.",
                    HTTPClient_strerror( xHTTPStatus ) ) );
    }

    if( xHTTPStatus == HTTPSuccess )
    {
        LogInfo( ( "Received HTTP response from %.*s%.*s...\n",
                   ( int32_t ) httpexampleSERVER_HOSTNAME_LENGTH, democonfigSERVER_HOSTNAME,
                   ( int32_t ) xRequestInfo.pathLen, xRequestInfo.pPath ) );
        LogDebug( ( "Response Headers:\n%.*s\n",
                    ( int32_t ) xResponse.headersLen, xResponse.pHeaders ) );
        LogDebug( ( "Status Code:\n%u\n",
                    xResponse.statusCode ) );
        LogDebug( ( "Response Body:\n%.*s\n",
                    ( int32_t ) xResponse.bodyLen, xResponse.pBody ) );
    }
    else
    {
        LogError( ( "Failed to send HTTP %.*s request to %.*s%.*s: Error=%s.",
                    ( int32_t ) xRequestInfo.methodLen, xRequestInfo.pMethod,
                    ( int32_t ) httpexampleSERVER_HOSTNAME_LENGTH, democonfigSERVER_HOSTNAME,
                    ( int32_t ) xRequestInfo.pathLen, xRequestInfo.pPath,
                    HTTPClient_strerror( xHTTPStatus ) ) );
    }

    if( xHTTPStatus != HTTPSuccess )
    {
        xStatus = pdFAIL;
    }

    return xStatus;
}
