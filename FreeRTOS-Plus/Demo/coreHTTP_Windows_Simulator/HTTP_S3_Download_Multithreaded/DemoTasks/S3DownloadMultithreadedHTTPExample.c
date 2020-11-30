/*
 * FreeRTOS V202011.00
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
 * Demo for showing use of the HTTP API using a server-authenticated network
 * connection.
 *
 * This example, using a pre-signed URL, resolves a S3 domain, establishes a TCP
 * connection, validates the server's certificate using the root CA certificate
 * defined in the config header, then finally performs a TLS handshake with the
 * HTTP server so that all communication is encrypted.
 *
 * Afterwards, two thread-safe queues are created -- a request and response
 * queue -- to be shared among two tasks, the main task and the HTTP task. The
 * main task adds HTTP request headers into the request queue, for the HTTP task
 * to retrieve and send to the server using the HTTP Client library API. The
 * HTTP task then places the server's response into the response queue, which
 * the main task parses and evaluates. The requests created by the main task are
 * range requests, used to download the S3 file in chunks. The main task reads
 * responses from the response queue continuously until the entire file is
 * received. If any request fails, an error code is returned.
 *
 * @Note: This demo requires user-generated pre-signed URLs to be pasted into
 * demo_config.h. Please use the provided script "presigned_urls_gen.py"
 * (located in located in coreHTTP_Windows_Simulator/Common) to generate these
 * URLs. For detailed instructions, see the accompanied README.md.
 */

/**
 * @file S3DownloadMultithreadedHTTPExample.c
 * @brief Demonstrates usage of the HTTP library.
 */

/* Standard includes. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/* Demo Specific configs. */
#include "demo_config.h"

/* HTTP library includes. */
#include "core_http_client.h"

/* Transport interface implementation include header for TLS. */
#include "using_mbedtls.h"

/* Common HTTP demo utilities. */
#include "http_demo_utils.h"

/*------------- Demo configurations -------------------------*/

/* Check that the root CA certificate is defined. */
#ifndef democonfigROOT_CA_PEM
    #error "Please define democonfigROOT_CA_PEM in demo_config.h."
#endif

/* Check that the pre-signed GET URL is defined. */
#ifndef democonfigS3_PRESIGNED_GET_URL
    #error "Please define democonfigS3_PRESIGNED_GET_URL in demo_config.h."
#endif

/* Check that a TLS port for AWS IoT Core is defined. */
#ifndef democonfigHTTPS_PORT
    #define democonfigHTTPS_PORT    ( 443 )
#endif

/* Check the the queue size is defined. */
#ifndef democonfigQUEUE_SIZE
    #define democonfigQUEUE_SIZE    ( 10 )
#endif

/* Check that a transport timeout for transport send and receive is defined. */
#ifndef democonfigTRANSPORT_SEND_RECV_TIMEOUT_MS
    #define democonfigTRANSPORT_SEND_RECV_TIMEOUT_MS    ( 1000 )
#endif

/* Check that a size for the user buffer is defined. */
#ifndef democonfigUSER_BUFFER_LENGTH
    #define democonfigUSER_BUFFER_LENGTH    ( 4096 )
#endif

/* Check that the range request length is defined. */
#ifndef democonfigRANGE_REQUEST_LENGTH
    #define democonfigRANGE_REQUEST_LENGTH    ( 2048 )
#endif

/* Check that the stack size to use for HTTP tasks is defined. */
#ifndef httpexampleTASK_STACK_SIZE
    #define httpexampleTASK_STACK_SIZE    ( configMINIMAL_STACK_SIZE * 4 )
#endif

/**
 * @brief Length of the pre-signed GET URL defined in demo_config.h.
 */
#define httpexampleS3_PRESIGNED_GET_URL_LENGTH               ( sizeof( democonfigS3_PRESIGNED_GET_URL ) - 1 )

/**
 * @brief The length of the HTTP GET method.
 */
#define httpexampleHTTP_METHOD_GET_LENGTH                    ( sizeof( HTTP_METHOD_GET ) - 1 )

/**
 * @brief Field name of the HTTP range header to read from the server response.
 */
#define httpexampleHTTP_CONTENT_RANGE_HEADER_FIELD           "Content-Range"

/**
 * @brief Length of the HTTP range header field.
 */
#define httpexampleHTTP_CONTENT_RANGE_HEADER_FIELD_LENGTH    ( sizeof( httpexampleHTTP_CONTENT_RANGE_HEADER_FIELD ) - 1 )

/**
 * @brief The HTTP status code returned for partial content.
 */
#define httpexampleHTTP_STATUS_CODE_PARTIAL_CONTENT          206

/**
 * @brief Ticks to wait for task notifications.
 */
#define httpexampleDEMO_TICKS_TO_WAIT                        pdMS_TO_TICKS( 1000 )

/**
 * @brief Notification bit indicating HTTPClient_Send() error in HTTP task.
 */
#define httpexampleHTTP_SEND_ERROR                           ( 1U << 1 )

/**
 * @brief The maximum number of loop iterations to wait after the last received
 * server response, before declaring failure.
 */
#define httpexampleMAX_WAIT_ITERATIONS                       ( 10 )

/**
 * @brief Represents the network context used for the TLS session with the
 * server.
 */
static NetworkContext_t xNetworkContext;

/**
 * @brief The host address string extracted from the pre-signed URL.
 *
 * @note httpexampleS3_PRESIGNED_GET_URL_LENGTH is set as the array length here
 * as the length of the host name string cannot exceed this value.
 */
static char cServerHost[ httpexampleS3_PRESIGNED_GET_URL_LENGTH ];

/**
 * @brief The length of the host address found in the pre-signed URL.
 */
static size_t xServerHostLength;

/**
 * @brief Data type for request queue.
 *
 * Contains the request header struct and its corresponding buffer, to be read
 * from the request queue by the HTTP task and sent to the server. Note that an
 * instance of this struct and its contents MUST stay in scope until the
 * associated HTTP send function is executed successfully by the HTTP task. In
 * this demo, it is initialized globally.
 */
typedef struct RequestItem
{
    HTTPRequestHeaders_t xRequestHeaders;
    uint8_t ucHeaderBuffer[ democonfigUSER_BUFFER_LENGTH ];
} RequestItem_t;

/**
 * @brief Data type for response queue.
 *
 * Contains the response data type and its corresponding buffer, to be read from
 * the response queue by the main task. Note that an instance of this struct and
 * its contents MUST stay in scope until the main task has finished parsing its
 * contents. In this demo, it is initialized globally.
 */
typedef struct ResponseItem
{
    HTTPResponse_t xResponse;
    uint8_t ucResponseBuffer[ democonfigUSER_BUFFER_LENGTH ];
} ResponseItem_t;

/**
 * @brief Struct used for sending requests to the HTTP task.
 *
 * This structure is modified by the main task and accessed by the HTTP task.
 * Once it is placed on the queue by the main task, it is modified only after
 * the HTTP task has successfully sent the HTTP request.
 *
 * Note that this value is not meant to be modified by `startHTTPThread`, since
 * access to this variable is not protected by thread synchronization
 * primitives.
 */
static RequestItem_t xRequestItem = { 0 };

/**
 * @brief Struct used for receiving responses from the HTTP task.
 *
 * This is modified by the HTTP task and accessed by the main task. Once it is
 * placed on the queue by the HTTP task, it is modified only after the main task
 * has successfully acknowledged its receipt.
 *
 * Note that this value is not meant to be modified by the main task, since
 * access to this variable is not protected by thread synchronization
 * primitives.
 */
static ResponseItem_t xResponseItem = { 0 };

/**
 * @brief Queue for HTTP requests. Requests are written by the main task, and
 * executed by the HTTP task.
 */
static QueueHandle_t xRequestQueue;

/**
 * @brief Queue for HTTP responses. Responses are written by the HTTP task,
 * and read by the main task.
 */
static QueueHandle_t xResponseQueue;

/**
 * @brief Handle of prvAsyncPublishTask.
 */
static TaskHandle_t xHTTPTask;

/**
 * @brief Handle for the main task.
 */
static TaskHandle_t xMainTask;

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
 * @param[out] pxNetworkContext The output parameter to return the created
 * network context.
 *
 * @return pdFAIL on failure; pdPASS on successful connection.
 */
static BaseType_t prvConnectToServer( NetworkContext_t * pxNetworkContext );

/**
 * @brief Send continuous range requests until the entire S3 file is downloaded,
 * and log the corresponding responses received from the server.
 *
 * @param[in] pcHost The host name of the server.
 * @param[in] xHostLen The length of pcHost.
 * @param[in] pcRequest The HTTP Request-URI.
 * @param[in] xRequestUriLen The length of pcRequest.
 * @param[in] xFileSize The length of the file at democonfigS3_PRESIGNED_GET_URL.
 * @param[in] xRequestQueue The queue to which HTTP requests should be written.
 * @param[in] xResponseQueue The queue from which HTTP responses should be read.
 *
 * @return pdFAIL on failure; pdPASS on success.
 */
static BaseType_t prvDownloadS3ObjectFile( const char * pcHost,
                                           const size_t xHostLen,
                                           const char * pcRequest,
                                           const size_t xRequestUriLen,
                                           QueueHandle_t xRequestQueue,
                                           QueueHandle_t xResponseQueue );

/**
 * @brief Enqueue an HTTP GET request for a given range of the S3 file.
 *
 * @param[in] pxRequestInfo The #HTTPRequestInfo_t for configuring the request.
 * @param[in] xRequestQueue The queue to which HTTP requests should be written.
 * @param[in] xStart The position of the first byte in the range.
 * @param[in] xEnd The position of the last byte in the range, inclusive.
 *
 * @return pdFAIL on failure; pdPASS on success.
 */
static BaseType_t prvRequestS3ObjectRange( const HTTPRequestInfo_t * pxRequestInfo,
                                           QueueHandle_t xRequestQueue,
                                           const size_t xStart,
                                           const size_t xEnd );

/**
 * @brief Check for an HTTP task notification.
 *
 * @param[in] pulNotification pointer holding notification value.
 * @param[in] ulExpectedBits Bits to wait for.
 * @param[in] xClearBits If bits should be cleared.
 *
 * @return `true` if notification received, `false` otherwise.
 */
static bool prvCheckNotification( uint32_t * pulNotification,
                                  uint32_t ulExpectedBits,
                                  bool xClearBits );

/**
 * @brief Retrieve the size of the S3 object that is specified in pcPath using
 * HTTP task.
 *
 * @param[in] pxRequestInfo The #HTTPRequestInfo_t for configuring the request.
 * @param[in] xRequestQueue The queue to which HTTP requests should be written.
 * @param[in] xResponseQueue The queue from which HTTP responses should be read.
 * @param[out] pxFileSize - The size of the S3 object.
 *
 * @return pdFAIL on failure; pdPASS on success.
 */
static BaseType_t prvGetS3ObjectFileSize( const HTTPRequestInfo_t * pxRequestInfo,
                                          QueueHandle_t xRequestQueue,
                                          QueueHandle_t xResponseQueue,
                                          size_t * pxFileSize );

/**
 * @brief Services HTTP requests from the request queue and writes responses to
 * the response queue.
 *
 * @param[in] pvArgs Parameters as passed at the time of task creation. Not used
 * in this example.
 * */
static void prvStartHTTPThread( void * pvArgs );

/**
 * @brief Clean up resources created by demo.
 *
 * @param[in] xHandle The HTTP task handle.
 * @param[in] xRequestQueue The request queue.
 * @param[in] xResponseQueue The response queue.
 */
static void prvTearDown( TaskHandle_t xHandle,
                         QueueHandle_t xRequestQueue,
                         QueueHandle_t xResponseQueue );

/*-----------------------------------------------------------*/

/*
 * @brief Create the task that demonstrates the HTTP API Demo over a
 * server-authenticated network connection with an HTTP server.
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
 * This example, using a pre-signed URL, resolves a S3 domain, establishes a TCP
 * connection, validates the server's certificate using the root CA certificate
 * defined in the config header, then finally performs a TLS handshake with the
 * HTTP server so that all communication is encrypted.
 *
 * Afterwards, two thread-safe queues are created -- a request and response
 * queue -- to be shared among two tasks, the main task and the HTTP task. The
 * main task adds HTTP request headers into the request queue, for the HTTP task
 * to retrieve and send to the server using the HTTP Client library API. The
 * HTTP task then places the server's response into the response queue, which
 * the main task parses and evaluates. The requests created by the main task are
 * range requests, used to download the S3 file in chunks. The main task reads
 * responses from the response queue continuously until the entire file is
 * received. If any request fails, an error code is returned.
 */
static void prvHTTPDemoTask( void * pvParameters )
{
    BaseType_t xIsConnectionEstablished = pdFALSE;
    /* HTTPS Client library return status. */
    HTTPStatus_t xHTTPStatus = HTTPSuccess;
    /* The location of the host address within the pre-signed URL. */
    const char * pcAddress = NULL;
    /* The location of the path within the pre-signed URL. */
    const char * pcPath = NULL;
    /* The user of this demo must check the logs for any failure codes. */
    BaseType_t xDemoStatus = pdPASS;

    /* The length of the path within the pre-signed URL. This variable is
     * defined in order to store the length returned from parsing the URL, but
     * it is unused. The path used for the requests in this demo needs all the
     * query information following the location of the object, to the end of the
     * S3 presigned URL. */
    size_t pathLen = 0;
    /* The length of the Request-URI within string S3_PRESIGNED_GET_URL */
    size_t xRequestUriLen = 0;

    /* Remove compiler warnings about unused parameters. */
    ( void ) pvParameters;

    xMainTask = xTaskGetCurrentTaskHandle();

    LogInfo( ( "HTTP Client S3 multi-threaded download demo using pre-signed URL:\n%s",
               democonfigS3_PRESIGNED_GET_URL ) );

    /**************************** Parse Signed URL. ******************************/
    if( xDemoStatus == pdPASS )
    {
        /* Retrieve the path location from democonfigS3_PRESIGNED_GET_URL. This
         * function returns the length of the path without the query into
         * pathLen. */
        xHTTPStatus = getUrlPath( democonfigS3_PRESIGNED_GET_URL,
                                  httpexampleS3_PRESIGNED_GET_URL_LENGTH,
                                  &pcPath,
                                  &pathLen );

        /* The path used for the requests in this demo needs all the query
         * information following the location of the object, to the end of the
         * S3 presigned URL. */
        xRequestUriLen = strlen( pcPath );

        xDemoStatus = ( xHTTPStatus == HTTPSuccess ) ? pdPASS : pdFAIL;
    }

    if( xDemoStatus == pdPASS )
    {
        /* Retrieve the address location and length from
         * democonfigS3_PRESIGNED_GET_URL. */
        xHTTPStatus = getUrlAddress( democonfigS3_PRESIGNED_GET_URL,
                                     httpexampleS3_PRESIGNED_GET_URL_LENGTH,
                                     &pcAddress,
                                     &xServerHostLength );

        xDemoStatus = ( xHTTPStatus == HTTPSuccess ) ? pdPASS : pdFAIL;
    }

    if( xDemoStatus == pdPASS )
    {
        /* cServerHost should consist only of the host address located in
         * democonfigS3_PRESIGNED_GET_URL. */
        memcpy( cServerHost, pcAddress, xServerHostLength );
        cServerHost[ xServerHostLength ] = '\0';
    }

    /**************************** Connect. ******************************/

    /* Attempt to connect to the HTTP server. If connection fails, retry after a
     * timeout. The timeout value will be exponentially increased until either the
     * maximum number of attempts or the maximum timeout value is reached. The
     * function returns pdFAIL if the TCP connection cannot be established with
     * the server after configured number of attempts. */
    xDemoStatus = connectToServerWithBackoffRetries( prvConnectToServer,
                                                     &xNetworkContext );

    if( xDemoStatus == pdPASS )
    {
        /* Set a flag indicating that a TLS connection exists. */
        xIsConnectionEstablished = pdTRUE;
    }
    else
    {
        /* Log an error to indicate connection failure after all
         * reconnect attempts are over. */
        LogError( ( "Failed to connect to HTTP server %s.",
                    cServerHost ) );
    }

    /***************** Open queues and create HTTP task. ****************/

    /* Open request and response queues. */
    if( xDemoStatus == pdPASS )
    {
        xRequestQueue = xQueueCreate( democonfigQUEUE_SIZE,
                                      sizeof( RequestItem_t ) );

        xResponseQueue = xQueueCreate( democonfigQUEUE_SIZE,
                                       sizeof( ResponseItem_t ) );

        xDemoStatus = xTaskCreate( prvStartHTTPThread, "HTTPTask", httpexampleTASK_STACK_SIZE, NULL, tskIDLE_PRIORITY, &xHTTPTask );
    }

    /******************** Download S3 Object File. **********************/

    if( xDemoStatus == pdPASS )
    {
        xDemoStatus = prvDownloadS3ObjectFile( cServerHost,
                                               xServerHostLength,
                                               pcPath,
                                               xRequestUriLen,
                                               xRequestQueue,
                                               xResponseQueue );
    }

    /************************** Disconnect. *****************************/

    /* Close the network connection to clean up any system resources that the
     * demo may have consumed. */
    if( xIsConnectionEstablished == pdTRUE )
    {
        /* Close the network connection.  */
        TLS_FreeRTOS_Disconnect( &xNetworkContext );
    }

    if( xDemoStatus == pdPASS )
    {
        LogInfo( ( "prvHTTPDemoTask() completed successfully. "
                   "Total free heap is %u.\r\n",
                   xPortGetFreeHeapSize() ) );
        LogInfo( ( "Demo completed successfully.\r\n" ) );
    }

    /* Close and delete the queues. */
    prvTearDown( xHTTPTask, xRequestQueue, xResponseQueue );
}

/*-----------------------------------------------------------*/

static BaseType_t prvConnectToServer( NetworkContext_t * pxNetworkContext )
{
    TlsTransportStatus_t xNetworkStatus;
    NetworkCredentials_t xNetworkCredentials = { 0 };
    BaseType_t xStatus = pdPASS;

    xNetworkCredentials.disableSni = democonfigDISABLE_SNI;
    /* Set the credentials for establishing a TLS connection. */
    xNetworkCredentials.pRootCa = ( const unsigned char * ) democonfigROOT_CA_PEM;
    xNetworkCredentials.rootCaSize = sizeof( democonfigROOT_CA_PEM );

    /* Establish a TLS session with the HTTP server. This example connects
     * to the server host located in democonfigPRESIGNED_GET_URL and
     * democonfigHTTPS_PORT in demo_config.h. */
    LogInfo( ( "Establishing a TLS session with %s:%d.",
               cServerHost,
               democonfigHTTPS_PORT ) );

    /* Attempt to create a server-authenticated TLS connection. */
    xNetworkStatus = TLS_FreeRTOS_Connect( pxNetworkContext,
                                           cServerHost,
                                           democonfigHTTPS_PORT,
                                           &xNetworkCredentials,
                                           democonfigTRANSPORT_SEND_RECV_TIMEOUT_MS,
                                           democonfigTRANSPORT_SEND_RECV_TIMEOUT_MS );

    if( xNetworkStatus != TLS_TRANSPORT_SUCCESS )
    {
        LogWarn( ( "Unsuccessful connection attempt, received error code:%d",
                   ( int ) xNetworkStatus ) );
        xStatus = pdFAIL;
    }

    return xStatus;
}

static BaseType_t prvDownloadS3ObjectFile( const char * pcHost,
                                           const size_t xHostLen,
                                           const char * pcRequest,
                                           const size_t xRequestUriLen,
                                           QueueHandle_t xRequestQueue,
                                           QueueHandle_t xResponseQueue )
{
    BaseType_t xStatus = pdPASS;
    size_t xResponseCount = 0;
    uint32_t ulWaitCounter = 0;
    uint32_t ulNotification = 0;

    /* Configurations of the initial request headers. */
    HTTPRequestInfo_t xRequestInfo = { 0 };

    /* The length of the file at democonfigS3_PRESIGNED_GET_URL. */
    size_t xFileSize = 0;

    /* The number of bytes we want to request within each range of the file. */
    size_t xNumReqBytes = 0;
    /* The starting byte for the next range request. */
    size_t xCurByte = 0;

    configASSERT( pcHost != NULL );
    configASSERT( pcRequest != NULL );

    /* Initialize the request object. */
    xRequestInfo.pHost = pcHost;
    xRequestInfo.hostLen = xHostLen;
    xRequestInfo.pMethod = HTTP_METHOD_GET;
    xRequestInfo.methodLen = httpexampleHTTP_METHOD_GET_LENGTH;
    xRequestInfo.pPath = pcRequest;
    xRequestInfo.pathLen = xRequestUriLen;

    /* Set "Connection" HTTP header to "keep-alive" so that multiple requests
     * can be sent over the same established TCP connection. This is done in
     * order to download the file in parts. */
    xRequestInfo.reqFlags = HTTP_REQUEST_KEEP_ALIVE_FLAG;

    /* Get the length of the S3 file. */
    xStatus = prvGetS3ObjectFileSize( &xRequestInfo,
                                      xRequestQueue,
                                      xResponseQueue,
                                      &xFileSize );

    /* Set the number of bytes to request in each iteration, defined by the user
     * in democonfigRANGE_REQUEST_LENGTH. */
    if( xFileSize < democonfigRANGE_REQUEST_LENGTH )
    {
        xNumReqBytes = xFileSize;
    }
    else
    {
        xNumReqBytes = democonfigRANGE_REQUEST_LENGTH;
    }

    /* Here we iterate sending byte range requests to the request queue and
     * retrieving responses from the response queue until the entire file has
     * been downloaded. We keep track of the next starting byte to download with
     * xCurByte, and increment by xNumReqBytes after each iteration. When
     * xCurByte reaches xFileSize, we stop downloading. We keep track of the
     * number of responses we are waiting for with xResponseCount.
     */
    while( ( xStatus != pdFAIL ) && ( xCurByte < xFileSize || xResponseCount > 0 ) )
    {
        /* Send a range request for the specified bytes, if remaining. */
        if( xCurByte < xFileSize )
        {
            /* Add range request to the request queue. */
            xStatus = prvRequestS3ObjectRange( &xRequestInfo,
                                               xRequestQueue,
                                               xCurByte,
                                               xCurByte + xNumReqBytes - 1 );

            /* Exit loop if the request was not successfully enqueued. */
            if( xStatus != pdPASS )
            {
                break;
            }

            /* Update the starting byte for the next iteration.*/
            xCurByte += xNumReqBytes;

            /* If the number of bytes left to download is less than the
             * pre-defined constant xNumReqBytes, set xNumReqBytes to equal the
             * accurate number of remaining bytes left to download. */
            if( ( xFileSize - xCurByte ) < xNumReqBytes )
            {
                xNumReqBytes = xFileSize - xCurByte;
            }

            /* If the request was successfully enqueued, we expect a
             * corresponding response. */
            xResponseCount += 1;
        }

        /* Retrieve response from the response queue, if available. */
        if( xResponseCount > 0 )
        {
            if( xQueueReceive( xResponseQueue, &xResponseItem, httpexampleDEMO_TICKS_TO_WAIT ) != pdFAIL )
            {
                LogInfo( ( "The main task retrieved a server response from the response queue." ) );
                LogDebug( ( "Response Headers:\n%.*s",
                            ( int32_t ) xResponseItem.xResponse.headersLen,
                            xResponseItem.xResponse.pHeaders ) );
                LogDebug( ( "Response Status:\n%u",
                            xResponseItem.xResponse.statusCode ) );
                LogInfo( ( "Response Body:\n%.*s\n",
                           ( int32_t ) xResponseItem.xResponse.bodyLen,
                           xResponseItem.xResponse.pBody ) );

                /* Check for a partial content status code (206), indicating a
                 * successful server response. */
                if( xResponseItem.xResponse.statusCode != httpexampleHTTP_STATUS_CODE_PARTIAL_CONTENT )
                {
                    LogError( ( "Received response with unexpected status code: %d", xResponseItem.xResponse.statusCode ) );
                    xStatus = pdFAIL;
                    break;
                }

                /* Reset the wait counter every time a response is received. */
                ulWaitCounter = 0;
                xResponseCount -= 1;
            }
            /* Check for a notification from the HTTP task about an HTTP send failure. */
            else if( prvCheckNotification( &ulNotification, httpexampleHTTP_SEND_ERROR, true ) != false )
            {
                LogError( ( "Received notification from the HTTP task indicating a HTTPClient_Send() error." ) );
                xStatus = pdFAIL;
                break;
            }
        }

        /* Break if we have been stuck waiting for a response for too long. The
         * total wait here will be the (notification check delay + queue check
         * delay), multiplied by `httpexampleMAX_WAIT_ITERATIONS`. For example,
         * with a 1000 ms delay for both checks, and a maximum iteration of 10,
         * this function will wait 20 seconds after receiving the last response
         * before exiting the loop. */
        if( ++ulWaitCounter > httpexampleMAX_WAIT_ITERATIONS )
        {
            LogError( ( "Response receive loop exceeded maximum wait time.\n" ) );
            xStatus = pdFAIL;
            break;
        }
    }

    return xStatus;
}

/*-----------------------------------------------------------*/

static BaseType_t prvRequestS3ObjectRange( const HTTPRequestInfo_t * pxRequestInfo,
                                           QueueHandle_t xRequestQueue,
                                           const size_t xStart,
                                           const size_t xEnd )
{
    HTTPStatus_t xHTTPStatus = HTTPSuccess;
    BaseType_t xStatus = pdPASS;

    configASSERT( pxRequestInfo != NULL );

    /* Set the buffer used for storing request headers. */
    xRequestItem.xRequestHeaders.pBuffer = xRequestItem.ucHeaderBuffer;
    xRequestItem.xRequestHeaders.bufferLen = democonfigUSER_BUFFER_LENGTH;

    xHTTPStatus = HTTPClient_InitializeRequestHeaders( &( xRequestItem.xRequestHeaders ),
                                                       pxRequestInfo );

    if( xHTTPStatus != HTTPSuccess )
    {
        LogError( ( "Failed to initialize HTTP request headers: Error=%s.",
                    HTTPClient_strerror( xHTTPStatus ) ) );
        xStatus = pdFAIL;
    }

    if( xStatus == pdPASS )
    {
        xHTTPStatus = HTTPClient_AddRangeHeader( &( xRequestItem.xRequestHeaders ),
                                                 xStart,
                                                 xEnd );

        if( xHTTPStatus != HTTPSuccess )
        {
            LogError( ( "Failed to add Range header to request headers: Error=%s.",
                        HTTPClient_strerror( xHTTPStatus ) ) );
            xStatus = pdFAIL;
        }
    }

    if( xStatus == pdPASS )
    {
        /* Enqueue the request. */
        LogInfo( ( "Enqueuing request for bytes %d to %d of S3 Object. ",
                   ( int32_t ) xStart,
                   ( int32_t ) xEnd ) );
        LogDebug( ( "Request Headers:\n%.*s",
                    ( int32_t ) xRequestItem.xRequestHeaders.headersLen,
                    ( char * ) xRequestItem.xRequestHeaders.pBuffer ) );

        xStatus = xQueueSendToBack( xRequestQueue,
                                    &xRequestItem,
                                    httpexampleDEMO_TICKS_TO_WAIT );

        /* Ensure request was added to the queue. */
        if( xStatus == pdFAIL )
        {
            LogError( ( "Could not enqueue request." ) );
        }
    }

    return xStatus;
}

/*-----------------------------------------------------------*/

static bool prvCheckNotification( uint32_t * pulNotification,
                                  uint32_t ulExpectedBits,
                                  bool xClearBits )
{
    bool ret = true;

    configASSERT( pulNotification != NULL );

    xTaskNotifyWait( 0,
                     ( xClearBits ) ? ulExpectedBits : 0,
                     pulNotification,
                     httpexampleDEMO_TICKS_TO_WAIT );

    ret = ( ( *pulNotification & ulExpectedBits ) == ulExpectedBits );

    return ret;
}

/*-----------------------------------------------------------*/

static BaseType_t prvGetS3ObjectFileSize( const HTTPRequestInfo_t * pxRequestInfo,
                                          QueueHandle_t xRequestQueue,
                                          QueueHandle_t xResponseQueue,
                                          size_t * pxFileSize )
{
    BaseType_t xStatus = pdPASS;
    HTTPStatus_t xHTTPStatus = HTTPSuccess;
    uint32_t ulNotification = 0;

    /* The location of the file size in pcContentRangeValStr. */
    char * pcFileSizeStr = NULL;

    /* String to store the Content-Range header value. */
    char * pcContentRangeValStr = NULL;
    size_t xContentRangeValStrLength = 0;

    configASSERT( pxRequestInfo != NULL );
    configASSERT( pxFileSize != NULL );

    LogInfo( ( "Getting file object size from host..." ) );

    /* Request bytes 0 to 0. S3 will respond with a Content-Range
     * header that contains the size of the file in it. This header will look
     * like: "Content-Range: bytes 0-0/FILESIZE". The body will have a single
     * byte that we are ignoring. */
    xStatus = prvRequestS3ObjectRange( pxRequestInfo,
                                       xRequestQueue,
                                       0,
                                       0 );

    if( xStatus == pdPASS )
    {
        xStatus = xQueueReceive( xResponseQueue, &xResponseItem, httpexampleDEMO_TICKS_TO_WAIT );
    }

    if( xStatus == pdPASS )
    {
        if( xResponseItem.xResponse.statusCode != httpexampleHTTP_STATUS_CODE_PARTIAL_CONTENT )
        {
            LogError( ( "Received response with unexpected status code: %d.", xResponseItem.xResponse.statusCode ) );
            xStatus = pdFAIL;
        }
        else
        {
            xHTTPStatus = HTTPClient_ReadHeader( &xResponseItem.xResponse,
                                                 ( char * ) httpexampleHTTP_CONTENT_RANGE_HEADER_FIELD,
                                                 ( size_t ) httpexampleHTTP_CONTENT_RANGE_HEADER_FIELD_LENGTH,
                                                 ( const char ** ) &pcContentRangeValStr,
                                                 &xContentRangeValStrLength );

            if( xHTTPStatus != HTTPSuccess )
            {
                LogError( ( "Failed to read Content-Range header from HTTP response: Error=%s.",
                            HTTPClient_strerror( xHTTPStatus ) ) );
                xStatus = pdFAIL;
            }
        }
    }
    /* Check for a notification from the HTTP task about an HTTP send failure. */
    else if( prvCheckNotification( &ulNotification, httpexampleHTTP_SEND_ERROR, true ) != false )
    {
        LogError( ( "Received notification from the HTTP task indicating a HTTPClient_Send() error." ) );
    }

    /* Parse the Content-Range header value to get the file size. */
    if( xStatus == pdPASS )
    {
        pcFileSizeStr = strstr( pcContentRangeValStr, "/" );

        if( pcFileSizeStr == NULL )
        {
            LogError( ( "'/' not present in Content-Range header value: %s.",
                        pcContentRangeValStr ) );
            xStatus = pdFAIL;
        }
    }

    if( xStatus == pdPASS )
    {
        pcFileSizeStr += sizeof( char );
        *pxFileSize = ( size_t ) strtoul( pcFileSizeStr, NULL, 10 );

        if( ( *pxFileSize == 0 ) || ( *pxFileSize == UINT32_MAX ) )
        {
            LogError( ( "Error using strtoul to get the file size from %s: xFileSize=%d.",
                        pcFileSizeStr, ( int32_t ) *pxFileSize ) );
            xStatus = pdFAIL;
        }
    }

    if( xStatus == pdPASS )
    {
        LogInfo( ( "The file is %d bytes long.", ( int32_t ) *pxFileSize ) );
    }

    return xStatus;
}

/*-----------------------------------------------------------*/

static void prvStartHTTPThread( void * pvArgs )
{
    HTTPStatus_t xHTTPStatus = HTTPSuccess;
    BaseType_t xStatus = pdPASS;
    /* The transport layer interface used by the HTTP Client library. */
    TransportInterface_t xTransportInterface;

    ( void ) pvArgs;

    /* Define the transport interface. */
    xTransportInterface.pNetworkContext = &xNetworkContext;
    xTransportInterface.send = TLS_FreeRTOS_send;
    xTransportInterface.recv = TLS_FreeRTOS_recv;

    /* Initialize response struct. */
    xResponseItem.xResponse.pBuffer = xResponseItem.ucResponseBuffer;
    xResponseItem.xResponse.bufferLen = democonfigUSER_BUFFER_LENGTH;

    for( ; ; )
    {
        /* Read request from queue. */
        xStatus = xQueueReceive( xRequestQueue,
                                 &xRequestItem,
                                 httpexampleDEMO_TICKS_TO_WAIT );

        if( xStatus == pdFAIL )
        {
            LogInfo( ( "No requests in the queue. Trying again." ) );
            continue;
        }

        LogInfo( ( "The HTTP task retrieved a request from the request queue." ) );
        LogDebug( ( "Request Headers:\n%.*s",
                    ( int32_t ) xRequestItem.xRequestHeaders.headersLen,
                    ( char * ) xRequestItem.xRequestHeaders.pBuffer ) );

        xHTTPStatus = HTTPClient_Send( &xTransportInterface,
                                       &xRequestItem.xRequestHeaders,
                                       NULL,
                                       0,
                                       &xResponseItem.xResponse,
                                       0 );

        if( xHTTPStatus != HTTPSuccess )
        {
            LogError( ( "Failed to send HTTP request: Error=%s.",
                        HTTPClient_strerror( xHTTPStatus ) ) );
            /*Notify the main task of failure. */
            xTaskNotify( xMainTask, httpexampleHTTP_SEND_ERROR, eSetBits );
            break;
        }
        else
        {
            LogInfo( ( "The HTTP task received a response from the server." ) );
            /* Write response to queue. */
            xStatus = xQueueSendToBack( xResponseQueue,
                                        &xResponseItem,
                                        httpexampleDEMO_TICKS_TO_WAIT );

            /* Ensure response was added to the queue. */
            if( xStatus != pdPASS )
            {
                LogError( ( "Could not enqueue response." ) );
                break;
            }
        }
    }
}

/*-----------------------------------------------------------*/

void prvTearDown( TaskHandle_t xHandle,
                  QueueHandle_t xRequestQueue,
                  QueueHandle_t xResponseQueue )
{
    /* Delete HTTP task. */
    LogInfo( ( "Deleting HTTP task." ) );
    vTaskDelete( xHandle );

    /* Close and delete the queues. */
    if( xRequestQueue != NULL )
    {
        vQueueDelete( xRequestQueue );
    }

    if( xResponseQueue != NULL )
    {
        vQueueDelete( xResponseQueue );
    }
}
