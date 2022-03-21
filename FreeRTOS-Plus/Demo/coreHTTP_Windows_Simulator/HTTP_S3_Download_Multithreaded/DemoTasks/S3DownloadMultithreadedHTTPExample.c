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
 * Demo for showing the use of the HTTP API using a server-authenticated network
 * connection.
 *
 * This example resolves a S3 domain (using a pre-signed URL), establishes a TCP
 * connection, validates the server's certificate using the configurable root CA
 * certificate, and then finally performs a TLS handshake with the HTTP server,
 * so that all communication is encrypted.
 *
 * Afterwards, two additional tasks are created (a request and response task),
 * along with two thread-safe queues (a request and response queue), to
 * demonstrate an asynchronous workflow for downloading an S3 file.
 *
 * There are three tasks to note in this demo:
 * - prvHTTPDemoTask() is responsible for sending HTTP requests to the server
 *   over the transport interface, using the HTTP Client library API. It reads
 *   requests from the request queue and places corresponding server responses
 *   on the response queue.
 * - prvRequestTask() is responsible for generating request objects and adding
 *   them to the request queue, specifying a byte range with each iteration in
 *   order to download the S3 file in partial content responses.
 * - prvResponseTask() logs and evaluates server responses to outgoing requests.
 *   It reads responses from the response queue until the expected number of
 *   responses have been received.
 *
 * Each individual task runs continuously in a loop, until its respective job is
 * completed. If any request fails, an error code is returned.
 *
 * @note This demo requires user-generated pre-signed URLs to be pasted into
 * demo_config.h. Please use the provided script "presigned_urls_gen.py"
 * (located in located in coreHTTP_Windows_Simulator/Common) to generate these
 * URLs. For detailed instructions, see the accompanied README.md.
 *
 * @note If your file requires more than 99 range requests to S3 (depending on the
 * size of the file and the length specified in democonfigRANGE_REQUEST_LENGTH),
 * your connection may be dropped by S3. In this case, either increase the
 * buffer size and range request length (if feasible), to reduce the number of
 * requests required, or re-establish the connection with S3 after receiving a
 * "Connection: close" response header.
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
    #define democonfigTRANSPORT_SEND_RECV_TIMEOUT_MS    ( 5000 )
#endif

/* Check that a size for the user buffer is defined. */
#ifndef democonfigUSER_BUFFER_LENGTH
    #define democonfigUSER_BUFFER_LENGTH    ( 2048 )
#endif

/* Check that the range request length is defined. */
#ifndef democonfigRANGE_REQUEST_LENGTH
    #define democonfigRANGE_REQUEST_LENGTH    ( 1024 )
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
 * @brief Notification bit indicating an error between tasks.
 */
#define httpexampleHTTP_FAILURE                              ( 1U << 1 )

/**
 * @brief Notification bit indicating completion of the request task.
 */
#define httpexampleREQUEST_TASK_COMPLETION                   ( 1U << 2 )

/**
 * @brief Notification bit indicating completion of the response task.
 */
#define httpexampleRESPONSE_TASK_COMPLETION                  ( 1U << 3 )

/**
 * @brief The maximum number of loop iterations to wait for task completion, or
 * after the last received server response, before declaring failure.
 */
#define httpexampleMAX_WAIT_ITERATIONS                       ( 5 )

/**
 * @brief The maximum number of times to run the loop in this demo.
 *
 * @note The loop is executed only if the demo fails initially. Once the demo
 * loop succeeds on a single iteration, the demo exits successfully.
 */
#ifndef HTTP_MAX_DEMO_LOOP_COUNT
    #define HTTP_MAX_DEMO_LOOP_COUNT    ( 3 )
#endif

/**
 * @brief Time in ticks to wait between retries of the demo loop, if
 * demo loop fails.
 */
#define DELAY_BETWEEN_DEMO_RETRY_ITERATIONS_TICKS    ( pdMS_TO_TICKS( 5000U ) )

/** 
 * @brief Each compilation unit that consumes the NetworkContext must define it. 
 * It should contain a single pointer to the type of your desired transport.
 * When using multiple transports in the same compilation unit, define this pointer as void *.
 *
 * @note Transport stacks are defined in FreeRTOS-Plus/Source/Application-Protocols/network_transport.
 */
struct NetworkContext
{
    TlsTransportParams_t * pParams;
};

/**
 * @brief The network context used for the TLS session with the server.
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
 * @brief The location of the path within the pre-signed URL.
 */
static const char * pcPath;

/**
 * @brief Data type for the request queue.
 *
 * Contains the request header struct and its corresponding buffer, to be
 * populated and enqueued by the request task, and read by the main task. The
 * buffer is included to avoid pointer inaccuracy during queue copy operations.
 */
typedef struct RequestItem
{
    HTTPRequestHeaders_t xRequestHeaders;
    uint8_t ucHeaderBuffer[ democonfigUSER_BUFFER_LENGTH ];
} RequestItem_t;

/**
 * @brief Data type for the response queue.
 *
 * Contains the response data type and its corresponding buffer, to be enqueued
 * by the main task, and interpreted by the response task. The buffer is
 * included to avoid pointer inaccuracy during queue copy operations.
 */
typedef struct ResponseItem
{
    HTTPResponse_t xResponse;
    uint8_t ucResponseBuffer[ democonfigUSER_BUFFER_LENGTH ];
} ResponseItem_t;

/**
 * @brief Struct used by the request task to add requests to the request queue.
 *
 * This structure is modified only by the request task. Since queue operations
 * are done by-copy, it is safe for the request task to modify this struct once
 * the previous request has been successfully enqueued.
 */
static RequestItem_t xRequestItem = { 0 };

/**
 * @brief Struct used by the response task to receive responses from the
 * response queue.
 *
 * This structure is modified only by the response task. Since queue operations
 * are done by-copy, it is safe for the response task to modify this struct once
 * the previous response has been parsed.
 */
static ResponseItem_t xResponseItem = { 0 };

/**
 * @brief Struct used by the main HTTP task to send requests to the server.
 *
 * This structure is modified only by the main HTTP task, and is used to receive
 * requests off of the request queue and send them to the HTTP server. Since
 * queue operations are done by-copy, it is safe for the main task to modify
 * this struct once the previous request has been sent to the server.
 */
static RequestItem_t xDownloadReqItem = { 0 };

/**
 * @brief Struct used by the main HTTP task to receive responses from the server
 * and place them on the response queue.
 *
 * This structure is modified only by the main HTTP task. Since queue operations
 * are done by-copy, it is safe for the main task to modify this struct once the
 * previous response has been successfully enqueued.
 */
static ResponseItem_t xDownloadRespItem = { 0 };

/**
 * @brief Queue for HTTP requests. Requests are enqueued by the request task,
 * and dequeued by the main HTTP task.
 */
static QueueHandle_t xRequestQueue;

/**
 * @brief Queue for HTTP responses. Responses are enqueued by the main HTTP
 * task, and dequeued by the response task.
 */
static QueueHandle_t xResponseQueue;

/**
 * @brief Handle for prvRequestTask.
 */
static TaskHandle_t xRequestTask;

/**
 * @brief Handle for prvResponseTask.
 */
static TaskHandle_t xResponseTask;

/**
 * @brief Handle for prvHTTPDemoTask.
 */
static TaskHandle_t xMainTask;

/**
 * @brief The length of the file located at democonfigS3_PRESIGNED_GET_URL.
 */
static size_t xFileSize = 0;

/**
 * @brief The number of responses expected by the response task.
 */
static size_t xResponseCount = 0;

/*-----------------------------------------------------------*/

/**
 * @brief The main task used to demonstrate the HTTP API.
 *
 * After creating the request and response tasks, this task will enter into a
 * loop, processing requests from the request queue and calling the HTTP API to
 * send them to the server. After the request task has finished adding requests
 * to the queue, the task will break from the loop.
 *
 * @param[in] pvParameters Parameters as passed at the time of task creation.
 * Not used in this example.
 */
static void prvHTTPDemoTask( void * pvParameters );

/**
 * @brief Connect to the HTTP server with reconnection retries.
 *
 * @param[out] pxNetworkContext The output parameter to return the created
 * network context.
 *
 * @return pdPASS on successful connection; pdFAIL otherwise.
 */
static BaseType_t prvConnectToServer( NetworkContext_t * pxNetworkContext );

/**
 * @brief Enqueue an HTTP GET request for a given range of the S3 file.
 *
 * @param[in] pxRequestInfo The #HTTPRequestInfo_t for configuring the request.
 * @param[in] xStart The position of the first byte in the range.
 * @param[in] xEnd The position of the last byte in the range, inclusive.
 *
 * @return pdPASS if request successfully enqueued; pdFAIL otherwise.
 */
static BaseType_t prvRequestS3ObjectRange( const HTTPRequestInfo_t * pxRequestInfo,
                                           const size_t xStart,
                                           const size_t xEnd );

/**
 * @brief Check for a task notification.
 *
 * @param[in] pulNotification Pointer holding the notification value.
 * @param[in] ulExpectedBits Bits to wait for.
 * @param[in] xClearBits If bits should be cleared.
 *
 * @return pdTRUE if notification received; pdFALSE otherwise.
 */
static BaseType_t prvCheckNotification( uint32_t * pulNotification,
                                        uint32_t ulExpectedBits,
                                        BaseType_t xClearBits );

/**
 * @brief Enqueue a request for the size of the S3 object specified in pcPath.
 *
 * @param[in] pxRequestInfo The #HTTPRequestInfo_t for configuring the request.
 *
 * @return pdFAIL on failure; pdPASS on success.
 */
static BaseType_t prvGetS3ObjectFileSize( const HTTPRequestInfo_t * pxRequestInfo );

/**
 * @brief Task to continuously enqueue HTTP range requests onto the request
 * queue, until the entire length of the file has been requested.
 *
 * @param[in] pvArgs Parameters as passed at the time of task creation. Not used
 * in this example.
 */
static void prvRequestTask( void * pvArgs );

/**
 * @brief Read and interpret the server response corresponding to the file size
 * request. Called by the response task.
 *
 * @return pdFAIL on failure; pdPASS on success.
 */
static BaseType_t prvReadFileSize( void );

/**
 * @brief Task to continuously log and interpret responses present on the
 * response queue, until the length of the file is downloaded.
 *
 * @param[in] pvArgs Parameters as passed at the time of task creation. Not used
 * in this example.
 */
static void prvResponseTask( void * pvArgs );

/**
 * @brief Services HTTP requests from the request queue and writes corresponding
 * responses to the response queue. Called by the main task.
 *
 * @return pdFAIL on failure; pdPASS on success.
 */
static BaseType_t prvDownloadLoop( void );

/*-----------------------------------------------------------*/

/*
 * @brief Create task to demonstrate the HTTP API over a server-authenticated
 * network connection with a server.
 */
void vStartSimpleHTTPDemo( void )
{
    /* This example uses one application task to process the request queue for
     * HTTP operations, and creates additional tasks to add operations to that
     * queue and interpret server responses. */
    xTaskCreate( prvHTTPDemoTask,          /* Function that implements the task. */
                 "MainTask",               /* Text name for the task - only used for debugging. */
                 democonfigDEMO_STACKSIZE, /* Size of stack (in words, not bytes) to allocate for the task. */
                 NULL,                     /* Task parameter - not used in this case. */
                 tskIDLE_PRIORITY + 1,     /* Task priority, must be between 0 and configMAX_PRIORITIES - 1. */
                 &xMainTask );             /* Used to pass out a handle to the created task. */
}

/*-----------------------------------------------------------*/

/**
 * @brief Entry point of the demo.
 *
 * This example resolves a S3 domain (using a pre-signed URL), establishes a TCP
 * connection, validates the server's certificate using the configurable root CA
 * certificate, and then finally performs a TLS handshake with the HTTP server,
 * so that all communication is encrypted.
 *
 * Afterwards, two additional tasks are created (a request and response task),
 * along with two thread-safe queues (a request and response queue), to
 * demonstrate an asynchronous workflow for downloading an S3 file. The tasks
 * run continuously until the entire file is downloaded. If any request fails,
 * an error code is returned.
 *
 * @note This demo requires user-generated pre-signed URLs to be pasted into
 * demo_config.h. Please use the provided script "presigned_urls_gen.py"
 * (located in located in coreHTTP_Windows_Simulator/Common) to generate these
 * URLs. For detailed instructions, see the accompanied README.md.
 *
 */
static void prvHTTPDemoTask( void * pvParameters )
{
    BaseType_t xIsConnectionEstablished = pdFALSE;
    TlsTransportParams_t xTlsTransportParams = { 0 };
    /* HTTP client library return status. */
    HTTPStatus_t xHTTPStatus = HTTPSuccess;
    /* The location of the host address within the pre-signed URL. */
    const char * pcAddress = NULL;
    /* The user of this demo must check the logs for any failure codes. */
    BaseType_t xDemoStatus = pdPASS;
    UBaseType_t uxDemoRunCount = 0UL;

    /* The length of the path within the pre-signed URL. This variable is
     * defined in order to store the length returned from parsing the URL, but
     * it is unused. The path used for the requests in this demo needs all the
     * query information following the location of the object, to the end of the
     * S3 presigned URL. */
    size_t pathLen = 0;

    /* Remove compiler warnings about unused parameters. */
    ( void ) pvParameters;

    /* Set the pParams member of the network context with desired transport. */
    xNetworkContext.pParams = &xTlsTransportParams;

    LogInfo( ( "HTTP Client S3 multi-threaded download demo using pre-signed URL:\n%s",
               democonfigS3_PRESIGNED_GET_URL ) );

    /* This demo runs once, unless there are failures in the demo execution. In
     * case of failure, the demo loop will be retried for up to
     * HTTP_MAX_DEMO_LOOP_COUNT times. */
    do
    {
        /**************************** Parse Signed URL. ******************************/

        /* Retrieve the path location from democonfigS3_PRESIGNED_GET_URL. This
         * function returns the length of the path without the query, into
         * pathLen. */
        xHTTPStatus = getUrlPath( democonfigS3_PRESIGNED_GET_URL,
                                  httpexampleS3_PRESIGNED_GET_URL_LENGTH,
                                  &pcPath,
                                  &pathLen );

        xDemoStatus = ( xHTTPStatus == HTTPSuccess ) ? pdPASS : pdFAIL;

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

        if( xDemoStatus == pdPASS )
        {
            /* Attempt to connect to the HTTP server. If connection fails, retry after a
             * timeout. The timeout value will be exponentially increased until either the
             * maximum number of attempts or the maximum timeout value is reached. The
             * function returns pdFAIL if the TCP connection cannot be established with
             * the server after the configured number of attempts. */
            xDemoStatus = connectToServerWithBackoffRetries( prvConnectToServer,
                                                             &xNetworkContext );
        }

        if( xDemoStatus == pdPASS )
        {
            /* Set a flag indicating that a TLS connection exists. */
            xIsConnectionEstablished = pdTRUE;
        }
        else
        {
            /* Log an error to indicate connection failure after all reconnect
             * attempts are over. */
            LogError( ( "Failed to connect to HTTP server %s.",
                        cServerHost ) );
        }

        /************* Open queues and create additional tasks. *************/
        if( xDemoStatus == pdPASS )
        {
            /* Open request and response queues. */
            xRequestQueue = xQueueCreate( democonfigQUEUE_SIZE,
                                          sizeof( RequestItem_t ) );

            xResponseQueue = xQueueCreate( democonfigQUEUE_SIZE,
                                           sizeof( ResponseItem_t ) );

            /* Open request and response tasks. */
            xDemoStatus = xTaskCreate( prvRequestTask,
                                       "RequestTask",
                                       democonfigDEMO_STACKSIZE,
                                       NULL,
                                       tskIDLE_PRIORITY,
                                       &xRequestTask );

            xDemoStatus = xTaskCreate( prvResponseTask,
                                       "ResponseTask",
                                       democonfigDEMO_STACKSIZE,
                                       NULL,
                                       tskIDLE_PRIORITY,
                                       &xResponseTask );
        }

        /******************** Download S3 Object File. **********************/

        if( xDemoStatus == pdPASS )
        {
            /* Enter main HTTP task download loop. */
            xDemoStatus = prvDownloadLoop();
        }

        /************************** Disconnect. *****************************/

        /* Close the network connection to clean up any system resources that the
         * demo may have consumed. */
        if( xIsConnectionEstablished == pdTRUE )
        {
            /* Close the network connection.  */
            TLS_FreeRTOS_Disconnect( &xNetworkContext );
        }

        LogInfo( ( "Deleting queues." ) );

        /* Close and delete the queues. */
        if( xRequestQueue != NULL )
        {
            vQueueDelete( xRequestQueue );
        }

        if( xResponseQueue != NULL )
        {
            vQueueDelete( xResponseQueue );
        }

        /******************** Retry in case of failure. *********************/

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
    TlsTransportStatus_t xNetworkStatus;
    NetworkCredentials_t xNetworkCredentials = { 0 };
    BaseType_t xStatus = pdPASS;

    configASSERT( pxNetworkContext != NULL );

    /* Set the credentials for establishing a TLS connection. */
    xNetworkCredentials.disableSni = democonfigDISABLE_SNI;
    xNetworkCredentials.pRootCa = ( const unsigned char * ) democonfigROOT_CA_PEM;
    xNetworkCredentials.rootCaSize = sizeof( democonfigROOT_CA_PEM );

    /* Establish a TLS session with the HTTP server. This example connects to
     * the server host found in democonfigPRESIGNED_GET_URL on port
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

/*-----------------------------------------------------------*/

static BaseType_t prvRequestS3ObjectRange( const HTTPRequestInfo_t * pxRequestInfo,
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
        LogInfo( ( "Request task: Enqueuing request for bytes %d to %d of S3 Object. ",
                   ( int32_t ) xStart,
                   ( int32_t ) xEnd ) );
        LogDebug( ( "Request Headers:\n%.*s",
                    ( int32_t ) xRequestItem.xRequestHeaders.headersLen,
                    ( char * ) xRequestItem.xRequestHeaders.pBuffer ) );

        /* Enqueue the request. */
        xStatus = xQueueSendToBack( xRequestQueue,
                                    &xRequestItem,
                                    httpexampleDEMO_TICKS_TO_WAIT );

        /* Ensure request was added to the queue. */
        if( xStatus == pdFAIL )
        {
            LogError( ( "Request task: Could not enqueue request." ) );
        }
    }

    return xStatus;
}

/*-----------------------------------------------------------*/

static BaseType_t prvGetS3ObjectFileSize( const HTTPRequestInfo_t * pxRequestInfo )
{
    BaseType_t xStatus = pdPASS;

    configASSERT( pxRequestInfo != NULL );

    LogInfo( ( "Getting file object size from host..." ) );

    /* Request bytes 0 to 0. S3 will respond with a Content-Range header that
     * contains the size of the file. The header will look like the following:
     * "Content-Range: bytes 0-0/FILESIZE". The response body will have a single
     * byte, that we are ignoring. */
    xStatus = prvRequestS3ObjectRange( pxRequestInfo,
                                       0,
                                       0 );

    return xStatus;
}

/*-----------------------------------------------------------*/

static void prvRequestTask( void * pvArgs )
{
    BaseType_t xStatus = pdPASS;
    uint32_t ulNotification = 0UL;

    /* Configurations of the initial request headers. */
    HTTPRequestInfo_t xRequestInfo = { 0 };

    /* The number of bytes to request on each iteration. */
    size_t xNumReqBytes = 0;
    /* The starting byte of the next range request. */
    size_t xCurByte = 0;

    /* The path used for the requests in this demo require all the query
     * information following the location of the object, to the end of the S3
     * presigned URL. */
    size_t xRequestUriLen = strlen( pcPath );

    ( void ) pvArgs;

    /* Initialize the request object. */
    xRequestInfo.pHost = cServerHost;
    xRequestInfo.hostLen = xServerHostLength;
    xRequestInfo.pMethod = HTTP_METHOD_GET;
    xRequestInfo.methodLen = httpexampleHTTP_METHOD_GET_LENGTH;
    xRequestInfo.pPath = pcPath;
    xRequestInfo.pathLen = xRequestUriLen;

    /* Set the HTTP "Connection" header to "keep-alive" to allow multiple
     * requests to be sent over the same established TCP connection. This is
     * done in order to download the file in parts. */
    xRequestInfo.reqFlags = HTTP_REQUEST_KEEP_ALIVE_FLAG;

    /* Get the length of the S3 file. */
    xStatus = prvGetS3ObjectFileSize( &xRequestInfo );

    /* Wait for the response task to receive and interpret the server response
     * to the file size request. */
    while( xFileSize == 0 )
    {
        /* Check if any errors in the response task have occurred. */
        if( prvCheckNotification( &ulNotification, httpexampleHTTP_FAILURE, pdTRUE ) != pdFALSE )
        {
            LogError( ( "Request task: Received error notification from response task while waiting for the file size. Exiting task." ) );
            xStatus = pdFAIL;
            break;
        }
    }

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

    /* Here we continuously add range requests to the request queue (and keep
     * track of their count, with xResponseCount), until the entire length of
     * the file has been requested. We keep track of the next starting byte to
     * download with xCurByte, and increment by xNumReqBytes after each
     * iteration, until xCurByte has reached xFileSize. */
    while( ( xStatus != pdFAIL ) && ( xCurByte < xFileSize ) )
    {
        /* Add range request to the request queue. */
        xStatus = prvRequestS3ObjectRange( &xRequestInfo,
                                           xCurByte,
                                           xCurByte + xNumReqBytes - 1 );

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

    /* Clear this task's notifications. */
    xTaskNotifyStateClear( NULL );
    ulNotification = ulTaskNotifyValueClear( NULL, ~( 0UL ) );

    /* Notify the main task of completion. */
    xTaskNotify( xMainTask, httpexampleREQUEST_TASK_COMPLETION, eSetBits );

    /* Delete this task. */
    LogInfo( ( "Deleting request task." ) );
    vTaskDelete( NULL );
}

/*-----------------------------------------------------------*/

static BaseType_t prvReadFileSize( void )
{
    BaseType_t xStatus = pdPASS;
    HTTPStatus_t xHTTPStatus = HTTPSuccess;

    /* The location of the file size in pcContentRangeValStr. */
    char * pcFileSizeStr = NULL;

    /* String to store the Content-Range header value. */
    char * pcContentRangeValStr = NULL;
    size_t xContentRangeValStrLength = 0;

    for( ; ; )
    {
        if( xQueueReceive( xResponseQueue, &xResponseItem, httpexampleDEMO_TICKS_TO_WAIT ) != pdFAIL )
        {
            /* Ensure that the buffer pointer is accurate after being copied from the queue. */
            xResponseItem.xResponse.pBuffer = xResponseItem.ucResponseBuffer;

            /* Ensure that we received a successful response from the server. */
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

            break;
        }
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
        xFileSize = ( size_t ) strtoul( pcFileSizeStr, NULL, 10 );

        if( ( xFileSize == 0 ) || ( xFileSize == UINT32_MAX ) )
        {
            LogError( ( "Error using strtoul to get the file size from %s: xFileSize=%d.",
                        pcFileSizeStr, ( int32_t ) xFileSize ) );
            xStatus = pdFAIL;
        }
    }

    if( xStatus == pdPASS )
    {
        LogInfo( ( "The file is %d bytes long.", ( int32_t ) xFileSize ) );
    }

    return xStatus;
}

/*-----------------------------------------------------------*/

static void prvResponseTask( void * pvArgs )
{
    uint32_t ulWaitCounter = 0UL;
    uint32_t ulNotification = 0UL;
    size_t xNumResponses = 0;

    ( void ) pvArgs;

    if( prvReadFileSize() != pdPASS )
    {
        LogError( ( "Response task: Error obtaining file size from the server response. Exiting task." ) );

        /* Notify the other tasks of failure. */
        xTaskNotify( xRequestTask, httpexampleHTTP_FAILURE, eSetBits );
        xTaskNotify( xMainTask, httpexampleHTTP_FAILURE, eSetBits );
    }
    else
    {
        for( ; ; )
        {
            /* Retrieve response from the response queue, if available. */
            while( ( xQueueReceive( xResponseQueue, &xResponseItem, httpexampleDEMO_TICKS_TO_WAIT ) != pdFAIL ) )
            {
                /* Ensure that the buffer pointer is accurate after being copied from the queue. */
                xResponseItem.xResponse.pBuffer = xResponseItem.ucResponseBuffer;

                /* Log contents of server response. */
                LogInfo( ( "The response task retrieved a server response from the response queue." ) );
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
                    break;
                }

                /* Increment the number of responses found on the queue. */
                xNumResponses += 1;
                /* Reset the wait counter every time a response is received. */
                ulWaitCounter = 0;
            }

            /* Break if we have received all expected responses. */
            if( xNumResponses >= xResponseCount )
            {
                break;
            }

            /* Break if we have been stuck waiting for a response for too long.
             * The total wait here will be the (notification check delay + queue
             * check delay), multiplied by `httpexampleMAX_WAIT_ITERATIONS`. For
             * example, with a 1000 ms delay for both checks, and a maximum
             * iteration of 5, this function will wait 10 seconds after
             * receiving the last response before exiting the loop. */
            if( ++ulWaitCounter > httpexampleMAX_WAIT_ITERATIONS )
            {
                LogError( ( "Response receive loop exceeded maximum wait time." ) );
                break;
            }
            else if( prvCheckNotification( &ulNotification, httpexampleHTTP_FAILURE, pdTRUE ) != pdFALSE )
            {
                LogError( ( "Response task: Received error notification from the main HTTP task. Exiting task." ) );
                break;
            }
        }
    }

    /* Clear this task's notifications. */
    xTaskNotifyStateClear( NULL );
    ulNotification = ulTaskNotifyValueClear( NULL, ~( 0UL ) );

    /* Notify the main task of completion. */
    xTaskNotify( xMainTask, httpexampleRESPONSE_TASK_COMPLETION, eSetBits );

    /* Delete this task. */
    LogInfo( ( "Deleting response task." ) );
    vTaskDelete( NULL );
}

/*-----------------------------------------------------------*/

static BaseType_t prvCheckNotification( uint32_t * pulNotification,
                                        uint32_t ulExpectedBits,
                                        BaseType_t xClearBits )
{
    BaseType_t xStatus = pdTRUE;

    configASSERT( pulNotification != NULL );

    xTaskNotifyWait( 0,
                     ( xClearBits == pdTRUE ) ? ulExpectedBits : 0,
                     pulNotification,
                     httpexampleDEMO_TICKS_TO_WAIT );

    xStatus = ( ( *pulNotification & ulExpectedBits ) == ulExpectedBits ) ? pdTRUE : pdFALSE;

    return xStatus;
}

/*-----------------------------------------------------------*/

static BaseType_t prvDownloadLoop( void )
{
    /* The transport layer interface used by the HTTP client library. */
    TransportInterface_t xTransportInterface;
    HTTPStatus_t xHTTPStatus = HTTPSuccess;
    BaseType_t xStatus = pdPASS;
    uint32_t ulNotification = 0UL;
    uint32_t ulWaitCounter = 0UL;

    /* Expected task completion notifications. */
    uint32_t ulExpectedNotifications = httpexampleREQUEST_TASK_COMPLETION |
                                       httpexampleRESPONSE_TASK_COMPLETION;

    /* Define the transport interface. */
    xTransportInterface.pNetworkContext = &xNetworkContext;
    xTransportInterface.send = TLS_FreeRTOS_send;
    xTransportInterface.recv = TLS_FreeRTOS_recv;

    /* Initialize response struct. */
    xDownloadRespItem.xResponse.pBuffer = xDownloadRespItem.ucResponseBuffer;
    xDownloadRespItem.xResponse.bufferLen = democonfigUSER_BUFFER_LENGTH;

    for( ; ; )
    {
        /* Read request from the request queue. */
        if( xQueueReceive( xRequestQueue, &xDownloadReqItem, httpexampleDEMO_TICKS_TO_WAIT ) != pdPASS )
        {
            /* Check for any errors in the response task. */
            if( prvCheckNotification( &ulNotification, httpexampleHTTP_FAILURE, pdFALSE ) != pdFALSE )
            {
                LogInfo( ( "Main HTTP task: Received error notification from response task. Exiting HTTP download loop." ) );
                xStatus = pdFAIL;
                break;
            }
            /* Check if the request task has finished adding requests to the queue. */
            else if( prvCheckNotification( &ulNotification, httpexampleREQUEST_TASK_COMPLETION, pdFALSE ) != pdFALSE )
            {
                LogInfo( ( "Main HTTP task: Received notification of completion from request task -- no more requests to process. "
                           "Exiting HTTP download loop." ) );
                break;
            }

            LogInfo( ( "Main HTTP task: No requests in the queue. Trying again." ) );
            continue;
        }

        /* Ensure that the buffer pointer is accurate after being copied from the queue. */
        xDownloadReqItem.xRequestHeaders.pBuffer = xDownloadReqItem.ucHeaderBuffer;

        LogInfo( ( "The main HTTP task retrieved a request from the request queue. Sending to server..." ) );
        LogDebug( ( "Request Headers:\n%.*s",
                    ( int32_t ) xDownloadReqItem.xRequestHeaders.headersLen,
                    ( char * ) xDownloadReqItem.xRequestHeaders.pBuffer ) );

        /* Send request to the S3 server. */
        xHTTPStatus = HTTPClient_Send( &xTransportInterface,
                                       &xDownloadReqItem.xRequestHeaders,
                                       NULL,
                                       0,
                                       &xDownloadRespItem.xResponse,
                                       0 );

        if( xHTTPStatus != HTTPSuccess )
        {
            LogError( ( "Main HTTP task: Failed to send HTTP request: Error=%s.",
                        HTTPClient_strerror( xHTTPStatus ) ) );

            /* Notify the response task that a response should not be expected. */
            xTaskNotify( xResponseTask, httpexampleHTTP_FAILURE, eSetBits );

            xStatus = pdFAIL;
            break;
        }
        else
        {
            LogInfo( ( "The HTTP task received a response from the server. Adding to response queue." ) );

            /* Add response to response queue. */
            xStatus = xQueueSendToBack( xResponseQueue,
                                        &xDownloadRespItem,
                                        httpexampleDEMO_TICKS_TO_WAIT );

            /* Ensure response was added to the queue successfully. */
            if( xStatus != pdPASS )
            {
                LogError( ( "Main HTTP task: Could not enqueue response." ) );
                break;
            }
        }
    }

    /* Wait for the other tasks to complete. */
    while( prvCheckNotification( &ulNotification, ulExpectedNotifications, pdFALSE ) != pdTRUE )
    {
        if( ++ulWaitCounter > httpexampleMAX_WAIT_ITERATIONS )
        {
            LogError( ( "Loop exceeded maximum wait time. Task completion error." ) );
            xStatus = pdFAIL;
            break;
        }
    }

    return xStatus;
}
