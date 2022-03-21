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
 * Demo for showing use of the HTTP API using a server-authenticated network
 * connection.
 *
 * This example, using a pre-signed URL, resolves a S3 domain, establishes a TCP
 * connection, validates the server's certificate using the root CA certificate
 * defined in the config header, and then finally performs a TLS handshake with
 * the HTTP server so that all communication is encrypted. After which, the HTTP
 * Client library API is used to upload a file to a S3 bucket by sending a PUT
 * request, and verify the file was uploaded using a GET request. If any request
 * fails, an error code is returned.
 *
 * @note This demo requires user-generated pre-signed URLs to be pasted into
 * demo_config.h. Please use the provided script "presigned_urls_gen.py"
 * (located in coreHTTP_Windows_Simulator/Common) to generate these URLs. For
 * detailed instructions, see the accompanied README.md.
 */

/**
 * @file S3UploadHTTPExample.c
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

/* Check that the pre-signed PUT URL is defined. */
#ifndef democonfigS3_PRESIGNED_PUT_URL
    #error "Please define democonfigS3_PRESIGNED_PUT_URL in demo_config.h."
#endif

/* Check that a TLS port for AWS IoT Core is defined. */
#ifndef democonfigHTTPS_PORT
    #define democonfigHTTPS_PORT    ( 443 )
#endif

/* Check that a transport timeout for transport send and receive is defined. */
#ifndef democonfigTRANSPORT_SEND_RECV_TIMEOUT_MS
    #define democonfigTRANSPORT_SEND_RECV_TIMEOUT_MS    ( 5000 )
#endif

/* Check that a size for the user buffer is defined. */
#ifndef democonfigUSER_BUFFER_LENGTH
    #define democonfigUSER_BUFFER_LENGTH    ( 2048 )
#endif

/* Pointer to the data to upload.*/
#ifndef democonfigDEMO_HTTP_UPLOAD_DATA
    #define democonfigDEMO_HTTP_UPLOAD_DATA    "Hello World!"
#endif

/**
 * @brief Length of the pre-signed GET URL defined in demo_config.h.
 */
#define httpexampleS3_PRESIGNED_GET_URL_LENGTH               ( sizeof( democonfigS3_PRESIGNED_GET_URL ) - 1 )

/**
 * @brief Length of the pre-signed PUT URL defined in demo_config.h.
 */
#define httpexampleS3_PRESIGNED_PUT_URL_LENGTH               ( sizeof( democonfigS3_PRESIGNED_PUT_URL ) - 1 )

/**
 * @brief The length of the HTTP GET method.
 */
#define httpexampleHTTP_METHOD_GET_LENGTH                    ( sizeof( HTTP_METHOD_GET ) - 1 )

/**
 * @brief The length of the HTTP PUT method.
 */
#define httpexampleHTTP_METHOD_PUT_LENGTH                    ( sizeof( HTTP_METHOD_PUT ) - 1 )

/**
 * @brief Field name of the HTTP range header to read from the server response.
 */
#define httpexampleHTTP_CONTENT_RANGE_HEADER_FIELD           "Content-Range"

/**
 * @brief Length of the HTTP range header field.
 */
#define httpexampleHTTP_CONTENT_RANGE_HEADER_FIELD_LENGTH    ( sizeof( httpexampleHTTP_CONTENT_RANGE_HEADER_FIELD ) - 1 )

/**
 * @brief The length of the data in bytes to upload.
 */
#define httpexampleDEMO_HTTP_UPLOAD_DATA_LENGTH              ( sizeof( democonfigDEMO_HTTP_UPLOAD_DATA ) - 1 )

/**
 * @brief The HTTP status code returned for partial content.
 */
#define httpexampleHTTP_STATUS_CODE_PARTIAL_CONTENT          206

/**
 * @brief The HTTP status code returned for a successful request.
 */
#define httpexampleHTTP_STATUS_CODE_SUCCESSFUL_REQUEST       200

/**
 * @brief The maximum number of times to run the loop in this demo.
 *
 * @note The demo loop is re-run only if the demo fails initially. Once the demo
 * loop succeeds on an iteration, the demo exits successfully.
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
 * @brief A buffer used in the demo for storing HTTP request headers, and HTTP
 * response headers and body.
 *
 * @note This demo shows how the same buffer can be re-used for storing the HTTP
 * response after the HTTP request is sent out. However, the user can decide how
 * to use buffers to store HTTP requests and responses.
 */
static uint8_t ucUserBuffer[ democonfigUSER_BUFFER_LENGTH ];

/**
 * @brief Header data sent as part of an HTTP request to the server.
 */
static HTTPRequestHeaders_t xRequestHeaders;

/**
 * @brief Configurations of the initial request headers that are passed to
 * #HTTPClient_InitializeRequestHeaders.
 */
static HTTPRequestInfo_t xRequestInfo;

/**
 * @brief Response returned from the HTTP server.
 */
static HTTPResponse_t xResponse;

/**
 * @brief The host address string extracted from the pre-signed URL.
 *
 * @note httpexampleS3_PRESIGNED_PUT_URL_LENGTH is set as the array length here
 * as the length of the host name string cannot exceed this value.
 */
static char cServerHost[ httpexampleS3_PRESIGNED_PUT_URL_LENGTH ];

/**
 * @brief The length of the host address found in the pre-signed URL.
 */
static size_t xServerHostLength;

/**
 * @brief The location of the path within the pre-signed URL.
 */
static const char * pcRequestURI;

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
 * @return pdPASS on successful connection; pdFAIL otherwise.
 */
static BaseType_t prvConnectToServer( NetworkContext_t * pxNetworkContext );

/**
 * @brief Retrieve the size of the S3 object that is specified in pcPath.
 *
 * @param[out] pxFileSize The size of the S3 object.
 * @param[in] pxTransportInterface The transport interface for making network
 * calls.
 * @param[in] pcHost The server host address. This string must be
 * null-terminated.
 * @param[in] xHostLen The length of the server host address.
 * @param[in] pcPath The Request-URI to the objects of interest. This string
 * should be null-terminated.
 *
 * @return The status of the file size acquisition using a GET request to the
 * server: pdPASS on success, pdFAIL on failure.
 */
static BaseType_t prvGetS3ObjectFileSize( size_t * pxFileSize,
                                          const TransportInterface_t * pxTransportInterface,
                                          const char * pcHost,
                                          size_t xHostLen,
                                          const char * pcPath );

/**
 * @brief Send an HTTP PUT request based on a specified path to upload a file,
 * then print the response received from the server.
 *
 * @param[in] pxTransportInterface The transport interface for making network
 * calls.
 * @param[in] pcPath The Request-URI to the objects of interest. This string must
 * be null-terminated.
 *
 * @return The status of the file upload using a PUT request to the server: pdPASS
 * on success, pdFAIL on failure.
 */
static BaseType_t prvUploadS3ObjectFile( const TransportInterface_t * pxTransportInterface,
                                         const char * pcPath );

/**
 * @brief Retrieve and verify the size of the S3 object that is specified in
 * pcPath.
 *
 * @param[in] pxTransportInterface The transport interface for making network
 * calls.
 * @param[in] pcPath The Request-URI to the objects of interest. This string must
 * be null-terminated.
 *
 * @return The status of the file size acquisition and verification using a GET
 * request to the server: pdPASS on success, pdFAIL on failure.
 */
static BaseType_t prvVerifyS3ObjectFileSize( const TransportInterface_t * pxTransportInterface,
                                             const char * pcPath );

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
 * defined in the config header, and then finally performs a TLS handshake with
 * the HTTP server so that all communication is encrypted. After which, the HTTP
 * Client library API is used to upload a file to a S3 bucket by sending a PUT
 * request, and verify that the file was uploaded using a GET request. If any
 * request fails, an error code is returned.
 *
 * @note This example is single-threaded.
 *
 */
static void prvHTTPDemoTask( void * pvParameters )
{
    /* The transport layer interface used by the HTTP Client library. */
    TransportInterface_t xTransportInterface;
    /* The network context for the transport layer interface. */
    NetworkContext_t xNetworkContext = { 0 };
    TlsTransportParams_t xTlsTransportParams = { 0 };
    BaseType_t xIsConnectionEstablished = pdFALSE;
    /* HTTP Client library return status. */
    HTTPStatus_t xHTTPStatus = HTTPSuccess;
    UBaseType_t uxDemoRunCount = 0UL;

    /* The user of this demo must check the logs for any failure codes. */
    BaseType_t xDemoStatus = pdPASS;

    /* The length of the path within the pre-signed URL. This variable is
     * defined in order to store the length returned from parsing the URL, but
     * it is unused. The path used for the requests in this demo needs all the
     * query information following the location of the object, to the end of the
     * S3 presigned URL. */
    size_t xPathLen = 0;

    /* Remove compiler warnings about unused parameters. */
    ( void ) pvParameters;

    /* Set the pParams member of the network context with desired transport. */
    xNetworkContext.pParams = &xTlsTransportParams;

    LogInfo( ( "HTTP Client Synchronous S3 upload demo using pre-signed URL:\n%s",
               democonfigS3_PRESIGNED_PUT_URL ) );

    /* This demo runs once, unless there are failures in the demo execution. In
     * case of failures, the demo loop will run up to HTTP_MAX_DEMO_LOOP_COUNT
     * times. */
    do
    {
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

            /* Define the transport interface. */
            xTransportInterface.pNetworkContext = &xNetworkContext;
            xTransportInterface.send = TLS_FreeRTOS_send;
            xTransportInterface.recv = TLS_FreeRTOS_recv;
        }
        else
        {
            /* Log an error to indicate connection failure after all
             * reconnect attempts are over. */
            LogError( ( "Failed to connect to HTTP server %s.",
                        cServerHost ) );
        }

        /********************** Upload S3 Object File. **********************/

        if( xDemoStatus == pdPASS )
        {
            /* Retrieve the path location from democonfigS3_PRESIGNED_PUT_URL. This
             * function returns the length of the path without the query into
             * xPathLen, which is left unused in this demo. */
            xHTTPStatus = getUrlPath( democonfigS3_PRESIGNED_PUT_URL,
                                      httpexampleS3_PRESIGNED_PUT_URL_LENGTH,
                                      &pcRequestURI,
                                      &xPathLen );

            xDemoStatus = ( xHTTPStatus == HTTPSuccess ) ? pdPASS : pdFAIL;
        }

        if( xDemoStatus == pdPASS )
        {
            xDemoStatus = prvUploadS3ObjectFile( &xTransportInterface,
                                                 pcRequestURI );
        }

        /******************* Verify S3 Object File Upload. ********************/

        if( xDemoStatus == pdPASS )
        {
            /* Retrieve the path location from democonfigS3_PRESIGNED_GET_URL. This
             * function returns the length of the path without the query into
             * xPathLen. */
            xHTTPStatus = getUrlPath( democonfigS3_PRESIGNED_GET_URL,
                                      httpexampleS3_PRESIGNED_GET_URL_LENGTH,
                                      &pcRequestURI,
                                      &xPathLen );

            xDemoStatus = ( xHTTPStatus == HTTPSuccess ) ? pdPASS : pdFAIL;
        }

        if( xDemoStatus == pdPASS )
        {
            /* Verify the file exists by retrieving the file size. */
            xDemoStatus = prvVerifyS3ObjectFileSize( &xTransportInterface,
                                                     pcRequestURI );
        }

        /************************** Disconnect. *****************************/

        /* Close the network connection to clean up any system resources that the
         * demo may have consumed. */
        if( xIsConnectionEstablished == pdTRUE )
        {
            /* Close the network connection.  */
            TLS_FreeRTOS_Disconnect( &xNetworkContext );
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
    TlsTransportStatus_t xNetworkStatus;
    NetworkCredentials_t xNetworkCredentials = { 0 };
    BaseType_t xStatus = pdPASS;
    HTTPStatus_t xHTTPStatus = HTTPSuccess;

    /* The location of the host address within the pre-signed URL. */
    const char * pcAddress = NULL;

    /* Retrieve the address location and length from democonfigS3_PRESIGNED_GET_URL. */
    xHTTPStatus = getUrlAddress( democonfigS3_PRESIGNED_GET_URL,
                                 httpexampleS3_PRESIGNED_GET_URL_LENGTH,
                                 &pcAddress,
                                 &xServerHostLength );

    xStatus = ( xHTTPStatus == HTTPSuccess ) ? pdPASS : pdFAIL;

    if( xStatus == pdPASS )
    {
        /* cServerHost should consist only of the host address located in
         * democonfigS3_PRESIGNED_GET_URL. */
        memcpy( cServerHost, pcAddress, xServerHostLength );
        cServerHost[ xServerHostLength ] = '\0';

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
            xStatus = pdFAIL;
        }
    }

    return xStatus;
}

/*-----------------------------------------------------------*/

static BaseType_t prvGetS3ObjectFileSize( size_t * pxFileSize,
                                          const TransportInterface_t * pxTransportInterface,
                                          const char * pcHost,
                                          size_t xHostLen,
                                          const char * pcPath )
{
    BaseType_t xStatus = pdPASS;
    HTTPStatus_t xHTTPStatus = HTTPSuccess;

    /* The location of the file size in pcContentRangeValStr. */
    char * pcFileSizeStr = NULL;

    /* String to store the Content-Range header value. */
    char * pcContentRangeValStr = NULL;
    size_t xContentRangeValStrLength = 0;

    configASSERT( pcHost != NULL );
    configASSERT( pcPath != NULL );

    /* Initialize all HTTP Client library API structs to 0. */
    ( void ) memset( &xRequestHeaders, 0, sizeof( xRequestHeaders ) );
    ( void ) memset( &xRequestInfo, 0, sizeof( xRequestInfo ) );
    ( void ) memset( &xResponse, 0, sizeof( xResponse ) );

    /* Initialize the request object. */
    xRequestInfo.pHost = pcHost;
    xRequestInfo.hostLen = xHostLen;
    xRequestInfo.pMethod = HTTP_METHOD_GET;
    xRequestInfo.methodLen = sizeof( HTTP_METHOD_GET ) - 1;
    xRequestInfo.pPath = pcPath;
    xRequestInfo.pathLen = strlen( pcPath );

    /* Set "Connection" HTTP header to "keep-alive" so that multiple requests
     * can be sent over the same established TCP connection. */
    xRequestInfo.reqFlags = HTTP_REQUEST_KEEP_ALIVE_FLAG;

    /* Set the buffer used for storing request headers. */
    xRequestHeaders.pBuffer = ucUserBuffer;
    xRequestHeaders.bufferLen = democonfigUSER_BUFFER_LENGTH;

    /* Initialize the response object. The same buffer used for storing request
     * headers is reused here. */
    xResponse.pBuffer = ucUserBuffer;
    xResponse.bufferLen = democonfigUSER_BUFFER_LENGTH;

    LogInfo( ( "Getting file object size from host..." ) );

    xHTTPStatus = HTTPClient_InitializeRequestHeaders( &xRequestHeaders,
                                                       &xRequestInfo );

    if( xHTTPStatus != HTTPSuccess )
    {
        LogError( ( "Failed to initialize HTTP request headers: Error=%s.",
                    HTTPClient_strerror( xHTTPStatus ) ) );
        xStatus = pdFAIL;
    }

    if( xStatus == pdPASS )
    {
        /* Add the header to get bytes=0-0. S3 will respond with a Content-Range
         * header that contains the size of the file in it. This header will
         * look like: "Content-Range: bytes 0-0/FILESIZE". The body will have a
         * single byte that we are ignoring. */
        xHTTPStatus = HTTPClient_AddRangeHeader( &xRequestHeaders, 0, 0 );

        if( xHTTPStatus != HTTPSuccess )
        {
            LogError( ( "Failed to add range header to request headers: Error=%s.",
                        HTTPClient_strerror( xHTTPStatus ) ) );
            xStatus = pdFAIL;
        }
    }

    if( xStatus == pdPASS )
    {
        /* Send the request and receive the response. */
        xHTTPStatus = HTTPClient_Send( pxTransportInterface,
                                       &xRequestHeaders,
                                       NULL,
                                       0,
                                       &xResponse,
                                       0 );

        if( xHTTPStatus != HTTPSuccess )
        {
            LogError( ( "Failed to send HTTP GET request to %s%s: Error=%s.",
                        pcHost, pcPath, HTTPClient_strerror( xHTTPStatus ) ) );
            xStatus = pdFAIL;
        }
    }

    if( xStatus == pdPASS )
    {
        LogDebug( ( "Received HTTP response from %s%s...",
                    pcHost, pcPath ) );
        LogDebug( ( "Response Headers:\n%.*s",
                    ( int32_t ) xResponse.headersLen,
                    xResponse.pHeaders ) );
        LogDebug( ( "Response Body:\n%.*s\n",
                    ( int32_t ) xResponse.bodyLen,
                    xResponse.pBody ) );

        if( xResponse.statusCode != httpexampleHTTP_STATUS_CODE_PARTIAL_CONTENT )
        {
            LogError( ( "Received an invalid response from the server "
                        "(Status Code: %u).",
                        xResponse.statusCode ) );
            xStatus = pdFAIL;
        }
    }

    if( xStatus == pdPASS )
    {
        LogInfo( ( "Received successful response from server "
                   "(Status Code: %u).",
                   xResponse.statusCode ) );

        xHTTPStatus = HTTPClient_ReadHeader( &xResponse,
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

static BaseType_t prvUploadS3ObjectFile( const TransportInterface_t * pxTransportInterface,
                                         const char * pcPath )
{
    BaseType_t xStatus = pdFAIL;
    HTTPStatus_t xHTTPStatus = HTTPSuccess;

    configASSERT( pcPath != NULL );

    /* Initialize all HTTP Client library API structs to 0. */
    ( void ) memset( &xRequestHeaders, 0, sizeof( xRequestHeaders ) );
    ( void ) memset( &xRequestInfo, 0, sizeof( xRequestInfo ) );
    ( void ) memset( &xResponse, 0, sizeof( xResponse ) );

    /* Initialize the request object. */
    xRequestInfo.pHost = cServerHost;
    xRequestInfo.hostLen = xServerHostLength;
    xRequestInfo.pMethod = HTTP_METHOD_PUT;
    xRequestInfo.methodLen = httpexampleHTTP_METHOD_PUT_LENGTH;
    xRequestInfo.pPath = pcPath;
    xRequestInfo.pathLen = strlen( pcPath );

    /* Set "Connection" HTTP header to "keep-alive" so that multiple requests
     * can be sent over the same established TCP connection. */
    xRequestInfo.reqFlags = HTTP_REQUEST_KEEP_ALIVE_FLAG;

    /* Set the buffer used for storing request headers. */
    xRequestHeaders.pBuffer = ucUserBuffer;
    xRequestHeaders.bufferLen = democonfigUSER_BUFFER_LENGTH;

    /* Initialize the response object. The same buffer used for storing request
     * headers is reused here. */
    xResponse.pBuffer = ucUserBuffer;
    xResponse.bufferLen = democonfigUSER_BUFFER_LENGTH;

    if( xHTTPStatus == HTTPSuccess )
    {
        xHTTPStatus = HTTPClient_InitializeRequestHeaders( &xRequestHeaders,
                                                           &xRequestInfo );
    }

    if( xHTTPStatus == HTTPSuccess )
    {
        LogInfo( ( "Uploading file..." ) );
        LogDebug( ( "Request Headers:\n%.*s",
                    ( int32_t ) xRequestHeaders.headersLen,
                    ( char * ) xRequestHeaders.pBuffer ) );
        xHTTPStatus = HTTPClient_Send( pxTransportInterface,
                                       &xRequestHeaders,
                                       ( const uint8_t * ) democonfigDEMO_HTTP_UPLOAD_DATA,
                                       httpexampleDEMO_HTTP_UPLOAD_DATA_LENGTH,
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
        LogDebug( ( "Received HTTP response from %s%s...",
                    cServerHost, pcPath ) );
        LogDebug( ( "Response Headers:\n%.*s",
                    ( int32_t ) xResponse.headersLen,
                    xResponse.pHeaders ) );
        LogDebug( ( "Response Body:\n%.*s\n",
                    ( int32_t ) xResponse.bodyLen,
                    xResponse.pBody ) );

        xStatus = ( xResponse.statusCode == httpexampleHTTP_STATUS_CODE_SUCCESSFUL_REQUEST ) ? pdPASS : pdFAIL;
    }
    else
    {
        LogError( ( "An error occurred in uploading the file."
                    "Failed to send HTTP PUT request to %s%s: Error=%s.",
                    cServerHost, pcPath, HTTPClient_strerror( xHTTPStatus ) ) );
    }

    if( xStatus == pdPASS )
    {
        LogInfo( ( "Received successful response from server "
                   "(Status Code: %u).",
                   xResponse.statusCode ) );
    }
    else
    {
        LogError( ( "Received an invalid response from the server "
                    "(Status Code: %u).",
                    xResponse.statusCode ) );
    }

    return( ( xStatus == pdPASS ) && ( xHTTPStatus == HTTPSuccess ) );
}

/*-----------------------------------------------------------*/

static BaseType_t prvVerifyS3ObjectFileSize( const TransportInterface_t * pxTransportInterface,
                                             const char * pcPath )
{
    BaseType_t xStatus = pdFAIL;
    /* The size of the file uploaded to S3. */
    size_t xFileSize = 0;

    /* Retrieve the file size. */
    xStatus = prvGetS3ObjectFileSize( &xFileSize,
                                      pxTransportInterface,
                                      cServerHost,
                                      xServerHostLength,
                                      pcPath );

    if( xStatus == pdPASS )
    {
        if( xFileSize != httpexampleDEMO_HTTP_UPLOAD_DATA_LENGTH )
        {
            LogError( ( "Failed to upload the data to S3. The file size found is %d, but it should be %d.",
                        ( int32_t ) xFileSize,
                        ( int32_t ) httpexampleDEMO_HTTP_UPLOAD_DATA_LENGTH ) );
        }
        else
        {
            LogInfo( ( "Successfully verified that the size of the file found on S3 matches the file size uploaded "
                       "(Uploaded: %d bytes, Found: %d bytes).",
                       ( int32_t ) httpexampleDEMO_HTTP_UPLOAD_DATA_LENGTH,
                       ( int32_t ) xFileSize ) );
        }
    }

    return xStatus;
}
