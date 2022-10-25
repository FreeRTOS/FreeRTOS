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
 * defined in the config header, then finally performs a TLS handshake with the
 * HTTP server so that all communication is encrypted. After which, the HTTP
 * client library API is used to download the S3 file (by sending multiple GET
 * requests, filling up the response buffer each time until all parts are
 * downloaded). If any request fails, an error code is returned.
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
 * @file S3DownloadHTTPExample.c
 * @brief Demonstrates usage of the HTTP library.
 */

/* Standard includes. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>

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

/* JSON API header. */
#include "core_json.h"

/* SIGV4 API header. */
#include "sigv4.h"

/* MBEDTLS API header. */
#include "mbedtls/sha256.h"

/*------------- Demo configurations -------------------------*/

/* Check that the root CA certificate for S3 is defined. */
#ifndef democonfigS3_ROOT_CA_PEM
    #error "Please define democonfigS3_ROOT_CA_PEM in demo_config.h."
#endif

/* Check that the root CA certificate for IoT credential provider is defined. */
#ifndef democonfigIOT_CRED_PROVIDER_ROOT_CA_PEM
    #error "Please define democonfigIOT_CRED_PROVIDER_ROOT_CA_PEM in demo_config.h."
#endif

/* Check that AWS IOT Thing Name is defined. */
#ifndef democonfigIOT_THING_NAME
    #error "Please define the democonfigIOT_THING_NAME macro in demo_config.h."
#endif

/* Check that AWS IOT credential provider endpoint is defined. */
#ifndef democonfigIOT_CREDENTIAL_PROVIDER_ENDPOINT
    #error "Please define the democonfigIOT_CREDENTIAL_PROVIDER_ENDPOINT macro in demo_config.h."
#endif

/* Check that AWS IOT credential provider role is defined. */
#ifndef democonfigIOT_CREDENTIAL_PROVIDER_ROLE
    #error "Please define the democonfigIOT_CREDENTIAL_PROVIDER_ROLE macro in demo_config.h."
#endif

/* Check that AWS S3 BUCKET NAME is defined. */
#ifndef democonfigS3_BUCKET_NAME
    #error "Please define the democonfigS3_BUCKET_NAME macro in demo_config.h."
#endif

/* Check that AWS S3 OBJECT NAME is defined. */
#ifndef democonfigS3_OBJECT_NAME
    #error "Please define the democonfigS3_OBJECT_NAME macro in demo_config.h."
#endif

/* Check that AWS S3 BUCKET REGION is defined. */
#ifndef democonfigS3_BUCKET_REGION
    #error "Please define the democonfigS3_BUCKET_REGION macro in which bucket resides in demo_config.h."
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
    #define democonfigUSER_BUFFER_LENGTH    ( 4096 )
#endif

/* Check that the range request length is defined. */
#ifndef democonfigRANGE_REQUEST_LENGTH
    #define democonfigRANGE_REQUEST_LENGTH    ( 2048 )
#endif

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
 * @brief Buffer Length for storing the AWS IoT Credentials retrieved from
 * AWS IoT credential provider which includes the following:
 * 1. Access Key ID
 * 2. Secret Access key
 * 3. Session Token
 * 4. Expiration Date
 */
#define CREDENTIAL_BUFFER_LENGTH                 1500U

/**
 * @brief AWS Service name to send HTTP request using SigV4 library.
 */
#define AWS_S3_SERVICE_NAME                      "s3"

/**
 * @brief AWS S3 Endpoint.
 */
#define AWS_S3_ENDPOINT                            \
    democonfigS3_BUCKET_NAME "." AWS_S3_SERVICE_NAME "." \
    democonfigS3_BUCKET_REGION  ".amazonaws.com"

/**
 * @brief AWS S3 URI PATH.
 */
#define AWS_S3_URI_PATH \
    "/" democonfigS3_OBJECT_NAME

/**
 * @brief The URI path for HTTP requests to AWS IoT Credential provider.
 */
#define AWS_IOT_CREDENTIAL_PROVIDER_URI_PATH \
    "/role-aliases/"                         \
    democonfigIOT_CREDENTIAL_PROVIDER_ROLE "/credentials"

/**
 * @brief HTTP header name for specifying the IOT Thing resource name in request to AWS S3.
 */
#define AWS_IOT_THING_NAME_HEADER_FIELD               "x-amz-iot-thing-name"

/**
 * @brief Field name of the HTTP date header to read from the AWS IOT credential provider server response.
 */
#define AWS_IOT_CRED_PROVIDER_RESPONSE_DATE_HEADER    "date"

/**
 * @brief Field name of the HTTP Authorization header to add to the request headers.
 */
#define SIGV4_AUTH_HEADER_FIELD_NAME                  "Authorization"

/**
 * @brief IS8601 formatted date length.
 */
#define SIGV4_ISO_STRING_LEN                          16U

/**
 * @brief Length of AWS HTTP Authorization header value generated using SigV4 library.
 */
#define AWS_HTTP_AUTH_HEADER_VALUE_LEN                2048U

/**
 * @brief Length in bytes of hex encoded hash digest.
 */
#define HEX_ENCODED_SHA256_HASH_DIGEST_LENGTH         ( ( ( uint16_t ) 64 ) )

/**
 * @brief Length in bytes of SHA256 hash digest.
 */
#define SHA256_HASH_DIGEST_LENGTH                     ( HEX_ENCODED_SHA256_HASH_DIGEST_LENGTH / 2 )

/**
 * @brief Access Key Id key to be searched in the IoT credentials response.
 */
#define CREDENTIALS_RESPONSE_ACCESS_KEY_ID_KEY        "credentials.accessKeyId"

/**
 * @brief Secret Access key to be searched in the IoT credentials response.
 */
#define CREDENTIALS_RESPONSE_SECRET_ACCESS_KEY        "credentials.secretAccessKey"

/**
 * @brief Session Token key to be searched in the IoT credentials response.
 */
#define CREDENTIALS_RESPONSE_SESSION_TOKEN_KEY        "credentials.sessionToken"

/**
 * @brief Expiration Date key to be searched in the IoT credentials response.
 */
#define CREDENTIALS_RESPONSE_EXPIRATION_DATE_KEY      "credentials.expiration"

/**
 * @brief Represents empty payload for HTTP GET request sent to AWS S3.
 */
#define S3_REQUEST_EMPTY_PAYLOAD                      ""

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
 * @brief Configurations of the initial request headers that are passed to
 * #HTTPClient_InitializeRequestHeaders.
 */


/**
 * @brief The location of the path within the pre-signed URL.
 */
static const char * pcRequestURI;

/**
 *  @brief mbedTLS Hash Context passed to SigV4 cryptointerface for generating the hash digest.
 */
static mbedtls_sha256_context xHashContext = { 0 };

/**
 *  @brief Configurations of the AWS credentials sent to sigV4 library for generating the Authorization Header.
 */
static SigV4Credentials_t xSigvCreds = { 0 };

/**
 * @brief Buffer used in the demo for storing temporary credentials
 * received from AWS TOT credential provider.
 */
static uint8_t ucCredBuffer[ CREDENTIAL_BUFFER_LENGTH ] = { 0 };

/**
 * @brief Represents date in ISO8601 format used in the HTTP requests sent to AWS S3.
 */
static char cDateISO8601[ SIGV4_ISO_STRING_LEN ] = { 0 };

/**
 * @brief Represents Authorization header value generated using SigV4 library.
 */
static char cSigv4Auth[ AWS_HTTP_AUTH_HEADER_VALUE_LEN ];

/**
 * @brief Represents Length of Authorization header value generated using SigV4 library.
 */
static size_t xSigv4AuthLen = AWS_HTTP_AUTH_HEADER_VALUE_LEN;

/**
 * @brief The security token retrieved from AWS IoT credential provider
 * required for making HTTP requests to AWS S3.
 */
static const char * pcSecurityToken;

/**
 * @brief Length of security token retrieved from AWS IoT credential provider
 * required for making HTTP requests to AWS S3.
 */
static size_t xSecurityTokenLen;

/*-----------------------------------------------------------*/

/**
 * @brief The task used to demonstrate the HTTP API.
 *
 * @param[in] pvParameters Parameters as passed at the time of task creation. Not
 * used in this example.
 */
static void prvHTTPDemoTask( void * pvParameters );


/**
 * @brief Establish a HTTP connection with AWS S3 server.
 *
 * @param[in] pxNetworkContext The network context for communication.
 * @param[in] pcServer Address of the server to connect to.
 * @param[in] pxNetworkCredentials Credentials for connecting to the server.
 *
 * @return pdPASS on success, pdFAIL on failure.
 */
static BaseType_t prvConnectToServer( NetworkContext_t * pxNetworkContext,
                                      const char * pcServer,
                                      NetworkCredentials_t * pxNetworkCredentials );
/**
 * @brief Establish a HTTP connection with AWS S3 server.
 *
 * @param[in] pxNetworkContext The network context for communication.
 *
 * @return pdPASS on success, pdFAIL on failure.
 */
static BaseType_t prvConnectToS3Server( NetworkContext_t * pxNetworkContext );

/**
 * @brief Establish a HTTP connection with AWS IoT credential provider server.
 *
 * @param[in] pxNetworkContext The network context for communication.
 *
 * @return pdPASS on success, pdFAIL on failure.
 */
static BaseType_t prvConnectToIotServer( NetworkContext_t * pxNetworkContext );

/**
 * @brief Send a HTTP GET request with empty body and Range header.
 *
 * @param[in] pxTransportInterface The transport interface for making network calls.
 * @param[in] ulRangeStart Start byte for Range header.
 * @param[in] ulRangeEnd End byte for Range header.
 * @param[in] pcPath The Request-URI to the objects of interest. This string
 * should be null-terminated.
 * @param[out] pxResponse Response from the GET request.
 *
 * @return pdPASS on success, pdFAIL on failure.
 */
static BaseType_t prvSendS3HttpEmptyGet( const TransportInterface_t * pxTransportInterface,
                                         uint32_t ulRangeStart,
                                         uint32_t ulRangeEnd,
                                         const char * pcPath,
                                         HTTPResponse_t * pxResponse );

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
 * @brief Send multiple HTTP GET requests, based on a specified path, to
 * download a file in chunks from the host S3 server.
 *
 * @param[in] pxTransportInterface The transport interface for making network
 * calls.
 * @param[in] pcPath The Request-URI to the objects of interest. This string
 * should be null-terminated.
 *
 * @return The status of the file download using multiple GET requests to the
 * server: pdPASS on success, pdFAIL on failure.
 */
static BaseType_t prvDownloadS3ObjectFile( const TransportInterface_t * pxTransportInterface,
                                           const char * pcPath );

/**
 * @brief Parse the credentials retrieved from AWS IOT Credential Provider using coreJSON API.
 *
 * @param[in] pxResponse HTTP response which needs to be parsed to get the credentials.
 * @param[out] pxSigvCreds Buffer passed to store the parsed credentials.
 *
 * @return #JSONSuccess if the credentials are parsed successfully;
 * #JSONNullParameter if any pointer parameters are NULL;
 * #JSONBadParameter if any of the response parameters that needs to be parsed are empty;
 * #JSONNotFound if the key to be parsed is not in the response.
 */
static JSONStatus_t prvParseCredentials( HTTPResponse_t * pxResponse,
                                         SigV4Credentials_t * pxSigvCreds );

/**
 * @brief Retrieve the temporary credentials from AWS IOT Credential Provider.
 *
 * @param[in] pxTransportInterface The transport interface for performing network send/recv operations.
 * @param[out] pcDateISO8601 Buffer to store the ISO8601 formatted date.
 * @param[in] xDateISO8601Len Length of the buffer provided to store ISO8601 formatted date.
 * @param[in,out] pxResponse Response buffer to store the HTTP response received.
 * @param[out] pxSigvCreds Buffer to store the parsed credentials.
 *
 * @return pdPASS on success, pdFAIL on failure.
 */
static BaseType_t prvGetTemporaryCredentials( TransportInterface_t * pxTransportInterface,
                                              const char * pcDateISO8601,
                                              size_t xDateISO8601Len,
                                              HTTPResponse_t * pxResponse,
                                              SigV4Credentials_t * pxSigvCreds );

/**
 * @brief Skip over request line and get the starting address of key-value pair
 * HTTP headers in an HTTP request.
 *
 * @param[in] pxRequestHeaders Pointer to HTTP request headers that contains the HTTP request information.
 * @param[out] pcStartHeaderLoc Buffer to store the start Location of the HTTP header.
 * @param[out] pxHeadersDataLen Length of @p pStartHeaderLoc.
 */
static void prvGetHeaderStartLocFromHttpRequest( HTTPRequestHeaders_t * pxRequestHeaders,
                                                 char ** pcStartHeaderLoc,
                                                 size_t * pxHeadersDataLen );

/**
 * @brief Compute the SHA256 hash of input and output hex representation.
 *
 * @param[in] pcInputStr Input string to compute SHA256
 * @param[in] xInputStrLen Length of `pcInputStr`.
 * @param[out] pcHexOutput Output buffer for hex encoded SHA256 hash.
 *
 * @note The size of `pcHexOutput` should be at least HEX_ENCODED_SHA256_HASH_DIGEST_LENGTH.
 */
static void prvSha256Encode( const char * pcInputStr,
                             size_t xInputStrLen,
                             char * pcHexOutput );

/**
 * @brief Application-defined Hash Initialization function provided
 * to the SigV4 library.
 *
 * @note Refer to SigV4CryptoInterface_t interface documentation for this function.
 */
static int32_t prvSha256Init( void * pxHashContext );

/**
 * @brief Application-defined Hash Update function provided to the SigV4 library.
 *
 * @note Refer to SigV4CryptoInterface_t interface documentation for this function.
 */
static int32_t prvSha256Update( void * pxHashContext,
                                const uint8_t * pucInput,
                                size_t xInputLen );

/**
 * @brief Application-defined Hash Final function provided to the SigV4 library.
 *
 * @note Refer to SigV4CryptoInterface_t interface documentation for this function.
 */
static int32_t prvSha256Final( void * pxHashContext,
                               uint8_t * pucOutput,
                               size_t xOutputLen );

/**
 * @brief CryptoInterface provided to SigV4 library for generating the hash digest.
 */
static SigV4CryptoInterface_t cryptoInterface =
{
    .hashInit      = prvSha256Init,
    .hashUpdate    = prvSha256Update,
    .hashFinal     = prvSha256Final,
    .pHashContext  = &xHashContext,
    .hashBlockLen  = HEX_ENCODED_SHA256_HASH_DIGEST_LENGTH,
    .hashDigestLen = SHA256_HASH_DIGEST_LENGTH,
};

/**
 * @brief SigV4 parameters provided to SigV4 library by the application for generating
 * the Authorization header.
 */
static SigV4Parameters_t xSigv4Params =
{
    .pCredentials     = &xSigvCreds,
    .pDateIso8601     = cDateISO8601,
    .pRegion          = democonfigS3_BUCKET_REGION,
    .regionLen        = sizeof( democonfigS3_BUCKET_REGION ) - 1,
    .pService         = AWS_S3_SERVICE_NAME,
    .serviceLen       = sizeof( AWS_S3_SERVICE_NAME ) - 1,
    .pCryptoInterface = &cryptoInterface,
    .pHttpParameters  = NULL
};

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
 * This demo demonstrates downloading a file from S3 using SigV4 authentication.
 * First the demo establishes a TLS connection with IoT credential provider
 * server to obtain temporary credentials. Then it connects to S3 server and
 * sends HTTP requests to download the file.
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
    UBaseType_t uxDemoRunCount = 0UL;
    /* Response from IoT credential provider */
    HTTPResponse_t xCredentialResponse = { 0 };

    /* The user of this demo must check the logs for any failure codes. */
    BaseType_t xDemoStatus = pdPASS;

    /* Remove compiler warnings about unused parameters. */
    ( void ) pvParameters;

    /* Set the pParams member of the network context with desired transport. */
    xNetworkContext.pParams = &xTlsTransportParams;

    LogInfo( ( "HTTP Client Synchronous S3 download demo using temporary credentials fetched from iot credential provider" ) );

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
        xDemoStatus = connectToServerWithBackoffRetries( prvConnectToIotServer,
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
            LogError( ( "Failed to connect to IoT server: %d.", xDemoStatus ) );
        }

        /******************* Get temp credential from IoT ********************/
        if( xDemoStatus == pdPASS )
        {
            xCredentialResponse.pBuffer = ucCredBuffer;
            xCredentialResponse.bufferLen = CREDENTIAL_BUFFER_LENGTH;
            xDemoStatus = prvGetTemporaryCredentials( &xTransportInterface, cDateISO8601, sizeof( cDateISO8601 ), &xCredentialResponse, &xSigvCreds );
            if( xDemoStatus != pdPASS )
            {
                LogError( ( "Failed to get credential from credential provider: %d.", xDemoStatus ) );
            }
        }
        if( xIsConnectionEstablished == pdTRUE )
        {
            /* Close the connection with IoT credential provider. */
            TLS_FreeRTOS_Disconnect( &xNetworkContext );
            xIsConnectionEstablished = pdFALSE;
        }

        /************************ Connect to S3 server ************************/
        if( xDemoStatus == pdPASS )
        {
            xDemoStatus = connectToServerWithBackoffRetries( prvConnectToS3Server,
                                                             &xNetworkContext );
            if( xDemoStatus != pdPASS )
            {
                LogError( ( "Failed to connect to AWS S3 server: %d.", xDemoStatus ) );
            }

        }

        if( xDemoStatus == pdPASS )
        {
            memset( &xTransportInterface, 0, sizeof( xTransportInterface ) );
            xTransportInterface.pNetworkContext = &xNetworkContext;
            xTransportInterface.send = TLS_FreeRTOS_send;
            xTransportInterface.recv = TLS_FreeRTOS_recv;
            xIsConnectionEstablished = pdTRUE;
        }

        /******************** Download S3 Object File. **********************/

        if( xDemoStatus == pdPASS )
        {
            xDemoStatus = prvDownloadS3ObjectFile( &xTransportInterface,
                                                   AWS_S3_URI_PATH );
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

static BaseType_t prvConnectToServer( NetworkContext_t * pxNetworkContext,
                                      const char * pcServer,
                                      NetworkCredentials_t * pxNetworkCredentials )
{
    TlsTransportStatus_t xNetworkStatus;

    configASSERT( pxNetworkContext != NULL );

    LogInfo( ( "Establishing a TLS session with %s:%d.",
               pcServer,
               democonfigHTTPS_PORT ) );

    /* Attempt to create a server-authenticated TLS connection. */
    xNetworkStatus = TLS_FreeRTOS_Connect( pxNetworkContext,
                                           pcServer,
                                           democonfigHTTPS_PORT,
                                           pxNetworkCredentials,
                                           democonfigTRANSPORT_SEND_RECV_TIMEOUT_MS,
                                           democonfigTRANSPORT_SEND_RECV_TIMEOUT_MS );

    return xNetworkStatus == TLS_TRANSPORT_SUCCESS? pdPASS : pdFAIL;

}

static BaseType_t prvConnectToS3Server( NetworkContext_t * pxNetworkContext )
{
    NetworkCredentials_t xNetworkCredentials = { 0 };
    xNetworkCredentials.disableSni = democonfigDISABLE_SNI;
    /* Set the credentials for establishing a TLS connection. */
    xNetworkCredentials.pRootCa = ( uint8_t * )democonfigS3_ROOT_CA_PEM;
    xNetworkCredentials.rootCaSize = sizeof( democonfigS3_ROOT_CA_PEM );

    return prvConnectToServer( pxNetworkContext, AWS_S3_ENDPOINT, &xNetworkCredentials );
}

static BaseType_t prvConnectToIotServer( NetworkContext_t * pxNetworkContext )
{
    NetworkCredentials_t xNetworkCredentials = { 0 };
    xNetworkCredentials.disableSni = democonfigDISABLE_SNI;
    /* Set the credentials for establishing a TLS connection. */
    xNetworkCredentials.pRootCa =  ( uint8_t * )democonfigIOT_CRED_PROVIDER_ROOT_CA_PEM;
    xNetworkCredentials.rootCaSize = sizeof( democonfigIOT_CRED_PROVIDER_ROOT_CA_PEM );
    xNetworkCredentials.pClientCert = ( uint8_t * )democonfigCLIENT_CERTIFICATE_PEM;
    xNetworkCredentials.clientCertSize = sizeof( democonfigCLIENT_CERTIFICATE_PEM );
    xNetworkCredentials.pPrivateKey = ( uint8_t * )democonfigCLIENT_PRIVATE_KEY_PEM;
    xNetworkCredentials.privateKeySize = sizeof( democonfigCLIENT_PRIVATE_KEY_PEM );

    return prvConnectToServer( pxNetworkContext, democonfigIOT_CREDENTIAL_PROVIDER_ENDPOINT, &xNetworkCredentials );
}

static BaseType_t prvGetS3ObjectFileSize( size_t * pxFileSize,
                                          const TransportInterface_t * pxTransportInterface,
                                          const char * pcHost,
                                          size_t xHostLen,
                                          const char * pcPath )
{
    BaseType_t xStatus = pdPASS;
    HTTPStatus_t xHTTPStatus;
    HTTPResponse_t xResponse;

    /* The location of the file size in pcContentRangeValStr. */
    char * pcFileSizeStr = NULL;

    /* String to store the Content-Range header value. */
    char * pcContentRangeValStr = NULL;
    size_t xContentRangeValStrLength = 0;

    configASSERT( pxTransportInterface != NULL );
    configASSERT( pcHost != NULL );
    configASSERT( pcPath != NULL );

    LogInfo( ( "Getting file object size from host..." ) );

    /* Add the header to get bytes=0-0. S3 will respond with a Content-Range
     * header that contains the size of the file in it. This header will
     * look like: "Content-Range: bytes 0-0/FILESIZE". The body will have a
     * single byte that we are ignoring. */
    xStatus = prvSendS3HttpEmptyGet( pxTransportInterface, 0, 0, pcPath, &xResponse );

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

static BaseType_t prvSendS3HttpEmptyGet( const TransportInterface_t * pxTransportInterface,
                                         uint32_t ulRangeStart,
                                         uint32_t ulRangeEnd,
                                         const char * pcPath,
                                         HTTPResponse_t * pxResponse )
{
    BaseType_t xStatus = pdPASS;
    HTTPStatus_t xHttpStatus;
    SigV4Status_t xSigv4Status;
    SigV4HttpParameters_t xSigv4HttpParams;

    HTTPRequestHeaders_t xRequestHeaders = { 0 };
    HTTPRequestInfo_t xRequestInfo = { 0 };

    /* Store Signature used in AWS HTTP requests generated using SigV4 library. */
    char * pcSignature = NULL;
    size_t xSignatureLen = 0;
    /* Pointer to start of key-value pair buffer in request buffer. This is
     * used for Sigv4 signing */
    char * pcHeaderStart;
    size_t xHeadersLen;
    static char cPayloadSha256[ HEX_ENCODED_SHA256_HASH_DIGEST_LENGTH ];

    configASSERT( pxTransportInterface != NULL );
    configASSERT( pcPath != NULL );

    /* Initialize all HTTP Client library API structs to 0. */
    ( void ) memset( pxResponse, 0, sizeof( HTTPResponse_t ) );

    /* Initialize the request object. */
    xRequestInfo.pHost = AWS_S3_ENDPOINT;
    xRequestInfo.hostLen = strlen( AWS_S3_ENDPOINT );
    xRequestInfo.pMethod = HTTP_METHOD_GET;
    xRequestInfo.methodLen = httpexampleHTTP_METHOD_GET_LENGTH;
    xRequestInfo.pPath = pcPath;
    xRequestInfo.pathLen = strlen( pcPath );

    /* Set "Connection" HTTP header to "keep-alive" so that multiple requests
     * can be sent over the same established TCP connection. This is done in
     * order to download the file in parts. */
    xRequestInfo.reqFlags = HTTP_REQUEST_KEEP_ALIVE_FLAG;

    /* Set the buffer used for storing request headers. */
    xRequestHeaders.pBuffer = ucUserBuffer;
    xRequestHeaders.bufferLen = democonfigUSER_BUFFER_LENGTH;

    /* Initialize the response object. The same buffer used for storing request
     * headers is reused here. */
    pxResponse->pBuffer = ucUserBuffer;
    pxResponse->bufferLen = democonfigUSER_BUFFER_LENGTH;

    xHttpStatus = HTTPClient_InitializeRequestHeaders( &xRequestHeaders,
                                                       &xRequestInfo );
    if( xHttpStatus != HTTPSuccess )
    {
        LogError( ( "Failed initialize HTTP headers: Error=%s.",
                    HTTPClient_strerror( xHttpStatus ) ) );
        xStatus = pdFAIL;
    }

    if( xStatus == pdPASS )
    {
        /* Add the X-AMZ-DATE required headers to the request. */
        xHttpStatus = HTTPClient_AddHeader( &xRequestHeaders,
                                            SIGV4_HTTP_X_AMZ_DATE_HEADER,
                                            sizeof( SIGV4_HTTP_X_AMZ_DATE_HEADER ) - 1,
                                            cDateISO8601,
                                            SIGV4_ISO_STRING_LEN );
        if( xHttpStatus != HTTPSuccess )
        {
            LogError( ( "Failed to add X-AMZ-DATE to request headers: Error=%s.",
                        HTTPClient_strerror( xHttpStatus ) ) );
            xStatus = pdFAIL;
        }
    }

    if( xStatus == pdPASS )
    {
        /* S3 requires the security token as part of the canonical headers. */
        xHttpStatus = HTTPClient_AddHeader( &xRequestHeaders,
                                            SIGV4_HTTP_X_AMZ_SECURITY_TOKEN_HEADER,
                                            sizeof( SIGV4_HTTP_X_AMZ_SECURITY_TOKEN_HEADER ) - 1,
                                            pcSecurityToken,
                                            xSecurityTokenLen );
        if( xHttpStatus != HTTPSuccess )
        {
            LogError( ( "Failed to add X-AMZ-SECURITY-TOKEN to request headers: Error=%s.",
                        HTTPClient_strerror( xHttpStatus ) ) );
            xStatus = pdFAIL;
        }
    }

    if( xStatus == pdPASS )
    {
        /* Add Range header */
        xHttpStatus = HTTPClient_AddRangeHeader( &xRequestHeaders,
                                                 ulRangeStart,
                                                 ulRangeEnd );
        if( xHttpStatus != HTTPSuccess )
        {
            LogError( ( "Failed to add range to request headers: Error=%s.",
                        HTTPClient_strerror( xHttpStatus ) ) );
            xStatus = pdFAIL;
        }
    }

    if( xStatus == pdPASS )
    {
        /* Add the SHA256 of an empty payload. */
        prvSha256Encode( S3_REQUEST_EMPTY_PAYLOAD, sizeof(S3_REQUEST_EMPTY_PAYLOAD) - 1, cPayloadSha256 );
        xHttpStatus = HTTPClient_AddHeader( &xRequestHeaders,
                                           SIGV4_HTTP_X_AMZ_CONTENT_SHA256_HEADER,
                                           sizeof( SIGV4_HTTP_X_AMZ_CONTENT_SHA256_HEADER ) - 1,
                                           cPayloadSha256,
                                           sizeof( cPayloadSha256 ) );
        if( xHttpStatus != HTTPSuccess )
        {
            LogError( ( "Failed to add X-AMZ-CONTENT-SHA256-HEADER to request headers: Error=%s.",
                        HTTPClient_strerror( xHttpStatus ) ) );
            xStatus = pdFAIL;
        }
    }

    if( xStatus == pdPASS )
    {
        /* Find the start key-value pairs for sigv4 signing. */
        prvGetHeaderStartLocFromHttpRequest( &xRequestHeaders, &pcHeaderStart, &xHeadersLen );

        /* Setup the HTTP parameters. */
        xSigv4HttpParams.pHttpMethod = xRequestInfo.pMethod;
        xSigv4HttpParams.httpMethodLen = xRequestInfo.methodLen;
        /* None of the requests parameters below are pre-canonicalized */
        xSigv4HttpParams.flags = 0;
        xSigv4HttpParams.pPath = xRequestInfo.pPath;
        xSigv4HttpParams.pathLen = xRequestInfo.pathLen;
        /* AWS S3 request does not require any Query parameters. */
        xSigv4HttpParams.pQuery = NULL;
        xSigv4HttpParams.queryLen = 0;
        xSigv4HttpParams.pHeaders = pcHeaderStart;
        xSigv4HttpParams.headersLen = xHeadersLen;
        xSigv4HttpParams.pPayload = S3_REQUEST_EMPTY_PAYLOAD;
        xSigv4HttpParams.payloadLen = sizeof( S3_REQUEST_EMPTY_PAYLOAD ) - 1U;

        /* Initializing sigv4Params with Http parameters required for the HTTP request. */
        xSigv4Params.pHttpParameters = &xSigv4HttpParams;

        /* Generate HTTP Authorization header using SigV4_GenerateHTTPAuthorization API. */
        xSigv4Status = SigV4_GenerateHTTPAuthorization( &xSigv4Params, cSigv4Auth, &xSigv4AuthLen, &pcSignature, &xSignatureLen );

        if( xSigv4Status != SigV4Success )
        {
            LogError( ( "Failed to generate HTTP AUTHORIZATION Header: %d", xSigv4Status ) );
            xStatus = pdFAIL;
        }
    }

    if( xStatus == pdPASS )
    {
        /* Add the authorization header to the HTTP request headers. */
        xHttpStatus = HTTPClient_AddHeader( &xRequestHeaders,
                                            SIGV4_AUTH_HEADER_FIELD_NAME,
                                            sizeof( SIGV4_AUTH_HEADER_FIELD_NAME ) - 1,
                                            cSigv4Auth,
                                            xSigv4AuthLen );

        if( xHttpStatus != HTTPSuccess )
        {
            LogError( ( "Failed to add Sigv4 auth header. Error=%s.",
                        HTTPClient_strerror( xHttpStatus ) ) );
            xStatus = pdFAIL;
        }
    }

    if( xStatus == pdPASS )
    {
        /* Send out the http request */
        xHttpStatus = HTTPClient_Send( pxTransportInterface,
                                       &xRequestHeaders,
                                       NULL,
                                       0,
                                       pxResponse,
                                       0 );
        if( xHttpStatus != HTTPSuccess )
        {
            LogError( ( "Failed to send HTTP GET request to %s%s: Error=%s.",
                        xRequestInfo.pHost, xRequestInfo.pPath, HTTPClient_strerror( xHttpStatus ) ) );
            xStatus = pdFAIL;
        }
    }

    if( xStatus == pdPASS )
    {
        LogDebug( ( "Received HTTP response from %s%s...",
                    xRequestInfo.pHost, xRequestInfo.pPath ) );
        LogDebug( ( "Response Headers:\n%.*s",
                    pxResponse->headersLen,
                    pxResponse->pHeaders ) );
        LogDebug( ( "Response Body:\n%.*s\n",
                    pxResponse->bodyLen,
                    pxResponse->pBody ) );

        /* Since Range is set in the header, the success status is 206 Partial Content. */
        if( pxResponse->statusCode != httpexampleHTTP_STATUS_CODE_PARTIAL_CONTENT )
        {
            LogError( ( "Received an invalid response from the server "
                        "(Status Code: %u).",
                        pxResponse->statusCode ) );
            xStatus = pdFAIL;
        }
    }

    return xStatus;
}

static BaseType_t prvDownloadS3ObjectFile( const TransportInterface_t * pxTransportInterface,
                                           const char * pcPath )
{
    BaseType_t xStatus = pdFAIL;
    HTTPResponse_t xResponse;
    /* The size of the file we are trying to download in S3. */
    size_t xFileSize = 0;
    /* The number of bytes we want to request with in each range of the file bytes. */
    size_t xNumReqBytes = 0;
    /* curByte indicates which starting byte we want to download next. */
    size_t xCurByte = 0;

    /* Verify the file exists by retrieving the file size. */
    xStatus = prvGetS3ObjectFileSize( &xFileSize,
                                      pxTransportInterface,
                                      AWS_S3_ENDPOINT,
                                      sizeof( AWS_S3_ENDPOINT ) - 1,
                                      pcPath );

    if( xFileSize < democonfigRANGE_REQUEST_LENGTH )
    {
        xNumReqBytes = xFileSize;
    }
    else
    {
        xNumReqBytes = democonfigRANGE_REQUEST_LENGTH;
    }

    /* Here we iterate sending byte range requests until the full file has been
     * downloaded. We keep track of the next byte to download with xCurByte. When
     * this reaches the xFileSize we stop downloading. */
    while( ( xStatus == pdPASS ) && ( xCurByte < xFileSize ) )
    {
        xStatus = prvSendS3HttpEmptyGet( pxTransportInterface,
                                         xCurByte,
                                         xCurByte + xNumReqBytes - 1,
                                         pcPath,
                                         &xResponse );

        if( xStatus == pdPASS )
        {
            /* We increment by the content length because the server may not
             * have sent us the range we request. */
            xCurByte += xResponse.contentLength;

            if( ( xFileSize - xCurByte ) < xNumReqBytes )
            {
                xNumReqBytes = xFileSize - xCurByte;
            }

            xStatus = ( xResponse.statusCode == httpexampleHTTP_STATUS_CODE_PARTIAL_CONTENT ) ? pdPASS : pdFAIL;
        }
        else
        {
            LogError( ( "An error occurred in downloading the file. "
                        "Failed to send HTTP GET request to %s%s: Error=%u.",
                        AWS_S3_ENDPOINT, pcPath, xResponse.statusCode ) );
        }
    }

    return xStatus;
}

static BaseType_t prvGetTemporaryCredentials( TransportInterface_t * pxTransportInterface,
                                              const char * pcDateISO8601,
                                              size_t xDateISO8601Len,
                                              HTTPResponse_t * pxResponse,
                                              SigV4Credentials_t * pxSigvCreds )
{
    BaseType_t xStatus = pdPASS;
    HTTPStatus_t xHttpStatus = HTTPSuccess;
    SigV4Status_t xSigv4Status = SigV4Success;
    JSONStatus_t xJsonStatus = JSONSuccess;
    HTTPRequestHeaders_t xRequestHeaders = { 0 };
    HTTPRequestInfo_t xRequestInfo = { 0 };
    const char * pcCredServer = democonfigIOT_CREDENTIAL_PROVIDER_ENDPOINT;
    size_t xCredServerLen = strlen( democonfigIOT_CREDENTIAL_PROVIDER_ENDPOINT );
    const char * pcPath = AWS_IOT_CREDENTIAL_PROVIDER_URI_PATH;
    size_t xPathLen = strlen( AWS_IOT_CREDENTIAL_PROVIDER_URI_PATH );
    const char * pDate = NULL;
    size_t xDateLen;

    configASSERT( pxTransportInterface != NULL );
    configASSERT( pxSigvCreds != NULL );
    configASSERT( pcDateISO8601 != NULL );
    configASSERT( xDateISO8601Len > 0 );

    /* Initialize Request header buffer. */
    xRequestHeaders.pBuffer = ucUserBuffer;
    xRequestHeaders.bufferLen = democonfigUSER_BUFFER_LENGTH;

    /* Set HTTP request parameters to get temporary AWS IoT credentials. */
    xRequestInfo.pMethod = HTTP_METHOD_GET;
    xRequestInfo.methodLen = sizeof( HTTP_METHOD_GET ) - 1;
    xRequestInfo.pPath = pcPath;
    xRequestInfo.pathLen = xPathLen;
    xRequestInfo.pHost = pcCredServer;
    xRequestInfo.hostLen = xCredServerLen;
    xRequestInfo.reqFlags = 0;

    pxResponse->pHeaderParsingCallback = NULL;

    /* Initialize request headers. */
    xHttpStatus = HTTPClient_InitializeRequestHeaders( &xRequestHeaders, &xRequestInfo );

    if( xHttpStatus != HTTPSuccess )
    {
        LogError( ( "Failed to initialize request headers: Error=%s.",
                    HTTPClient_strerror( xHttpStatus ) ) );
        xStatus = pdFAIL;
    }

    if( xStatus == pdPASS )
    {
        /* Add AWS_IOT_THING_NAME_HEADER_FIELD header to the HTTP request headers. */
        xHttpStatus = HTTPClient_AddHeader( &xRequestHeaders,
                                            AWS_IOT_THING_NAME_HEADER_FIELD,
                                            sizeof( AWS_IOT_THING_NAME_HEADER_FIELD ) - 1U,
                                            democonfigIOT_THING_NAME,
                                            sizeof( democonfigIOT_THING_NAME ) - 1U );

        if( xHttpStatus != HTTPSuccess )
        {
            LogError( ( "Failed to add x-amz-iot-thing-name header to request headers: Error=%s.",
                        HTTPClient_strerror( xHttpStatus ) ) );
            xStatus = pdFAIL;
        }
    }

    if( xStatus == pdPASS )
    {
        /* Send the request to AWS IoT Credentials Provider to obtain temporary credentials
         * so that the demo application can access configured S3 bucket thereafter. */
        xHttpStatus = HTTPClient_Send( pxTransportInterface,
                                       &xRequestHeaders,
                                       NULL,
                                       0,
                                       pxResponse,
                                       0 );

        if( xHttpStatus != HTTPSuccess )
        {
            LogError( ( "Failed to send HTTP GET request to %s%s  for obtaining temporary credentials: Error=%s.",
                        pcCredServer, pcPath, HTTPClient_strerror( xHttpStatus ) ) );
            xStatus = pdFAIL;
        }
    }

    if( xStatus == pdPASS )
    {
        LogDebug( ( "AWS IoT credential provider response: %.*s.",
                    ( int32_t ) pxResponse->bufferLen, pxResponse->pBuffer ) );

        /* Parse the credentials received in the response. */
        xJsonStatus = prvParseCredentials( pxResponse, pxSigvCreds );

        if( xJsonStatus != JSONSuccess )
        {
            LogError( ( "Failed to parse temporary IoT credentials retrieved from AWS IoT credential provider" ) );
            xStatus = pdFAIL;
        }
    }

    /* Get the AWS IoT date from the http response. */
    if( xStatus == pdPASS )
    {
        xHttpStatus = HTTPClient_ReadHeader( pxResponse,
                                             AWS_IOT_CRED_PROVIDER_RESPONSE_DATE_HEADER,
                                             sizeof( AWS_IOT_CRED_PROVIDER_RESPONSE_DATE_HEADER ) - 1,
                                             &pDate,
                                             &xDateLen );

        if( xHttpStatus != HTTPSuccess )
        {
            LogError( ( "Failed to retrieve \"%s\" header from response: Error=%s.",
                        AWS_IOT_CRED_PROVIDER_RESPONSE_DATE_HEADER, HTTPClient_strerror( xHttpStatus ) ) );
            xStatus = pdFAIL;
        }
    }

    if( xStatus == pdPASS )
    {
        /* Convert AWS IoT date retrieved from IoT server to ISO 8601 date format. */
        xSigv4Status = SigV4_AwsIotDateToIso8601( pDate, xDateLen, pcDateISO8601, xDateISO8601Len );

        if( xSigv4Status != SigV4Success )
        {
            LogError( ( "Failed to convert AWS IoT date to ISO 8601 format." ) );
            xStatus = pdFAIL;
        }
    }

    return xStatus;
}

/*-----------------------------------------------------------*/

static JSONStatus_t prvParseCredentials( HTTPResponse_t * pxResponse,
                                         SigV4Credentials_t * pxSigvCreds )
{
    JSONStatus_t xJsonStatus = JSONSuccess;
    /* Expiration time for temporary credentials */
    char * pcExpiration;
    size_t xExpirationLen;

    configASSERT( pxResponse != NULL );
    configASSERT( pxSigvCreds != NULL );

    if( xJsonStatus == JSONSuccess )
    {
        /* Get accessKeyId from HTTP response. */
        xJsonStatus = JSON_Search( ( char * ) pxResponse->pBody,
                                   pxResponse->bodyLen,
                                   CREDENTIALS_RESPONSE_ACCESS_KEY_ID_KEY,
                                   strlen( CREDENTIALS_RESPONSE_ACCESS_KEY_ID_KEY ),
                                   ( char ** ) &( pxSigvCreds->pAccessKeyId ),
                                   &( pxSigvCreds->accessKeyIdLen ) );

        if( xJsonStatus != JSONSuccess )
        {
            LogError( ( "Error parsing accessKeyId in the credentials." ) );
        }
    }

    if( xJsonStatus == JSONSuccess )
    {
        /* Get secretAccessKey from HTTP response. */
        xJsonStatus = JSON_Search( ( char * ) pxResponse->pBody,
                                   pxResponse->bodyLen,
                                   CREDENTIALS_RESPONSE_SECRET_ACCESS_KEY,
                                   strlen( CREDENTIALS_RESPONSE_SECRET_ACCESS_KEY ),
                                   ( char ** ) &( pxSigvCreds->pSecretAccessKey ),
                                   &( pxSigvCreds->secretAccessKeyLen ) );

        if( xJsonStatus != JSONSuccess )
        {
            LogError( ( "Error parsing secretAccessKey in the credentials." ) );
        }
    }

    if( xJsonStatus == JSONSuccess )
    {
        /* Get sessionToken from HTTP response. */
        xJsonStatus = JSON_Search( ( char * ) pxResponse->pBody,
                                  pxResponse->bodyLen,
                                  CREDENTIALS_RESPONSE_SESSION_TOKEN_KEY,
                                  strlen( CREDENTIALS_RESPONSE_SESSION_TOKEN_KEY ),
                                  ( char ** ) &( pcSecurityToken ),
                                  &( xSecurityTokenLen ) );

        if( xJsonStatus != JSONSuccess )
        {
            LogError( ( "Error parsing sessionToken in the credentials." ) );
        }
    }

    if( xJsonStatus == JSONSuccess )
    {
        /* Get expiration date from HTTP response. */
        xJsonStatus = JSON_Search( ( char * ) pxResponse->pBody,
                                  pxResponse->bodyLen,
                                  CREDENTIALS_RESPONSE_EXPIRATION_DATE_KEY,
                                  strlen( CREDENTIALS_RESPONSE_EXPIRATION_DATE_KEY ),
                                  ( char ** ) &( pcExpiration ),
                                  &( xExpirationLen ) );

        if( xJsonStatus != JSONSuccess )
        {
            LogError( ( "Error parsing expiration date in the credentials." ) );
        }
        else
        {
            LogInfo( ( "AWS IoT credentials will expire after this timestamp: %.*s.", xExpirationLen, pcExpiration ) );
        }
    }

    return xJsonStatus;
}

static int32_t prvSha256Init( void * pxHashContext )
{
    mbedtls_sha256_init( ( mbedtls_sha256_context * ) pxHashContext );
    return mbedtls_sha256_starts_ret( ( mbedtls_sha256_context * ) pxHashContext, 0 );
}

/*-----------------------------------------------------------*/

static int32_t prvSha256Update( void * pxHashContext,
                                const uint8_t * pucInput,
                                size_t xInputLen )
{
    return mbedtls_sha256_update_ret( ( mbedtls_sha256_context * ) pxHashContext,
                                      ( const unsigned char * ) pucInput,
                                      xInputLen );
}

/*-----------------------------------------------------------*/

static int32_t prvSha256Final( void * pxHashContext,
                               uint8_t * pucOutput,
                               size_t xOutputLen )
{
    configASSERT( xOutputLen >= SHA256_HASH_DIGEST_LENGTH );

    ( void ) xOutputLen;

    return mbedtls_sha256_finish_ret( ( mbedtls_sha256_context * ) pxHashContext,
                                      ( unsigned char * ) pucOutput );
}

static void prvGetHeaderStartLocFromHttpRequest( HTTPRequestHeaders_t * pxRequestHeaders,
                                                 char ** pcStartHeaderLoc,
                                                 size_t * pxHeadersDataLen )
{
    size_t xHeaderLen = pxRequestHeaders->headersLen;
    char * pcHeaders = ( char * ) pxRequestHeaders->pBuffer;
    bool xNewLineFound = false;

    configASSERT( pcStartHeaderLoc != NULL );
    configASSERT( pxHeadersDataLen != NULL );

    while( xHeaderLen >= 2 )
    {
        /* The request line ends in \r\n. Look for \r\n. */
        if( 0 == strncmp( pcHeaders, "\r\n", strlen( "\r\n" ) ) )
        {
            xNewLineFound = true;
            break;
        }

        pcHeaders++;
        xHeaderLen--;
    }

    if( xNewLineFound == false )
    {
        LogError( ( "Failed to find starting location of HTTP headers in HTTP request: \"\\r\\n\" missing before start of HTTP headers." ) );
    }

    configASSERT( xNewLineFound != false );

    /* Moving header pointer past "\r\n" .*/
    *pxHeadersDataLen = xHeaderLen - 2;
    *pcStartHeaderLoc = pcHeaders + 2;
}

static void prvSha256Encode( const char * pcInputStr,
                             size_t xInputStrLen,
                             char * pcHexOutput )
{
    configASSERT( pcInputStr != NULL );
    configASSERT( xInputStrLen >= 0 );
    configASSERT( pcHexOutput != NULL );

    const char cHexChars[] = "0123456789abcdef";
    char * pcOutputChar = pcHexOutput;
    static uint8_t ucSha256[ SHA256_HASH_DIGEST_LENGTH ];

    mbedtls_sha256_ret( pcInputStr, xInputStrLen, ucSha256, 0 );

    for(size_t i = 0; i < SHA256_HASH_DIGEST_LENGTH; i++ )
    {
        *pcOutputChar = cHexChars[ ( ucSha256[ i ] & 0xF0 ) >> 4 ];
        pcOutputChar++;
        *pcOutputChar = cHexChars[ ( ucSha256[ i ] & 0x0F ) ];
        pcOutputChar++;
    }
}
