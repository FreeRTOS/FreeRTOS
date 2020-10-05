/*
 * FreeRTOS OTA V1.2.0
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
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */


/* Standard library include. */
#include <stdbool.h>
#include <string.h>
#include <stdio.h>

/* Error handling from C-SDK. */
#include "iot_error.h"

/* HTTP includes. */
#include "iot_https_client.h"
#include "iot_https_utils.h"

/* Network manager. */
#include "platform/iot_network.h"

/* OTA includes. */
#include "aws_iot_ota_agent.h"
#include "aws_iot_ota_agent_internal.h"
#include "aws_iot_ota_http.h"

/* Logging includes. */
#ifdef IOT_LOG_LEVEL_GLOBAL
    #define LIBRARY_LOG_LEVEL    IOT_LOG_LEVEL_GLOBAL
#else
    #define LIBRARY_LOG_LEVEL    IOT_LOG_INFO
#endif
#define LIBRARY_LOG_NAME         ( "OTA" )
#include "iot_logging_setup.h"

/* Jump to cleanup section. */
#define OTA_GOTO_CLEANUP()              IOT_GOTO_CLEANUP()

/* Start of the cleanup section. */
#define OTA_FUNCTION_CLEANUP_BEGIN()    IOT_FUNCTION_CLEANUP_BEGIN()

/* End of the cleanup section. */
#define OTA_FUNCTION_CLEANUP_END()

/* Empty cleanup section. */
#define OTA_FUNCTION_NO_CLEANUP()    OTA_FUNCTION_CLEANUP_BEGIN(); OTA_FUNCTION_CLEANUP_END()

/* Maximum OTA file size string in byte. The OTA service current limits the file size to 16 MB.*/
#define OTA_MAX_FILE_SIZE_STR        "16777216"

/* String length of the maximum OTA file size string, not including the null character. */
#define OTA_MAX_FILE_SIZE_STR_LEN    ( sizeof( OTA_MAX_FILE_SIZE_STR ) - 1 )

/* TLS port for HTTPS. */
#define HTTPS_PORT                   ( ( uint16_t ) 443 )

/* Baltimore Cybertrust associated with the S3 server certificate. */
#define HTTPS_TRUSTED_ROOT_CA                                            \
    "-----BEGIN CERTIFICATE-----\n"                                      \
    "MIIDdzCCAl+gAwIBAgIEAgAAuTANBgkqhkiG9w0BAQUFADBaMQswCQYDVQQGEwJJ\n" \
    "RTESMBAGA1UEChMJQmFsdGltb3JlMRMwEQYDVQQLEwpDeWJlclRydXN0MSIwIAYD\n" \
    "VQQDExlCYWx0aW1vcmUgQ3liZXJUcnVzdCBSb290MB4XDTAwMDUxMjE4NDYwMFoX\n" \
    "DTI1MDUxMjIzNTkwMFowWjELMAkGA1UEBhMCSUUxEjAQBgNVBAoTCUJhbHRpbW9y\n" \
    "ZTETMBEGA1UECxMKQ3liZXJUcnVzdDEiMCAGA1UEAxMZQmFsdGltb3JlIEN5YmVy\n" \
    "VHJ1c3QgUm9vdDCCASIwDQYJKoZIhvcNAQEBBQADggEPADCCAQoCggEBAKMEuyKr\n" \
    "mD1X6CZymrV51Cni4eiVgLGw41uOKymaZN+hXe2wCQVt2yguzmKiYv60iNoS6zjr\n" \
    "IZ3AQSsBUnuId9Mcj8e6uYi1agnnc+gRQKfRzMpijS3ljwumUNKoUMMo6vWrJYeK\n" \
    "mpYcqWe4PwzV9/lSEy/CG9VwcPCPwBLKBsua4dnKM3p31vjsufFoREJIE9LAwqSu\n" \
    "XmD+tqYF/LTdB1kC1FkYmGP1pWPgkAx9XbIGevOF6uvUA65ehD5f/xXtabz5OTZy\n" \
    "dc93Uk3zyZAsuT3lySNTPx8kmCFcB5kpvcY67Oduhjprl3RjM71oGDHweI12v/ye\n" \
    "jl0qhqdNkNwnGjkCAwEAAaNFMEMwHQYDVR0OBBYEFOWdWTCCR1jMrPoIVDaGezq1\n" \
    "BE3wMBIGA1UdEwEB/wQIMAYBAf8CAQMwDgYDVR0PAQH/BAQDAgEGMA0GCSqGSIb3\n" \
    "DQEBBQUAA4IBAQCFDF2O5G9RaEIFoN27TyclhAO992T9Ldcw46QQF+vaKSm2eT92\n" \
    "9hkTI7gQCvlYpNRhcL0EYWoSihfVCr3FvDB81ukMJY2GQE/szKN+OMY3EU/t3Wgx\n" \
    "jkzSswF07r51XgdIGn9w/xZchMB5hbgF/X++ZRGjD8ACtPhSNzkE1akxehi/oCr0\n" \
    "Epn3o0WC4zxe9Z2etciefC7IpJ5OCBRLbf1wbWsaY71k5h+3zvDyny67G7fyUIhz\n" \
    "ksLi4xaNmjICq44Y3ekQEe5+NauQrz4wlHrQMz2nZQ/1/I6eYs9HRCwBXbsdtTLS\n" \
    "R9I4LtD+gdwyah617jzV/OeBHRnDJELqYzmp\n"                             \
    "-----END CERTIFICATE-----\n"

/* Buffer size for HTTP connection context. This is the minimum size from HTTP library, we cannot
 * use it directly because it's only available at runtime. */
#define HTTPS_CONNECTION_USER_BUFFER_SIZE       256

/* Buffer size for HTTP request context and header.*/
#define HTTPS_REQUEST_USER_BUFFER_SIZE          2048

/* Buffer size for HTTP response context and header.*/
#define HTTPS_RESPONSE_USER_BUFFER_SIZE         1024

/* Buffer size for HTTP response body.*/
#define HTTPS_RESPONSE_BODY_BUFFER_SIZE         OTA_FILE_BLOCK_SIZE

/* Default timeout for HTTP synchronous request. */
#define HTTP_SYNC_TIMEOUT                       3000

/**
 * The maximum length of the "Range" field in HTTP header.
 *
 * The maximum file size of OTA download is OTA_MAX_FILE_SIZE_STR bytes. The header value string is
 * of the form: "bytes=N-M". So the length is len("bytes=-") + len(N) + len(M) + the NULL terminator.
 * The maximum length is 7 + OTA_MAX_FILE_SIZE_STR_LEN * 2 + 1.
 */
#define HTTP_HEADER_RANGE_VALUE_MAX_LEN         ( 7 + ( OTA_MAX_FILE_SIZE_STR_LEN ) * 2 + 1 )

/**
 * The maximum length of the "Connection" field in HTTP header.
 *
 * The value could be "close" or "keep-alive", so the maximum length is sizeof("keep-alive"), this
 * includes the NULL terminator.
 */
#define HTTP_HEADER_CONNECTION_VALUE_MAX_LEN    ( sizeof( "keep-alive" ) )

/* Struct for HTTP callback data. */
typedef struct _httpCallbackData
{
    char pRangeValueStr[ HTTP_HEADER_RANGE_VALUE_MAX_LEN ]; /* Buffer to write the HTTP "range" header value string. */
} _httpCallbackData_t;

/* Struct for HTTP connection configuration and handle. */
typedef struct _httpConnection
{
    IotHttpsConnectionInfo_t connectionConfig;   /* Configurations for the HTTPS connection. */
    IotHttpsConnectionHandle_t connectionHandle; /* Handle identifying the HTTPS connection. */
} _httpConnection_t;

/* Struct for HTTP request configuration and handle. */
typedef struct _httpRequest
{
    IotHttpsAsyncInfo_t asyncInfo;         /* Asynchronous request configurations. */
    IotHttpsRequestInfo_t requestConfig;   /* Configurations for the HTTPS request. */
    IotHttpsRequestHandle_t requestHandle; /* Handle identifying the HTTP request. */
} _httpRequest_t;

/* Struct for HTTP response configuration and handle. */
typedef struct _httpResponse
{
    IotHttpsResponseInfo_t responseConfig;   /* Configurations for the HTTPS response. */
    IotHttpsResponseHandle_t responseHandle; /* Handle identifying the HTTP response. */
} _httpResponse_t;

/* Struct for HTTP download information. */
typedef struct _httpUrlInfo
{
    const char * pPath;    /* Resource path to the firmware in HTTP URL. */
    size_t pathLength;     /* Length of the resource path. */
    const char * pAddress; /* Address to the server in HTTP URL. */
    size_t addressLength;  /* Length of the address. */
} _httpUrlInfo_t;

/* Struct to keep track of the internal HTTP downloader state. */
typedef enum
{
    OTA_HTTP_ERR_NONE = 0,
    OTA_HTTP_ERR_GENERIC = 101,
    OTA_HTTP_ERR_CANCELED = 102,
    OTA_HTTP_ERR_NEED_RECONNECT = 103,
    OTA_HTTP_ERR_URL_EXPIRED = 104
} _httpErr;

typedef enum
{
    OTA_HTTP_IDLE = 0,
    OTA_HTTP_SENDING_REQUEST,
    OTA_HTTP_WAITING_RESPONSE,
    OTA_HTTP_PROCESSING_RESPONSE
} _httpState;

/* Struct for OTA HTTP downloader. */
typedef struct _httpDownloader
{
    OTA_AgentContext_t * pAgentCtx;       /* OTA agent context. */
    _httpState state;                     /* HTTP downloader state. */
    _httpErr err;                         /* HTTP downloader error status. */
    _httpUrlInfo_t httpUrlInfo;           /* HTTP url of the file to download. */
    _httpConnection_t httpConnection;     /* HTTP connection data. */
    _httpRequest_t httpRequest;           /* HTTP request data. */
    _httpResponse_t httpResponse;         /* HTTP response data. */
    _httpCallbackData_t httpCallbackData; /* Data used in the HTTP callback. */
    uint32_t currBlock;                   /* Current requesting block in bitmap. */
    uint32_t currBlockSize;               /* Size of current requesting block. */
} _httpDownloader_t;

/* Global HTTP downloader instance. */
static _httpDownloader_t _httpDownloader = { 0 };

/* Buffers for HTTP library. */
uint8_t * pConnectionUserBuffer = NULL; /* Buffer to store the HTTP connection context. */
uint8_t * pRequestUserBuffer = NULL;    /* Buffer to store the HTTP request context and header. */
uint8_t * pResponseUserBuffer = NULL;   /* Buffer to store the HTTP response context and header. */
uint8_t * pResponseBodyBuffer = NULL;   /* Buffer to store the HTTP response body. */

/* We need to use this function defined in iot_logging_task_dynamic_buffers.c to print HTTP message
 * without appending the task name and tick count. */
void vLoggingPrint( const char * pcMessage );

/*-----------------------------------------------------------*/

/* Helper function to allocate buffers for HTTP library. */
static bool _httpAllocateBuffers()
{
    bool isSuccess = true;

    pConnectionUserBuffer = pvPortMalloc( HTTPS_CONNECTION_USER_BUFFER_SIZE );

    if( pConnectionUserBuffer == NULL )
    {
        IotLogError( "Failed to allocate memory for HTTP connection user buffer." );
        isSuccess = false;
    }

    pRequestUserBuffer = pvPortMalloc( HTTPS_REQUEST_USER_BUFFER_SIZE );

    if( isSuccess && ( pRequestUserBuffer == NULL ) )
    {
        IotLogError( "Failed to allocate memory for HTTP request user buffer." );
        isSuccess = false;
    }

    pResponseUserBuffer = pvPortMalloc( HTTPS_RESPONSE_USER_BUFFER_SIZE );

    if( isSuccess && ( pResponseUserBuffer == NULL ) )
    {
        IotLogError( "Failed to allocate memory for HTTP response user buffer." );
        isSuccess = false;
    }

    pResponseBodyBuffer = pvPortMalloc( HTTPS_RESPONSE_BODY_BUFFER_SIZE );

    if( isSuccess && ( pResponseBodyBuffer == NULL ) )
    {
        IotLogError( "Failed to allocate memory for HTTP response body buffer." );
        isSuccess = false;
    }

    return isSuccess;
}

/* Helper function to free buffers for HTTP library. */
static void _httpFreeBuffers()
{
    if( pResponseBodyBuffer )
    {
        vPortFree( pResponseBodyBuffer );
        pResponseBodyBuffer = NULL;
    }

    if( pResponseUserBuffer )
    {
        vPortFree( pResponseUserBuffer );
        pResponseUserBuffer = NULL;
    }

    if( pRequestUserBuffer )
    {
        vPortFree( pRequestUserBuffer );
        pRequestUserBuffer = NULL;
    }

    if( pConnectionUserBuffer )
    {
        vPortFree( pConnectionUserBuffer );
        pConnectionUserBuffer = NULL;
    }
}

/* Process the HTTP response body, copy to another buffer and signal OTA agent the file block
 * download is complete. */
static void _httpProcessResponseBody( OTA_AgentContext_t * pAgentCtx,
                                      uint8_t * pHTTPResponseBody,
                                      uint32_t bufferSize )
{
    IotLogDebug( "Invoking _httpProcessResponseBody" );

    OTA_EventData_t * pMessage;
    OTA_EventMsg_t eventMsg = { 0 };

    pAgentCtx->xStatistics.ulOTA_PacketsReceived++;

    /* Try to get OTA data buffer. */
    pMessage = prvOTAEventBufferGet();

    if( pMessage == NULL )
    {
        pAgentCtx->xStatistics.ulOTA_PacketsDropped++;
        IotLogError( "Could not get a free buffer to copy callback data." );
    }
    else
    {
        pMessage->ulDataLength = bufferSize;

        memcpy( pMessage->ucData, pHTTPResponseBody, pMessage->ulDataLength );
        eventMsg.xEventId = eOTA_AgentEvent_ReceivedFileBlock;
        eventMsg.pxEventData = pMessage;
        /* Send job document received event. */
        OTA_SignalEvent( &eventMsg );
    }
}

/* Error handler for HTTP response code. */
static void _httpErrorHandler( uint16_t responseCode )
{
    const char * pResponseBody = ( const char * ) pResponseBodyBuffer;
    char * endPos = NULL;

    /* Force the response body to be NULL terminated. */
    pResponseBodyBuffer[ HTTPS_RESPONSE_BODY_BUFFER_SIZE - 1 ] = '\0';

    /* Search the </Error> tag, if found, set the NULL terminator at the end of this tag. */
    endPos = strstr( pResponseBody, "</Error>" );

    if( NULL != endPos )
    {
        endPos += sizeof( "</Error>" ) - 1;
        *endPos = '\0';
    }

    IotLogInfo( "HTTP message body:" );
    vLoggingPrintf( pResponseBody );
    vLoggingPrintf( "\n" );

    if( responseCode == IOT_HTTPS_STATUS_FORBIDDEN )
    {
        if( NULL != strstr( pResponseBody, "Request has expired" ) )
        {
            IotLogInfo( "Pre-signed URL have expired, requesting new job document." );
            _httpDownloader.err = OTA_HTTP_ERR_URL_EXPIRED;
        }
        else
        {
            _httpDownloader.err = OTA_HTTP_ERR_GENERIC;
        }
    }
    else
    {
        _httpDownloader.err = OTA_HTTP_ERR_GENERIC;
    }
}

/* Helper function to reconnect to the HTTP server. */
static IotHttpsReturnCode_t _httpReconnect()
{
    /* HTTP API return status. */
    IotHttpsReturnCode_t httpsStatus = IotHttpsClient_Connect(
        &_httpDownloader.httpConnection.connectionHandle,
        &_httpDownloader.httpConnection.connectionConfig );

    if( httpsStatus != IOT_HTTPS_OK )
    {
        IotLogError( "Failed to reconnect to the HTTP server. Error code: %d.", httpsStatus );
        _httpDownloader.err = OTA_HTTP_ERR_NEED_RECONNECT;
    }
    else
    {
        IotLogInfo( "Successfully reconnected to %.*s",
                    _httpDownloader.httpUrlInfo.addressLength,
                    _httpDownloader.httpUrlInfo.pAddress );
    }

    return httpsStatus;
}

/* HTTP async callback for adding header to HTTP request, called after IotHttpsClient_SendAsync. */
static void _httpAppendHeaderCallback( void * pPrivateData,
                                       IotHttpsRequestHandle_t requestHandle )
{
    IotLogDebug( "Invoking _httpAppendHeaderCallback." );

    /* Value of the "Range" field in HTTP GET request header, set when requesting the file block. */
    char * pRangeValueStr = ( ( _httpCallbackData_t * ) ( pPrivateData ) )->pRangeValueStr;

    /* Set the header for this range request. */
    IotHttpsReturnCode_t status = IotHttpsClient_AddHeader( requestHandle,
                                                            "Range",
                                                            sizeof( "Range" ) - 1,
                                                            pRangeValueStr,
                                                            strlen( pRangeValueStr ) );

    /* If case of error, the request will be canceled, then _httpErrorCallback will be invoked,
     * followed by _httpResponseCompleteCallback. */
    if( status != IOT_HTTPS_OK )
    {
        IotLogError( "Failed to add HTTP header. Error code: %d. Canceling current request.", status );
        IotHttpsClient_CancelRequestAsync( requestHandle );
        _httpDownloader.err = OTA_HTTP_ERR_CANCELED;
    }
    else
    {
        /* We've successfully sent the request, now waiting for a response, _httpReadReadyCallback
         * is expected to be invoked next upon receiving a response from the server. */
        _httpDownloader.state = OTA_HTTP_WAITING_RESPONSE;
    }
}

static void _httpReadReadyCallback( void * pPrivateData,
                                    IotHttpsResponseHandle_t responseHandle,
                                    IotHttpsReturnCode_t returnCode,
                                    uint16_t responseStatus )
{
    IotLogDebug( "Invoking _httpReadReadyCallback." );

    /* Unused parameters. */
    ( void ) pPrivateData;
    ( void ) returnCode;

    /* HTTP return status. */
    IotHttpsReturnCode_t httpsStatus = IOT_HTTPS_OK;

    /* The content length of this HTTP response. */
    uint32_t contentLength = 0;

    /* Size of the response body returned from HTTP API. */
    uint32_t responseBodyLength = 0;

    /* Buffer to read the "Connection" field in HTTP header. */
    char connectionValueStr[ HTTP_HEADER_CONNECTION_VALUE_MAX_LEN ] = { 0 };

    /* A response is received from the server, setting the state to processing response. */
    _httpDownloader.state = OTA_HTTP_PROCESSING_RESPONSE;

    /* Read the data from the network. */
    responseBodyLength = HTTPS_RESPONSE_BODY_BUFFER_SIZE;
    httpsStatus = IotHttpsClient_ReadResponseBody( responseHandle,
                                                   pResponseBodyBuffer,
                                                   &responseBodyLength );

    if( httpsStatus != IOT_HTTPS_OK )
    {
        IotLogError( "Failed to read the response body. Error code: %d.", httpsStatus );
        _httpDownloader.err = OTA_HTTP_ERR_GENERIC;
        OTA_GOTO_CLEANUP();
    }

    /* The HTTP response should be partial content with response code 206. */
    if( responseStatus != IOT_HTTPS_STATUS_PARTIAL_CONTENT )
    {
        IotLogError( "Expect a HTTP partial response, but received code %d", responseStatus );
        _httpErrorHandler( responseStatus );
        OTA_GOTO_CLEANUP();
    }

    /* Read the "Content-Length" field from HTTP header. */
    httpsStatus = IotHttpsClient_ReadContentLength( responseHandle, &contentLength );

    if( ( httpsStatus != IOT_HTTPS_OK ) || ( contentLength == 0 ) )
    {
        IotLogError( "Failed to retrieve the Content-Length from the response. " );
        _httpDownloader.err = OTA_HTTP_ERR_GENERIC;
        OTA_GOTO_CLEANUP();
    }

    /* Check if the value of "Content-Length" matches what we have requested. */
    if( contentLength != _httpDownloader.currBlockSize )
    {
        IotLogError( "Content-Length value in HTTP header does not match what we requested. " );
        _httpDownloader.err = OTA_HTTP_ERR_GENERIC;
        OTA_GOTO_CLEANUP();
    }

    OTA_FUNCTION_CLEANUP_BEGIN();

    /* The connection could be closed by S3 after 100 requests, so we need to check the value
     * of the "Connection" filed in HTTP header to see if we need to reconnect. */
    memset( connectionValueStr, 0, sizeof( connectionValueStr ) );
    httpsStatus = IotHttpsClient_ReadHeader( responseHandle,
                                             "Connection",
                                             sizeof( "Connection" ) - 1,
                                             connectionValueStr,
                                             sizeof( connectionValueStr ) );

    /* Check if there is any other error besides not found when parsing the http header. */
    if( ( httpsStatus != IOT_HTTPS_OK ) && ( httpsStatus != IOT_HTTPS_NOT_FOUND ) )
    {
        IotLogError( "Failed to read header Connection. Error code: %d.", httpsStatus );
        _httpDownloader.err = OTA_HTTP_ERR_GENERIC;
    }
    else
    {
        /* Check if the server returns a response with connection field set to "close". */
        if( strncmp( "close", connectionValueStr, sizeof( "close" ) ) == 0 )
        {
            IotLogInfo( "Connection has been closed by the HTTP server, reconnecting to the server..." );
            _httpReconnect();
        }
    }

    /* Cancel receiving the response in case of error, _httpErrorCallback will be invoked next.
     * If the HTTP error is IOT_HTTPS_NETWORK_ERROR, the connection will then be closed by the HTTP
     * client, followed by invoking _httpConnectionClosedCallback and _httpResponseCompleteCallback.
     * In other cases, only _httpResponseCompleteCallback will be invoked. */
    if( _httpDownloader.err != OTA_HTTP_ERR_NONE )
    {
        IotHttpsClient_CancelResponseAsync( responseHandle );
    }

    OTA_FUNCTION_CLEANUP_END();
}

static void _httpResponseCompleteCallback( void * pPrivateData,
                                           IotHttpsResponseHandle_t responseHandle,
                                           IotHttpsReturnCode_t returnCode,
                                           uint16_t responseStatus )
{
    IotLogDebug( "Invoking _httpResponseCompleteCallback." );

    /* Unused parameters. */
    ( void ) pPrivateData;
    ( void ) responseHandle;
    ( void ) returnCode;
    ( void ) responseStatus;

    /* OTA Event. */
    OTA_EventMsg_t eventMsg = { 0 };

    /* Bail out if this callback is invoked after the OTA agent is stopped. */
    if( _httpDownloader.pAgentCtx->eState == eOTA_AgentState_Stopped )
    {
        return;
    }

    if( _httpDownloader.err == OTA_HTTP_ERR_NONE )
    {
        _httpProcessResponseBody( _httpDownloader.pAgentCtx, pResponseBodyBuffer, _httpDownloader.currBlockSize );
    }
    else
    {
        /* Reset the state to idle when current download fails. */
        _httpDownloader.state = OTA_HTTP_IDLE;

        switch( _httpDownloader.err )
        {
            case OTA_HTTP_ERR_NEED_RECONNECT:
                IotLogInfo( "HTTP connection is closed, will reconnection in next request." );
                break;

            case OTA_HTTP_ERR_URL_EXPIRED:
                eventMsg.xEventId = eOTA_AgentEvent_RequestJobDocument;
                IotLogInfo( "URL has expired, requesting a new job document." );
                OTA_SignalEvent( &eventMsg );
                break;

            case OTA_HTTP_ERR_CANCELED:
                IotLogError( "Request to download block %d has been canceled.", _httpDownloader.currBlock );
                break;

            case OTA_HTTP_ERR_GENERIC:
                IotLogError( "Fail to download block %d.", _httpDownloader.currBlock );
                break;

            default:
                IotLogError( "Unhandled OTA HTTP state %d, aborting OTA.", _httpDownloader.state );
                eventMsg.xEventId = eOTA_AgentEvent_UserAbort;
                OTA_SignalEvent( &eventMsg );
                break;
        }
    }
}

static void _httpErrorCallback( void * pPrivateData,
                                IotHttpsRequestHandle_t requestHandle,
                                IotHttpsResponseHandle_t responseHandle,
                                IotHttpsReturnCode_t returnCode )
{
    IotLogDebug( "Invoking _httpErrorCallback." );

    /* Unused parameters. */
    ( void ) pPrivateData;
    ( void ) requestHandle;
    ( void ) responseHandle;
    ( void ) returnCode;

    if( _httpDownloader.err == OTA_HTTP_ERR_NONE )
    {
        _httpDownloader.err = OTA_HTTP_ERR_GENERIC;
    }

    IotLogError( "An error occurred for HTTP async request: %d", returnCode );
}

static void _httpConnectionClosedCallback( void * pPrivateData,
                                           IotHttpsConnectionHandle_t connectionHandle,
                                           IotHttpsReturnCode_t returnCode )
{
    IotLogDebug( "Invoking _httpConnectionClosedCallback." );

    /* Unused parameters. */
    ( void ) pPrivateData;
    ( void ) connectionHandle;
    ( void ) returnCode;

    IotLogInfo( "Connection has been closed by the HTTP client due to an error, reconnecting to the server..." );
    _httpReconnect();
}

static IotHttpsReturnCode_t _httpInitUrl( const char * pURL )
{
    /* HTTP API return status. */
    IotHttpsReturnCode_t httpsStatus = IOT_HTTPS_OK;

    /* HTTP URL information. */
    _httpUrlInfo_t * pUrlInfo = &_httpDownloader.httpUrlInfo;

    /* Retrieve the resource path from the HTTP URL. pPath will point to the start of this part. */
    httpsStatus = IotHttpsClient_GetUrlPath( pURL,
                                             strlen( pURL ),
                                             &pUrlInfo->pPath,
                                             &pUrlInfo->pathLength );

    if( httpsStatus == IOT_HTTPS_OK )
    {
        /* pathLength is set to the length of path component, but we also need the query part that
         * comes after that. */
        pUrlInfo->pathLength = strlen( pUrlInfo->pPath );

        /* Retrieve the authority part and length from the HTTP URL. */
        httpsStatus = IotHttpsClient_GetUrlAddress( pURL,
                                                    strlen( pURL ),
                                                    &pUrlInfo->pAddress,
                                                    &pUrlInfo->addressLength );

        if( httpsStatus != IOT_HTTPS_OK )
        {
            IotLogError( "Fail to parse the server address from given HTTP URL. Error code: %d.", httpsStatus );
        }
    }
    else
    {
        IotLogError( "Fail to parse the resource path from given HTTP URL. Error code: %d.", httpsStatus );
    }

    return httpsStatus;
}

static IotHttpsReturnCode_t _httpConnect( const IotNetworkInterface_t * pNetworkInterface,
                                          struct IotNetworkCredentials * pNetworkCredentials )
{
    /* HTTP API return status. */
    IotHttpsReturnCode_t httpsStatus = IOT_HTTPS_OK;

    /* HTTP connection data. */
    _httpConnection_t * pConnection = &_httpDownloader.httpConnection;

    /* HTTP connection configuration. */
    IotHttpsConnectionInfo_t * pConnectionConfig = &pConnection->connectionConfig;

    /* HTTP request data. */
    _httpRequest_t * pRequest = &_httpDownloader.httpRequest;

    /* HTTP response data. */
    _httpResponse_t * pResponse = &_httpDownloader.httpResponse;

    /* HTTP URL information. */
    _httpUrlInfo_t * pUrlInfo = &_httpDownloader.httpUrlInfo;

    /* Set the connection configurations. */
    pConnectionConfig->pAddress = pUrlInfo->pAddress;
    pConnectionConfig->addressLen = pUrlInfo->addressLength;
    pConnectionConfig->port = HTTPS_PORT;
    pConnectionConfig->pCaCert = HTTPS_TRUSTED_ROOT_CA;
    pConnectionConfig->caCertLen = sizeof( HTTPS_TRUSTED_ROOT_CA );
    pConnectionConfig->userBuffer.pBuffer = pConnectionUserBuffer;
    pConnectionConfig->userBuffer.bufferLen = HTTPS_CONNECTION_USER_BUFFER_SIZE;
    pConnectionConfig->pClientCert = pNetworkCredentials->pClientCert;
    pConnectionConfig->clientCertLen = pNetworkCredentials->clientCertSize;
    pConnectionConfig->pPrivateKey = pNetworkCredentials->pPrivateKey;
    pConnectionConfig->privateKeyLen = pNetworkCredentials->privateKeySize;
    pConnectionConfig->pNetworkInterface = pNetworkInterface;

    /* Initialize HTTP request configuration. */
    pRequest->requestConfig.pPath = pUrlInfo->pPath;
    pRequest->requestConfig.pathLen = pUrlInfo->pathLength;
    pRequest->requestConfig.pHost = pUrlInfo->pAddress;
    pRequest->requestConfig.hostLen = pUrlInfo->addressLength;
    pRequest->requestConfig.method = IOT_HTTPS_METHOD_GET;
    pRequest->requestConfig.userBuffer.pBuffer = pRequestUserBuffer;
    pRequest->requestConfig.userBuffer.bufferLen = HTTPS_REQUEST_USER_BUFFER_SIZE;
    pRequest->requestConfig.isAsync = true;
    pRequest->requestConfig.u.pAsyncInfo = &pRequest->asyncInfo;

    /* Initialize HTTP response configuration. */
    pResponse->responseConfig.userBuffer.pBuffer = pResponseUserBuffer;
    pResponse->responseConfig.userBuffer.bufferLen = HTTPS_RESPONSE_USER_BUFFER_SIZE;
    pResponse->responseConfig.pSyncInfo = NULL;

    /* Initialize HTTP asynchronous configuration. */
    pRequest->asyncInfo.callbacks.appendHeaderCallback = _httpAppendHeaderCallback;
    pRequest->asyncInfo.callbacks.readReadyCallback = _httpReadReadyCallback;
    pRequest->asyncInfo.callbacks.responseCompleteCallback = _httpResponseCompleteCallback;
    pRequest->asyncInfo.callbacks.errorCallback = _httpErrorCallback;
    pRequest->asyncInfo.callbacks.connectionClosedCallback = _httpConnectionClosedCallback;
    pRequest->asyncInfo.pPrivData = ( void * ) ( &_httpDownloader.httpCallbackData );

    httpsStatus = IotHttpsClient_Connect( &pConnection->connectionHandle, pConnectionConfig );

    return httpsStatus;
}

/* Ideally we could use a HEAD request to get the file size. However, performing a HEAD request
 * with S3 requires generating a Sigv4 signature in an authorization header field. So here we use
 * a GET request with range set to 0, then extract the file size from the "Content-Range" field in
 * the HTTP response. */
static _httpErr _httpGetFileSize( uint32_t * pFileSize )
{
    /* Return status. */
    _httpErr status = OTA_HTTP_ERR_NONE;
    IotHttpsReturnCode_t httpsStatus = IOT_HTTPS_OK;

    /* HTTP response code. */
    uint16_t responseStatus = IOT_HTTPS_STATUS_OK;

    /* HTTP request and response configurations. We're creating local variables here because this is
     * a temporary synchronous request. */
    IotHttpsRequestInfo_t requestConfig = { 0 };
    IotHttpsResponseInfo_t responseConfig = { 0 };

    /* Synchronous request and response configurations. */
    IotHttpsSyncInfo_t requestSyncInfo = { 0 };
    IotHttpsSyncInfo_t responseSyncInfo = { 0 };

    /* Handle for HTTP request and response. */
    IotHttpsRequestHandle_t requestHandle = NULL;
    IotHttpsResponseHandle_t responseHandle = NULL;

    /* HTTP URL information. */
    _httpUrlInfo_t * pUrlInfo = &_httpDownloader.httpUrlInfo;

    /* Value of the "Content-Range" field in HTTP response header. The format is "bytes 0-0/FILESIZE". */
    char pContentRange[ sizeof( "bytes 0-0/" ) + OTA_MAX_FILE_SIZE_STR_LEN ] = { 0 };

    /* Pointer to the location of the file size in pContentRange. */
    char * pFileSizeStr = NULL;

    /* There's no message body in this GET request. */
    requestSyncInfo.pBody = NULL;
    requestSyncInfo.bodyLen = 0;

    /* Store the response body in case there's any failure. */
    responseSyncInfo.pBody = pResponseBodyBuffer;
    responseSyncInfo.bodyLen = HTTPS_RESPONSE_BODY_BUFFER_SIZE;

    /* Set the request configurations. */
    requestConfig.pPath = pUrlInfo->pPath;
    requestConfig.pathLen = pUrlInfo->pathLength;
    requestConfig.pHost = pUrlInfo->pAddress;
    requestConfig.hostLen = pUrlInfo->addressLength;
    requestConfig.method = IOT_HTTPS_METHOD_GET;
    requestConfig.userBuffer.pBuffer = pRequestUserBuffer;
    requestConfig.userBuffer.bufferLen = HTTPS_REQUEST_USER_BUFFER_SIZE;
    requestConfig.isAsync = false;
    requestConfig.u.pSyncInfo = &requestSyncInfo;

    /* Set the response configurations. */
    responseConfig.userBuffer.pBuffer = pResponseUserBuffer;
    responseConfig.userBuffer.bufferLen = HTTPS_RESPONSE_USER_BUFFER_SIZE;
    responseConfig.pSyncInfo = &responseSyncInfo;

    /* Initialize the request to retrieve a request handle. */
    httpsStatus = IotHttpsClient_InitializeRequest( &requestHandle, &requestConfig );

    if( httpsStatus != IOT_HTTPS_OK )
    {
        IotLogError( "Fail to initialize the HTTP request context. Error code: %d.", httpsStatus );
        status = OTA_HTTP_ERR_GENERIC;
        OTA_GOTO_CLEANUP();
    }

    /* Set the "Range" field in HTTP header to "bytes=0-0" since we just want the file size. */
    httpsStatus = IotHttpsClient_AddHeader( requestHandle,
                                            "Range",
                                            sizeof( "Range" ) - 1,
                                            "bytes=0-0",
                                            sizeof( "bytes=0-0" ) - 1 );

    if( httpsStatus != IOT_HTTPS_OK )
    {
        IotLogError( "Fail to populate the HTTP header for request. Error code: %d", httpsStatus );
        status = OTA_HTTP_ERR_GENERIC;
        OTA_GOTO_CLEANUP();
    }

    /* Send the request synchronously. */
    httpsStatus = IotHttpsClient_SendSync( _httpDownloader.httpConnection.connectionHandle,
                                           requestHandle,
                                           &responseHandle,
                                           &responseConfig,
                                           HTTP_SYNC_TIMEOUT );

    if( httpsStatus != IOT_HTTPS_OK )
    {
        IotLogError( "Fail to send the HTTP request synchronously. Error code: %d", httpsStatus );
        status = OTA_HTTP_ERR_GENERIC;
        OTA_GOTO_CLEANUP();
    }

    httpsStatus = IotHttpsClient_ReadResponseStatus( responseHandle, &responseStatus );

    if( httpsStatus != IOT_HTTPS_OK )
    {
        IotLogError( "Fail to read the HTTP response status. Error code: %d", httpsStatus );
        status = OTA_HTTP_ERR_GENERIC;
        OTA_GOTO_CLEANUP();
    }

    if( responseStatus != IOT_HTTPS_STATUS_PARTIAL_CONTENT )
    {
        IotLogError( "Fail to get the object size from HTTP server, HTTP response code from server: %d", responseStatus );
        status = OTA_HTTP_ERR_GENERIC;
        _httpErrorHandler( responseStatus );
        OTA_GOTO_CLEANUP();
    }

    /* Parse the HTTP header and retrieve the file size. */
    httpsStatus = IotHttpsClient_ReadHeader( responseHandle,
                                             "Content-Range",
                                             sizeof( "Content-Range" ) - 1,
                                             pContentRange,
                                             sizeof( pContentRange ) );

    if( httpsStatus != IOT_HTTPS_OK )
    {
        IotLogError( "Fail to read the \"Content-Range\" field from HTTP header. Error code: %d", httpsStatus );
        status = OTA_HTTP_ERR_GENERIC;
        OTA_GOTO_CLEANUP();
    }

    pFileSizeStr = strstr( pContentRange, "/" );

    if( pFileSizeStr == NULL )
    {
        IotLogError( "Could not find '/' from \"Content-Range\" field: %s", pContentRange );
        status = OTA_HTTP_ERR_GENERIC;
        OTA_GOTO_CLEANUP();
    }
    else
    {
        pFileSizeStr += sizeof( char );
    }

    *pFileSize = ( uint32_t ) strtoul( pFileSizeStr, NULL, 10 );

    if( ( *pFileSize == 0 ) || ( *pFileSize == UINT32_MAX ) )
    {
        IotLogError( "Failed to convert \"Content-Range\" value %s to integer. strtoul returned %d", pFileSizeStr, *pFileSize );
        status = OTA_HTTP_ERR_GENERIC;
        OTA_GOTO_CLEANUP();
    }

    OTA_FUNCTION_NO_CLEANUP();

    return status;
}

/* Performs some pre-checks before requesting a new block. */
static _httpErr _requestDataBlockPreCheck()
{
    _httpErr status = OTA_HTTP_ERR_NONE;

    /* Reconnect to the HTTP server if we detect an error when processing the response and a reconnect
     * is needed or we did not receive any response within OTA agent request data timeout. */
    if( _httpDownloader.err == OTA_HTTP_ERR_NEED_RECONNECT )
    {
        IotLogInfo( "Error happened during last request requires reconnecting." );

        if( _httpReconnect() != IOT_HTTPS_OK )
        {
            status = OTA_HTTP_ERR_NEED_RECONNECT;
        }
    }
    else if( _httpDownloader.state == OTA_HTTP_WAITING_RESPONSE )
    {
        IotLogInfo( "Still waiting for a response from the server after request timeout. Assuming "
                    "the connection is closed by the server, reconnecting..." );

        if( _httpReconnect() != IOT_HTTPS_OK )
        {
            status = OTA_HTTP_ERR_NEED_RECONNECT;
        }
    }

    /* Otherwise exit if not in idle state, this means we're still sending the request or processing
     * a response. */
    else if( _httpDownloader.state != OTA_HTTP_IDLE )
    {
        IotLogInfo( "Current download is not finished, skipping the request." );
        status = OTA_HTTP_ERR_GENERIC;
    }
    else
    {
        status = OTA_HTTP_ERR_NONE;
    }

    return status;
}

OTA_Err_t _AwsIotOTA_InitFileTransfer_HTTP( OTA_AgentContext_t * pAgentCtx )
{
    IotLogDebug( "Invoking _AwsIotOTA_InitFileTransfer_HTTP" );

    /* Return status. */
    OTA_Err_t status = kOTA_Err_None;
    IotHttpsReturnCode_t httpsStatus = IOT_HTTPS_OK;

    /* Cleanup status. */
    bool cleanupRequired = false;

    /* Network interface and credentials from OTA agent. */
    OTA_ConnectionContext_t * connContext = pAgentCtx->pvConnectionContext;
    const IotNetworkInterface_t * pNetworkInterface = connContext->pxNetworkInterface;
    struct IotNetworkCredentials * pNetworkCredentials = connContext->pvNetworkCredentials;

    /* Pre-signed URL. */
    const char * pURL = NULL;

    /* File context from OTA agent. */
    OTA_FileContext_t * fileContext = &( pAgentCtx->pxOTA_Files[ pAgentCtx->ulFileIndex ] );

    /* OTA download file size from OTA agent (parsed from job document). */
    uint32_t otaFileSize = 0;

    /* OTA download file size from the HTTP server, this should match otaFileSize. */
    uint32_t httpFileSize = 0;

    /* Store the OTA agent for later access. */
    _httpDownloader.pAgentCtx = pAgentCtx;

    if( fileContext == NULL )
    {
        IotLogError( "File context from OTA agent is NULL." );
        status = kOTA_Err_Panic;
        OTA_GOTO_CLEANUP();
    }

    /* Get the file size from OTA agent (parsed from job document). */
    otaFileSize = fileContext->ulFileSize;

    /* Get pre-signed URL from pAgentCtx. */
    pURL = ( const char * ) ( fileContext->pucUpdateUrlPath );
    IotLogInfo( "Pre-signed URL size: %d.", strlen( pURL ) );

    /* Initialize the HTTPS library. */
    httpsStatus = IotHttpsClient_Init();

    if( httpsStatus != IOT_HTTPS_OK )
    {
        IotLogError( "Fail to initialize HTTP library. Error code: %d", httpsStatus );
        status = kOTA_Err_HTTPInitFailed;
        OTA_GOTO_CLEANUP();
    }

    /* Allocate buffers for HTTP library. */
    if( _httpAllocateBuffers() == false )
    {
        cleanupRequired = true;
        OTA_GOTO_CLEANUP();
    }

    /* Connect to the HTTP server and initialize download information. */
    httpsStatus = _httpInitUrl( pURL );

    if( httpsStatus != IOT_HTTPS_OK )
    {
        IotLogError( "Failed to parse the HTTP Url. Error code: %d", httpsStatus );
        status = kOTA_Err_HTTPInitFailed;
        cleanupRequired = true;
        OTA_GOTO_CLEANUP();
    }

    httpsStatus = _httpConnect( pNetworkInterface, pNetworkCredentials );

    if( httpsStatus != IOT_HTTPS_OK )
    {
        IotLogError( "Failed to connect to %.*s. Error code: %d", _httpDownloader.httpUrlInfo.addressLength,
                     _httpDownloader.httpUrlInfo.pAddress, httpsStatus );
        status = kOTA_Err_HTTPInitFailed;
        cleanupRequired = true;
        OTA_GOTO_CLEANUP();
    }

    IotLogInfo( "Successfully connected to %.*s", _httpDownloader.httpUrlInfo.addressLength, _httpDownloader.httpUrlInfo.pAddress );

    /* Check if the file size from HTTP server matches the file size from OTA job document. */
    if( _httpGetFileSize( &httpFileSize ) != OTA_HTTP_ERR_NONE )
    {
        IotLogError( "Cannot retrieve the file size from HTTP server." );
        status = kOTA_Err_HTTPInitFailed;
        cleanupRequired = true;
        OTA_GOTO_CLEANUP();
    }

    if( httpFileSize != otaFileSize )
    {
        IotLogError( "File size from the HTTP server (%u bytes) does not match the size from OTA "
                     "job document (%u bytes).",
                     ( unsigned int ) httpFileSize,
                     ( unsigned int ) otaFileSize );
        status = kOTA_Err_HTTPInitFailed;
        cleanupRequired = true;
        OTA_GOTO_CLEANUP();
    }

    /* Exit directly if everything succeed. */
    IotLogInfo( "Start requesting %u bytes from HTTP server.", ( unsigned int ) httpFileSize );

    OTA_FUNCTION_CLEANUP_BEGIN();

    if( cleanupRequired )
    {
        _httpFreeBuffers();
    }

    OTA_FUNCTION_CLEANUP_END();

    return status;
}

OTA_Err_t _AwsIotOTA_RequestDataBlock_HTTP( OTA_AgentContext_t * pAgentCtx )
{
    IotLogDebug( "Invoking _AwsIotOTA_RequestDataBlock_HTTP" );

    /* Return status. */
    OTA_Err_t status = kOTA_Err_None;
    IotHttpsReturnCode_t httpsStatus = IOT_HTTPS_OK;

    /* HTTP connection data. */
    _httpConnection_t * pConnection = &_httpDownloader.httpConnection;

    /* HTTP request data. */
    _httpRequest_t * pRequest = &_httpDownloader.httpRequest;

    /* HTTP response data. */
    _httpResponse_t * pResponse = &_httpDownloader.httpResponse;

    /* Values for the "Range" field in HTTP header. */
    uint32_t rangeStart = 0;
    uint32_t rangeEnd = 0;
    int numWritten = 0;

    /* File context from OTA agent. */
    OTA_FileContext_t * fileContext = &( pAgentCtx->pxOTA_Files[ pAgentCtx->ulFileIndex ] );

    /* Exit if we're still busy downloading or reconnect is required but failed. */
    if( _requestDataBlockPreCheck() != OTA_HTTP_ERR_NONE )
    {
        status = kOTA_Err_HTTPRequestFailed;
        OTA_GOTO_CLEANUP();
    }

    _httpDownloader.state = OTA_HTTP_SENDING_REQUEST;
    _httpDownloader.err = OTA_HTTP_ERR_NONE;

    if( fileContext == NULL )
    {
        IotLogError( "File context from OTA agent is NULL." );
        status = kOTA_Err_Panic;
        OTA_GOTO_CLEANUP();
    }

    /* Set number of blocks to request to 1. */
    pAgentCtx->ulNumOfBlocksToReceive = 1;

    /* Calculate ranges. */
    rangeStart = _httpDownloader.currBlock * OTA_FILE_BLOCK_SIZE;

    if( fileContext->ulBlocksRemaining == 1 )
    {
        rangeEnd = fileContext->ulFileSize - 1;
    }
    else
    {
        rangeEnd = rangeStart + OTA_FILE_BLOCK_SIZE - 1;
    }

    _httpDownloader.currBlockSize = rangeEnd - rangeStart + 1;

    /* Creating the "range" field in HTTP header. */
    numWritten = snprintf( _httpDownloader.httpCallbackData.pRangeValueStr,
                           HTTP_HEADER_RANGE_VALUE_MAX_LEN,
                           "bytes=%u-%u",
                           ( unsigned int ) rangeStart,
                           ( unsigned int ) rangeEnd );

    if( ( numWritten < 0 ) || ( numWritten >= HTTP_HEADER_RANGE_VALUE_MAX_LEN ) )
    {
        IotLogError( "Fail to write the \"Range\" value for HTTP header." );
        status = kOTA_Err_HTTPRequestFailed;
        OTA_GOTO_CLEANUP();
    }

    /* Re-initialize the request handle as it could be changed when handling last response. */
    httpsStatus = IotHttpsClient_InitializeRequest( &pRequest->requestHandle, &pRequest->requestConfig );

    if( httpsStatus != IOT_HTTPS_OK )
    {
        IotLogError( "Fail to initialize the HTTP request. Error code: %d.", httpsStatus );
        status = kOTA_Err_HTTPRequestFailed;
        OTA_GOTO_CLEANUP();
    }

    /* Send the request asynchronously. Receiving is handled in a callback. */
    IotLogInfo( "Sending HTTP request to download block %d.", _httpDownloader.currBlock );
    httpsStatus = IotHttpsClient_SendAsync( pConnection->connectionHandle,
                                            pRequest->requestHandle,
                                            &pResponse->responseHandle,
                                            &pResponse->responseConfig );

    if( httpsStatus != IOT_HTTPS_OK )
    {
        IotLogError( "Fail to send the HTTP request asynchronously. Error code: %d.", httpsStatus );
        status = kOTA_Err_HTTPRequestFailed;
        OTA_GOTO_CLEANUP();
    }

    OTA_FUNCTION_CLEANUP_BEGIN();

    /* Reset the state to idle if there's any error occurred, i.e. the request is not sent. */
    if( status != kOTA_Err_None )
    {
        _httpDownloader.state = OTA_HTTP_IDLE;
    }

    OTA_FUNCTION_CLEANUP_END();

    return status;
}

OTA_Err_t _AwsIotOTA_DecodeFileBlock_HTTP( uint8_t * pMessageBuffer,
                                           size_t messageSize,
                                           int32_t * pFileId,
                                           int32_t * pBlockId,
                                           int32_t * pBlockSize,
                                           uint8_t ** pPayload,
                                           size_t * pPayloadSize )
{
    IotLogDebug( "Invoking _AwsIotOTA_DecodeFileBlock_HTTP" );

    /* Unused parameters. */
    ( void ) messageSize;

    *pPayload = pMessageBuffer;
    *pFileId = 0;
    *pBlockId = _httpDownloader.currBlock;
    *pBlockSize = _httpDownloader.currBlockSize;
    *pPayloadSize = _httpDownloader.currBlockSize;

    /* Current block is processed, set the file block to next one and the state to idle. */
    _httpDownloader.state = OTA_HTTP_IDLE;
    _httpDownloader.currBlock += 1;

    return kOTA_Err_None;
}


OTA_Err_t _AwsIotOTA_CleanupData_HTTP( OTA_AgentContext_t * pAgentCtx )
{
    IotLogDebug( "Invoking _AwsIotOTA_CleanupData_HTTP" );

    /* Unused parameters. */
    ( void ) pAgentCtx;

    memset( &_httpDownloader, 0, sizeof( _httpDownloader_t ) );

    _httpFreeBuffers();

    return kOTA_Err_None;
}
