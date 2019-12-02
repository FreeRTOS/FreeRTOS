/*
 * Amazon FreeRTOS HTTPS Client V1.1.0
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

#ifndef IOT_HTTPS_INTERNAL_H_
#define IOT_HTTPS_INTERNAL_H_

/* The config header is always included first. */
#include "iot_config.h"

/* Standard Includes. */
#include <string.h>
#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>

/* Third party http-parser include. */
#include "http_parser.h"

/* HTTPS Client library includes. */
#include "iot_https_client.h"

/* Task pool include. */
#include "iot_taskpool_freertos.h"

/* Linear containers (lists and queues) include. */
#include "iot_linear_containers.h"

/* Types include. */
#include "types/iot_taskpool_types_freertos.h"

/* Platform layer includes. */
#include "platform/iot_threads.h"
#include "platform/iot_network.h"

/* Error handling include. */
#include "iot_error.h"

/*-----------------------------------------------------------*/

/* Convenience macros for handling errors in a standard way. */

/**
 * @brief Every public API return an enumeration value with an underlying value of 0 in case of success.
 */
#define HTTPS_SUCCEEDED( x )                         ( ( x ) == IOT_HTTPS_OK )

/**
 * @brief Every public API returns an enumeration value with an underlying value different than 0 in case of success.
 */
#define HTTPS_FAILED( x )                            ( ( x ) != IOT_HTTPS_OK )

/**
 * @brief Declare the storage for the error status variable.
 */
#define HTTPS_FUNCTION_ENTRY( result )               IOT_FUNCTION_ENTRY( IotHttpsReturnCode_t, result )

/**
 * @brief Jump to the cleanup area.
 */
#define HTTPS_GOTO_CLEANUP()                         IOT_GOTO_CLEANUP()

/**
 * @brief Set error and leave.
 */
#define HTTPS_SET_AND_GOTO_CLEANUP( statusValue )    IOT_SET_AND_GOTO_CLEANUP( statusValue )

/**
 * @brief Initialize error and declare start of cleanup area.
 */
#define HTTPS_FUNCTION_CLEANUP_BEGIN()               IOT_FUNCTION_CLEANUP_BEGIN()

/**
 * @brief Initialize error and declare end of cleanup area.
 */
#define HTTPS_FUNCTION_CLEANUP_END()                 IOT_FUNCTION_CLEANUP_END()

/**
 * @brief Create an empty cleanup area.
 */
#define HTTPS_FUNCTION_EXIT_NO_CLEANUP()             IOT_FUNCTION_EXIT_NO_CLEANUP()

/**
 * @brief Exit if an argument is NULL.
 */
#define HTTPS_ON_NULL_ARG_GOTO_CLEANUP( ptr )                    \
    if( ( ptr == NULL ) )                                        \
    {                                                            \
        IotLogError( # ptr " was NULL." );                       \
        IOT_SET_AND_GOTO_CLEANUP( IOT_HTTPS_INVALID_PARAMETER ); \
    }

/**
 * @brief Exit if an condition is false.
 */
#define HTTPS_ON_ARG_ERROR_GOTO_CLEANUP( expr )                  \
    if( ( expr ) == false )                                      \
    {                                                            \
        IotLogError( # expr " must be true." );                  \
        IOT_SET_AND_GOTO_CLEANUP( IOT_HTTPS_INVALID_PARAMETER ); \
    }

/**
 * @brief Exit if an argument is false with a message.
 */
#define HTTPS_ON_ARG_ERROR_MSG_GOTO_CLEANUP( expr, statusValue, ... ) \
    if( ( expr ) == false )                                           \
    {                                                                 \
        IotLogError( __VA_ARGS__ );                                   \
        IOT_SET_AND_GOTO_CLEANUP( statusValue );                      \
    }

/* Configure logs for HTTPS Client functions. */
#ifdef IOT_LOG_LEVEL_HTTPS
    #define LIBRARY_LOG_LEVEL        IOT_LOG_LEVEL_HTTPS
#else
    #ifdef IOT_LOG_LEVEL_GLOBAL
        #define LIBRARY_LOG_LEVEL    IOT_LOG_LEVEL_GLOBAL
    #else
        #define LIBRARY_LOG_LEVEL    IOT_LOG_NONE
    #endif
#endif

#define LIBRARY_LOG_NAME    ( "HTTPS Client" )
#include "iot_logging_setup.h"

/*
 * Provide default values for undefined memory allocation functions based on
 * the usage of dynamic memory allocation.
 */
#if IOT_STATIC_MEMORY_ONLY == 1
    #include "iot_static_memory.h"
#endif

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this section.
 *
 * Provide default values for undefined configuration constants.
 */
#ifndef AWS_IOT_HTTPS_ENABLE_METRICS
    #define AWS_IOT_HTTPS_ENABLE_METRICS           ( 1 )
#endif
#ifndef IOT_HTTPS_USER_AGENT
    #define IOT_HTTPS_USER_AGENT                   "FreeRTOS"
#endif
#ifndef IOT_HTTPS_MAX_FLUSH_BUFFER_SIZE
    #define IOT_HTTPS_MAX_FLUSH_BUFFER_SIZE        ( 1024 )
#endif
#ifndef IOT_HTTPS_RESPONSE_WAIT_MS
    #define IOT_HTTPS_RESPONSE_WAIT_MS             ( 1000 )
#endif
#ifndef IOT_HTTPS_MAX_HOST_NAME_LENGTH
    #define IOT_HTTPS_MAX_HOST_NAME_LENGTH         ( 255 ) /* Per FQDN, the maximum host name length is 255 bytes. */
#endif
#ifndef IOT_HTTPS_MAX_ALPN_PROTOCOLS_LENGTH
    #define IOT_HTTPS_MAX_ALPN_PROTOCOLS_LENGTH    ( 255 ) /* The maximum alpn protocols length is chosen arbitrarily. */
#endif

/** @endcond */

/**
 * @brief The HTTP protocol version of this library is HTTP/1.1.
 */
#define HTTPS_PROTOCOL_VERSION                        "HTTP/1.1"

/**
 * @brief An empty path for a NULL specified path in the request initialization configuration.
 */
#define HTTPS_EMPTY_PATH                              "/"

/**
 * @brief HTTPS "CONNECT" method, defined as the longest string length method.
 */
#define HTTPS_CONNECT_METHOD                          "CONNECT"

/*
 * Constants for the values of the HTTP "Connection" header field.
 *
 * This is used for writing headers automatically during the sending of the HTTP request.
 * "Connection: keep-alive\r\n" is written automatically for a persistent connection.
 * "Connection: close\r\n" is written automatically for a non-persistent connection.
 */
#define HTTPS_CONNECTION_KEEP_ALIVE_HEADER_VALUE      "keep-alive"
#define HTTPS_CONNECTION_CLOSE_HEADER_VALUE           "close"

/**
 * Constants for HTTP header formatting.
 *
 * ": " separates and header field from the header value.
 */
#define HTTPS_HEADER_FIELD_SEPARATOR                  ": "
#define HTTPS_HEADER_FIELD_SEPARATOR_LENGTH           ( 2 )
#define COLON_CHARACTER                               ':'
#define SPACE_CHARACTER                               ' '

/**
 * Constants for HTTP header formatting.
 *
 * "\r\n" Ends the header line.
 */
#define HTTPS_END_OF_HEADER_LINES_INDICATOR           "\r\n"
#define HTTPS_END_OF_HEADER_LINES_INDICATOR_LENGTH    ( 2 )
#define CARRIAGE_RETURN_CHARACTER                     '\r'
#define NEWLINE_CHARACTER                             '\n'

/*
 * Constants for header fields added automatically during the request initialization.
 */
#define HTTPS_USER_AGENT_HEADER                       "User-Agent"
#define HTTPS_HOST_HEADER                             "Host"

/*
 * Constants for the header fields added automatically during the sending of the HTTP request.
 */
#define HTTPS_CONTENT_LENGTH_HEADER                   "Content-Length"
#define HTTPS_CONNECTION_HEADER                       "Connection"

/**
 * @brief The maximum Content-Length header line size.
 *
 * This is the length of header line string: "Content-Length: 4294967296\r\n". 4294967296 is 2^32. This number is chosen
 * because it is the maximum file size that can be represented in a 32 bit system.
 *
 * This is used to initialize a local array for the final headers to send.
 */
#define HTTPS_MAX_CONTENT_LENGTH_LINE_LENGTH          ( 26 )

/**
 * @brief Macro for fast string length calculation of string macros.
 *
 * We subtract 1 to subtract the NULL terminating character.
 * We do not assume that the size of a character is a single byte or 8 bits with this calculation.
 */
#define FAST_MACRO_STRLEN( x )    ( ( sizeof( x ) / sizeof( char ) ) - 1 )

/*-----------------------------------------------------------*/

/**
 * @brief The state of the HTTP response parsing.
 *
 * This state notes what has been parsed in the HTTP response. As soon as any part of the HTTP response is received from
 * the network, it is sent to be parsed.
 *
 * The states move as follows:
 * PARSER_STATE_NONE --> PARSER_STATE_IN_HEADERS --> PARSER_STATE_HEADERS_COMPLETE --> PARSER_STATE_BODY_COMPLETE
 *
 * The parser callbacks are called in the following order:
 * 1. _httpParserOnMessageBeginCallback()
 * 2. _httpParserOnStatusCallback()
 * 3. _httpParserOnHeaderFieldCallback()
 * 4. _httpParserOnHeaderValueCallback()
 * 5. _httpParserOnHeadersCompleteCallback()
 * 6. _httpParserOnChunkHeaderCallback() (optional only if the response is chunked)
 * 7. _httpParserOnBodyCallback()
 * 8. _httpParserOnChunkCompleteCallback() (optional only if the response is chunked)
 * 9. _httpParserOnMessageCompleteCallback()
 *
 * Theses states are set in the parser callbacks and used outside the callbacks to determine action.
 *
 * PARSER_STATE_NONE is assigned to #_httpsResponse_t.parserState when the _httpsResponse_t.parserState is initialized
 * in @ref IotHttpsClient_InitializeRequest and before parsing a new respone message from the server.
 *
 * PARSER_STATE_IN_HEADERS is assigned at the start of the HTTP Response message. This occurs in the
 * _httpParserOnMessageBeginCallback(). HTTP headers are always first and there is always the response status line
 * and some headers in a response message according to RFC 2616.
 *
 * PARSER_STATE_HEADERS_COMPLETE is assigned when all of the headers are finished being parsed in the HTTP response
 * message. This occurs in the _httpParserOnHeadersCompleteCallback(). The state can end here if the response has no
 * body, like for a response to a HEAD request.
 * If this state is not reached after receiving headers from the network into the user configured header buffer and
 * running it through the parser, then we know that not all of the headers from the response could fit into the buffer.
 *
 * PARSER_STATE_IN_BODY is assigned each time the parser reaches HTTP response body. This occurs in the
 * _httpParserOnBodyCallback().
 *
 * PARSER_STATE_BODY_COMPLETE is assigned when the parser has finished with the whole HTTP response message. This
 * happens when _httpParserOnMessageCompleteCallback() is invoked.
 * If this state is not reached after receiving body from the network into the user configured body buffer and
 * running it through the parser, then we know that not all of the body from the response could fit into the buffer.
 */
typedef enum IotHttpsResponseParserState
{
    PARSER_STATE_NONE = 0,         /**< @brief The parser has not started so we are neither in the headers or the body. */
    PARSER_STATE_IN_HEADERS,       /**< @brief The parser is currently parsing the HTTP respone headers. */
    PARSER_STATE_HEADERS_COMPLETE, /**< @brief The parser has finished parsing the headers. */
    PARSER_STATE_IN_BODY,          /**< @brief The parser is currently parsing the HTTP response body. */
    PARSER_STATE_BODY_COMPLETE     /**< @brief The parser has completed parsing the HTTP response body. */
} IotHttpsResponseParserState_t;

/**
 * @brief The state denoting which buffer (the header buffer or the body buffer) is currently being processed
 * and for what.
 *
 * This state is set outside of the parser callbacks and used inside the of parser callbacks to determine actions.
 *
 * The state moves as follows:
 * Receiving and parsing a response: PROCESSING_STATE_NONE --> PROCESSING_STATE_FILLING_HEADER_BUFFER --> PROCESSING_STATE_FILLING_BODY_BUFFER --> PROCESSING_STATE_FINISHED
 * Searching a response for headers: ((enter state)) --> PROCESSING_STATE_SEARCHING_HEADER_BUFFER --> ((enter state))
 *
 * PROCESSING_STATE_NONE is assigned when #_httpsResponse_t.bufferProcessingState is initialized in
 * @ref IotHttpsClient_InitializeRequest.
 *
 * PROCESSING_STATE_FILLING_HEADER_BUFFER is assigned at the start of receiving HTTP response headers from the network
 * into the header buffer, before processing the received headers with the parser.
 * This state is then used in the parser callbacks _httpParserOnStatusCallback(), _httpParserOnHeaderFieldCallback(),
 * _httpParserOnHeaderValueCallback(), and _httpParserOnHeadersCompleteCallback() to move the
 * #_httpsResponse_t.headersCur pointer along in the header buffer.
 * Since the server sends the HTTP response as a single continuous message, sometimes during receiving of the HTTP
 * headers we may receive part or all of the HTTP response body:
 * ((example header buffer))[headers headers headers headers body body body]
 * When parsing this header buffer the parser will execute _httpParserOnBodyCallback() in the
 * PROCESSING_STATE_FILLING_HEADER_BUFFER state. The state is used here, for an asynchronous response, to save where
 * and how much body is inside the of the header buffer. When a body buffer becomes available, the body in the header
 * buffer will be copied to the body buffer.
 *
 * PROCESSING_STATE_FILLING_BODY_BUFFER is assigned at the start of receiving the HTTP response body form the network
 * into the body buffer, before processing the received body with the parser.
 *
 * PROCESSING_STATE_FINISHED is assigned at the end of IotHttpsClient_SendSync() or at the end of
 * IotHttpsClient_SendAsync() when both the header and body buffer are finished being filled with network data and
 * parsed.
 *
 * PROCESSING_STATE_SEARCHING_HEADER_BUFFER is assigned in IotHttpsClient_ReadHeader() when searching for a header
 * in the header buffer.
 * This state is used in the parser callback _httpParserOnHeaderFieldCallback() to check if the current header field
 * parsed equals the header we are searching for. It is used in parser callback _httpParserOnHeaderValueCallback() to
 * return the header value if the corresponding field we are searching for was found. It is used in parser callback
 * _httpParserOnHeadersCompleteCallback() to stop parsing the header buffer if the header we are searching for was not
 * found.
 *
 * The header buffer is separate from the body buffer.
 * The header buffer is configured in #IotHttpRequestInfo_t.respUserBuff. The body buffer is configured in
 * #IotHttpRequestInfo_t.syncInfo->respData or as buffer provided asynchronously during the
 * #IotHttpsClientCallbacks_t.readReadyCallback() to call to @ref IotHttpsClient_ReadResponseBody().
 */
typedef enum IotHttpsResponseBufferState
{
    PROCESSING_STATE_NONE,                   /**< @brief There is no buffer processing currently. */
    PROCESSING_STATE_FILLING_HEADER_BUFFER,  /**< @brief The header buffer is being filled and parsed. */
    PROCESSING_STATE_FILLING_BODY_BUFFER,    /**< @brief The body buffer is being filled and parsed. */
    PROCESSING_STATE_FINISHED,               /**< @brief Filling and parsing of both buffers is finished. */
    PROCESSING_STATE_SEARCHING_HEADER_BUFFER /**< @brief The header buffer is being searched. */
} IotHttpsResponseBufferState_t;

/*-----------------------------------------------------------*/

/**
 * @brief Represents an HTTP connection.
 */
typedef struct _httpsConnection
{
    const IotNetworkInterface_t * pNetworkInterface; /**< @brief Network interface with calls for connect, disconnect, send, and receive. */
    IotNetworkConnection_t pNetworkConnection;       /**< @brief Pointer to the network connection to use pNetworkInterface calls on. */
    uint32_t timeout;                                /**< @brief Timeout for a connection and waiting for a response from the network. */

    /**
     * @brief true if a connection was successful most recently on this context
     *
     * We have no way of knowing if the server closed the connection because that error is unique to the underlying TLS
     * layer. This is set to false initially, then set to true for a successful intentional call to connect.
     * Post connection, this is set to false only after an implicit disconnect with a non-persistent request, an implicit
     * disconnect with a network error, or an explicit disconnect with a call to @ref https_client_function_disconnect.
     */
    bool isConnected;
    bool isDestroyed;                           /**< @brief true if the connection is already destroyed and we should call anymore  */
    IotMutex_t connectionMutex;                 /**< @brief Mutex protecting operations on this entire connection context. */
    IotDeQueue_t reqQ;                          /**< @brief The queue for the requests that are not finished yet. */
    IotDeQueue_t respQ;                         /**< @brief The queue for the responses that are waiting to be processed. */
    IotTaskPoolJobStorage_t taskPoolJobStorage; /**< @brief An asynchronous operation requires storage for the task pool job. */
    IotTaskPoolJob_t taskPoolJob;               /**< @brief The task pool job identifier for an asynchronous request. */
} _httpsConnection_t;

/**
 * @brief Third party library http-parser information.
 *
 * There are two separate structures for http_parser state information. This is so that the application can read
 * a header during it's readReadyCallback. The readReadyCallback could be invoked many times and the parser will
 * therefore be invoked many times for each response read from the network. In order to ensure that the state of
 * the parser remains intact whilst headers may be read, two structures holding the state are kept.
 */
typedef struct _httpParserInfo
{
    http_parser responseParser; /**< @brief http_parser state information for parsing the response. */
    size_t ( * parseFunc )( http_parser * parser,
                            const http_parser_settings * settings,
                            const char * data,
                            size_t len ); /**< @brief http_parser_execute function is to be plugged in here during initialization of the response. */
    http_parser readHeaderParser;         /**< @brief http_parser state information for parsing the header buffer for reading a header. */
} _httpParserInfo_t;

/**
 * @brief Represents an HTTP response.
 */
typedef struct _httpsResponse
{
    IotLink_t link;                                      /**< @brief The link to insert the job in the connection's respQ. */
    uint8_t * pHeaders;                                  /**< @brief Pointer to the start of the headers buffer. */
    uint8_t * pHeadersEnd;                               /**< @brief Pointer to the end of the headers buffer. */
    uint8_t * pHeadersCur;                               /**< @brief Pointer to the next location to write in the headers buffer. */
    uint8_t * pBody;                                     /**< @brief Pointer to the start of the body buffer. */
    uint8_t * pBodyEnd;                                  /**< @brief Pointer to the end of the body buffer. */
    uint8_t * pBodyCur;                                  /**< @brief Pointer to the next location to write in the body buffer. */
    _httpParserInfo_t httpParserInfo;                    /**< @brief Third party http-parser information. */
    uint16_t status;                                     /**< @brief The HTTP response status code of this response. */
    IotHttpsMethod_t method;                             /**< @brief The method of the originating request. */
    IotHttpsResponseParserState_t parserState;           /**< @brief The current state of the parser. See IotHttpsResponseParserState_t documentation for more details. */
    IotHttpsResponseBufferState_t bufferProcessingState; /**< @brief Which buffer is currently being processed and for what. See IotHttpsResponseBufferState_t documentation. */
    char * pReadHeaderField;                             /**< @brief Header field that we want to read from the headers buffer when IotHttpsClient_ReadHeader() is called. */
    size_t readHeaderFieldLength;                        /**< @brief Length of pReadHeaderField */
    char * pReadHeaderValue;                             /**< @brief Header value that we read from the headers buffer when IotHttpsClient_ReadHeader() is called. */
    size_t readHeaderValueLength;                        /**< @brief Length of pReadHeaderValue. */
    bool foundHeaderField;                               /**< @brief State to use during parsing to let us know when we found the header field in the https-parser callbacks.
                                                          *          This is set to true when the header field is found in parser callback _httpParserOnHeaderFieldCallback().
                                                          *          On the following parser callback _httpParserOnHeaderValueCallback() we will store the value in pReadHeaderValue and then exit the parsing. */
    struct _httpsConnection * pHttpsConnection;          /**< @brief Connection associated with response. This is set during IotHttpsClient_SendAsync(). This is needed during the asynchronous workflow to receive data given the respHandle only in the callback. */
    bool isAsync;                                        /**< @brief This is set to true if this response is to be retrieved asynchronously. Set to false otherwise. */
    uint8_t * pBodyInHeaderBuf;                          /**< @brief Pointer to the start of body inside the header buffer for copying to a body buffer provided later by the asynchronous response process. */
    uint8_t * pBodyCurInHeaderBuf;                       /**< @brief Pointer to the next location to write body data during processing of the header buffer. This is necessary in case there is a chunk encoded HTTP response. */
    IotHttpsReturnCode_t bodyRxStatus;                   /**< @brief The status of network receiving the HTTPS body to be returned during the #IotHttpsClientCallbacks_t.readReadyCallback. */
    bool cancelled;                                      /**< @brief This is set to true to stop the request/response processing in the asynchronous request workflow. */
    IotSemaphore_t respFinishedSem;                      /**< @brief This is for synchronous response to post that is finished being received. It is better to use a task event signal, but that is not implemented yet in the iot_threads.h API. */
    IotHttpsReturnCode_t syncStatus;                     /**< @brief The status of the synchronous response. */

    /**
     * @brief This is set to true to when the request is finished being sent on the network
     *
     * A request is not shared with multiple tasks, so only one task will update this. This is to let the let the
     * network receive callback know that the request is fully pushed out to the server. This is also to let the
     * disconnect know that the request is not using the network interface resources anymore.
     */
    bool reqFinishedSending;
    IotHttpsClientCallbacks_t * pCallbacks; /**< @brief Pointer to the asynchronous request callbacks. */
    void * pUserPrivData;                   /**< @brief User private data to hand back in the asynchronous callbacks for context. */
    bool isNonPersistent;                   /**< @brief Non-persistent flag to indicate closing the connection immediately after receiving the response. */
} _httpsResponse_t;

/**
 * @brief Represents and HTTP request.
 */
typedef struct _httpsRequest
{
    IotLink_t link;                             /**< @brief The link to insert the job in the connection's reqQ. */
    uint8_t * pHeaders;                         /**< @brief Pointer to the start of the headers buffer. */
    uint8_t * pHeadersEnd;                      /**< @brief Pointer to the end of the headers buffer. */
    uint8_t * pHeadersCur;                      /**< @brief Pointer to the next location to write in the headers buffer. */
    uint8_t * pBody;                            /**< @brief Pointer to the start of the body buffer. */
    uint32_t bodyLength;                        /**< @brief Length of request body buffer. */
    IotHttpsMethod_t method;                    /**< @brief The method of the originating request. */
    IotHttpsConnectionInfo_t * pConnInfo;       /**< @brief Connection info associated with this request. For an implicit connection. */
    struct _httpsResponse * pHttpsResponse;     /**< @brief Response associated with request. This is initialized during IotHttpsClient_InitializeRequest(), then returned to the application in IotHttpsClient_SendAsync() and IotHttpsClient_SendSync(). */
    struct _httpsConnection * pHttpsConnection; /**< @brief Connection associated with request. This is set during IotHttpsClient_SendAsync(). It is needed for the asynchronous workflow to use to send data given the reqHandle only in the callback. */
    bool isNonPersistent;                       /**< @brief Non-persistent flag to indicate closing the connection immediately after receiving the response. */
    bool isAsync;                               /**< @brief This is set to true if this request is to be sent asynchronously. Set to false otherwise. */
    void * pUserPrivData;                       /**< @brief User private data to hand back in the asynchronous callbacks for context. */
    IotHttpsClientCallbacks_t * pCallbacks;     /**< @brief Pointer to the asynchronous request callbacks. */
    bool cancelled;                             /**< @brief Set this to true to stop the response processing in the asynchronous workflow. */
    IotHttpsReturnCode_t bodyTxStatus;          /**< @brief The status of network sending the HTTPS body to be returned during the #IotHttpsClientCallbacks_t.writeCallback. */
    bool scheduled;                             /**< @brief Set to true when this request has already been scheduled to the task pool. */
} _httpsRequest_t;

/*-----------------------------------------------------------*/

/**
 * @brief A map of the method enum to strings
 *
 * These are in order to the HTTP request method enums defined in IotHttpsMethod_t.
 */
static const char * _pHttpsMethodStrings[] = {
    "GET",
    "HEAD",
    "PUT",
    "POST"
};

#endif /* IOT_HTTPS_INTERNAL_H_ */
