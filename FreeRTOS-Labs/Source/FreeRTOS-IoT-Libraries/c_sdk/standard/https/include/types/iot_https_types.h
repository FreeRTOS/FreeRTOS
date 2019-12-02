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

/**
 * @file iot_https_types.h
 * @brief Types of the HTTPS Client library.
 */

#ifndef IOT_HTTPS_TYPES_H_
#define IOT_HTTPS_TYPES_H_

/* The config header is always included first. */
#include "iot_config.h"

/* C standard includes. */
#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

/* Type includes. */
#include "types/iot_platform_types.h"

/* Platform network include. */
#include "platform/iot_network.h"

/*------------------------- HTTPS defined constants --------------------------*/

/**
 * @constantspage{https_client,HTTPS Client library}
 *
 * @section https_minimum_user_buffer_sizes HTTPS Client Minimum User Buffer Sizes
 * @brief Variables calculating the size of #IotHttpsUserBuffer_t.bufferLen needed for the request, response, and
 * connection.
 *
 * @note These user buffer minimum values may change at any time in future versions, but their names will remain the
 * same.
 * - @ref requestUserBufferMinimumSize <br>
 *   @copybrief requestUserBufferMinimumSize
 * - @ref responseUserBufferMinimumSize <br>
 *   @copybrief responseUserBufferMinimumSize
 * - @ref connectionUserBufferMinimumSize <br>
 *   @copybrief connectionUserBufferMinimumSize
 *
 * @section https_connection_flags HTTPS Client Connection Flags
 * @brief Flags that modify the behavior of the HTTPS Connection.
 *
 * Flags should be bitwise-ORed with each other to change the behavior of @ref https_client_function_sendasync and
 * @ref https_client_function_sendsync. These flags are set in #IotHttpsConnectionInfo_t.flags.
 *
 * @note The values of flags may change at any time in future versions, but their names will remain the same.
 *
 * @section https_initializers HTTP Initializers
 * @brief Provide default values for the data types of the HTTP Client Library.
 *
 * @snippet this define_https_initializers
 *
 * All user-facing data types of the HTTPS Client library should be initialized using one of the following.
 *
 * @warning Failing to initialize an HTTPS Client data type with the appropriate initializer may result in undefined
 * behavior.
 * @note The initializers may change at any time in future versions, but their names will remain the same.
 *
 * <b>Example</b>
 * @code{c}
 * IotHttpsConnectionHandle_t connHandle = IOT_HTTPS_CONNECTION_HANDLE_INITIALIZER;
 * IotHttpsRequestHandle_t reqHandle = IOT_HTTPS_REQUEST_HANDLE_INITIALIZER;
 * IotHttpsResponseHandle_t respHandle = IOT_HTTPS_RESPONSE_HANDLE_INITIALIZER;
 * IotHttpsUserBuffer_t userBuffer = IOT_HTTPS_USER_BUFFER_INITIALIZER;
 * IotHttpsSyncInfo_t syncInfoReq = IOT_HTTPS_SYNC_INFO_INITIALIZER;
 * IotHttpsSyncInfo_t syncInfoResp = IOT_HTTPS_SYNC_INFO_INITIALIZER;
 * IotHttpsConnectionInfo_t connInfo = IOT_HTTPS_CONNECTION_INFO_INITIALIZER;
 * IotHttpsRequestInfo_t reqInfo = IOT_HTTPS_REQUEST_INFO_INITIALIZER
 * IotHttpsResponseInfo_t respInfo = IOT_HTTPS_RESPONSE_INFO_INITIALIZER
 * @endcode
 *
 * @section http_constants_connection_flags HTTPS Client Connection Flags
 * @brief Flags that modify the behavior the HTTPS connection.
 * - #IOT_HTTPS_IS_NON_TLS_FLAG <br>
 *   @copybrief IOT_HTTPS_IS_NON_TLS_FLAG
 * - #IOT_HTTPS_DISABLE_SNI <br>
 *   @copybrief IOT_HTTPS_DISABLE_SNI
 */

/**
 * @brief The minimum user buffer size for the HTTP request context and headers.
 *
 * This helps to calculate the size of the buffer needed for #IotHttpsRequestInfo_t.userBuffer.
 *
 * This buffer size is calculated to fit the HTTP Request-Line and the default headers. It does not account for the
 * length of the path in the Request-Line nor does it account for the length of the host name. It also does not account
 * for extra headers that the application may add. These sizes need to be accounted for by the application when
 * assigning a buffer.
 *
 * A typical value for sizing the request user buffer for the request context is 512 bytes. See the example below.
 * @code{c}
 * uint8_t requestUserBuffer[512] = { 0 };
 * IotHttpsRequestInfo_t requestInfo = IOT_HTTPS_REQUEST_INFO_INITIALIZER;
 * requestInfo.userBuffer.pBuffer = requestUserBuffer;
 * @endcode
 *
 * By the application providing the memory for the internal context, no memory is needed to be allocated internally to
 * the library for the internal context. The application has control over the memory allocation related to the request,
 * response, and connection.
 */
extern const uint32_t requestUserBufferMinimumSize;

/**
 * @brief The minimum user buffer size for the HTTP response context and headers.
 *
 * This helps to calculate the size of the buffer needed for #IotHttpsResponseInfo_t.userBuffer.
 *
 * The buffer size is calculated to fit the HTTP response context only. It does not account for the HTTP response status
 * line. It does not account for any HTTP response headers. If the buffer assigned to
 * #IotHttpsResponseInfo_t.userBuffer is of this minimum size, then the response Status-Line and the response headers
 * will not be stored. These sizes need to be accounted for by the application when assigning a buffer.
 *
 * If the response Status-Line and response headers cannot fit into #IotHttpsResponseInfo_t.userBuffer, then after a
 * call to @ref https_client_function_sendsync, calls to @ref https_client_function_readresponsestatus,
 * @ref https_client_function_readcontentlength, and @ref https_client_function_readheader will return a failure code.
 *
 * A typical value for sizing the response user buffer for the response context is 512 bytes. See the example below.
 * @code{c}
 * uint8_t responseUserBuffer[512] = { 0 };
 * IotHttpsResponseInfo_t responseInfo = IOT_HTTPS_RESPONSE_INFO_INITIALIZER;
 * responseInfo.userBuffer.pBuffer = responseUserBuffer;
 * @endcode
 *
 * By the application providing the memory for the internal context, no memory is needed to be allocated internally to
 * the library for the internal context. The application has control over the memory allocation related to the request,
 * response, and connection.
 */
extern const uint32_t responseUserBufferMinimumSize;

/**
 * @brief The minimum user buffer size for the HTTP connection context and headers.
 *
 * This helps to calculate the size of the buffer needed for #IotHttpsConnectionInfo_t.userBuffer.
 *
 * The buffer size is calculated to fit the HTTP connection context only. The buffer assigned by the application must be
 * at least this size.
 *
 * A typical value for sizing the request user buffer for the connection context is 512 bytes. See the example below.
 * @code{c}
 * uint8_t connectionUserBuffer[512] = { 0 };
 * IotHttpsConnectionInfo_t connectionInfo = IOT_HTTPS_CONNECTION_INFO_INITIALIZER;
 * connectionInfo.userBuffer.pBuffer = connectionUserBuffer;
 * @endcode
 *
 * By the application providing the memory for the internal context, no memory is needed to be allocated internally to
 * the library for the internal context. The application has control over the memory allocation related to the request,
 * response, and connection.
 */
extern const uint32_t connectionUserBufferMinimumSize;

/**
 * @brief Flag for #IotHttpsConnectionInfo_t that disables TLS.
 *
 * Set this bit in #IotHttpsConnectionInfo_t.flags to disable use of TLS when the connection is created. This library
 * creates secure connections by default.
 */
#define IOT_HTTPS_IS_NON_TLS_FLAG    ( 0x00000001 )

/**
 * @brief Flag for #IotHttpsConnectionInfo_t that disables Server Name Indication (SNI).
 *
 * Set this bit  #IotHttpsConnectionInfo_t.flags to disable SNI. SNI is enabled by default in this library. When SNI is
 * enabled  #IotHttpsConnectionInfo_t.pAddress will be used for the server name verification.
 */
#define IOT_HTTPS_DISABLE_SNI        ( 0x00000008 )

/* @[define_https_initializers] */
/** @brief Initializer for #IotHttpsConnectionHandle_t. */
#define IOT_HTTPS_CONNECTION_HANDLE_INITIALIZER    NULL
/** @brief Initializer for #IotHttpsRequestHandle_t. */
#define IOT_HTTPS_REQUEST_HANDLE_INITIALIZER       NULL
/** @brief Initializer for #IotHttpsResponseHandle_t. */
#define IOT_HTTPS_RESPONSE_HANDLE_INITIALIZER      NULL
/** @brief Initializer for #IotHttpsUserBuffer_t. */
#define IOT_HTTPS_USER_BUFFER_INITIALIZER          { 0 }
/** @brief Initializer for #IotHttpsSyncInfo_t. */
#define IOT_HTTPS_SYNC_INFO_INITIALIZER            { 0 }
/** @brief Initializer for #IotHttpsAsyncInfo_t. */
#define IOT_HTTPS_ASYNC_INFO_INITIALIZER           { 0 }
/** @brief Initializer for #IotHttpsConnectionInfo_t. */
#define IOT_HTTPS_CONNECTION_INFO_INITIALIZER      { 0 }
/** @brief Initializer for #IotHttpsRequestInfo_t. */
#define IOT_HTTPS_REQUEST_INFO_INITIALIZER         { 0 }
/** @brief Initializer for #IotHttpsResponseInfo_t. */
#define IOT_HTTPS_RESPONSE_INFO_INITIALIZER        { 0 }
/* @[define_https_initializers] */

/* Network include for the network types below. */
#include "platform/iot_network.h"

/**
 * @brief Type for the network interface containing the operations to send, receive, connect, and disconnect from
 * the network.
 */
#define IOT_HTTPS_NETWORK_INTERFACE_TYPE    const IotNetworkInterface_t *

/*---------------------------- HTTPS handle types ----------------------------*/

/**
 * @handles{https_client,HTTPS Client library}
 */

/**
 * @ingroup https_client_datatypes_handles
 * @brief Opaque handle of an HTTP connection.
 *
 * A connection handle is needed to send many requests over a single persistent connection. This handle is valid after
 * a successful call to @ref https_client_function_connect or @ref https_client_function_sendsync or
 * @ref https_client_function_sendasync. A variable of this type is passed to @ref https_client_function_sendsync,
 * @ref https_client_function_sendasync, and @ref https_client_function_disconnect to identify which connection that
 * function acts on.
 *
 * A call to @ref https_client_function_disconnect makes a connection handle invalid. Once @ref https_client_function_disconnect
 * returns, the connection handle should no longer be used. The application must call @ref https_client_function_connect
 * again to retrieve a new handle and a new connection.
 *
 * Typical web servers disconnect the client in around 30-60 seconds. The application needs to be aware of this, when
 * taking time between requests in a persistent connection.
 *
 * A connection handle is not thread safe. Multiple threads cannot connect and disconnect with the same handle at the
 * same time.
 *
 * Multiple threads can call @ref https_client_function_sendasync or @ref https_client_function_sendsync with the same
 * connection handle.
 */
typedef struct _httpsConnection   * IotHttpsConnectionHandle_t;

/**
 * @ingroup https_client_datatypes_handles
 * @brief Opaque handle of an HTTP request.
 *
 * Having a separate handle for the HTTP request allows the application to re-use a request.
 *
 * This handle is valid after a successful call to @ref https_client_function_initializerequest. A variable of this type
 * is passed to @ref https_client_function_sendasync or @ref https_client_function_sendsync.
 *
 * A request handle cannot be sent on multiple connections at the same time.
 *
 * A request handle is not thread safe. Multiple threads cannot write headers to the same request handle.
 */
typedef struct _httpsRequest      * IotHttpsRequestHandle_t;

/**
 * @ingroup https_client_datatypes_handles
 * @brief Opaque handle of an HTTP response.
 *
 * This handle is valid after a successful call to @ref https_client_function_sendsync or
 * @ref https_client_function_sendasync. A variable of this type is passed to
 * @ref https_client_function_readresponsestatus, @ref https_client_function_readcontentlength,
 * @ref https_client_function_readheader, and @ref https_client_function_readresponsebody.
 *
 * When returned from @ref https_client_function_sendsync or @ref https_client_function_sendasync, there is an
 * associated #IotHttpsRequestHandle_t. If the #IotHttpsRequestHandle_t associated with this response is re-initialized
 * with @ref https_client_function_initializerequest, then this response handle is no longer valid.
 *
 * A response handle is not thread safe. Multiple threads cannot read the headers in a response at the same time.
 */
typedef struct _httpsResponse     * IotHttpsResponseHandle_t;

/*-------------------------- HTTPS enumerated types --------------------------*/

/**
 * @enums{https_client,HTTPS Client library}
 */

/**
 * @ingroup https_client_datatypes_enums
 * @brief Return codes of [HTTPS Client functions](@ref https_client_functions).
 */
typedef enum IotHttpsReturnCode
{
    /**
     * @brief Returned for a successful operation.
     */
    IOT_HTTPS_OK = 0,

    /**
     * @brief An invalid parameter was passed into an API function.
     */
    IOT_HTTPS_INVALID_PARAMETER = 101,

    /**
     * @brief Invalid payload.
     */
    IOT_HTTPS_INVALID_PAYLOAD = 102,

    /**
     * @brief HTTPS message was too large to fit into a configured synchronous body buffer.
     */
    IOT_HTTPS_MESSAGE_TOO_LARGE = 103,

    /**
     * @brief Overflow occurred somewhere.
     */
    IOT_HTTPS_OVERFLOW = 104,

    /**
     * @brief A buffer provided could not hold data required by the library.
     */
    IOT_HTTPS_INSUFFICIENT_MEMORY = 105,

    /**
     * @brief Queue full.
     */
    IOT_HTTPS_QUEUE_FULL = 106,

    /**
     * @brief Operation retry.
     */
    IOT_HTTPS_RETRY = 107,

    /**
     * @brief Could not find an item specified by an API.
     *
     * Returned for not being able to find the address in a URL, the path in a URL, or a header field from the response
     * headers.
     */
    IOT_HTTPS_NOT_FOUND = 108,

    /**
     * @brief The HTTP request message was finished being written and we cannot write more with @ref https_client_function_writerequestbody.
     */
    IOT_HTTPS_MESSAGE_FINISHED = 109,

    /**
     * @brief An error occurred internally to the library.
     */
    IOT_HTTPS_INTERNAL_ERROR = 201,

    /**
     * @brief A network error occurred.
     */
    IOT_HTTPS_NETWORK_ERROR = 202,

    /**
     * @brief A network connection error occurred.
     */
    IOT_HTTPS_CONNECTION_ERROR = 203,

    /**
     * @brief A stream error occurred.
     */
    IOT_HTTPS_STREAM_ERROR = 204,

    /**
     * @brief An authentication error occurred.
     */
    IOT_HTTPS_AUTHENTICATION_ERROR = 205,

    /**
     * @brief A TLS error occurred.
     */
    IOT_HTTPS_TLS_ERROR = 206,

    /**
     * @brief An error occurred during the user callback.
     */
    IOT_HTTPS_USER_CALLBACK_ERROR = 207,

    /**
     * @brief The synchronous response could not be received in the specified timeout in @ref https_client_function_sendsync.
     */
    IOT_HTTPS_TIMEOUT_ERROR = 208,

    /**
     * @brief An error in the HTTP protocol.
     */
    IOT_HTTPS_PROTOCOL_ERROR = 209,

    /**
     * @brief The HTTPS request send was cancelled.
     */
    IOT_HTTPS_SEND_ABORT = 210,

    /**
     * @brief The HTTPS response receiving was cancelled.
     */
    IOT_HTTPS_RECEIVE_ABORT = 211,

    /**
     * @brief The asynchronous request had an error being scheduled.
     */
    IOT_HTTPS_ASYNC_SCHEDULING_ERROR = 212,

    /**
     * @brief There was an error parsing the HTTP response.
     */
    IOT_HTTPS_PARSING_ERROR = 213,

    /**
     * @brief Fatal HTTP library error.
     */
    IOT_HTTPS_FATAL = 901,

    /**
     * @brief The connection is busy and cannot be cleaned up.
     *
     * The connection was closed, but @ref https_client_function_disconnect must be called again to cleanup connection
     * resources.
     */
    IOT_HTTPS_BUSY = 902,

    /**
     * @brief Try again.
     */
    IOT_HTTPS_TRY_AGAIN = 903,

    /**
     * @brief Data exists.
     */
    IOT_HTTPS_DATA_EXIST = 904,

    /**
     * @brief The operation on the public API is not supported.
     */
    IOT_HTTPS_NOT_SUPPORTED = 905
} IotHttpsReturnCode_t;

/**
 * @ingroup https_client_datatypes_enums
 * @brief Types of HTTP methods.
 *
 * The HTTP method is configured in  #IotHttpsRequestInfo_t.method.
 */
typedef enum IotHttpsMethod
{
    IOT_HTTPS_METHOD_GET = 0, /* Client-to-server method GET */
    IOT_HTTPS_METHOD_HEAD,    /* Client-to-server method HEAD */
    IOT_HTTPS_METHOD_PUT,     /* Client-to-server method PUT */
    IOT_HTTPS_METHOD_POST     /* Client-to-server method POST. */
} IotHttpsMethod_t;

/**
 * @ingroup https_client_datatypes_enums
 * @brief Types of standard HTTP Response status codes.
 *
 * These status codes are taken from RFC 2616. Please see RFC 2616 for a description of each response status.
 */
enum IotHttpsResponseStatus
{
    IOT_HTTPS_STATUS_CONTINUE = 100,
    IOT_HTTPS_STATUS_SWITCHING_PROTOCOLS,
    IOT_HTTPS_STATUS_OK = 200,
    IOT_HTTPS_STATUS_CREATED,
    IOT_HTTPS_STATUS_ACCEPTED,
    IOT_HTTPS_STATUS_NON_AUTHORITIVE_INFORMATION,
    IOT_HTTPS_STATUS_NO_CONTENT,
    IOT_HTTPS_STATUS_RESET_CONTENT,
    IOT_HTTPS_STATUS_PARTIAL_CONTENT,
    IOT_HTTPS_STATUS_MULTIPLE_CHOICES = 300,
    IOT_HTTPS_STATUS_MOVED_PERMANENTLY,
    IOT_HTTPS_STATUS_FOUND,
    IOT_HTTPS_STATUS_SEE_OTHER,
    IOT_HTTPS_STATUS_NOT_MODIFIED,
    IOT_HTTPS_STATUS_USE_PROXY,
    IOT_HTTPS_STATUS_UNUSED,
    IOT_HTTPS_STATUS_TEMPORARY_REDIRECT,
    IOT_HTTPS_STATUS_BAD_REQUEST = 400,
    IOT_HTTPS_STATUS_UNAUTHORIZED,
    IOT_HTTPS_STATUS_PAYMENT_REQUIRED,
    IOT_HTTPS_STATUS_FORBIDDEN,
    IOT_HTTPS_STATUS_NOT_FOUND,
    IOT_HTTPS_STATUS_METHOD_NOT_ALLOWED,
    IOT_HTTPS_STATUS_NOT_ACCEPTABLE,
    IOT_HTTPS_STATUS_PROXY_AUTHENTICATION_REQUIRED,
    IOT_HTTPS_STATUS_REQUEST_TIMEOUT,
    IOT_HTTPS_STATUS_CONFLICT,
    IOT_HTTPS_STATUS_GONE,
    IOT_HTTPS_STATUS_LENGTH_REQUIRED,
    IOT_HTTPS_STATUS_PRECONDITION_FAILED,
    IOT_HTTPS_STATUS_REQUEST_ENTITY_TOO_LARGE,
    IOT_HTTPS_STATUS_REQUEST_URI_TOO_LONG,
    IOT_HTTPS_STATUS_UNSUPPORTED_MEDIA_TYPE,
    IOT_HTTPS_STATUS_REQUEST_RANGE_NOT_SATISFIABLE,
    IOT_HTTPS_STATUS_EXPECTATION_FAILED,
    IOT_HTTPS_STATUS_INTERNAL_SERVER_ERROR = 500,
    IOT_HTTPS_STATUS_NOT_IMPLEMENTED,
    IOT_HTTPS_STATUS_BAD_GATEWAY,
    IOT_HTTPS_STATUS_SERVICE_UNAVAILABLE,
    IOT_HTTPS_STATUS_GATEWAY_TIMEOUT,
    IOT_HTTPS_STATUS_HTTP_VERSION_NOT_SUPPORTED
};

/*------------------------- HTTPS parameter structs --------------------------*/

/**
 * @paramstructs{https_client,HTTPS Client library}
 */

/**
 * @ingroup https_client_datatypes_paramstructs
 *
 * @brief HTTPS Client library callbacks for asynchronous requests.
 *
 * @paramfor @ref https_client_function_initializerequest
 *
 * This type is a parameter in #IotHttpsResponseInfo_t.
 *
 * If any of the members in this type are set to NULL, then they will not be invoked during the asynchronous
 * request/response process.
 *
 * See @ref Asynchronous_Callback_Order for the order of the order of the callbacks and when they will be invoked.
 */
typedef struct IotHttpsClientCallbacks
{
    /**
     * @brief User-provided callback function signature for appending a header to current asynchronous request.
     *
     * If this is set to NULL, then it will not be invoked.
     * See @ref https_client_function_addheader for more information on adding a header in this callback.
     *
     * Appending the header when request is in progress is good for things like time limited authentication tokens.
     *
     * @param[in] pPrivData - User context configured in #IotHttpsAsyncInfo_t.pPrivData
     * @param[in] reqHandle - The handle for the current HTTP request in progress.
     */
    void ( * appendHeaderCallback )( void * pPrivData,
                                     IotHttpsRequestHandle_t reqHandle );

    /**
     * @brief User-provided callback function signature for writing data to the network for a current asynchronous
     * request.
     *
     * If this is set to NULL, then it will not be invoked.
     * See @ref https_client_function_writerequestbody for more information on writing request body.
     *
     * @param[in] pPrivData - User context configured in #IotHttpsAsyncInfo_t.pPrivData
     * @param[in] reqHandle - The handle for the current HTTP request in progress.
     */
    void ( * writeCallback )( void * pPrivData,
                              IotHttpsRequestHandle_t reqHandle );

    /**
     * @brief User-provided callback function signature for reading data from the network for a current asynchronous
     * response.
     *
     * The network indicated that after sending the associated request, the response is available for reading.
     * If this is set to NULL, then it will not be invoked and any response body received will be ignored.
     * See @ref https_client_function_readresponsebody for more information about reading the response body in this
     * callback.
     *
     * @param[in] pPrivData - User context configured in #IotHttpsAsyncInfo_t.pPrivData
     * @param[in] respHandle - The handle for the current HTTP response in progress.
     * @param[in] rc - A return code indicating any errors before this callback was invoked.
     * @param[in] status - The HTTP response status code of the current response in progress.
     */
    void ( * readReadyCallback )( void * pPrivData,
                                  IotHttpsResponseHandle_t respHandle,
                                  IotHttpsReturnCode_t rc,
                                  uint16_t status );

    /**
     * @brief User-provided callback function signature to indicate that the asynchronous response is completed.
     *
     * If this is set to NULL, then it will not be invoked.
     *
     * This callback is invoked when the response is fully received from the network and the request/response pair is
     * complete.
     * If there was an error in sending the request or an error in receiving the associated response, this callback will
     * be invoked, if the error caused the request or associated response to finish.
     * #IotHttpsClientCallbacks_t.errorCallback will be invoked first before this callback.
     * This callback is invoked to let the application know that memory used by #IotHttpsRequestInfo_t.userBuffer and
     * #IotHttpsResponseInfo_t.userBuffer can be freed, modified, or reused.
     *
     * For a non-persistent connection, the connection will be closed first before invoking this callback.
     *
     * @param[in] pPrivData - User context configured in #IotHttpsAsyncInfo_t.pPrivData
     * @param[in] respHandle - The handle for the current HTTP response in progress.
     * @param[in] rc - A return code indicating any errors before this callback was invoked.
     * @param[in] status - The HTTP response status code of the current response in progress.
     */
    void ( * responseCompleteCallback )( void * pPrivData,
                                         IotHttpsResponseHandle_t respHandle,
                                         IotHttpsReturnCode_t rc,
                                         uint16_t status );

    /**
     * @brief User-provided callback function signature to indicate that the connection has been close in an asynchronous
     * request process.
     *
     * If this is set to NULL, then it will not be invoked.
     * If there are errors during sending/receiving in the asynchronous process, the connection is not automatically
     * closed. If the server closes the connection during the asynchronous process, this callback is not invoked.
     * This callback is invoked only if the connection was flagged as non-persistent in
     * #IotHttpsConnectionInfo_t.flags.
     *
     * @param[in] pPrivData - User context configured in #IotHttpsAsyncInfo_t.pPrivData
     * @param[in] connHandle - The handle for the current HTTP connection.
     * @param[in] rc - A return code indicating any errors before this callback was invoked.
     */
    void ( * connectionClosedCallback )( void * pPrivData,
                                         IotHttpsConnectionHandle_t connHandle,
                                         IotHttpsReturnCode_t rc );

    /**
     * @brief User-provided callback function signature to indicate that an error occurred during the asynchronous
     * request process.
     *
     * If respHandle is NULL, then reqHandle will not be NULL and vise-versa. This signals which handle the error
     * occurred and if it is during the sending or receiving.
     *
     * @param[in] pPrivData - User context configured in #IotHttpsAsyncInfo_t.pPrivData
     * @param[in] respHandle - The handle for the current HTTP response.
     * @param[in] reqHandle - The handle for the current HTTP request.
     * @param[in] rc - A return code indicating any errors before this callback was invoked.
     */
    void ( * errorCallback )( void * pPrivData,
                              IotHttpsRequestHandle_t reqHandle,
                              IotHttpsResponseHandle_t respHandle,
                              IotHttpsReturnCode_t rc );
} IotHttpsClientCallbacks_t;

/**
 * @ingroup https_client_datatypes_paramstructs
 * @brief User-provided buffer for storing the HTTPS headers and library internal context.
 *
 * @paramfor @ref https_client_function_initializerequest.
 *
 * The user buffer is configured in #IotHttpsConnectionInfo_t.userBuffer, #IotHttpsRequestInfo_t.userBuffer and
 * #IotHttpsResponseInfo_t.userBuffer.
 *
 * The minimum size that the buffer must be configured to is indicated by requestUserBufferMinimumSize,
 * responseUserBufferMinimumSize, connectionUserBufferMinimumSize.
 */
typedef struct IotHttpsUserBuffer
{
    uint8_t * pBuffer;  /**< @brief Application provided buffer pointer. */
    uint32_t bufferLen; /**< @brief The length of the application provided buffer. */
} IotHttpsUserBuffer_t;

/**
 * @ingroup https_client_datatypes_paramstructs
 * @brief HTTPS Client synchronous request information.
 *
 * @paramfor @ref https_client_function_initializerequest, @ref https_client_function_sendsync,
 * @ref https_client_function_sendasync
 *
 * This structure is configured in #IotHttpsRequestInfo_t.u and #IotHttpsResponseInfo_t.
 *
 * A synchronous request will block until the response is fully received from the network.
 * This structure defines memory locations to store the response body.
 */
typedef struct IotHttpsSyncRequestInfo
{
    /**
     * Pointer to the HTTP message body.
     *
     * For a request this is the file or data we want to send.  The data is separated from the headers for the
     * flexibility to point to an already established file elsewhere in memory.
     *
     * For a response this is where to receive the response entity body.
     * If the length of the buffer provided to store the response body is smaller than the amount of body received,
     * then @ref https_client_function_sendsync will return a IOT_HTTPS_INSUFFICIENT_MEMORY error code. Although an error
     * was returned, the first #IotHttpsSyncInfo_t.bodyLen of the response received on the network will
     * still be available in the buffer.
     */
    uint8_t * pBody;
    uint32_t bodyLen; /**< @brief The length of the HTTP message body. */
} IotHttpsSyncInfo_t;

/**
 * @ingroup https_client_datatypes_paramstructs
 * @brief HTTPS Client asynchronous request information.
 *
 * @paramfor @ref https_client_function_initializerequest.
 *
 * This is parameter in #IotHttpsRequestInfo_t.u.
 *
 * An asynchronous request will ask the application for headers and body right before the request is ready
 * to be sent onto the network.
 * An asynchronous request will have the application read headers and body as soon as the response is received
 * on the network.
 */
typedef struct IotHttpsAsyncInfo
{
    /**
     * @brief Callbacks are used for an asynchronous request.
     * See #IotHttpsClientCallbacks_t for more information.
     */
    IotHttpsClientCallbacks_t callbacks;
    void * pPrivData; /**< @brief User private data to provide context to the asynchronous callbacks. */
} IotHttpsAsyncInfo_t;

/**
 * @ingroup https_client_datatypes_paramstructs
 * @brief HTTP connection configuration.
 *
 * @paramfor @ref https_client_function_connect or @ref https_client_function_sendsync or
 * @ref https_client_function_sendasync.
 *
 * This parameter is used to connection in @ref https_client_function_connect.
 *
 * @note The lengths of the strings in this struct should not include the NULL
 * terminator. Strings in this struct do not need to be NULL-terminated.
 */
typedef struct IotHttpsConnectionInfo
{
    /**
     * @brief Remote server address that is DNS discoverable.
     *
     * For example: avs-alexa-na.amazon.com.
     */
    const char * pAddress;
    uint32_t addressLen; /**< @brief remote address length. */

    uint16_t port;       /**< @brief Remote port number */

    /**
     * @brief Flags to configure the HTTPS connection.
     *
     * See @ref https_connection_flags for the available flags.
     *
     * Unknown flags are ignored.
     */
    uint32_t flags; /**< @brief Flags to configure the HTTPS connection. */

    /**
     * @brief Timeout waiting for a response from the network in milliseconds.
     *
     * If this is set to zero, it will default to @ref IOT_HTTPS_RESPONSE_WAIT_MS.
     */
    uint32_t timeout;

    const char * pCaCert;     /**< @brief Server trusted certificate store for this connection. */
    uint32_t caCertLen;       /**< @brief Server trusted certificate store size. */

    const char * pClientCert; /**< @brief Client certificate store for this connection. */
    uint32_t clientCertLen;   /**< @brief Client certificate store size. */

    const char * pPrivateKey; /**< @brief Client private key store for this connection. */
    uint32_t privateKeyLen;   /**< @brief Client private key store size. */

    /**
     * @brief String of all the ALPN protocols separated by commas needed for this connection.
     *
     * For the protocols needed for the AWS Iot Message broker endpoint please see:
     * https://docs.aws.amazon.com/iot/latest/developerguide/protocols.html
     */
    char * pAlpnProtocols;
    uint32_t alpnProtocolsLen; /**< @brief ALPN protocol string length. */

    /**
     * @brief User buffer to store the internal connection context.
     *
     * See @ref connectionUserBufferMinimumSize for information about the user buffer configured in
     * #IotHttpsConnectionInfo_t.userBuffer needed to create a valid connection handle.
     */
    IotHttpsUserBuffer_t userBuffer;

    /**
     * @brief The IOT network abstraction interface.
     *
     * This contains the interface to connect, disconnect, send data, and receive data from the network.
     *
     * In Amazon FreeRTOS this should be of the type IotNetworkInterface_t.
     */
    IOT_HTTPS_NETWORK_INTERFACE_TYPE pNetworkInterface;
} IotHttpsConnectionInfo_t;

/**
 * @ingroup https_client_datatypes_paramstructs
 * @brief HTTP request configuration.
 *
 * @paramfor @ref https_client_function_initializerequest.
 *
 * This parameter is used to configure the request in https_client_function_initializerequest.
 *
 * @note The lengths of the strings in this struct should not include the NULL
 * terminator. Strings in this struct do not need to be NULL-terminated.
 */
typedef struct IotHttpsRequestInfo
{
    /**
     * @brief The absolute path to the HTTP request object.
     *
     * The absolute path includes the path to the file AND the optional query.
     * An example URI path: "/v20160207/directives?query".
     *
     * If this is NULL, a "/" will be added to the Request-Line automatically.
     *
     * This is used to generate the Request-Line in the HTTP request message, see
     * @ref https_client_function_initializerequest for more information.
     */
    const char * pPath;
    uint32_t pathLen; /**< @brief URI path length */

    /**
     * @brief On of the HTTP method tokens defined in #IotHttpsMethod_t.
     *
     * This is used to generate the Request-Line in the HTTP request message, see
     * @ref https_client_function_initializerequest for more information.
     */
    IotHttpsMethod_t method;

    /**
     * @brief Host address this request is intended for, e.g., "awsamazon.com".
     *
     * This is the same as the address in #IotHttpsConnectionInfo_t.pAddress. This is here in the request structure to
     * automatically generate the "Host" header field in the header buffer space configured in
     * #IotHttpsRequestInfo_t.userBuffer. See @ref https_client_function_initializerequest for more information.
     */
    const char * pHost;
    uint32_t hostLen; /**< @brief Host address length. */

    /**
     * @brief Flag denoting if the connection should be non-persistent.
     *
     * If this flag is set to false, then the connection is persistent. When the connection is persistent, the HTTP
     * header "Connection: keep-alive" is automatically added to the headers to send to the server. This header
     * asks the server to not close the connection after sending the response.
     *
     * If this flag is set to true, then the connection is non-persistent. When the connection is non-persistent, then
     * HTTP header "Connection: close" is automatically added to the headers to send to the server. This header asks
     * the server to close the connection after sending the response.
     *
     * Please see https://tools.ietf.org/html/rfc2616#section-8.1.1 for more details.
     */
    bool isNonPersistent;

    /**
     * @brief Application owned buffer for storing the request headers and internal request context.
     *
     * For an asynchronous request, if the application owns the memory for this buffer, then it must not be modified,
     * freed, or reused until the the #IotHttpsClientCallbacks_t.responseCompleteCallback is invoked.
     *
     * Please see #IotHttpsUserBuffer_t for more information.
     */
    IotHttpsUserBuffer_t userBuffer;

    /**
     * @brief Indicator if this request is sync or async.
     *
     * Set this to false to use a synchronous request. Set this to true to use an asynchronous request.
     */
    bool isAsync;

    /**
     * @brief Specific information for either a synchronous request or an asynchronous request.
     *
     * See #IotHttpsAsyncInfo_t for information on pAsyncInfo.
     * See #IotHttpsSyncInfo_t for information on u.pSyncInfo.
     */
    union
    {
        IotHttpsAsyncInfo_t * pAsyncInfo; /**< @brief Information specifically for Asynchronous requests. */
        IotHttpsSyncInfo_t * pSyncInfo;   /**< @brief Information specifically for synchronous requests. */
    } u;
} IotHttpsRequestInfo_t;

/**
 * @ingroup https_client_datatypes_paramstructs
 * @brief HTTP request configuration.
 *
 * @paramfor @ref https_client_function_sendsync and @ref https_client_function_sendasync
 *
 * A separate response info is defined so that the application can re-initialize a request for re-use while still
 * processing a response that was already completed.
 */
typedef struct IotHttpsResponseInfo
{
    /**
     * The application owned buffer for storing the response headers and internal response context.
     *
     * For an asynchronous request, if the application owns the memory for this buffer, then it must not be modified,
     * freed, or reused until the the #IotHttpsClientCallbacks_t.responseCompleteCallback is invoked.
     *
     * Please see #IotHttpsUserBuffer_t for more information.
     */
    IotHttpsUserBuffer_t userBuffer;

    /**
     * @brief Specific information for a synchronously received response.
     *
     * Set this to NULL if the response is to be received asynchronously.
     *
     * See #IotHttpsSyncInfo_t for more information.
     */
    IotHttpsSyncInfo_t * pSyncInfo;
} IotHttpsResponseInfo_t;

#endif /* ifndef IOT_HTTPS_TYPES_H_ */
