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
 * @file iot_https_client.h
 * @brief User-facing functions of the Amazon FreeRTOS HTTPS Client library.
 */

#ifndef IOT_HTTPS_CLIENT_H_
#define IOT_HTTPS_CLIENT_H_

/* The config header is always included first. */
#include "iot_config.h"

/* HTTP types include. */
#include "types/iot_https_types.h"

/**
 * @functionspage{https_client,HTTPS Client Library}
 * - @functionname{https_client_function_init}
 * - @functionname{https_client_function_deinit}
 * - @functionname{https_client_function_disconnect}
 * - @functionname{https_client_function_connect}
 * - @functionname{https_client_function_initializerequest}
 * - @functionname{https_client_function_addheader}
 * - @functionname{https_client_function_writerequestbody}
 * - @functionname{https_client_function_sendsync}
 * - @functionname{https_client_function_sendasync}
 * - @functionname{https_client_function_cancelrequestasync}
 * - @functionname{https_client_function_cancelresponseasync}
 * - @functionname{https_client_function_readresponsestatus}
 * - @functionname{https_client_function_readcontentlength}
 * - @functionname{https_client_function_readheader}
 * - @functionname{https_client_function_readresponsebody}
 */

/**
 * @functionpage{IotHttpsClient_Init,https_client,init}
 * @functionpage{IotHttpsClient_Deinit,https_client,deinit}
 * @functionpage{IotHttpsClient_Disconnect,https_client,disconnect}
 * @functionpage{IotHttpsClient_Connect,https_client,connect}
 * @functionpage{IotHttpsClient_InitializeRequest,https_client,initializerequest}
 * @functionpage{IotHttpsClient_AddHeader,https_client,addheader}
 * @functionpage{IotHttpsClient_WriteRequestBody,https_client,writerequestbody}
 * @functionpage{IotHttpsClient_SendSync,https_client,sendsync}
 * @functionpage{IotHttpsClient_SendAsync,https_client,sendasync}
 * @functionpage{IotHttpsClient_CancelRequestAsync,https_client,cancelrequestasync}
 * @functionpage{IotHttpsClient_CancelResponseAsync,https_client,cancelresponseasync}
 * @functionpage{IotHttpsClient_ReadResponseStatus,https_client,readresponsestatus}
 * @functionpage{IotHttpsClient_ReadContentLength,https_client,readcontentlength}
 * @functionpage{IotHttpsClient_ReadHeader,https_client,readheader}
 * @functionpage{IotHttpsClient_ReadResponseBody,https_client,readresponsebody}
 */


/**
 * @brief One-time initialization of the IoT HTTPS Client library.
 *
 * <b>This must be called once before calling any API.</b>
 *
 * @warning No thread safety guarantees are provided for this function.
 *
 * @return One of the following:
 * - #IOT_HTTPS_OK if the HTTPS library is successfully initialized.
 *
 * @see @ref https_client_function_cleanup
 */
/* @[declare_https_client_init] */
IotHttpsReturnCode_t IotHttpsClient_Init( void );
/* @[declare_https_client_init] */

/**
 * @brief One time clean up of the IoT HTTPS Client library.
 *
 * This function frees resources taken in in @ref https_client_function_init. It should be called after
 * all HTTPS Connections have been close. HTTPS Connections are represented by #IotHttpsConnectionHandle_t and returned
 * by @ref https_client_function_connect. After this function returns @ref https_client_function_init
 * must be called again to use this library.
 *
 * @warning No thread safety guarantees are provided for this function.
 */
/* @[declare_https_client_cleanup] */
void IotHttpsClient_Cleanup( void );
/* @[declare_https_client_cleanup] */

/**
 * @cond DOXYGEN_IGNORE
 *
 * Backward compatibility function for one time clean up of the IoT HTTPS Client library.
 */
#define IotHttpsClient_Deinit    IotHttpsClient_Cleanup
/** @endcond */

/**
 * @brief Explicitly connect to the HTTPS server given the connection configuration pConnConfig.
 *
 * This routine blocks until the connection is complete.
 *
 * This function opens a new HTTPS connection with the server specified in #IotHttpsConnectionInfo_t.pAddress. The
 * connection is established by default on top of TLS over TCP. If the application wants to connect over TCP only, then
 * it must add the @ref IOT_HTTPS_IS_NON_TLS_FLAG to #IotHttpsConnectionInfo_t.flags. This is done at the application's
 * own risk.
 *
 * When the the last HTTP request sent on the connection is specified as persistent and we want to close the connection,
 * @ref https_client_function_disconnect must always be called on the valid #IotHttpsConnectionHandle_t. For more
 * information about persistent HTTP connections please see #IotHttpsRequestInfo_t.isNonPersistent.
 *
 * If the application receives a #IOT_HTTPS_NETWORK_ERROR from @ref https_client_function_sendsync or
 * @ref https_client_function_sendasync, on a persistent request, then the connection will be closed. The application
 * can call this this function again to reestablish the connection.
 *
 * If pConnHandle passed in is valid and represents a previously opened connection, this function will disconnect,
 * then reconnect. Before calling this function make sure that all outstanding requests on the connection have
 * completed. Outstanding requests are completed when @ref https_client_function_sendsync has returned or when
 * #IotHttpsClientCallbacks_t.responseCompleteCallback has been invoked for requests scheduled with
 * @ref https_client_function_sendasync.
 *
 * Keep in mind that many HTTP servers will close a connection, if it does not receive any requests, after a certain
 * amount of time. Many web servers may close the connection after 30-60 seconds. The state of pConnHandle will still be
 * in a connected state if this happens. If the server closed the connection, then the next request on the connection
 * will fail to send with a network error and the connection will move to a closed state.
 *
 * Also keep in mind that some HTTP servers do not accept persistent requests. Some HTTP servers will ignore that the
 * request contains the "Connection: keep-alive" header and close the connection immediately after sending the response.
 * If this happens, then the next request on the connection will fail to send with a network error and the connection
 * will close.
 *
 * To know if the connection was closed by the server, debug logging can be turned on to view the network error code
 * received. Debug logging is configured when @ref IOT_LOG_LEVEL_HTTPS is set to @ref IOT_LOG_DEBUG in iot_config.h.
 *
 * #IotHttpsConnectionInfo_t.userBuffer is used to store the internal context and therefore, multiple threads
 * calling this function simultaneously must ensure to use different #IotHttpsConnectionInfo_t objects.
 *
 * See @ref connectionUserBufferMinimumSize for information about the user buffer configured in
 * #IotHttpsConnectionInfo_t.userBuffer needed to create a valid connection handle.
 *
 * @param[out] pConnHandle - Handle returned representing the open connection. NULL if the function failed.
 * @param[in] pConnInfo - Configurations for the HTTPS connection.
 *
 * @return One of the following:
 * - #IOT_HTTPS_OK if the connection was successful.
 * - #IOT_HTTPS_CONNECTION_ERROR if the connection failed.
 * - #IOT_HTTPS_INVALID_PARAMETER if NULL parameters were passed in.
 * - #IOT_HTTPS_INTERNAL_ERROR if there was an error creating resources for the connection context.
 *
 * <b>Example</b>
 * @code{c}
 * // An initialized network interface.
 * IotNetworkInterface_t* pNetworkInterface;
 *
 * // Parameters to HTTPS Client connect.
 * IotHttpsConnectionInfo_t connInfo = IOT_HTTPS_CONNECTION_INFO_INITIALIZER;
 * IotHttpsConnectionHandle_t connHandle = IOT_HTTPS_CONNECTION_HANDLE_INITIALIZER;
 * uint8_t* pConnUserBuffer = (uint8_t*)malloc(connectionUserBufferMinimumSize);
 *
 * // Set the connection configuration information.
 * connInfo.pAddress = "www.amazon.com";
 * connInfo.addressLen = strlen("www.amazon.com");
 * connInfo.port = 443;
 * connInfo.flags = 0;
 * connInfo.pAlpnProtocols = "alpnproto0,alpnproto1"
 * connInfo.pCaCert = HTTPS_TRUSTED_ROOT_CA; // defined elsewhere
 * connInfo.caCertLen = sizeof( HTTPS_TRUSTED_ROOT_CA );
 * connInfo.userBuffer.pBuffer = pConnUserBuffer;
 * connInfo.userBuffer.bufferLen = connectionUserBufferMinimumSize;
 * connInfo.pClientCert = TLS_CLIENT_CERT;
 * connInfo.clientCertLen = sizeof( TLS_CLIENT_CERT );
 * connInfo.pPrivateKey = TLS_CLIENT_PRIV_KEY;
 * connInfo.privateKeyLen = sizeof( TLS_CLIENT_PRIV_KEY );
 * connInfo.pNetworkInterface = pNetworkInterface;
 *
 * IotHttpsReturnCode_t returnCode = IotHttpsClient_Connect(&connHandle, &connInfo);
 * if( returnCode == IOT_HTTPS_OK )
 * {
 *      // Do something with the HTTPS connection...
 *
 *      // Clean up and close the HTTPS connection once it's no longer needed.
 *      IotHttpsClient_Disconnect(connHandle);
 * }
 * @endcode
 */
/* @[declare_https_client_connect] */
IotHttpsReturnCode_t IotHttpsClient_Connect( IotHttpsConnectionHandle_t * pConnHandle,
                                             IotHttpsConnectionInfo_t * pConnInfo );
/* @[declare_https_client_connect] */

/**
 * @brief Disconnect from the HTTPS server given the connection handle connHandle.
 *
 * This routine blocks until the disconnect is complete.
 * If the connection handle is not valid, the behavior is undefined.
 * If the connection handle is already disconnected then this routine will return IOT_HTTPS_OK.
 *
 * When the HTTP request is specified as persistent and we want to close the connection, this API must always
 * be called on the valid #IotHttpsConnectionHandle_t. For more information about persistent HTTP connections please see
 * #IotHttpsRequestInfo_t.isNonPersistent.
 *
 * When the HTTP request is specified as non-persistent, by setting #IotHttpsRequestInfo_t.isNonPersistent to true, then
 * this function will be called automatically on the valid IotHttpsConnectionHandle_t after receiving the response. There
 * is no need to call this function in case of a non-persistent request.
 *
 * This will put the internal connection state in #IotHttpsConnectionHandle_t to disconnected.
 *
 * If the application receives a #IOT_HTTPS_NETWORK_ERROR from @ref https_client_function_sendsync or
 * @ref https_client_function_sendasync, on a persistent request, that does not always mean the connection has been
 * disconnected. This function MUST be called to close the connection and clean up connection resources taken by
 * #IotHttpsConnectionHandle_t.
 *
 * This function will cancel all pending requests on the connection. If a request currently being sent on the connection,
 * then this function will disconnect the connection, but it will not free network connection resource and will return
 * with #IOT_HTTPS_BUSY. The application may call this function again later to try again.
 *
 * Multiple threads must not call this function for the same #IotHttpsConnectionHandle_t. Multiple threads
 * can call this function for different #IotHttpsConnectionHandle_t. Make sure that all request/responses
 * have finished on the connection before calling this API. Outstanding requests are completed when
 * @ref https_client_function_sendsync has returned or when #IotHttpsClientCallbacks_t.responseCompleteCallback
 * has been invoked for requests scheduled with @ref https_client_function_sendasync.
 *
 * @param[in] connHandle - Valid handle representing an open connection.
 *
 * @return One of the following:
 * - #IOT_HTTPS_OK if the disconnect was successful
 * - #IOT_HTTPS_INVALID_PARAMETER if NULL parameters were passed in.
 * - #IOT_HTTPS_BUSY if the connection is in use and cannot be destroyed.
 */
/* @[declare_https_client_disconnect] */
IotHttpsReturnCode_t IotHttpsClient_Disconnect( IotHttpsConnectionHandle_t connHandle );
/* @[declare_https_client_disconnect] */

/**
 * @brief Initializes the request by adding a formatted Request-Line to the start of HTTPS request header buffer.
 *
 * This function will initialize the HTTP request context by setting where to write the next headers to the start
 * of the configured header buffer in #IotHttpsRequestInfo_t.userBuffer.
 *
 * The Request-Line will be added to the start of the headers space in #IotHttpsRequestInfo_t.userBuffer.
 * The header space follows the request context in the user buffer. See @ref requestUserBufferMinimumSize for more
 * information on sizing the #IotHttpsRequestInfo_t.userBuffer so that this function does not fail.
 *
 * The Request-Line generated is of the following format:
 *
 * @code
 * method path version\r\n
 * @endcode
 *
 * Example:
 *
 * @code
 * GET /path/to/item.file?possible_query HTTP/1.1\r\n
 * @endcode
 *
 * The initial required headers are also added to the #IotHttpsRequestInfo_t.userBuffer. These headers are User-Agent
 * and Host. The User-Agent value is configured in iot_config.h using IOT_HTTPS_USER_AGENT. The Host value is the DNS
 * resolvable server address.
 *
 * @param[out] pReqHandle - request handle representing the internal request context is returned. NULL if the function failed.
 * @param[in] pReqInfo - HTTPS request information.
 *
 * @return One of the following:
 * - #IOT_HTTPS_OK if the Request-Line was successfully added to the header space in #IotHttpsRequestInfo_t.userBuffer.
 * - #IOT_HTTPS_INSUFFICIENT_MEMORY if the Request-Line generated exceeds #IotHttpsUserBuffer_t.bufferLen in #IotHttpsRequestInfo_t.userBuffer.
 * - #IOT_HTTPS_INVALID_PARAMETER for NULL parameters.
 * - #IOT_HTTPS_INTERNAL_ERROR for library internal errors.
 *
 * <b>Example</b>
 * @code{c}
 * // An initialized network interface.
 * IotNetworkInterface_t* pNetworkInterface;
 *
 * // Parameters to HTTPS Client request initialization.
 * IotHttpsRequestInfo_t reqInfo = IOT_HTTPS_REQUEST_INFO_INITIALIZER;
 * IotHttpsRequestHandle_t reqHandle = IOT_HTTPS_REQUEST_HANDLE_INITIALIZER;
 * IotHttpsSyncInfo_t syncInfo = IOT_HTTPS_SYNC_INFO_INITIALIZER;
 * // Leave some room for extra headers.
 * uint32_t userBufferSize = requestUserBufferMinimumSize + 256;
 * uint8_t* pRequestUserBuffer = (uint8_t*)malloc(userBufferSize);
 *
 * // Set the synchronous information.
 * syncInfo.pBody = PREDEFINED_BODY_BUFFER;
 * syncInfo.bodyLen = PREDEFINED_BODY_BUFFER_LEN;
 *
 * // Set the request configuration information.
 * reqInfo.pPath = "/path_to_item?query_maybe";
 * reqInfo.pPathLen = strlen("/path_to_item?query_maybe");
 * reqInfo.method = IOT_HTTPS_METHOD_GET;
 * reqInfo.pHost = "www.amazon.com";
 * reqInfo.hostLen = strlen("www.amazon.com");
 * reqInfo.isNonPersistent = false;
 * reqInfo.userBuffer.pBuffer = pRequestUserBuffer;
 * reqInfo.userBuffer.bufferLen = userBufferSize;
 * reqInfo.isAsync = false;
 * reqInfo.pSyncInfo = &syncInfo;
 *
 * IotHttpsReturnCode_t returnCode = IotHttpsClient_InitializeRequest(&reqHandle, &reqInfo);
 * if( returnCode == IOT_HTTPS_OK )
 * {
 *      // Handle the error.
 * }
 * @endcode
 */
/* @[declare_https_client_initializerequest] */
IotHttpsReturnCode_t IotHttpsClient_InitializeRequest( IotHttpsRequestHandle_t * pReqHandle,
                                                       IotHttpsRequestInfo_t * pReqInfo );
/* @[declare_https_client_initializerequest] */

/**
 * @brief Add a header to the current HTTPS request represented by reqHandle.
 *
 * The header line is appended to the request header buffer space in #IotHttpsRequestInfo_t.userBuffer.
 * Please see #requestUserBufferMinimumSize for information about sizing the #IotHttpsRequestInfo_t.userBuffer so
 * that this function does not fail.
 *
 * Header lines are appended in the following format:
 * @code
 * header_field_name: header_value\r\n"
 * @endcode
 * Example:
 * @code
 * Range: bytes=1024-2047\r\n
 * @endcode
 * The last header line must be followed by a "\r\n" to separate the last header line from
 * the entity body. These 2 characters are accounted for in #requestUserBufferMinimumSize.
 *
 * The remaining length, after the header is added, is printed to the system configured standard debug output when
 * @ref IOT_LOG_LEVEL_HTTPS is set to @ref IOT_LOG_DEBUG in iot_config.h.
 *
 * For an asynchronous request, this function can be invoked before the request is sent with
 * @ref https_client_function_sendasync, or during #IotHttpsClientCallbacks_t.appendHeaderCallback. It is
 * recommended to invoke this function in #IotHttpsClientCallbacks_t.appendHeaderCallback.
 *
 * <b> Asynchronous Example </b>
 * @code{c}
 * void _applicationDefined_appendHeaderCallback(void * pPrivData, IotHttpsRequestHandle_t reqHandle)
 * {
 *      ...
 *      char date_in_iso8601[17] = { 0 };
 *      GET_DATE_IN_ISO8601(date_in_iso8601);
 *      const char amz_date_header[] = "x-amz-date";
 *      uint32_t amz_date_header_length = strlen(amz_date_header);
 *      IotHttpsClient_AddHeader(reqHandle, amz_date_header, amz_date_header_length, date_in_iso8601, strlen(date_in_iso8601));
 *      ...
 * }
 * @endcode
 *
 * For a synchronous request, if extra headers are desired to be added, this function must be invoked before
 * @ref https_client_function_sendsync.
 * <b> Synchronous Example </b>
 * @code{c}
 * ...
 * char date_in_iso8601[17] = { 0 };
 * GET_DATE_IN_ISO8601(date_in_iso8601);
 * const char amz_date_header[] = "x-amz-date";
 * uint32_t amz_date_header_length = strlen(amz_date_header);
 * IotHttpsClient_AddHeader(reqHandle, amz_date_header, amz_date_header_length, date_in_iso8601, strlen(date_in_iso8601));
 * ...
 * IotHttpsClient_SendSync(connHandle, reqHandle, &respHandle, &respInfo, timeout);
 * ...
 * @endcode
 *
 * The following header fields are automatically added to the request header buffer and must NOT be added again with
 * this routine:
 * - Connection:     - This header is added to the request when the headers are being sent on the network.
 * - User-agent:     - This header is added during @ref https_client_function_initializerequest
 * - Host:           - This header is added during @ref https_client_function_initializerequest
 * - Content-Length: - This header is added to the request when the headers are being sent on the network.
 *
 * The reqHandle is not thread safe. If two threads have the same reqHandle and attempt to add headers at the same
 * time, garbage strings may be written to the reqHandle.
 *
 * @param[in] reqHandle - HTTPS request to write the header line to.
 * @param[in] pName - String header field name to write.
 * @param[in] nameLen - The length of the header name to write.
 * @param[in] pValue - https header value buffer pointer. Do not include token name.
 * @param[in] valueLen - length of header value to write.
 *
 * @return One of the following:
 * - #IOT_HTTPS_OK if the header line was successfully added to the header space in #IotHttpsRequestInfo_t.userBuffer.
 * - #IOT_HTTPS_INSUFFICIENT_MEMORY if the header line cannot fit into the header buffer.
 * - #IOT_HTTPS_INVALID_PARAMETER for NULL parameters or if an attempt to add automatically added headers is made.
 */
/* @[declare_https_client_addheader] */
IotHttpsReturnCode_t IotHttpsClient_AddHeader( IotHttpsRequestHandle_t reqHandle,
                                               char * pName,
                                               uint32_t nameLen,
                                               char * pValue,
                                               uint32_t valueLen );
/* @[declare_https_client_addheader] */

/**
 * @brief Writes the request body to the network for the request represented by reqHandle.
 *
 * This function is intended to be used by an asynchronous request. It must be called within the
 * #IotHttpsClientCallbacks_t.writeCallback.
 *
 * In HTTP/1.1 the headers are sent on the network first before any body can be sent. The auto-generated header
 * Content-Length is taken from the len parameter and sent first before the data in parameter pBuf is sent.
 * This library does not support Transfer-Encoding: chunked or other requests where the Content-Length is unknown, so
 * this function cannot be called more than once in #IotHttpsClientCallbacks_t.writeCallback for an HTTP/1.1 request.
 *
 * isComplete must always be set to 1 in this current version of the HTTPS client library.
 *
 * If there are network errors in sending the HTTP headers, then the #IotHttpsClientCallbacks_t.errorCallback will be
 * invoked following a return from the #IotHttpsClientCallbacks_t.writeCallback.
 *
 * <b> Example Asynchronous Code </b>
 * @code{c}
 * void applicationDefined_writeCallback(void * pPrivData, IotHttpsRequestHandle_t reqHandle)
 * {
 *      ...
 *      char * writeData[1024];
 *      IotHttpsClient_WriteRequestBody(reqHandle, writeData, 1024, 1);
 *      ...
 * }
 * @endcode
 *
 * @param[in] reqHandle - identifier of the connection.
 * @param[in] pBuf - client write data buffer pointer.
 * @param[in] len - length of data to write.
 * @param[in] isComplete - This parameter parameter must be set to 1.
 *
 * @return one of the following:
 * - #IOT_HTTPS_OK if write successfully, failure code otherwise.
 * - #IOT_HTTPS_MESSAGE_FINISHED if this function is called a second time with the same reqHandle.
 * - #IOT_HTTPS_NOT_SUPPORTED if isComplete is set to 0.
 * - #IOT_HTTPS_INVALID_PARAMETER if this API is used for a synchronous request.
 * - #IOT_HTTPS_NETWORK_ERROR if there was an error sending the headers or body on the network.
 * - Please see #IotHttpsReturnCode_t for other failure codes.
 */
/* @[declare_https_client_writerequestbody] */
IotHttpsReturnCode_t IotHttpsClient_WriteRequestBody( IotHttpsRequestHandle_t reqHandle,
                                                      uint8_t * pBuf,
                                                      uint32_t len,
                                                      int isComplete );
/* @[declare_https_client_writerequestbody] */

/**
 * @brief Synchronous send of the HTTPS request.
 *
 * This function blocks waiting for the entirety of sending the request and receiving the response.
 *
 * If #IotHttpsRequestInfo_t.isNonPersistent is set to true, then the connection will disconnect, close, and clean all
 * taken resources automatically after receiving the first response.
 *
 * See @ref connectionUserBufferMinimumSize for information about the user buffer configured in
 * #IotHttpsConnectionInfo_t.userBuffer needed to create a valid connection handle.
 *
 * To retrieve the response body applications must directly refer #IotHttpsSyncInfo_t.pBody configured in #IotHttpsRequestInfo_t.u.
 *
 * If the response body does not fit in the configured #IotHttpsSyncInfo_t.pBody, then this function will return with error
 * #IOT_HTTPS_MESSAGE_TOO_LARGE. To avoid this issue, the application needs to determine beforehand how large the file
 * to download is. This can be done with a HEAD request first, then extracting the "Content-Length" with
 * @ref https_client_function_readcontentlength. This could also be done with a GET request with the header
 * "Range: bytes=0-0", then extracting the "Content-Range" with @ref https_client_function_readheader. Keep in mind that
 * not all HTTP servers support Partial Content responses.
 *
 * Once a the file size is known, the application can initialize the request with a large
 * enough buffer or the application can make a partial content request with the header
 * "Range: bytes=N-M", where N is the starting byte requested and M is the ending byte requested.
 *
 * The response headers as received from the network will be stored in the header buffer space in
 * #IotHttpsResponseInfo_t.userBuffer. If the configured #IotHttpsResponseInfo_t.userBuffer is too small
 * to fit the headers received, then headers that don't fit will be thrown away. Please see
 * #responseUserBufferMinimumSize for information about sizing the #IotHttpsResponseInfo_t.userBuffer.
 * To receive feedback on headers discarded, debug logging must be turned on in iot_config.h by setting
 * @ref IOT_LOG_LEVEL_HTTPS to @ref IOT_LOG_DEBUG.
 *
 * Multiple threads must not call this function for the same #IotHttpsRequestHandle_t. Multiple threads can call this
 * function for a different #IotHttpsRequestHandle_t, even on the same #IotHttpsConnectionHandle_t. An application must
 * wait util a request is fully sent, before scheduling it again. A request is fully sent when this function has returned.
 *
 * @param[in] connHandle - Handle from an HTTPS connection created with @ref https_client_function_connect.
 * @param[in] reqHandle - Handle from a request created with @ref https_client_function_initializerequest.
 * @param[out] pRespHandle - HTTPS response handle resulting from a successful send and receive.
 * @param[in] pRespInfo - HTTP response configuration information.
 * @param[in] timeoutMs - Timeout waiting for the sync request to finish. Set this to 0 to wait forever.
 *
 * @return One of the following:
 * - #IOT_HTTPS_OK if the request was sent and the response was received successfully.
 * - #IOT_HTTPS_MESSAGE_TOO_LARGE if the response cannot fit in the configured struct IotHttpsRequestHandle.userBuffer.pBuffer and struct IotHttpsRequestHandle.u.pSyncInfo.pRespData.
 * - #IOT_HTTPS_CONNECTION_ERROR if the connection failed.
 * - #IOT_HTTPS_INVALID_PARAMETER if there are NULL parameters or the request is asynchronous.
 * - #IOT_HTTPS_NETWORK_ERROR if there was an error sending the data on the network.
 * - #IOT_HTTPS_PARSING_ERROR if there was an error parsing the HTTP response.
 * - #IOT_HTTPS_TIMEOUT_ERROR if the timeoutMs is reached when waiting for a response to the request.
 */
/* @[declare_https_client_sendsync] */
IotHttpsReturnCode_t IotHttpsClient_SendSync( IotHttpsConnectionHandle_t connHandle,
                                              IotHttpsRequestHandle_t reqHandle,
                                              IotHttpsResponseHandle_t * pRespHandle,
                                              IotHttpsResponseInfo_t * pRespInfo,
                                              uint32_t timeoutMs );
/* @[declare_https_client_sendsync] */

/**
 * @brief Asynchronous send of the the HTTPS request.
 *
 * This function will invoke, as needed, each of the non-NULL callbacks configured in #IotHttpsAsyncInfo_t.callbacks
 * when the scheduled asynchronous request is progress. Please see #IotHttpsClientCallbacks_t for information on each of
 * the callbacks.
 *
 * After this API is executed, the scheduled async response will store the response headers as received from
 * the network, in the header buffer space configured in #IotHttpsResponseInfo_t.userBuffer. If the
 * configured #IotHttpsResponseInfo_t.userBuffer is too small to fit the headers received, then headers that don't
 * fit will be thrown away. Please see #responseUserBufferMinimumSize for information about sizing the
 * #IotHttpsResponseInfo_t.userBuffer.
 *
 * If #IotHttpsRequestInfo_t.isNonPersistent is set to true, then the connection will disconnect, close, and clean all
 * taken resources automatically after receiving the first response.
 *
 * See @ref connectionUserBufferMinimumSize for information about the user buffer configured in
 * #IotHttpsConnectionInfo_t.userBuffer needed to create a valid connection handle.
 *
 * A #IotHttpsRequestHandle_t cannot be schedule again or reused until the request has finished sending. The request
 * has safely finished sending once #IotHttpsClientCallbacks_t.readReadyCallback is invoked. After the
 * #IotHttpsClientCallbacks_t.readReadyCallback is invoked the #IotHttpsRequestInfo_t.userBuffer can freed,
 * modified, or reused.
 *
 * @param[in] connHandle - Handle from an HTTPS connection.
 * @param[in] reqHandle - Handle from a request created with IotHttpsClient_initialize_request.
 * @param[out] pRespHandle - HTTPS response handle.
 * @param[in] pRespInfo - HTTP response configuration information.
 *
 * @return One of the following:
 * - #IOT_HTTPS_OK if the request was sent and the response was received successfully.
 * - #IOT_HTTPS_MESSAGE_TOO_LARGE if the response cannot fit in the configured
 *      IotHttpsRequestHandle_t.response_message.headers and IotHttpsRequestHandle_t.response_message.body.
 * - #IOT_HTTPS_CONNECTION_ERROR if the connection failed.
 * - #IOT_HTTPS_FATAL if there was a grave error with the last async job finishing.
 * - #IOT_HTTPS_ASYNC_SCHEDULING_ERROR if there was an error scheduling the asynchronous request.
 * - #IOT_HTTPS_INTERNAL_ERROR if there was an internal error with starting an asynchronous request servicing task.
 * - #IOT_HTTPS_INVALID_PARAMETER if there were NULL parameters or the request passed in was a synchronous type.
 *
 */
/* @[declare_https_client_sendasync] */
IotHttpsReturnCode_t IotHttpsClient_SendAsync( IotHttpsConnectionHandle_t connHandle,
                                               IotHttpsRequestHandle_t reqHandle,
                                               IotHttpsResponseHandle_t * pRespHandle,
                                               IotHttpsResponseInfo_t * pRespInfo );
/* @[declare_https_client_sendasync] */

/**
 * @brief Cancel an Asynchronous request.
 *
 * This will stop an asynchronous request. When an asynchronous request is stopped it will not proceed to do any of
 * the following: send headers, send body, receive headers, or receive body. This depends on where in the process
 * the request is. For example, if the request is cancelled after sending the headers, then it will not attempt tp
 * send the body. A cancelled return code will be returned to the application.
 *
 * If this is called before the scheduled asynchronous request actually runs, then request will not be sent.
 * If this is called during any of the asynchronous callbacks, then the library will stop processing the request when
 * the callback returns. This is useful for any error conditions, found during the asynchronous callbacks, where the
 * application wants to stop the rest of the request processing.
 *
 * If the asynchronous request stops processing, the buffers in #IotHttpsRequestInfo_t.userBuffer can be safely freed,
 * modified, or reused, only once #IotHttpsClientCallbacks_t.readReadyCallback is invoked.
 *
 * <b> Example Asynchronous Code </b>
 * @code{c}
 * void _applicationDefined_appendHeaderCallback(void * pPrivData, IotHttpsRequestHandle_t reqHandle)
 * {
 *      char token[MAX_TOKEN_LENGTH] = { 0 }
 *      int len = MAX_TOKEN_LENGTH;
 *      int status = gen_auth_token(token, &len);
 *      if( status == GEN_TOKEN_FAIL)
 *      {
 *          IotHttpsClient_CancelRequestAsync(reqHandle);
 *      }
 *      ...
 * }
 *
 * void _applicationDefined_writeCallback(void * pPrivData, IotHttpsRequestHandle_t reqHandle)
 * {
 *      if( application_data_get(writeBuffer, writeBufferLen) == GEN_TOKEN_FAIL)
 *      {
 *          IotHttpsClient_CancelRequestAsync(reqHandle);
 *      }
 *      ...
 * }
 * @endcode
 *
 * @param[in] reqHandle - Request handle associated with the request.
 *
 * @return One of the following:
 * - IOT_HTTPS_OK if the request was successfully cancelled.
 */
/* @[declare_https_client_cancelrequestasync] */
IotHttpsReturnCode_t IotHttpsClient_CancelRequestAsync( IotHttpsRequestHandle_t reqHandle );
/* @[declare_https_client_cancelrequestasync] */

/**
 * @brief Cancel an Asynchronous response.
 *
 * This will stop an asynchronous response. When an asynchronous response is stopped it will not proceed to do any of
 * the following: send headers, send body, receive headers, or receive body. This depends on where in the process
 * the response is. For example, if the response is cancelled after receiving the headers, then it will not attempt tp
 * receive the body. A cancelled return code will be returned to the application.
 *
 * If this is called during ANY of the asynchronous callbacks, then the library will stop processing the response when
 * the callback returns. This is useful for any error conditions, found during the asynchronous callbacks, where the
 * application wants to stop the rest of the response processing.
 *
 * If the asynchronous response stops processing, the buffers configured in #IotHttpsResponseInfo_t.userBuffer can
 * be freed, modified, or reused only after the #IotHttpsClientCallbacks_t.responseCompleteCallback in invoked.
 *
 * <b> Example Asynchronous Code </b>
 * @code{c}
 *
 * void applicationDefined_readReadyCallback(void * pPrivData, IotHttpsResponseHandle_t respHandle, IotHttpsReturnCode_t rc, uint16_t status)
 * {
 *      ...
 *      if (status != IOT_HTTPS_STATUS_OK)
 *      {
 *          IotHttpsClient_CancelResponseAsync(NULL, respHandle);
 *      }
 *      ...
 * }
 * @endcode
 *
 * @param[in] respHandle - Response handle associated with the response.
 *
 * @return One of the following:
 * - #IOT_HTTPS_OK if the response was successfully cancelled.
 */
/* @[declare_https_client_cancelresponseasync] */
IotHttpsReturnCode_t IotHttpsClient_CancelResponseAsync( IotHttpsResponseHandle_t respHandle );
/* @[declare_https_client_cancelresponseasync] */

/**
 * @brief Retrieve the HTTPS response status.
 *
 * The HTTP response status code is contained in the Status-Line of the response header buffer configured in
 * #IotHttpsResponseInfo_t.userBuffer. It is the first line of a standard HTTP response message. If the response
 * Status-Line could not fit into #IotHttpsResponseInfo_t.userBuffer, then this function will return an error code.
 * Please see #responseUserBufferMinimumSize for information about sizing the #IotHttpsResponseInfo_t.userBuffer.
 *
 * This routine can be used for both a synchronous and asynchronous response.
 *
 * <b> Example Synchronous Code </b>
 * @code{c}
 *      ...
 *      IotHttpsClient_SendSync(connHandle, reqHandle, &respHandle, &respInfo, timeout);
 *      uint16_t status = 0;
 *      IotHttpsClient_ReadResponseStatus(respHandle, &status);
 *      if (status != IOT_HTTPS_STATUS_OK)
 *      {
 *          // Handle server response status.
 *      }
 *      ...
 * @endcode
 *
 * For an asynchronous response the response status is the status parameter in
 * #IotHttpsClientCallbacks_t.readReadyCallback and #IotHttpsClientCallbacks_t.responseCompleteCallback. The application
 * should refer to that instead of using this function.
 * <b> Example Asynchronous Code </b>
 * @code
 * void applicationDefined_readReadyCallback(void * pPrivData, IotHttpsResponseHandle_t respHandle, IotHttpsReturnCode_t rc, uint16_t status)
 * {
 *      ...
 *      if (status != IOT_HTTPS_STATUS_OK)
 *      {
 *          // Handle error server response status.
 *      }
 *      ...
 * }
 * @endcode
 *
 * @param[in] respHandle - Unique handle representing the HTTPS response.
 * @param[out] pStatus - Integer status returned by the server.
 *
 * @return One of the following:
 * - #IOT_HTTPS_OK if the response status was successfully read into *status.
 * - #IOT_HTTPS_INVALID_PARAMETER for NULL parameters.
 * - #IOT_HTTPS_NOT_FOUND if the HTTP response status was not found in the header buffer.
 */
/* @[declare_https_client_readresponsestatus] */
IotHttpsReturnCode_t IotHttpsClient_ReadResponseStatus( IotHttpsResponseHandle_t respHandle,
                                                        uint16_t * pStatus );
/* @[declare_https_client_readresponsestatus] */

/**
 * @brief Retrieve the HTTPS response content length.
 *
 * If the "Content-Length" header is available in #IotHttpsResponseInfo_t.userBuffer, this routine extracts that
 * value. In some cases the "Content-Length" header is not available. This could be because the server sent a multi-part
 * encoded response (For example, "Transfer-Encoding: chunked") or the "Content-Length" header was far down in the list
 * of response headers and could not fit into the header buffer configured in #IotHttpsResponseInfo_t.userBuffer.
 * Please see #responseUserBufferMinimumSize for information about sizing the #IotHttpsResponseInfo_t.userBuffer.
 *
 * In the asynchronous request process, the Content-Length is not available until the
 * #IotHttpsClientCallbacks_t.readReadyCallback. Before the #IotHttpsClientCallbacks_t.readReadyCallback is invoked, the
 * headers are read into as much as can fit in in the header buffer space of #IotHttpsResponseInfo_t.userBuffer.
 * <b> Example Asynchronous Code </b>
 * @code{c}
 * void applicationDefined_readReadyCallback(void * pPrivData, IotHttpsResponseHandle_t respHandle, IotHttpsReturnCode_t rc, uint16_t status)
 * {
 *      uint8_t * readBuffer = NULL;
 *      uint32_t contentLength = 0;
 *      IotHttpsClient_ReadContentLength(respHandle, &contentLength);
 *      readBuffer = (uint8_t*)malloc(contentLength);
 *      ...
 * }
 * @endcode
 *
 * In a synchronous request process, the Content-Length is available after @ref https_client_function_sendsync has
 * returned successfully.
 * <b> Example Synchronous Code </b>
 * @code{c}
 *      ...
 *      IotHttpsClient_SendSync(connHandle, reqHandle, &respHandle, &respInfo, timeout);
 *      uint32_t contentLength = 0;
 *      IotHttpsClient_ReadContentLength(respHandle, &contentLength);
 *      printf("Content-Length: %u", (unsigned int)contentLength);
 *      ...
 * @endcode
 *
 * @param[in] respHandle - Unique handle representing the HTTPS response.
 * @param[out] pContentLength - Integer content length from the Content-Length header from the server. If the content
 *      length is not found this will be 0.
 *
 * @return One of the following:
 * - #IOT_HTTPS_OK if the response body Content-Length was successfully read into contentLength.
 * - #IOT_HTTPS_NOT_FOUND if the Content-Length header was not found in the header buffer.
 * - #IOT_HTTPS_INVALID_PARAMETER if NULL parameters are passed in.
 */
/* @[declare_https_client_readcontentlength] */
IotHttpsReturnCode_t IotHttpsClient_ReadContentLength( IotHttpsResponseHandle_t respHandle,
                                                       uint32_t * pContentLength );
/* @[declare_https_client_readcontentlength] */

/**
 * @brief Retrieve the header of interest from the response represented by respHandle.
 *
 * The response headers as received from the network will be stored in the header buffer space in
 * #IotHttpsResponseInfo_t.userBuffer. If the configured #IotHttpsResponseInfo_t.userBuffer is too small to fit
 * the headers received, then headers that don't fit will be thrown away. Please see #responseUserBufferMinimumSize for
 * information about sizing the #IotHttpsResponseInfo_t.userBuffer.
 *
 * This routine parses the formatted HTTPS header lines in the header buffer for the header field name specified. If the
 * header is not available, then #IOT_HTTPS_NOT_FOUND is returned.
 *
 * For an asynchronous response, this routine is to be called during the #IotHttpsClientCallbacks_t.readReadyCallback.
 * Before the #IotHttpsClientCallbacks_t.readReadyCallback is invoked, the
 * headers are read into as much as can fit in in the header buffer space of #IotHttpsResponseInfo_t.userBuffer.
 * <b> Example Asynchronous Code </b>
 * @code{c}
 * void applicationDefined_readReadyCallback(void * pPrivData, IotHttpsResponseHandle_t respHandle, IotHttpsReturnCode_t rc, uint16_t status)
 * {
 *      ...
 *      char valueBuf[64];
 *      const char contentTypeName[] = "Content-Type";
 *      uint32_t contentTypeNmeLength = strlen(contentTypeName);
 *      IotHttpsClient_ReadHeader(respHandle, contentTypeName, contentTypeNameLength, valueBuf, sizeof(valueBuf));
 *      ...
 * }
 * @endcode
 *
 * For a syncrhonous response, this routine is to be called after @ref https_client_function_sendsync has
 * returned successfully.
 * <b> Example Synchronous Code </b>
 * @code{c}
 *      ...
 *      IotHttpsClient_SendSync(&connHandle, reqHandle, &respHandle, &respInfo, timeout);
 *      char valueBuf[10];
 *      const char contentTypeName[] = "Content-Type";
 *      uint32_t contentTypeNmeLength = strlen(contentTypeName);
 *      IotHttpsClient_ReadHeader(respHandle, contentTypeName, contentTypeNmeLength, valueBuf, sizeof(valueBuf));
 *      uint32_t length = strtoul(valueBuf, NULL, 10);
 *      ...
 * @endcode
 *
 * @param[in] respHandle - Unique handle representing the HTTPS response.
 * @param[in] pName - HTTPS Header field name we want the value of. This must be NULL terminated.
 * @param[in] nameLen - The length of the name string.
 * @param[out] pValue - Buffer to hold the HTTPS field's value. The returned value will be NULL terminated
 *                      and therfore the buffer must be large enough to hold the terminating NULL character.
 * @param[in] valueLen - The length of the value buffer.
 *
 * @return One of the following:
 * - #IOT_HTTPS_OK if the header's corresponding value was read into *pValue.
 * - #IOT_HTTPS_NOT_FOUND if the header value was not found.
 * - #IOT_HTTPS_INVALID_PARAMETER if the respHandle is not valid, there is no response saved or the handle does not exist.
 * - #IOT_HTTPS_INSUFFICIENT_MEMORY if the value is too large to fit into *pValue.
 */
/* @[declare_https_client_readheader] */
IotHttpsReturnCode_t IotHttpsClient_ReadHeader( IotHttpsResponseHandle_t respHandle,
                                                char * pName,
                                                uint32_t nameLen,
                                                char * pValue,
                                                uint32_t valueLen );
/* @[declare_https_client_readheader] */

/**
 * @brief Read the HTTPS response body from the network.
 *
 * This is intended to be used with an asynchronous response, this is to be invoked during the
 * #IotHttpsClientCallbacks_t.readReadyCallback to read data directly from the network into pBuf.
 * <b> Example Asynchronous Code </b>
 * @code{c}
 * void applicationDefined_readReadyCallback(void * pPrivData, IotHttpsRequestHandle_t handle, IotHttpsReturnCode_t rc, uint16_t status)
 * {
 *      ...
 *      char * myBuf = STORE_ADDRESS;
 *      uint32_t len = STORE_READ_SIZE;
 *      IotHttpsClient_ReadResponseBody(handle, myBuf, &len);
 *      ...
 * }
 * @endcode
 *
 * For a syncrhonous response, to retrieve the response body applications must directly refer to the memory configured
 * to receive the response body: #IotHttpsSyncInfo_t.pBody in #IotHttpsResponseInfo_t.pSyncInfo. Otherwise this function
 * will return an #IOT_HTTPS_INVALID_PARAMETER error code. This function is intended to read the response entity body
 * from the network and the synchronous response process handles all of that in @ref https_client_function_sendsync.
 *
 * @param[in] respHandle - Unique handle representing the HTTPS response.
 * @param[out] pBuf - Pointer to the response body memory location. This is not a char* because the body may have binary data.
 * @param[in,out] pLen - The length of the response to read. This should not exceed the size of the buffer that we are reading into. This will be replace with the amount of data read upon return.
 *
 * @return One of the following:
 * - #IOT_HTTPS_OK if the response body was successfully retrieved.
 * - #IOT_HTTPS_INVALID_PARAMETER if there are NULL parameters or if the response is a synchronous type.
 * - #IOT_HTTPS_NETWORK_ERROR if there was an error sending the data on the network.
 * - #IOT_HTTPS_PARSING_ERROR if there was an error parsing the HTTP response.
 */
/* @[declare_https_client_readresponsebody] */
IotHttpsReturnCode_t IotHttpsClient_ReadResponseBody( IotHttpsResponseHandle_t respHandle,
                                                      uint8_t * pBuf,
                                                      uint32_t * pLen );
/* @[declare_https_client_readresponsebody] */

#endif /* IOT_HTTPS_CLIENT_ */
