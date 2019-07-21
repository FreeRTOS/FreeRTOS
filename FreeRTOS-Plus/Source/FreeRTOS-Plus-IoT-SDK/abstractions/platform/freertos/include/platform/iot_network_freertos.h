/*
 * Amazon FreeRTOS Platform V1.0.0
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
 * @file iot_network_freertos.h
 * @brief Declares the network stack functions specified in aws_iot_network.h for
 * Amazon FreeRTOS Secure Sockets.
 */

#ifndef _IOT_NETWORK_AFR_H_
#define _IOT_NETWORK_AFR_H_

/* Standard includes. */
#include <stdbool.h>

/* Platform network include. */
#include "platform/iot_network.h"

/* Amazon FreeRTOS Secure Sockets include. */
#include "iot_secure_sockets.h"

/**
 * @brief Represents a network connection that uses Amazon FreeRTOS Secure Sockets.
 *
 * This is an incomplete type. In application code, only pointers to this type
 * should be used.
 */
typedef struct _networkConnection IotNetworkConnectionAfr_t;

/**
 * @brief Provides a default value for an #IotNetworkConnectionAfr_t.
 *
 * All instances of #IotNetworkConnectionAfr_t should be initialized with
 * this constant.
 *
 * @warning Failing to initialize an #IotNetworkConnectionAfr_t with this
 * initializer may result in undefined behavior!
 * @note This initializer may change at any time in future versions, but its
 * name will remain the same.
 */
#define IOT_NETWORK_CONNECTION_AFR_INITIALIZER     { 0 }

/**
 * @brief Generic initializer for an #IotNetworkServerInfo_t.
 *
 * @note This initializer may change at any time in future versions, but its
 * name will remain the same.
 */
#define IOT_NETWORK_SERVER_INFO_AFR_INITIALIZER    { 0 }

/**
 * @brief Generic initializer for an #IotNetworkCredentials_t.
 *
 * @note This initializer may change at any time in future versions, but its
 * name will remain the same.
 */
#define IOT_NETWORK_CREDENTIALS_AFR_INITIALIZER    { 0 }

/**
 * @brief Provides a pointer to an #IotNetworkInterface_t that uses the functions
 * declared in this file.
 */
#define IOT_NETWORK_INTERFACE_AFR    ( &( IotNetworkAfr ) )

/**
 * @brief An implementation of #IotNetworkInterface_t::create for Amazon FreeRTOS
 * Secure Sockets.
 */
IotNetworkError_t IotNetworkAfr_Create( void * pConnectionInfo,
                                        void * pCredentialInfo,
                                        void ** const pConnection );

/**
 * @brief An implementation of #IotNetworkInterface_t::setReceiveCallback for
 * Amazon FreeRTOS Secure Sockets.
 */
IotNetworkError_t IotNetworkAfr_SetReceiveCallback( void * pConnection,
                                                    IotNetworkReceiveCallback_t receiveCallback,
                                                    void * pContext );

/**
 * @brief An implementation of #IotNetworkInterface_t::send for Amazon FreeRTOS
 * Secure Sockets.
 */
size_t IotNetworkAfr_Send( void * pConnection,
                           const uint8_t * pMessage,
                           size_t messageLength );

/**
 * @brief An implementation of #IotNetworkInterface_t::receive for Amazon FreeRTOS
 * Secure Sockets.
 */
size_t IotNetworkAfr_Receive( void * pConnection,
                              uint8_t * pBuffer,
                              size_t bytesRequested );

/**
 * @brief An implementation of #IotNetworkInterface_t::close for Amazon FreeRTOS
 * Secure Sockets.
 */
IotNetworkError_t IotNetworkAfr_Close( void * pConnection );

/**
 * @brief An implementation of #IotNetworkInterface_t::destroy for Amazon FreeRTOS
 * Secure Sockets.
 */
IotNetworkError_t IotNetworkAfr_Destroy( void * pConnection );

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this section.
 *
 * Declaration of a network interface struct using the functions in this file.
 */
extern const IotNetworkInterface_t IotNetworkAfr;
/** @endcond */

#endif /* ifndef _IOT_NETWORK_AFR_H_ */
