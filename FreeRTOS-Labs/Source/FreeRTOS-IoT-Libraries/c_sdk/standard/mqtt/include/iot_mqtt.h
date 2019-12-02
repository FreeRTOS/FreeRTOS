/*
 * IoT MQTT V2.1.0
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 */

/**
 * @file iot_mqtt.h
 * @brief User-facing functions of the MQTT 3.1.1 library.
 */

#ifndef IOT_MQTT_H_
#define IOT_MQTT_H_

/* The config header is always included first. */
#include "iot_config.h"

/* MQTT types include. */
#include "types/iot_mqtt_types.h"

/*------------------------- MQTT library functions --------------------------*/

/**
 * @functionspage{mqtt,MQTT library}
 * - @functionname{mqtt_function_init}
 * - @functionname{mqtt_function_cleanup}
 * - @functionname{mqtt_function_receivecallback}
 * - @functionname{mqtt_function_connect}
 * - @functionname{mqtt_function_disconnect}
 * - @functionname{mqtt_function_subscribeasync}
 * - @functionname{mqtt_function_subscribesync}
 * - @functionname{mqtt_function_unsubscribeasync}
 * - @functionname{mqtt_function_unsubscribesync}
 * - @functionname{mqtt_function_publishasync}
 * - @functionname{mqtt_function_publishsync}
 * - @functionname{mqtt_function_wait}
 * - @functionname{mqtt_function_strerror}
 * - @functionname{mqtt_function_operationtype}
 * - @functionname{mqtt_function_issubscribed}
 */

/**
 * @functionpage{IotMqtt_Init,mqtt,init}
 * @functionpage{IotMqtt_Cleanup,mqtt,cleanup}
 * @functionpage{IotMqtt_ReceiveCallback,mqtt,receivecallback}
 * @functionpage{IotMqtt_Connect,mqtt,connect}
 * @functionpage{IotMqtt_Disconnect,mqtt,disconnect}
 * @functionpage{IotMqtt_SubscribeAsync,mqtt,subscribeasync}
 * @functionpage{IotMqtt_SubscribeSync,mqtt,subscribesync}
 * @functionpage{IotMqtt_UnsubscribeAsync,mqtt,unsubscribeasync}
 * @functionpage{IotMqtt_UnsubscribeSync,mqtt,unsubscribesync}
 * @functionpage{IotMqtt_PublishAsync,mqtt,publishasync}
 * @functionpage{IotMqtt_PublishSync,mqtt,publishsync}
 * @functionpage{IotMqtt_Wait,mqtt,wait}
 * @functionpage{IotMqtt_strerror,mqtt,strerror}
 * @functionpage{IotMqtt_OperationType,mqtt,operationtype}
 * @functionpage{IotMqtt_IsSubscribed,mqtt,issubscribed}
 */

/**
 * @brief One-time initialization function for the MQTT library.
 *
 * This function performs setup of the MQTT library. <b>It must be called
 * once (and only once) before calling any other MQTT function.</b> Calling this
 * function more than once without first calling @ref mqtt_function_cleanup
 * may result in a crash.
 *
 * @return One of the following:
 * - #IOT_MQTT_SUCCESS
 * - #IOT_MQTT_NOT_INITIALIZED
 *
 * @warning No thread-safety guarantees are provided for this function.
 *
 * @see @ref mqtt_function_cleanup
 */
/* @[declare_mqtt_init] */
IotMqttError_t IotMqtt_Init( void );
/* @[declare_mqtt_init] */

/**
 * @brief One-time deinitialization function for the MQTT library.
 *
 * This function frees resources taken in @ref mqtt_function_init. It should be
 * called after [closing all MQTT connections](@ref mqtt_function_disconnect) to
 * clean up the MQTT library. After this function returns, @ref mqtt_function_init
 * must be called again before calling any other MQTT function.
 *
 * @warning No thread-safety guarantees are provided for this function. Do not
 * call this function if any MQTT connections are open!
 *
 * @see @ref mqtt_function_init
 */
/* @[declare_mqtt_cleanup] */
void IotMqtt_Cleanup( void );
/* @[declare_mqtt_cleanup] */

/**
 * @brief Network receive callback for the MQTT library.
 *
 * This function should be called by the system whenever data is available for
 * the MQTT library.
 *
 * @param[in] pNetworkConnection The network connection associated with the MQTT
 * connection, passed by the network stack.
 * @param[in] pReceiveContext A pointer to the MQTT connection handle for which
 * the packet was received.
 */
/* @[declare_mqtt_receivecallback] */
void IotMqtt_ReceiveCallback( IotNetworkConnection_t pNetworkConnection,
                              void * pReceiveContext );
/* @[declare_mqtt_receivecallback] */

/**
 * @brief Establish a new MQTT connection.
 *
 * This function opens a connection between a new MQTT client and an MQTT server
 * (also called a <i>broker</i>). MQTT connections are established on top of transport
 * layer protocols (such as TCP/IP), and optionally, application layer security
 * protocols (such as TLS). The MQTT packet that establishes a connection is called
 * the MQTT CONNECT packet. After @ref mqtt_function_init, this function must be
 * called before any other MQTT library function.
 *
 * If [pConnectInfo->cleanSession](@ref IotMqttConnectInfo_t.cleanSession) is `true`,
 * this function establishes a clean MQTT session. Subscriptions and unacknowledged
 * PUBLISH messages will be discarded when the connection is closed.
 *
 * If [pConnectInfo->cleanSession](@ref IotMqttConnectInfo_t.cleanSession) is `false`,
 * this function establishes (or re-establishes) a persistent MQTT session. The parameters
 * [pConnectInfo->pPreviousSubscriptions](@ref IotMqttConnectInfo_t.pPreviousSubscriptions)
 * and [pConnectInfo->previousSubscriptionCount](@ref IotMqttConnectInfo_t.previousSubscriptionCount)
 * may be used to restore subscriptions present in a re-established persistent session.
 * Any restored subscriptions <b>MUST</b> have been present in the persistent session;
 * <b>this function does not send an MQTT SUBSCRIBE packet!</b>
 *
 * [pConnectInfo->pPreviousSubscriptions](@ref IotMqttConnectInfo_t.pPreviousSubscriptions)
 * and [pConnectInfo->previousSubscriptionCount](@ref IotMqttConnectInfo_t.previousSubscriptionCount) can
 * also be used to pass a list of subscriptions to be stored locally without a SUBSCRIBE packet being
 * sent to the broker. These subscriptions are useful to invoke application level callbacks for messages received
 * on unsolicited topics from the broker.
 *
 * This MQTT library is network agnostic, meaning it has no knowledge of the
 * underlying network protocol carrying the MQTT packets. It interacts with the
 * network through a network abstraction layer, allowing it to be used with many
 * different network stacks. The network abstraction layer is established
 * per-connection, allowing every #IotMqttConnection_t to use a different network
 * stack. The parameter `pNetworkInterface` sets up the network abstraction layer
 * for an MQTT connection; see the documentation on #IotMqttNetworkInfo_t for details
 * on its members.
 *
 * The `pConnectInfo` parameter provides the contents of the MQTT CONNECT packet.
 * Most members [are defined by the MQTT spec.](@ref IotMqttConnectInfo_t). The
 * [pConnectInfo->pWillInfo](@ref IotMqttConnectInfo_t.pWillInfo) member provides
 * information on a Last Will and Testament (LWT) message to be published if the
 * MQTT connection is closed without [sending a DISCONNECT packet]
 * (@ref mqtt_function_disconnect). Unlike other PUBLISH
 * messages, a LWT message payload is limited to 65535 bytes in length. Additionally,
 * the retry [interval](@ref IotMqttPublishInfo_t.retryMs) and [limit]
 * (@ref IotMqttPublishInfo_t.retryLimit) members of #IotMqttPublishInfo_t
 * are ignored for LWT messages. The LWT message is optional; `pWillInfo` may be NULL.
 *
 * Unlike @ref mqtt_function_publishasync, @ref mqtt_function_subscribeasync, and
 * @ref mqtt_function_unsubscribeasync, this function is always blocking. Additionally,
 * because the MQTT connection acknowledgement packet (CONNACK packet) does not
 * contain any information on <i>which</i> CONNECT packet it acknowledges, only one
 * CONNECT operation may be in progress at any time. This means that parallel
 * threads making calls to @ref mqtt_function_connect will be serialized to send
 * their CONNECT packets one-by-one.
 *
 * @param[in] pNetworkInfo Information on the transport-layer network connection
 * to use with the MQTT connection.
 * @param[in] pConnectInfo MQTT connection setup parameters.
 * @param[in] timeoutMs If the MQTT server does not accept the connection within
 * this timeout in milliseconds, this function returns #IOT_MQTT_TIMEOUT.
 * @param[out] pMqttConnection Set to a newly-initialized MQTT connection handle
 * if this function succeeds.
 *
 * @return One of the following:
 * - #IOT_MQTT_SUCCESS
 * - #IOT_MQTT_NOT_INITIALIZED
 * - #IOT_MQTT_BAD_PARAMETER
 * - #IOT_MQTT_NO_MEMORY
 * - #IOT_MQTT_NETWORK_ERROR
 * - #IOT_MQTT_SCHEDULING_ERROR
 * - #IOT_MQTT_BAD_RESPONSE
 * - #IOT_MQTT_TIMEOUT
 * - #IOT_MQTT_SERVER_REFUSED
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Callback function to receive messages from the broker on an unsolicited topic.
 * void unsolicitedMessageCallback( void * pArgument, IotMqttCallbackParam_t * pPublish );
 *
 * // Parameters to MQTT connect.
 * IotMqttConnection_t mqttConnection = IOT_MQTT_CONNECTION_INITIALIZER;
 * IotMqttNetworkInfo_t networkInfo = IOT_MQTT_NETWORK_INFO_INITIALIZER;
 * IotMqttConnectInfo_t connectInfo = IOT_MQTT_CONNECT_INFO_INITIALIZER;
 * IotMqttPublishInfo_t willInfo = IOT_MQTT_PUBLISH_INFO_INITIALIZER;
 *
 * // A local subscription to receive messages from the broker on an unsolicited topic.
 * IotMqttSubscription_t subscription = IOT_MQTT_SUBSCRIPTION_INITIALIZER;
 *
 * // Example network abstraction types.
 * IotNetworkServerInfo_t serverInfo = { ... };
 * IotNetworkCredentials_t credentialInfo = { ... };
 * IotNetworkInterface_t networkInterface = { ... };
 *
 * // Example using a generic network implementation.
 * networkInfo.createNetworkConnection = true;
 * networkInfo.u.setup.pNetworkServerInfo = &serverInfo;
 * networkInfo.u.setup.pNetworkCredentialInfo = &credentialInfo;
 * networkInfo.pNetworkInterface = &networkInterface;
 *
 * // Set the members of the connection info (password and username not used).
 * connectInfo.cleanSession = true;
 * connectInfo.keepAliveSeconds = 30;
 * connectInfo.pClientIdentifier = "uniqueclientidentifier";
 * connectInfo.clientIdentifierLength = 22;
 *
 * // Set the members of the will info (retain and retry not used).
 * willInfo.qos = IOT_MQTT_QOS_1;
 * willInfo.pTopicName = "will/topic/name";
 * willInfo.topicNameLength = ( uint16_t ) strlen( willInfo.pTopicName );
 * willInfo.pPayload = "MQTT client unexpectedly disconnected.";
 * willInfo.payloadLength = strlen( willInfo.pPayload );
 *
 * // Set the pointer to the will info.
 * connectInfo.pWillInfo = &willInfo;
 *
 * // [Optional] Set a local subscription to receive the broker messages on an unsolicited topic.
 * subscription.qos = IOT_MQTT_QOS_0;
 * subscription.pTopicFilter = "some/unsolicited/topic";
 * subscription.topicLength = ( uint16_t ) strlen( subscription.pTopicFilter );
 * subscription.callback.function = unsolicitedMessageCallback;
 * connectInfo.pPreviousSubscriptions = &subscription;
 * connectInfo.previousSubscriptionCount = 1;
 *
 *
 * // Call CONNECT with a 5 second block time. Should return
 * // IOT_MQTT_SUCCESS when successful.
 * IotMqttError_t result = IotMqtt_Connect( &networkInfo,
 *                                          &connectInfo,
 *                                          5000,
 *                                          &mqttConnection );
 *
 * if( result == IOT_MQTT_SUCCESS )
 * {
 *     // Do something with the MQTT connection...
 *
 *     // Clean up and close the MQTT connection once it's no longer needed.
 *     IotMqtt_Disconnect( mqttConnection, 0 );
 * }
 * @endcode
 */
/* @[declare_mqtt_connect] */
IotMqttError_t IotMqtt_Connect( const IotMqttNetworkInfo_t * pNetworkInfo,
                                const IotMqttConnectInfo_t * pConnectInfo,
                                uint32_t timeoutMs,
                                IotMqttConnection_t * const pMqttConnection );
/* @[declare_mqtt_connect] */

/**
 * @brief Closes an MQTT connection and frees resources.
 *
 * This function closes an MQTT connection and should only be called once
 * the MQTT connection is no longer needed. Its exact behavior depends on the
 * `flags` parameter.
 *
 * Normally, `flags` should be `0`. This gracefully shuts down an MQTT
 * connection by sending an MQTT DISCONNECT packet. Any [network close function]
 * (@ref IotNetworkInterface_t::close) provided [when the connection was established]
 * (@ref mqtt_function_connect) will also be called. Note that because the MQTT server
 * will not acknowledge a DISCONNECT packet, the client has no way of knowing if
 * the server received the DISCONNECT packet. In the case where the DISCONNECT
 * packet is lost in transport, any Last Will and Testament (LWT) message established
 * with the connection may be published. However, if the DISCONNECT reaches the
 * MQTT server, the LWT message will be discarded and not published.
 *
 * Should the underlying network connection become unusable, this function should
 * be called with `flags` set to #IOT_MQTT_FLAG_CLEANUP_ONLY. In this case, no
 * DISCONNECT packet will be sent, though the [network close function](@ref IotNetworkInterface_t::close)
 * will still be called. This function will only free the resources used by the MQTT
 * connection; it still must be called even if the network is offline to avoid leaking
 * resources.
 *
 * @ref mqtt_function_disconnect modifies `mqttConnection`, so it shouldn't
 * be used after calling this function.
 *
 * @param[in] mqttConnection The MQTT connection to close and clean up.
 * @param[in] flags Flags which modify the behavior of this function. See @ref mqtt_constants_flags.
 */
/* @[declare_mqtt_disconnect] */
void IotMqtt_Disconnect( IotMqttConnection_t mqttConnection,
                         uint32_t flags );
/* @[declare_mqtt_disconnect] */

/**
 * @brief Subscribes to the given array of topic filters and optionally
 * receive an asynchronous notification when the subscribe completes.
 *
 * This function sends an MQTT SUBSCRIBE packet to the server. A SUBSCRIBE
 * packet notifies the server to send any matching PUBLISH messages to this client.
 * A single SUBSCRIBE packet may carry more than one topic filter, hence the
 * parameters to this function include an array of [subscriptions]
 * (@ref IotMqttSubscription_t).
 *
 * An MQTT subscription has two pieces:
 * 1. The subscription topic filter registered with the MQTT server. The MQTT
 * SUBSCRIBE packet sent from this client to server notifies the server to send
 * messages matching the given topic filters to this client.
 * 2. The [callback function](@ref IotMqttCallbackInfo_t.function) that this
 * client will invoke when an incoming message is received. The callback function
 * notifies applications of an incoming PUBLISH message.
 *
 * The helper function @ref mqtt_function_issubscribed can be used to check if a
 * [callback function](@ref IotMqttCallbackInfo_t.function) is registered for
 * a particular topic filter.
 *
 * To modify an already-registered subscription callback, call this function with
 * a new `pSubscriptionList`. Any topic filters in `pSubscriptionList` that already
 * have a registered callback will be replaced with the new values in `pSubscriptionList`.
 *
 * @attention QoS 2 subscriptions are currently unsupported. Only 0 or 1 are valid
 * for subscription QoS.
 *
 * @param[in] mqttConnection The MQTT connection to use for the subscription.
 * @param[in] pSubscriptionList Pointer to the first element in the array of
 * subscriptions.
 * @param[in] subscriptionCount The number of elements in pSubscriptionList.
 * @param[in] flags Flags which modify the behavior of this function. See @ref mqtt_constants_flags.
 * @param[in] pCallbackInfo Asynchronous notification of this function's completion (`NULL` to disable).
 * @param[out] pSubscribeOperation Set to a handle by which this operation may be
 * referenced after this function returns. This reference is invalidated once
 * the subscription operation completes.
 *
 * @return This function will return #IOT_MQTT_STATUS_PENDING upon success.
 * @return Upon completion of the subscription (either through an
 * #IotMqttCallbackInfo_t or @ref mqtt_function_wait), the status will be one of:
 * - #IOT_MQTT_SUCCESS
 * - #IOT_MQTT_NETWORK_ERROR
 * - #IOT_MQTT_SCHEDULING_ERROR
 * - #IOT_MQTT_BAD_RESPONSE
 * - #IOT_MQTT_SERVER_REFUSED
 * @return If this function fails before queuing a subscribe operation, it will return
 * one of:
 * - #IOT_MQTT_NOT_INITIALIZED
 * - #IOT_MQTT_BAD_PARAMETER
 * - #IOT_MQTT_NO_MEMORY
 *
 * @see @ref mqtt_function_subscribesync for a blocking variant of this function.
 * @see @ref mqtt_function_unsubscribeasync for the function that removes subscriptions.
 *
 * <b>Example</b>
 * @code{c}
 * #define NUMBER_OF_SUBSCRIPTIONS ...
 *
 * // Subscription callback function.
 * void subscriptionCallback( void * pArgument, IotMqttCallbackParam_t * pPublish );
 *
 * // An initialized and connected MQTT connection.
 * IotMqttConnection_t mqttConnection;
 *
 * // Subscription information.
 * pSubscriptions[ NUMBER_OF_SUBSCRIPTIONS ] = { IOT_MQTT_SUBSCRIPTION_INITIALIZER };
 * IotMqttOperation_t lastOperation = IOT_MQTT_OPERATION_INITIALIZER;
 *
 * // Set the subscription information.
 * for( int i = 0; i < NUMBER_OF_SUBSCRIPTIONS; i++ )
 * {
 *     pSubscriptions[ i ].qos = IOT_MQTT_QOS_1;
 *     pSubscriptions[ i ].pTopicFilter = "some/topic/filter";
 *     pSubscriptions[ i ].topicLength = ( uint16_t ) strlen( pSubscriptions[ i ].pTopicFilter );
 *     pSubscriptions[ i ].callback.function = subscriptionCallback;
 * }
 *
 * IotMqttError_t result = IotMqtt_SubscribeAsync( mqttConnection,
 *                                                 pSubscriptions,
 *                                                 NUMBER_OF_SUBSCRIPTIONS,
 *                                                 IOT_MQTT_FLAG_WAITABLE,
 *                                                 NULL,
 *                                                 &lastOperation );
 *
 * // Subscribe returns IOT_MQTT_STATUS_PENDING when successful. Wait up to
 * // 5 seconds for the operation to complete.
 * if( result == IOT_MQTT_STATUS_PENDING )
 * {
 *     result = IotMqtt_Wait( subscriptionRef, 5000 );
 * }
 *
 * // Check that the subscriptions were successful.
 * if( result == IOT_MQTT_SUCCESS )
 * {
 *     // Wait for messages on the subscription topic filters...
 *
 *     // Unsubscribe once the subscriptions are no longer needed.
 *     result = IotMqtt_UnsubscribeAsync( mqttConnection,
 *                                        pSubscriptions,
 *                                        NUMBER_OF_SUBSCRIPTIONS,
 *                                        IOT_MQTT_FLAG_WAITABLE,
 *                                        NULL,
 *                                        &lastOperation );
 *
 *     // UNSUBSCRIBE returns IOT_MQTT_STATUS_PENDING when successful.
 *     // Wait up to 5 seconds for the operation to complete.
 *     if( result == IOT_MQTT_STATUS_PENDING )
 *     {
 *         result = IotMqtt_Wait( lastOperation, 5000 );
 *     }
 * }
 * // Check which subscriptions were rejected by the server.
 * else if( result == IOT_MQTT_SERVER_REFUSED )
 * {
 *     for( int i = 0; i < NUMBER_OF_SUBSCRIPTIONS; i++ )
 *     {
 *         if( IotMqtt_IsSubscribed( mqttConnection,
 *                                   pSubscriptions[ i ].pTopicFilter,
 *                                   pSubscriptions[ i ].topicFilterLength,
 *                                   NULL ) == false )
 *         {
 *             // This subscription was rejected.
 *         }
 *     }
 * }
 * @endcode
 */
/* @[declare_mqtt_subscribeasync] */
IotMqttError_t IotMqtt_SubscribeAsync( IotMqttConnection_t mqttConnection,
                                       const IotMqttSubscription_t * pSubscriptionList,
                                       size_t subscriptionCount,
                                       uint32_t flags,
                                       const IotMqttCallbackInfo_t * pCallbackInfo,
                                       IotMqttOperation_t * const pSubscribeOperation );
/* @[declare_mqtt_subscribeasync] */

/**
 * @brief Subscribes to the given array of topic filters with a timeout.
 *
 * This function sends an MQTT SUBSCRIBE packet to the server, then waits for
 * a server response to the packet. Internally, this function is a call to @ref
 * mqtt_function_subscribeasync followed by @ref mqtt_function_wait. See @ref
 * mqtt_function_subscribeasync for more information about the MQTT SUBSCRIBE operation.
 *
 * @attention QoS 2 subscriptions are currently unsupported. Only 0 or 1 are valid
 * for subscription QoS.
 *
 * @param[in] mqttConnection The MQTT connection to use for the subscription.
 * @param[in] pSubscriptionList Pointer to the first element in the array of
 * subscriptions.
 * @param[in] subscriptionCount The number of elements in pSubscriptionList.
 * @param[in] flags Flags which modify the behavior of this function. See @ref mqtt_constants_flags.
 * Currently, flags are ignored by this function; this parameter is for
 * future-compatibility.
 * @param[in] timeoutMs If the MQTT server does not acknowledge the subscriptions within
 * this timeout in milliseconds, this function returns #IOT_MQTT_TIMEOUT.
 *
 * @return One of the following:
 * - #IOT_MQTT_SUCCESS
 * - #IOT_MQTT_NOT_INITIALIZED
 * - #IOT_MQTT_BAD_PARAMETER
 * - #IOT_MQTT_NO_MEMORY
 * - #IOT_MQTT_NETWORK_ERROR
 * - #IOT_MQTT_SCHEDULING_ERROR
 * - #IOT_MQTT_BAD_RESPONSE
 * - #IOT_MQTT_TIMEOUT
 * - #IOT_MQTT_SERVER_REFUSED
 */
/* @[declare_mqtt_subscribesync] */
IotMqttError_t IotMqtt_SubscribeSync( IotMqttConnection_t mqttConnection,
                                      const IotMqttSubscription_t * pSubscriptionList,
                                      size_t subscriptionCount,
                                      uint32_t flags,
                                      uint32_t timeoutMs );
/* @[declare_mqtt_subscribesync] */

/**
 * @brief Unsubscribes from the given array of topic filters and optionally
 * receive an asynchronous notification when the unsubscribe completes.
 *
 * This function sends an MQTT UNSUBSCRIBE packet to the server. An UNSUBSCRIBE
 * packet removes registered topic filters from the server. After unsubscribing,
 * the server will no longer send messages on these topic filters to the client.
 *
 * Corresponding [subscription callback functions](@ref IotMqttCallbackInfo_t.function)
 * are also removed from the MQTT connection. These subscription callback functions
 * will be removed even if the MQTT UNSUBSCRIBE packet fails to send.
 *
 * @param[in] mqttConnection The MQTT connection used for the subscription.
 * @param[in] pSubscriptionList Pointer to the first element in the array of
 * subscriptions.
 * @param[in] subscriptionCount The number of elements in pSubscriptionList.
 * @param[in] flags Flags which modify the behavior of this function. See @ref mqtt_constants_flags.
 * @param[in] pCallbackInfo Asynchronous notification of this function's completion (`NULL` to disable).
 * @param[out] pUnsubscribeOperation Set to a handle by which this operation may be
 * referenced after this function returns. This reference is invalidated once
 * the unsubscribe operation completes.
 *
 * @return This function will return #IOT_MQTT_STATUS_PENDING upon success.
 * @return Upon completion of the unsubscribe (either through an
 * #IotMqttCallbackInfo_t or @ref mqtt_function_wait), the status will be one of:
 * - #IOT_MQTT_SUCCESS
 * - #IOT_MQTT_NETWORK_ERROR
 * - #IOT_MQTT_SCHEDULING_ERROR
 * - #IOT_MQTT_BAD_RESPONSE
 * @return If this function fails before queuing an unsubscribe operation, it will return
 * one of:
 * - #IOT_MQTT_NOT_INITIALIZED
 * - #IOT_MQTT_BAD_PARAMETER
 * - #IOT_MQTT_NO_MEMORY
 *
 * @see @ref mqtt_function_unsubscribesync for a blocking variant of this function.
 * @see @ref mqtt_function_subscribeasync for the function that adds subscriptions.
 */
/* @[declare_mqtt_unsubscribeasync] */
IotMqttError_t IotMqtt_UnsubscribeAsync( IotMqttConnection_t mqttConnection,
                                         const IotMqttSubscription_t * pSubscriptionList,
                                         size_t subscriptionCount,
                                         uint32_t flags,
                                         const IotMqttCallbackInfo_t * pCallbackInfo,
                                         IotMqttOperation_t * const pUnsubscribeOperation );
/* @[declare_mqtt_unsubscribeasync] */

/**
 * @brief Unsubscribes from a given array of topic filters with a timeout.
 *
 * This function sends an MQTT UNSUBSCRIBE packet to the server, then waits
 * for a server response to the packet. Internally, this function is a call to
 * @ref mqtt_function_unsubscribeasync followed by @ref mqtt_function_wait. See @ref
 * mqtt_function_unsubscribeasync for more information about the MQTT UNSUBSCRIBE
 * operation.
 *
 * @param[in] mqttConnection The MQTT connection used for the subscription.
 * @param[in] pSubscriptionList Pointer to the first element in the array of
 * subscriptions.
 * @param[in] subscriptionCount The number of elements in pSubscriptionList.
 * @param[in] flags Flags which modify the behavior of this function. See @ref mqtt_constants_flags.
 * Flags are currently ignored but reserved for future use.
 * @param[in] timeoutMs If the MQTT server does not acknowledge the UNSUBSCRIBE within
 * this timeout in milliseconds, this function returns #IOT_MQTT_TIMEOUT.
 *
 * @return One of the following:
 * - #IOT_MQTT_SUCCESS
 * - #IOT_MQTT_NOT_INITIALIZED
 * - #IOT_MQTT_BAD_PARAMETER
 * - #IOT_MQTT_NO_MEMORY
 * - #IOT_MQTT_NETWORK_ERROR
 * - #IOT_MQTT_SCHEDULING_ERROR
 * - #IOT_MQTT_BAD_RESPONSE
 */
/* @[declare_mqtt_unsubscribesync] */
IotMqttError_t IotMqtt_UnsubscribeSync( IotMqttConnection_t mqttConnection,
                                        const IotMqttSubscription_t * pSubscriptionList,
                                        size_t subscriptionCount,
                                        uint32_t flags,
                                        uint32_t timeoutMs );
/* @[declare_mqtt_unsubscribesync] */

/**
 * @brief Publishes a message to the given topic name and optionally
 * receive an asynchronous notification when the publish completes.
 *
 * This function sends an MQTT PUBLISH packet to the server. A PUBLISH packet
 * contains a payload and a topic name. Any clients with a subscription on a
 * topic filter matching the PUBLISH topic name will receive a copy of the
 * PUBLISH packet from the server.
 *
 * If a PUBLISH packet fails to reach the server and it is not a QoS 0 message,
 * it will be retransmitted. See #IotMqttPublishInfo_t for a description
 * of the retransmission strategy.
 *
 * @attention QoS 2 messages are currently unsupported. Only 0 or 1 are valid
 * for message QoS.
 *
 * @param[in] mqttConnection The MQTT connection to use for the publish.
 * @param[in] pPublishInfo MQTT publish parameters.
 * @param[in] flags Flags which modify the behavior of this function. See @ref mqtt_constants_flags.
 * @param[in] pCallbackInfo Asynchronous notification of this function's completion (`NULL` to disable).
 * @param[out] pPublishOperation Set to a handle by which this operation may be
 * referenced after this function returns. This reference is invalidated once
 * the publish operation completes.
 *
 * @return This function will return #IOT_MQTT_STATUS_PENDING upon success for
 * QoS 1 publishes. For a QoS 0 publish it returns #IOT_MQTT_SUCCESS upon
 * success.
 * @return Upon completion of a QoS 1 publish (either through an
 * #IotMqttCallbackInfo_t or @ref mqtt_function_wait), the status will be one of:
 * - #IOT_MQTT_SUCCESS
 * - #IOT_MQTT_NETWORK_ERROR
 * - #IOT_MQTT_SCHEDULING_ERROR
 * - #IOT_MQTT_BAD_RESPONSE
 * - #IOT_MQTT_RETRY_NO_RESPONSE (if [pPublishInfo->retryMs](@ref IotMqttPublishInfo_t.retryMs)
 * and [pPublishInfo->retryLimit](@ref IotMqttPublishInfo_t.retryLimit) were set).
 * @return If this function fails before queuing an publish operation (regardless
 * of QoS), it will return one of:
 * - #IOT_MQTT_NOT_INITIALIZED
 * - #IOT_MQTT_BAD_PARAMETER
 * - #IOT_MQTT_NO_MEMORY
 *
 * @note The parameters `pCallbackInfo` and `pPublishOperation` should only be used for QoS
 * 1 publishes. For QoS 0, they should both be `NULL`.
 *
 * @see @ref mqtt_function_publishsync for a blocking variant of this function.
 *
 * <b>Example</b>
 * @code{c}
 * // An initialized and connected MQTT connection.
 * IotMqttConnection_t mqttConnection;
 *
 * // Publish information.
 * IotMqttPublishInfo_t publishInfo = IOT_MQTT_PUBLISH_INFO_INITIALIZER;
 *
 * // Set the publish information. QoS 0 example (retain not used):
 * publishInfo.qos = IOT_MQTT_QOS_0;
 * publishInfo.pTopicName = "some/topic/name";
 * publishInfo.topicNameLength = ( uint16_t ) strlen( publishInfo.pTopicName );
 * publishInfo.pPayload = "payload";
 * publishInfo.payloadLength = strlen( publishInfo.pPayload );
 *
 * // QoS 0 publish should return IOT_MQTT_SUCCESS upon success.
 * IotMqttError_t qos0Result = IotMqtt_PublishAsync( mqttConnection,
 *                                                   &publishInfo,
 *                                                   0,
 *                                                   NULL,
 *                                                   NULL );
 *
 * // QoS 1 with retry example (using same topic name and payload as QoS 0 example):
 * IotMqttOperation_t qos1Operation = IOT_MQTT_OPERATION_INITIALIZER;
 * publishInfo.qos = IOT_MQTT_QOS_1;
 * publishInfo.retryMs = 1000; // Retry if no response is received in 1 second.
 * publishInfo.retryLimit = 5; // Retry up to 5 times.
 *
 * // QoS 1 publish should return IOT_MQTT_STATUS_PENDING upon success.
 * IotMqttError_t qos1Result = IotMqtt_PublishAsync( mqttConnection,
 *                                                   &publishInfo,
 *                                                   IOT_MQTT_FLAG_WAITABLE,
 *                                                   NULL,
 *                                                   &qos1Operation );
 *
 * // Wait up to 5 seconds for the publish to complete.
 * if( qos1Result == IOT_MQTT_STATUS_PENDING )
 * {
 *     qos1Result = IotMqtt_Wait( qos1Operation, 5000 );
 * }
 * @endcode
 */
/* @[declare_mqtt_publishasync] */
IotMqttError_t IotMqtt_PublishAsync( IotMqttConnection_t mqttConnection,
                                     const IotMqttPublishInfo_t * pPublishInfo,
                                     uint32_t flags,
                                     const IotMqttCallbackInfo_t * pCallbackInfo,
                                     IotMqttOperation_t * const pPublishOperation );
/* @[declare_mqtt_publishasync] */

/**
 * @brief Publish a message to the given topic name with a timeout.
 *
 * This function sends an MQTT PUBLISH packet to the server, then waits for
 * a server response to the packet. Internally, this function is a call to @ref
 * mqtt_function_publishasync followed by @ref mqtt_function_wait. See @ref
 * mqtt_function_publishasync for more information about the MQTT PUBLISH operation.
 *
 * @attention QoS 2 messages are currently unsupported. Only 0 or 1 are valid
 * for message QoS.
 *
 * @param[in] mqttConnection The MQTT connection to use for the publish.
 * @param[in] pPublishInfo MQTT publish parameters.
 * @param[in] flags Flags which modify the behavior of this function. See @ref mqtt_constants_flags.
 * Currently, flags are ignored by this function; this parameter is for
 * future-compatibility.
 * @param[in] timeoutMs If the MQTT server does not acknowledge a QoS 1 PUBLISH
 * within this timeout in milliseconds, this function returns #IOT_MQTT_TIMEOUT.
 * This parameter is ignored for QoS 0 PUBLISH messages.
 *
 * @return One of the following:
 * - #IOT_MQTT_SUCCESS
 * - #IOT_MQTT_NOT_INITIALIZED
 * - #IOT_MQTT_BAD_PARAMETER
 * - #IOT_MQTT_NO_MEMORY
 * - #IOT_MQTT_NETWORK_ERROR
 * - #IOT_MQTT_SCHEDULING_ERROR
 * - #IOT_MQTT_BAD_RESPONSE
 * - #IOT_MQTT_RETRY_NO_RESPONSE (if [pPublishInfo->retryMs](@ref IotMqttPublishInfo_t.retryMs)
 * and [pPublishInfo->retryLimit](@ref IotMqttPublishInfo_t.retryLimit) were set).
 */
/* @[declare_mqtt_publishsync] */
IotMqttError_t IotMqtt_PublishSync( IotMqttConnection_t mqttConnection,
                                    const IotMqttPublishInfo_t * pPublishInfo,
                                    uint32_t flags,
                                    uint32_t timeoutMs );
/* @[declare_mqtt_publishsync] */

/**
 * @brief Waits for an operation to complete.
 *
 * This function blocks to wait for a [subscribe](@ref mqtt_function_subscribeasync),
 * [unsubscribe](@ref mqtt_function_unsubscribeasync), or [publish]
 * (@ref mqtt_function_publishasync) to complete. These operations are by default
 * asynchronous; the function calls queue an operation for processing, and a
 * callback is invoked once the operation is complete.
 *
 * To use this function, the flag #IOT_MQTT_FLAG_WAITABLE must have been
 * set in the operation's function call. Additionally, this function must always
 * be called with any waitable operation to clean up resources.
 *
 * Regardless of its return value, this function always clean up resources used
 * by the waitable operation. This means `reference` is invalidated as soon as
 * this function returns, even if it returns #IOT_MQTT_TIMEOUT or another error.
 *
 * @param[in] operation Reference to the operation to wait for. The flag
 * #IOT_MQTT_FLAG_WAITABLE must have been set for this operation.
 * @param[in] timeoutMs How many milliseconds to wait before returning
 * #IOT_MQTT_TIMEOUT.
 *
 * @return The return value of this function depends on the MQTT operation associated
 * with `reference`. See #IotMqttError_t for possible return values.
 *
 * <b>Example</b>
 * @code{c}
 * // Operation reference and timeout.
 * IotMqttOperation_t publishOperation = IOT_MQTT_OPERATION_INITIALIZER;
 * uint32_t timeoutMs = 5000; // 5 seconds
 *
 * // MQTT operation to wait for.
 * IotMqttError_t result = IotMqtt_PublishAsync( mqttConnection,
 *                                               &publishInfo,
 *                                               IOT_MQTT_FLAG_WAITABLE,
 *                                               NULL,
 *                                               &publishOperation );
 *
 * // Publish should have returned IOT_MQTT_STATUS_PENDING. The call to wait
 * // returns once the result of the publish is available or the timeout expires.
 * if( result == IOT_MQTT_STATUS_PENDING )
 * {
 *     result = IotMqtt_Wait( publishOperation, timeoutMs );
 *
 *     // After the call to wait, the result of the publish is known
 *     // (not IOT_MQTT_STATUS_PENDING).
 *     assert( result != IOT_MQTT_STATUS_PENDING );
 * }
 * @endcode
 */
/* @[declare_mqtt_wait] */
IotMqttError_t IotMqtt_Wait( IotMqttOperation_t operation,
                             uint32_t timeoutMs );
/* @[declare_mqtt_wait] */

/*-------------------------- MQTT helper functions --------------------------*/

/**
 * @brief Returns a string that describes an #IotMqttError_t.
 *
 * Like the POSIX `strerror`, this function returns a string describing a
 * return code. In this case, the return code is an MQTT library error code,
 * `status`.
 *
 * The string returned by this function <b>MUST</b> be treated as read-only: any
 * attempt to modify its contents may result in a crash. Therefore, this function
 * is limited to usage in logging.
 *
 * @param[in] status The status to describe.
 *
 * @return A read-only string that describes `status`.
 *
 * @warning The string returned by this function must never be modified.
 */
/* @[declare_mqtt_strerror] */
const char * IotMqtt_strerror( IotMqttError_t status );
/* @[declare_mqtt_strerror] */

/**
 * @brief Returns a string that describes an #IotMqttOperationType_t.
 *
 * This function returns a string describing an MQTT operation type, `operation`.
 *
 * The string returned by this function <b>MUST</b> be treated as read-only: any
 * attempt to modify its contents may result in a crash. Therefore, this function
 * is limited to usage in logging.
 *
 * @param[in] operation The operation to describe.
 *
 * @return A read-only string that describes `operation`.
 *
 * @warning The string returned by this function must never be modified.
 */
/* @[declare_mqtt_operationtype] */
const char * IotMqtt_OperationType( IotMqttOperationType_t operation );
/* @[declare_mqtt_operationtype] */

/**
 * @brief Check if an MQTT connection has a subscription for a topic filter.
 *
 * This function checks whether an MQTT connection `mqttConnection` has a
 * subscription callback registered for a topic filter `pTopicFilter`. If a
 * subscription callback is found, its details are copied into the output parameter
 * `pCurrentSubscription`. This subscription callback will be invoked for incoming
 * PUBLISH messages on `pTopicFilter`.
 *
 * <b>The check for a matching subscription is only performed client-side</b>;
 * therefore, this function should not be relied upon for perfect accuracy. For
 * example, this function may return an incorrect result if the MQTT server
 * crashes and drops subscriptions without informing the client.
 *
 * Note that an MQTT connection's subscriptions might change between the time this
 * function checks the subscription list and its caller tests the return value.
 * This function certainly should not be used concurrently with any pending SUBSCRIBE
 * or UNSUBSCRIBE operations.
 *
 * One suitable use of this function is to check <i>which</i> subscriptions were rejected
 * if @ref mqtt_function_subscribeasync returns #IOT_MQTT_SERVER_REFUSED; that return
 * code only means that <i>at least one</i> subscription was rejected.
 *
 * @param[in] mqttConnection The MQTT connection to check.
 * @param[in] pTopicFilter The topic filter to check.
 * @param[in] topicFilterLength Length of `pTopicFilter`.
 * @param[out] pCurrentSubscription If a subscription is found, its details are
 * copied here. This output parameter is only valid if this function returns `true` (`NULL` to disable).
 *
 * @return `true` if a subscription was found; `false` otherwise.
 *
 * @note The subscription QoS is not stored by the MQTT library; therefore,
 * `pCurrentSubscription->qos` will always be set to #IOT_MQTT_QOS_0.
 */
/* @[declare_mqtt_issubscribed] */
bool IotMqtt_IsSubscribed( IotMqttConnection_t mqttConnection,
                           const char * pTopicFilter,
                           uint16_t topicFilterLength,
                           IotMqttSubscription_t * const pCurrentSubscription );
/* @[declare_mqtt_issubscribed] */

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this section.
 *
 * Backwards compatibility macros for previous function names.
 */
#define IotMqtt_Subscribe           IotMqtt_SubscribeAsync
#define IotMqtt_TimedSubscribe      IotMqtt_SubscribeSync
#define IotMqtt_Unsubscribe         IotMqtt_UnsubscribeAsync
#define IotMqtt_TimedUnsubscribe    IotMqtt_UnsubscribeSync
#define IotMqtt_Publish             IotMqtt_PublishAsync
#define IotMqtt_TimedPublish        IotMqtt_PublishSync
/** @endcond */

#endif /* ifndef IOT_MQTT_H_ */
