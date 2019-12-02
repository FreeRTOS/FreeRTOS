/*
 * IoT MQTT V2.1.0
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
 */

/**
 * @file iot_mqtt_types.h
 * @brief MQTT library types.
 */

#ifndef IOT_MQTT_TYPES_H_
#define IOT_MQTT_TYPES_H_

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>

/* Type includes. */
#include "types/iot_platform_types.h"
#include "types/iot_taskpool_types_freertos.h"

/* Platform network include. */
#include "platform/iot_network.h"

/*---------------------------- MQTT handle types ----------------------------*/

/**
 * @handles{mqtt,MQTT library}
 */

/**
 * @ingroup mqtt_datatypes_handles
 * @brief Opaque handle of an MQTT connection.
 *
 * MQTT connection handle type.  MQTT connection handles are created by
 * successful calls to @ref mqtt_function_connect and are used to refer to
 * the connection when calling MQTT library functions.
 *
 * A call to @ref mqtt_function_disconnect makes a connection handle invalid. Once
 * @ref mqtt_function_disconnect returns, the connection handle should no longer
 * be used.
 *
 * @initializer{IotMqttConnection_t,IOT_MQTT_CONNECTION_INITIALIZER}
 */
typedef struct _mqttConnection   * IotMqttConnection_t;

/**
 * @ingroup mqtt_datatypes_handles
 * @brief Opaque handle that references an in-progress MQTT operation.
 *
 * Set as an output parameter of @ref mqtt_function_publishasync, @ref mqtt_function_subscribeasync,
 * and @ref mqtt_function_unsubscribeasync. These functions queue an MQTT operation; the result
 * of the operation is unknown until a response from the MQTT server is received. Therefore,
 * this handle serves as a reference to MQTT operations awaiting MQTT server response.
 *
 * This reference will be valid from the successful return of @ref mqtt_function_publishasync,
 * @ref mqtt_function_subscribeasync, or @ref mqtt_function_unsubscribeasync. The reference becomes
 * invalid once the [completion callback](@ref IotMqttCallbackInfo_t) is invoked, or
 * @ref mqtt_function_wait returns.
 *
 * @initializer{IotMqttOperation_t,IOT_MQTT_OPERATION_INITIALIZER}
 *
 * @see @ref mqtt_function_wait and #IOT_MQTT_FLAG_WAITABLE for waiting on a reference.
 * #IotMqttCallbackInfo_t and #IotMqttCallbackParam_t for an asynchronous notification
 * of completion.
 */
typedef struct _mqttOperation    * IotMqttOperation_t;

/*-------------------------- MQTT enumerated types --------------------------*/

/**
 * @enums{mqtt,MQTT library}
 */

/**
 * @ingroup mqtt_datatypes_enums
 * @brief Return codes of [MQTT functions](@ref mqtt_functions).
 *
 * The function @ref mqtt_function_strerror can be used to get a return code's
 * description.
 */
typedef enum IotMqttError
{
    /**
     * @brief MQTT operation completed successfully.
     *
     * Functions that may return this value:
     * - @ref mqtt_function_connect
     * - @ref mqtt_function_publishasync with QoS 0 parameter
     * - @ref mqtt_function_wait
     * - @ref mqtt_function_subscribesync
     * - @ref mqtt_function_unsubscribesync
     * - @ref mqtt_function_publishsync
     *
     * Will also be the value of an operation completion callback's
     * #IotMqttCallbackParam_t.result when successful.
     */
    IOT_MQTT_SUCCESS = 0,

    /**
     * @brief MQTT operation queued, awaiting result.
     *
     * Functions that may return this value:
     * - @ref mqtt_function_subscribeasync
     * - @ref mqtt_function_unsubscribeasync
     * - @ref mqtt_function_publishasync with QoS 1 parameter
     */
    IOT_MQTT_STATUS_PENDING = 1,

    /**
     * @brief Initialization failed.
     *
     * Functions that may return this value:
     * - @ref mqtt_function_init
     */
    IOT_MQTT_INIT_FAILED = 2,

    /**
     * @brief At least one parameter is invalid.
     *
     * Functions that may return this value:
     * - @ref mqtt_function_connect
     * - @ref mqtt_function_subscribeasync and @ref mqtt_function_subscribesync
     * - @ref mqtt_function_unsubscribeasync and @ref mqtt_function_unsubscribesync
     * - @ref mqtt_function_publishasync and @ref mqtt_function_publishsync
     * - @ref mqtt_function_wait
     */
    IOT_MQTT_BAD_PARAMETER = 3,

    /**
     * @brief MQTT operation failed because of memory allocation failure.
     *
     * Functions that may return this value:
     * - @ref mqtt_function_connect
     * - @ref mqtt_function_subscribeasync and @ref mqtt_function_subscribesync
     * - @ref mqtt_function_unsubscribeasync and @ref mqtt_function_unsubscribesync
     * - @ref mqtt_function_publishasync and @ref mqtt_function_publishsync
     */
    IOT_MQTT_NO_MEMORY = 4,

    /**
     * @brief MQTT operation failed because the network was unusable.
     *
     * This return value may indicate that the network is disconnected.
     *
     * Functions that may return this value:
     * - @ref mqtt_function_connect
     * - @ref mqtt_function_wait
     * - @ref mqtt_function_subscribesync
     * - @ref mqtt_function_unsubscribesync
     * - @ref mqtt_function_publishsync
     *
     * May also be the value of an operation completion callback's
     * #IotMqttCallbackParam_t.result.
     */
    IOT_MQTT_NETWORK_ERROR = 5,

    /**
     * @brief MQTT operation could not be scheduled, i.e. enqueued for sending.
     *
     * Functions that may return this value:
     * - @ref mqtt_function_connect
     * - @ref mqtt_function_subscribeasync and @ref mqtt_function_subscribesync
     * - @ref mqtt_function_unsubscribeasync and @ref mqtt_function_unsubscribesync
     * - @ref mqtt_function_publishasync and @ref mqtt_function_publishsync
     */
    IOT_MQTT_SCHEDULING_ERROR = 6,

    /**
     * @brief MQTT response packet received from the network is malformed.
     *
     * Functions that may return this value:
     * - @ref mqtt_function_connect
     * - @ref mqtt_function_wait
     * - @ref mqtt_function_subscribesync
     * - @ref mqtt_function_unsubscribesync
     * - @ref mqtt_function_publishsync
     *
     * May also be the value of an operation completion callback's
     * #IotMqttCallbackParam_t.result.
     *
     * @note If this value is received, the network connection has been closed.
     */
    IOT_MQTT_BAD_RESPONSE = 7,

    /**
     * @brief A blocking MQTT operation timed out.
     *
     * Functions that may return this value:
     * - @ref mqtt_function_connect
     * - @ref mqtt_function_wait
     * - @ref mqtt_function_subscribesync
     * - @ref mqtt_function_unsubscribesync
     * - @ref mqtt_function_publishsync
     */
    IOT_MQTT_TIMEOUT = 8,

    /**
     * @brief A CONNECT or at least one subscription was refused by the server.
     *
     * Functions that may return this value:
     * - @ref mqtt_function_connect
     * - @ref mqtt_function_wait, but only when its #IotMqttOperation_t parameter
     * is associated with a SUBSCRIBE operation.
     * - @ref mqtt_function_subscribesync
     *
     * May also be the value of an operation completion callback's
     * #IotMqttCallbackParam_t.result for a SUBSCRIBE.
     *
     * @note If this value is returned and multiple subscriptions were passed to
     * @ref mqtt_function_subscribeasync (or @ref mqtt_function_subscribesync), it's
     * still possible that some of the subscriptions succeeded. This value only
     * signifies that AT LEAST ONE subscription was rejected. The function @ref
     * mqtt_function_issubscribed can be used to determine which subscriptions
     * were accepted or rejected.
     */
    IOT_MQTT_SERVER_REFUSED = 9,

    /**
     * @brief A QoS 1 PUBLISH received no response and [the retry limit]
     * (#IotMqttPublishInfo_t.retryLimit) was reached.
     *
     * Functions that may return this value:
     * - @ref mqtt_function_wait, but only when its #IotMqttOperation_t parameter
     * is associated with a QoS 1 PUBLISH operation
     * - @ref mqtt_function_publishsync
     *
     * May also be the value of an operation completion callback's
     * #IotMqttCallbackParam_t.result for a QoS 1 PUBLISH.
     */
    IOT_MQTT_RETRY_NO_RESPONSE = 10,

    /**
     * @brief An API function was called before @ref mqtt_function_init.
     *
     * Functions that may return this value:
     * - @ref mqtt_function_connect
     * - @ref mqtt_function_subscribeasync
     * - @ref mqtt_function_subscribesync
     * - @ref mqtt_function_unsubscribeasync
     * - @ref mqtt_function_unsubscribesync
     * - @ref mqtt_function_publishasync
     * - @ref mqtt_function_publishsync
     * - @ref mqtt_function_wait
     */
    IOT_MQTT_NOT_INITIALIZED = 11
} IotMqttError_t;

/**
 * @ingroup mqtt_datatypes_enums
 * @brief Types of MQTT operations.
 *
 * The function @ref mqtt_function_operationtype can be used to get an operation
 * type's description.
 */
typedef enum IotMqttOperationType
{
    IOT_MQTT_CONNECT,           /**< Client-to-server CONNECT. */
    IOT_MQTT_PUBLISH_TO_SERVER, /**< Client-to-server PUBLISH. */
    IOT_MQTT_PUBACK,            /**< Client-to-server PUBACK. */
    IOT_MQTT_SUBSCRIBE,         /**< Client-to-server SUBSCRIBE. */
    IOT_MQTT_UNSUBSCRIBE,       /**< Client-to-server UNSUBSCRIBE. */
    IOT_MQTT_PINGREQ,           /**< Client-to-server PINGREQ. */
    IOT_MQTT_DISCONNECT         /**< Client-to-server DISCONNECT. */
} IotMqttOperationType_t;

/**
 * @ingroup mqtt_datatypes_enums
 * @brief Quality of service levels for MQTT PUBLISH messages.
 *
 * All MQTT PUBLISH messages, including Last Will and Testament and messages
 * received on subscription filters, have an associated <i>Quality of Service</i>,
 * which defines any delivery guarantees for that message.
 * - QoS 0 messages will be delivered at most once. This is a "best effort"
 * transmission with no retransmissions.
 * - QoS 1 messages will be delivered at least once. See #IotMqttPublishInfo_t
 * for the retransmission strategy this library uses to redeliver messages
 * assumed to be lost.
 *
 * @attention QoS 2 is not supported by this library and should not be used.
 */
typedef enum IotMqttQos
{
    IOT_MQTT_QOS_0 = 0, /**< Delivery at most once. */
    IOT_MQTT_QOS_1 = 1, /**< Delivery at least once. See #IotMqttPublishInfo_t for client-side retry strategy. */
    IOT_MQTT_QOS_2 = 2  /**< Delivery exactly once. Unsupported, but enumerated for completeness. */
} IotMqttQos_t;

/**
 * @ingroup mqtt_datatypes_enums
 * @brief The reason that an MQTT connection (and its associated network connection)
 * was disconnected.
 *
 * When an MQTT connection is closed, its associated [disconnect callback]
 * (@ref IotMqttNetworkInfo_t::disconnectCallback) will be invoked. This type
 * is passed inside of an #IotMqttCallbackParam_t to provide a reason for the
 * disconnect.
 */
typedef enum IotMqttDisconnectReason
{
    IOT_MQTT_DISCONNECT_CALLED,   /**< @ref mqtt_function_disconnect was invoked. */
    IOT_MQTT_BAD_PACKET_RECEIVED, /**< An invalid packet was received from the network. */
    IOT_MQTT_KEEP_ALIVE_TIMEOUT   /**< Keep-alive response was not received within @ref IOT_MQTT_RESPONSE_WAIT_MS. */
} IotMqttDisconnectReason_t;

/*------------------------- MQTT parameter structs --------------------------*/

/**
 * @paramstructs{mqtt,MQTT}
 */

/**
 * @ingroup mqtt_datatypes_paramstructs
 * @brief Information on a PUBLISH message.
 *
 * @paramfor @ref mqtt_function_connect, @ref mqtt_function_publishasync
 *
 * Passed to @ref mqtt_function_publishasync as the message to publish and @ref
 * mqtt_function_connect as the Last Will and Testament (LWT) message.
 *
 * @initializer{IotMqttPublishInfo_t,IOT_MQTT_PUBLISH_INFO_INITIALIZER}
 *
 * #IotMqttPublishInfo_t.retryMs and #IotMqttPublishInfo_t.retryLimit are only
 * relevant to QoS 1 PUBLISH messages. They are ignored for QoS 0 PUBLISH
 * messages and LWT messages. These members control retransmissions of QoS 1
 * messages under the following rules:
 * - Retransmission is disabled when #IotMqttPublishInfo_t.retryLimit is 0.
 * After sending the PUBLISH, the library will wait indefinitely for a PUBACK.
 * - If #IotMqttPublishInfo_t.retryLimit is greater than 0, then QoS 1 publishes
 * that do not receive a PUBACK within #IotMqttPublishInfo_t.retryMs will be
 * retransmitted, up to #IotMqttPublishInfo_t.retryLimit times.
 *
 * Retransmission follows a truncated exponential backoff strategy. The constant
 * @ref IOT_MQTT_RETRY_MS_CEILING controls the maximum time between retransmissions.
 *
 * After #IotMqttPublishInfo_t.retryLimit retransmissions are sent, the MQTT
 * library will wait @ref IOT_MQTT_RESPONSE_WAIT_MS before a final check
 * for a PUBACK. If no PUBACK was received within this time, the QoS 1 PUBLISH
 * fails with the code #IOT_MQTT_RETRY_NO_RESPONSE.
 *
 * @note The lengths of the strings in this struct should not include the NULL
 * terminator. Strings in this struct do not need to be NULL-terminated.
 *
 * @note The AWS IoT MQTT broker does not support the DUP bit.  More
 * information about connecting to AWS IoT via MQTT is available
 * [here](https://docs.aws.amazon.com/iot/latest/developerguide/mqtt.html).
 *
 * <b>Example</b>
 *
 * Consider a situation where
 * - @ref IOT_MQTT_RETRY_MS_CEILING is 60000
 * - #IotMqttPublishInfo_t.retryMs is 2000
 * - #IotMqttPublishInfo_t.retryLimit is 20
 *
 * A PUBLISH message will be retransmitted at the following times after the initial
 * transmission if no PUBACK is received:
 * - 2000 ms (2000 ms after previous transmission)
 * - 6000 ms (4000 ms after previous transmission)
 * - 14000 ms (8000 ms after previous transmission)
 * - 30000 ms (16000 ms after previous transmission)
 * - 62000 ms (32000 ms after previous transmission)
 * - 122000 ms, 182000 ms, 242000 ms... (every 60000 ms until 20 transmissions have been sent)
 *
 * After the 20th retransmission, the MQTT library will wait
 * @ref IOT_MQTT_RESPONSE_WAIT_MS before checking a final time for a PUBACK.
 */
typedef struct IotMqttPublishInfo
{
    IotMqttQos_t qos;         /**< @brief QoS of message. Must be 0 or 1. */
    bool retain;              /**< @brief MQTT message retain flag. */

    const char * pTopicName;  /**< @brief Topic name of PUBLISH. */
    uint16_t topicNameLength; /**< @brief Length of #IotMqttPublishInfo_t.pTopicName. */

    const void * pPayload;    /**< @brief Payload of PUBLISH. */
    size_t payloadLength;     /**< @brief Length of #IotMqttPublishInfo_t.pPayload. For LWT messages, this is limited to 65535. */

    uint32_t retryMs;         /**< @brief If no response is received within this time, the message is retransmitted. */
    uint32_t retryLimit;      /**< @brief How many times to attempt retransmission. */
} IotMqttPublishInfo_t;

/**
 * @ingroup mqtt_datatypes_paramstructs
 * @brief Parameter to an MQTT callback function.
 *
 * @paramfor MQTT callback functions
 *
 * The MQTT library passes this struct to a registered callback whenever an
 * operation completes, a message is received on a topic filter, or an MQTT
 * connection is disconnected.
 *
 * The members of this struct are different based on the callback trigger. If the
 * callback function was triggered for completed operation, the `operation`
 * member is valid. Otherwise, if the callback was triggered because of a
 * server-to-client PUBLISH, the `message` member is valid. Finally, if the callback
 * was triggered because of a disconnect, the `disconnectReason` member is valid.
 *
 * For an incoming PUBLISH, the `message.pTopicFilter` parameter provides the
 * subscription topic filter that matched the topic name in the PUBLISH. Because
 * topic filters may use MQTT wildcards, the topic filter may be different from the
 * topic name. This pointer must be treated as read-only; the topic filter must not
 * be modified. Additionally, the topic filter may go out of scope as soon as the
 * callback function returns, so it must be copied if it is needed at a later time.
 *
 * @attention Any pointers in this callback parameter may be freed as soon as
 * the [callback function](@ref IotMqttCallbackInfo_t.function) returns.
 * Therefore, data must be copied if it is needed after the callback function
 * returns.
 * @attention The MQTT library may set strings that are not NULL-terminated.
 *
 * @see #IotMqttCallbackInfo_t for the signature of a callback function.
 */
typedef struct IotMqttCallbackParam
{
    /**
     * @brief The MQTT connection associated with this completed operation,
     * incoming PUBLISH, or disconnect.
     *
     * [MQTT API functions](@ref mqtt_functions) are safe to call from a callback
     * for completed operations or incoming PUBLISH messages. However, blocking
     * function calls (including @ref mqtt_function_wait) are not recommended
     * (though still safe). Do not call any API functions from a disconnect
     * callback.
     */
    IotMqttConnection_t mqttConnection;

    union
    {
        /* Valid for completed operations. */
        struct
        {
            IotMqttOperationType_t type;  /**< @brief Type of operation that completed. */
            IotMqttOperation_t reference; /**< @brief Reference to the operation that completed. */
            IotMqttError_t result;        /**< @brief Result of operation, e.g. succeeded or failed. */
        } operation;

        /* Valid for incoming PUBLISH messages. */
        struct
        {
            const char * pTopicFilter;  /**< @brief Topic filter that matched the message. */
            uint16_t topicFilterLength; /**< @brief Length of `pTopicFilter`. */
            IotMqttPublishInfo_t info;  /**< @brief PUBLISH message received from the server. */
        } message;

        /* Valid when a connection is disconnected. */
        IotMqttDisconnectReason_t disconnectReason; /**< @brief Why the MQTT connection was disconnected. */
    } u;                                            /**< @brief Valid member depends on callback type. */
} IotMqttCallbackParam_t;

/**
 * @ingroup mqtt_datatypes_paramstructs
 * @brief MQTT callback function and context.
 *
 * @paramfor @ref mqtt_function_subscribeasync, @ref mqtt_function_unsubscribeasync,
 * and @ref mqtt_function_publishasync. Cannot be used with #IOT_MQTT_FLAG_WAITABLE.
 *
 * Specifies a function to be invoked with optional context when an operation
 * completes or when a server-to-client PUBLISH is received.
 *
 * @initializer{IotMqttCallbackInfo_t,IOT_MQTT_CALLBACK_INFO_INITIALIZER}
 *
 * Below is an example for receiving an asynchronous notification on operation
 * completion. See @ref mqtt_function_subscribeasync for an example of using this struct
 * with for incoming PUBLISH messages.
 *
 * @code{c}
 * // Operation completion callback.
 * void operationComplete( void * pArgument, IotMqttCallbackParam_t * pOperation );
 *
 * // Callback information.
 * IotMqttCallbackInfo_t callbackInfo = IOT_MQTT_CALLBACK_INFO_INITIALIZER;
 * callbackInfo.function = operationComplete;
 *
 * // Operation to wait for.
 * IotMqttError_t result = IotMqtt_PublishAsync( &mqttConnection,
 *                                               &publishInfo,
 *                                               0,
 *                                               &callbackInfo,
 *                                               &reference );
 *
 * // Publish should have returned IOT_MQTT_STATUS_PENDING. Once a response
 * // is received, operationComplete is executed with the actual status passed
 * // in pOperation.
 * @endcode
 */
typedef struct IotMqttCallbackInfo
{
    void * pCallbackContext; /**< @brief The first parameter to pass to the callback function to provide context. */

    /**
     * @brief User-provided callback function signature.
     *
     * @param[in] void * #IotMqttCallbackInfo_t.pCallbackContext
     * @param[in] IotMqttCallbackParam_t * Details on the outcome of the MQTT operation
     * or an incoming MQTT PUBLISH.
     *
     * @see #IotMqttCallbackParam_t for more information on the second parameter.
     */
    void ( * function )( void *,
                         IotMqttCallbackParam_t * );
} IotMqttCallbackInfo_t;

/**
 * @ingroup mqtt_datatypes_paramstructs
 * @brief MQTT subscription.
 *
 * @paramfor @ref mqtt_function_subscribeasync, @ref mqtt_function_unsubscribeasync,
 * @ref mqtt_function_subscribesync, @ref mqtt_function_unsubscribesync
 *
 * An array of these is passed to @ref mqtt_function_subscribeasync and @ref
 * mqtt_function_unsubscribeasync. However, #IotMqttSubscription_t.callback and
 * and #IotMqttSubscription_t.qos are ignored by @ref mqtt_function_unsubscribeasync.
 *
 * @initializer{IotMqttSubscription_t,IOT_MQTT_SUBSCRIPTION_INITIALIZER}
 *
 * @note The lengths of the strings in this struct should not include the NULL
 * terminator. Strings in this struct do not need to be NULL-terminated.
 * @see #IotMqttCallbackInfo_t for details on setting a callback function.
 */
typedef struct IotMqttSubscription
{
    /**
     * @brief QoS of messages delivered on subscription.
     *
     * Must be `0` or `1`. Ignored by @ref mqtt_function_unsubscribeasync.
     */
    IotMqttQos_t qos;

    const char * pTopicFilter;  /**< @brief Topic filter of subscription. */
    uint16_t topicFilterLength; /**< @brief Length of #IotMqttSubscription_t.pTopicFilter. */

    /**
     * @brief Callback to invoke when a message is received.
     *
     * See #IotMqttCallbackInfo_t. Ignored by @ref mqtt_function_unsubscribeasync.
     */
    IotMqttCallbackInfo_t callback;
} IotMqttSubscription_t;

/**
 * @ingroup mqtt_datatypes_paramstructs
 * @brief MQTT connection details.
 *
 * @paramfor @ref mqtt_function_connect
 *
 * Passed as an argument to @ref mqtt_function_connect. Most members of this struct
 * correspond to the content of an [MQTT CONNECT packet.]
 * (http://docs.oasis-open.org/mqtt/mqtt/v3.1.1/csprd02/mqtt-v3.1.1-csprd02.html#_Toc385349764)
 *
 * @initializer{IotMqttConnectInfo_t,IOT_MQTT_CONNECT_INFO_INITIALIZER}
 *
 * @note The lengths of the strings in this struct should not include the NULL
 * terminator. Strings in this struct do not need to be NULL-terminated.
 */
typedef struct IotMqttConnectInfo
{
    /**
     * @brief Specifies if this MQTT connection is to an AWS IoT MQTT server.
     *
     * Set this member to `true` when connecting to the AWS IoT MQTT broker or
     * `false` otherwise.  Additional details about connecting to AWS IoT
     * via MQTT are available [here]
     * (https://docs.aws.amazon.com/iot/latest/developerguide/mqtt.html)
     *
     * @attention This setting <b>MUST</b> be `true` when using the AWS IoT MQTT
     * server; it <b>MUST</b> be `false` otherwise.
     * @note Currently, @ref IOT_MQTT_CONNECT_INFO_INITIALIZER sets this
     * this member to `true`.
     */
    bool awsIotMqttMode;

    /**
     * @brief Whether this connection is a clean session.
     *
     * MQTT servers can maintain and topic filter subscriptions and unacknowledged
     * PUBLISH messages. These form part of an <i>MQTT session</i>, which is identified by
     * the [client identifier](@ref IotMqttConnectInfo_t.pClientIdentifier).
     *
     * Setting this value to `true` establishes a <i>clean session</i>, which causes
     * the MQTT server to discard any previous session data for a client identifier.
     * When the client disconnects, the server discards all session data. If this
     * value is `true`, #IotMqttConnectInfo_t.pPreviousSubscriptions and
     * #IotMqttConnectInfo_t.previousSubscriptionCount are ignored.
     *
     * Setting this value to `false` does one of the following:
     * - If no previous session exists, the MQTT server will create a new
     * <i>persistent session</i>. The server may maintain subscriptions and
     * unacknowledged PUBLISH messages after a client disconnects, to be restored
     * once the same client identifier reconnects.
     * - If a previous session exists, the MQTT server restores all of the session's
     * subscriptions for the client identifier and may immediately transmit any
     * unacknowledged PUBLISH packets to the client.
     *
     * When a client with a persistent session disconnects, the MQTT server
     * continues to maintain all subscriptions and unacknowledged PUBLISH messages.
     * The client must also remember the session subscriptions to restore them
     * upon reconnecting. #IotMqttConnectInfo_t.pPreviousSubscriptions and
     * #IotMqttConnectInfo_t.previousSubscriptionCount are used to restore a
     * previous session's subscriptions client-side.
     */
    bool cleanSession;

    /**
     * @brief An array of MQTT subscriptions present in a previous session, if any.
     *
     * Pointer to the start of an array of subscriptions present a previous session,
     * if any. These subscriptions will be immediately restored upon reconnecting.
     *
     * [Optional] The field can also be used to pass a list of subscriptions to be
     * stored locally without a SUBSCRIBE packet being sent to the broker. These subscriptions
     * are useful to invoke application level callbacks for messages received on unsolicited
     * topics from the broker.
     *
     * This member is ignored if it is `NULL`. If this member is not `NULL`,
     * #IotMqttConnectInfo_t.previousSubscriptionCount must be nonzero.
     */
    const IotMqttSubscription_t * pPreviousSubscriptions;

    /**
     * @brief The number of MQTT subscriptions present in a previous session, if any.
     *
     * Number of subscriptions contained in the array
     * #IotMqttConnectInfo_t.pPreviousSubscriptions.
     *
     * This value is ignored if #IotMqttConnectInfo_t.pPreviousSubscriptions
     * is `NULL`. If #IotMqttConnectInfo_t.pPreviousSubscriptions is not `NULL`,
     * this value must be nonzero.
     */
    size_t previousSubscriptionCount;

    /**
     * @brief A message to publish if the new MQTT connection is unexpectedly closed.
     *
     * A Last Will and Testament (LWT) message may be published if this connection is
     * closed without sending an MQTT DISCONNECT packet. This pointer should be set to
     * an #IotMqttPublishInfo_t representing any LWT message to publish. If an LWT
     * is not needed, this member must be set to `NULL`.
     *
     * Unlike other PUBLISH messages, an LWT message is limited to 65535 bytes in
     * length. Additionally, [pWillInfo->retryMs](@ref IotMqttPublishInfo_t.retryMs)
     * and [pWillInfo->retryLimit](@ref IotMqttPublishInfo_t.retryLimit) will
     * be ignored.
     */
    const IotMqttPublishInfo_t * pWillInfo;

    uint16_t keepAliveSeconds;       /**< @brief Period of keep-alive messages. Set to 0 to disable keep-alive. */

    const char * pClientIdentifier;  /**< @brief MQTT client identifier. */
    uint16_t clientIdentifierLength; /**< @brief Length of #IotMqttConnectInfo_t.pClientIdentifier. */

    /* These credentials are not used by AWS IoT and may be ignored if
     * awsIotMqttMode is true. */
    const char * pUserName;  /**< @brief Username for MQTT connection. */
    uint16_t userNameLength; /**< @brief Length of #IotMqttConnectInfo_t.pUserName. */
    const char * pPassword;  /**< @brief Password for MQTT connection. */
    uint16_t passwordLength; /**< @brief Length of #IotMqttConnectInfo_t.pPassword. */
} IotMqttConnectInfo_t;

/**
 * @ingroup mqtt_datatypes_paramstructs
 * @brief MQTT packet details.
 *
 * @paramfor @ref mqtt_function_deserializeresponse @ref mqtt_function_deserializepublish
 *
 * Passed as an argument to public low level mqtt deserialize functions.
 *
 * @initializer{IotMqttPacketInfo_t,IOT_MQTT_PACKET_INFO_INITIALIZER}
 *
 * @note This structure should be only used while accessing low level MQTT deserialization API.
 * The low level serialization/ deserialization API should be only used for implementing
 * light weight single threaded mqtt client.
 */
typedef struct IotMqttPacketInfo
{
    uint8_t * pRemainingData;     /**< @brief (Input) The remaining data in MQTT packet. */
    size_t remainingLength;       /**< @brief (Input) Length of the remaining data in the MQTT packet. */
    uint16_t packetIdentifier;    /**< @brief (Output) MQTT packet identifier. */
    uint8_t type;                 /**< @brief (Input) A value identifying the packet type. */
    IotMqttPublishInfo_t pubInfo; /**< @brief (Output) Publish info in case of deserializing PUBLISH. */
} IotMqttPacketInfo_t;

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this section.
 *
 * Forward declaration of the internal MQTT packet structure.
 */
struct _mqttPacket;
/** @endcond */

/**
 * @brief Get the MQTT packet type from a stream of bytes off the network.
 *
 * @param[in] pNetworkConnection Reference to the network connection.
 * @param[in] pNetworkInterface Function pointers used to interact with the
 * network.
 */
typedef uint8_t ( * IotMqttGetPacketType_t )( void * pNetworkConnection,
                                              const IotNetworkInterface_t * pNetworkInterface );

/**
 * @brief Get the remaining length from a stream of bytes off the network.
 *
 * @param[in] pNetworkConnection Reference to the network connection.
 * @param[in] pNetworkInterface Function pointers used to interact with the
 * network.
 */
typedef size_t ( * IotMqttGetRemainingLength_t )( void * pNetworkConnection,
                                                  const IotNetworkInterface_t * pNetworkInterface );

/**
 * @brief Free a packet generated by the serializer.
 *
 * This function pointer must be set if any other serializer override is set.
 * @param[in] uint8_t* The packet to free.
 */
typedef void ( * IotMqttFreePacket_t )( uint8_t * pPacket );

/**
 * @brief CONNECT packet serializer function.
 * @param[in] IotMqttConnectInfo_t* User-provided CONNECT information.
 * @param[out] uint8_t** Where the CONNECT packet is written.
 * @param[out] size_t* Size of the CONNECT packet.
 */
typedef IotMqttError_t ( * IotMqttSerializeConnect_t )( const IotMqttConnectInfo_t * pConnectInfo,
                                                        uint8_t ** pConnectPacket,
                                                        size_t * pPacketSize );

/**
 * @brief PINGREQ packet serializer function.
 * @param[out] uint8_t** Where the PINGREQ packet is written.
 * @param[out] size_t* Size of the PINGREQ packet.
 */
typedef IotMqttError_t ( * IotMqttSerializePingreq_t )( uint8_t ** pDisconnectPacket,
                                                        size_t * pPacketSize );

/**
 * @brief PUBLISH packet serializer function.
 * @param[in] IotMqttPublishInfo_t* User-provided PUBLISH information.
 * @param[out] uint8_t** Where the PUBLISH packet is written.
 * @param[out] size_t* Size of the PUBLISH packet.
 * @param[out] uint16_t* The packet identifier generated for this PUBLISH.
 * @param[out] uint8_t** Where the high byte of the packet identifier
 * is written.
 */
typedef IotMqttError_t ( * IotMqtt_SerializePublish_t )( const IotMqttPublishInfo_t * pPublishInfo,
                                                         uint8_t ** pPublishPacket,
                                                         size_t * pPacketSize,
                                                         uint16_t * pPacketIdentifier,
                                                         uint8_t ** pPacketIdentifierHigh );

/**
 * @brief SUBSCRIBE/UNSUBSCRIBE packet serializer function.
 * @param[in] IotMqttSubscription_t* User-provided array of subscriptions.
 * @param[in] size_t Number of elements in the subscription array.
 * @param[out] uint8_t** Where the SUBSCRIBE packet is written.
 * @param[out] size_t* Size of the SUBSCRIBE packet.
 * @param[out] uint16_t* The packet identifier generated for this SUBSCRIBE.
 */
typedef IotMqttError_t ( * IotMqttSerializeSubscribe_t )( const IotMqttSubscription_t * pSubscriptionList,
                                                          size_t subscriptionCount,
                                                          uint8_t ** pSubscribePacket,
                                                          size_t * pPacketSize,
                                                          uint16_t * pPacketIdentifier );

/**
 * @brief DISCONNECT packet serializer function.
 * @param[out] uint8_t** Where the DISCONNECT packet is written.
 * @param[out] size_t* Size of the DISCONNECT packet.
 */
typedef IotMqttError_t ( * IotMqttSerializeDisconnect_t )( uint8_t ** ppDisconnectPacket,
                                                           size_t * pPacketSize );

/**
 * @brief MQTT packet deserializer function.
 * @param[in,out] _mqttPacket* Pointer to an MQTT packet structure
 */
typedef IotMqttError_t ( * IotMqttDeserialize_t )( struct _mqttPacket * pMqttPacket );

/**
 * @brief PUBACK packet serializer function.
 * @param[in] uint16_t The packet identifier to place in PUBACK.
 * @param[out] uint8_t** Where the PUBACK packet is written.
 * @param[out] size_t* Size of the PUBACK packet.
 */
typedef IotMqttError_t ( * IotMqttSerializePuback_t )( uint16_t packetIdentifier,
                                                       uint8_t ** pPubackPacket,
                                                       size_t * pPacketSize );

/**
 * @brief Set the `DUP` bit in a QoS `1` PUBLISH packet.
 * @param[in] uint8_t* Pointer to the PUBLISH packet to modify.
 * @param[in] uint8_t* The high byte of any packet identifier to modify.
 * @param[out] uint16_t* New packet identifier (AWS IoT MQTT mode only).
 */
typedef void ( * IotMqttPublishSetDup_t )( uint8_t * pPublishPacket,
                                           uint8_t * pPacketIdentifierHigh,
                                           uint16_t * pNewPacketIdentifier );

/**
 * @brief Function pointer to read the next available byte on a network connection.
 * @param[in] pNetworkContext reference to network connection like socket.
 * @param[out] pNextByte Pointer to the byte read from the network.
 */
typedef IotMqttError_t (* IotMqttGetNextByte_t)( void * pNetworkContext,
                                                 uint8_t * pNextByte );

#if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1

/**
 * @ingroup mqtt_datatypes_paramstructs
 * @brief Function pointers for MQTT packet serializer overrides.
 *
 * These function pointers allow the MQTT serialization and deserialization functions
 * to be overridden for an MQTT connection. The compile-time setting
 * @ref IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES must be `1` to enable this functionality.
 * See the #IotMqttSerializer_t::serialize and #IotMqttSerializer_t::deserialize
 * members for a list of functions that can be overridden. In addition, the functions
 * for freeing packets and determining the packet type can also be overridden. If
 * @ref IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES is `1`, the serializer initialization and
 * cleanup functions may be extended. See documentation of
 * @ref IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES for more information.
 *
 * If any function pointers that are `NULL`, then the default implementation of that
 * function will be used.
 */
    typedef struct IotMqttSerializer
    {
        /**
         * @brief Get the MQTT packet type from a stream of bytes off the network.
         * <b>Default implementation:</b> #_IotMqtt_GetPacketType
         */
        IotMqttGetPacketType_t getPacketType;

        /**
         * @brief Get the remaining length from a stream of bytes off the network.
         * <b>Default implementation:</b> #_IotMqtt_GetRemainingLength
         */
        IotMqttGetRemainingLength_t getRemainingLength;

        /**
         * @brief Free a packet generated by the serializer.
         *
         * <b>Default implementation:</b> #_IotMqtt_FreePacket
         */
        IotMqttFreePacket_t freePacket;

        struct
        {
            /**
             * @brief CONNECT packet serializer function.
             *
             * <b>Default implementation:</b> #_IotMqtt_SerializeConnect
             */
            IotMqttSerializeConnect_t connect;

            /**
             * @brief PUBLISH packet serializer function.
             *
             * <b>Default implementation:</b> #_IotMqtt_SerializePublish
             */
            IotMqtt_SerializePublish_t publish;

            /**
             * @brief Set the `DUP` bit in a QoS `1` PUBLISH packet.
             *
             * <b>Default implementation:</b> #_IotMqtt_PublishSetDup
             */
            IotMqttPublishSetDup_t publishSetDup;

            /**
             * @brief PUBACK packet serializer function.
             *
             * <b>Default implementation:</b> #_IotMqtt_SerializePuback
             */
            IotMqttSerializePuback_t puback;

            /**
             * @brief SUBSCRIBE packet serializer function.
             *
             * <b>Default implementation:</b> #_IotMqtt_SerializeSubscribe
             */
            IotMqttSerializeSubscribe_t subscribe;

            /**
             * @brief UNSUBSCRIBE packet serializer function.
             *
             * <b>Default implementation:</b> #_IotMqtt_SerializeUnsubscribe
             */
            IotMqttSerializeSubscribe_t unsubscribe;

            /**
             * @brief PINGREQ packet serializer function.
             *
             * <b>Default implementation:</b> #_IotMqtt_SerializePingreq
             */
            IotMqttSerializePingreq_t pingreq;

            /**
             * @brief DISCONNECT packet serializer function.
             *
             * <b>Default implementation:</b> #_IotMqtt_SerializeDisconnect
             */
            IotMqttSerializeDisconnect_t disconnect;
        } serialize; /**< @brief Overrides the packet serialization functions for a single connection. */

        struct
        {
            /**
             * @brief CONNACK packet deserializer function.
             *
             * <b>Default implementation:</b> #_IotMqtt_DeserializeConnack
             */
            IotMqttDeserialize_t connack;

            /**
             * @brief PUBLISH packet deserializer function.
             *
             * <b>Default implementation:</b> #_IotMqtt_DeserializePublish
             */
            IotMqttDeserialize_t publish;

            /**
             * @brief PUBACK packet deserializer function.
             *
             * <b>Default implementation:</b> #_IotMqtt_DeserializePuback
             */
            IotMqttDeserialize_t puback;

            /**
             * @brief SUBACK packet deserializer function.
             *
             * <b>Default implementation:</b> #_IotMqtt_DeserializeSuback
             */
            IotMqttDeserialize_t suback;

            /**
             * @brief UNSUBACK packet deserializer function.
             *
             * <b>Default implementation:</b> #_IotMqtt_DeserializeUnsuback
             */
            IotMqttDeserialize_t unsuback;

            /**
             * @brief PINGRESP packet deserializer function.
             *
             * <b>Default implementation:</b> #_IotMqtt_DeserializePingresp
             */
            IotMqttDeserialize_t pingresp;
        } deserialize; /**< @brief Overrides the packet deserialization functions for a single connection. */
    } IotMqttSerializer_t;

#else /* if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1 */

/* When MQTT packet serializer overrides are disabled, this struct is an
 * incomplete type. */
    typedef struct IotMqttSerializer IotMqttSerializer_t;

#endif /* if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1 */

/**
 * @ingroup mqtt_datatypes_paramstructs
 * @brief MQTT network connection details.
 *
 * @paramfor @ref mqtt_function_connect
 *
 * The MQTT library needs to be able to send and receive data over a network.
 * This struct provides an interface for interacting with the network.
 *
 * @initializer{IotMqttNetworkInfo_t,IOT_MQTT_NETWORK_INFO_INITIALIZER}
 */
typedef struct IotMqttNetworkInfo
{
    /**
     * @brief Whether a new network connection should be created.
     *
     * When this value is `true`, a new transport-layer network connection will
     * be created along with the MQTT connection. #IotMqttNetworkInfo_t::pNetworkServerInfo
     * and #IotMqttNetworkInfo_t::pNetworkCredentialInfo are valid when this value
     * is `true`.
     *
     * When this value is `false`, the MQTT connection will use a transport-layer
     * network connection that has already been established. The MQTT library will
     * still set the appropriate receive callback even if the network connection
     * has been established.
     * #IotMqttNetworkInfo_t::pNetworkConnection, which represents an established
     * network connection, is valid when this value is `false`.
     */
    bool createNetworkConnection;

    union
    {
        struct
        {
            /**
             * @brief Information on the MQTT server, passed as `pServerInfo` to
             * #IotNetworkInterface_t::create.
             *
             * This member is opaque to the MQTT library. It is passed to the network
             * interface when creating a new network connection. It is only valid when
             * #IotMqttNetworkInfo_t::createNetworkConnection is `true`.
             */
            IotNetworkServerInfo_t pNetworkServerInfo;

            /**
             * @brief Credentials for the MQTT server, passed as `pCredentialInfo` to
             * #IotNetworkInterface_t::create.
             *
             * This member is opaque to the MQTT library. It is passed to the network
             * interface when creating a new network connection. It is only valid when
             * #IotMqttNetworkInfo_t::createNetworkConnection is `true`.
             */
            IotNetworkCredentials_t pNetworkCredentialInfo;
        } setup;

        /**
         * @brief An established transport-layer network connection.
         *
         * This member is opaque to the MQTT library. It is passed to the network
         * interface to reference an established network connection. It is only
         * valid when #IotMqttNetworkInfo_t::createNetworkConnection is `false`.
         */
        IotNetworkConnection_t pNetworkConnection;
    } u /**< @brief Valid member depends of IotMqttNetworkInfo_t.createNetworkConnection. */;

    /**
     * @brief The network functions used by the new MQTT connection.
     *
     * @attention The function pointers of the network interface must remain valid
     * for the lifetime of the MQTT connection.
     */
    const IotNetworkInterface_t * pNetworkInterface;

    /**
     * @brief A callback function to invoke when this MQTT connection is disconnected.
     */
    IotMqttCallbackInfo_t disconnectCallback;

    #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1

        /**
         * @brief MQTT packet serializer overrides used by the new MQTT connection.
         *
         * @attention The function pointers of the MQTT serializer overrides must
         * remain valid for the lifetime of the MQTT connection.
         */
        const IotMqttSerializer_t * pMqttSerializer;
    #endif
} IotMqttNetworkInfo_t;

/*------------------------- MQTT defined constants --------------------------*/

/**
 * @constantspage{mqtt,MQTT library}
 *
 * @section mqtt_constants_initializers MQTT Initializers
 * @brief Provides default values for the data types of the MQTT library.
 *
 * @snippet this define_mqtt_initializers
 *
 * All user-facing data types of the MQTT library should be initialized using
 * one of the following.
 *
 * @warning Failing to initialize an MQTT data type with the appropriate initializer
 * may result in undefined behavior!
 * @note The initializers may change at any time in future versions, but their
 * names will remain the same.
 *
 * <b>Example</b>
 * @code{c}
 * IotMqttNetworkInfo_t networkInfo = IOT_MQTT_NETWORK_INFO_INITIALIZER;
 * IotMqttSerializer_t serializer = IOT_MQTT_SERIALIZER_INITIALIZER;
 * IotMqttConnectInfo_t connectInfo = IOT_MQTT_CONNECT_INFO_INITIALIZER;
 * IotMqttPublishInfo_t publishInfo = IOT_MQTT_PUBLISH_INFO_INITIALIZER;
 * IotMqttSubscription_t subscription = IOT_MQTT_SUBSCRIPTION_INITIALIZER;
 * IotMqttCallbackInfo_t callbackInfo = IOT_MQTT_CALLBACK_INFO_INITIALIZER;
 * IotMqttConnection_t connection = IOT_MQTT_CONNECTION_INITIALIZER;
 * IotMqttOperation_t operation = IOT_MQTT_OPERATION_INITIALIZER;
 * @endcode
 *
 * @section mqtt_constants_flags MQTT Function Flags
 * @brief Flags that modify the behavior of MQTT library functions.
 * - #IOT_MQTT_FLAG_WAITABLE <br>
 *   @copybrief IOT_MQTT_FLAG_WAITABLE
 * - #IOT_MQTT_FLAG_CLEANUP_ONLY <br>
 *   @copybrief IOT_MQTT_FLAG_CLEANUP_ONLY
 *
 * Flags should be bitwise-ORed with each other to change the behavior of
 * @ref mqtt_function_subscribeasync, @ref mqtt_function_unsubscribeasync,
 * @ref mqtt_function_publishasync, their blocking versions; or @ref mqtt_function_disconnect.
 *
 * @note The values of the flags may change at any time in future versions, but
 * their names will remain the same. Additionally, flags that may be used together
 * will be bitwise-exclusive of each other.
 */

/* @[define_mqtt_initializers] */
/** @brief Initializer for #IotMqttNetworkInfo_t. */
#define IOT_MQTT_NETWORK_INFO_INITIALIZER     { .createNetworkConnection = true }
/** @brief Initializer for #IotMqttSerializer_t. */
#define IOT_MQTT_SERIALIZER_INITIALIZER       { 0 }
/** @brief Initializer for #IotMqttConnectInfo_t. */
#define IOT_MQTT_CONNECT_INFO_INITIALIZER     { .cleanSession = true }
/** @brief Initializer for #IotMqttPublishInfo_t. */
#define IOT_MQTT_PUBLISH_INFO_INITIALIZER     { .qos = IOT_MQTT_QOS_0 }
/** @brief Initializer for #IotMqttSubscription_t. */
#define IOT_MQTT_SUBSCRIPTION_INITIALIZER     { .qos = IOT_MQTT_QOS_0 }
/** @brief Initializer for #IotMqttCallbackInfo_t. */
#define IOT_MQTT_CALLBACK_INFO_INITIALIZER    { 0 }
/** @brief Initializer for #IotMqttConnection_t. */
#define IOT_MQTT_CONNECTION_INITIALIZER       NULL
/** @brief Initializer for #IotMqttOperation_t. */
#define IOT_MQTT_OPERATION_INITIALIZER        NULL
/** @brief Initializer for #IotMqttPacketInfo_t. */
#define IOT_MQTT_PACKET_INFO_INITIALIZER      { .pRemainingData = NULL, remainingLength = 0, packetIdentifier = 0, .type = 0 }
/* @[define_mqtt_initializers] */

/**
 * @brief Allows the use of @ref mqtt_function_wait for blocking until completion.
 *
 * This flag is always valid for @ref mqtt_function_subscribeasync and
 * @ref mqtt_function_unsubscribeasync. If passed to @ref mqtt_function_publishasync,
 * the parameter [pPublishInfo->qos](@ref IotMqttPublishInfo_t.qos) must not be `0`.
 *
 * An #IotMqttOperation_t <b>MUST</b> be provided if this flag is set. Additionally, an
 * #IotMqttCallbackInfo_t <b>MUST NOT</b> be provided.
 *
 * @note If this flag is set, @ref mqtt_function_wait <b>MUST</b> be called to clean up
 * resources.
 */
#define IOT_MQTT_FLAG_WAITABLE        ( 0x00000001 )

/**
 * @brief Causes @ref mqtt_function_disconnect to only free memory and not send
 * an MQTT DISCONNECT packet.
 *
 * This flag is only valid for @ref mqtt_function_disconnect. It should be passed
 * to @ref mqtt_function_disconnect if the network goes offline or is otherwise
 * unusable.
 */
#define IOT_MQTT_FLAG_CLEANUP_ONLY    ( 0x00000001 )

#endif /* ifndef IOT_MQTT_TYPES_H_ */
