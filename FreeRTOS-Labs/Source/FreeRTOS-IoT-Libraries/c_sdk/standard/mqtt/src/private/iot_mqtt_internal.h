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
 * @file iot_mqtt_internal.h
 * @brief Internal header of MQTT library. This header should not be included in
 * typical application code.
 */

#ifndef IOT_MQTT_INTERNAL_H_
#define IOT_MQTT_INTERNAL_H_

/* The config header is always included first. */
#include "iot_config.h"

/* Linear containers (lists and queues) include. */
#include "iot_linear_containers.h"

/* MQTT include. */
#include "iot_mqtt.h"

/* Task pool include. */
#include "iot_taskpool_freertos.h"

/**
 * @def IotMqtt_Assert( expression )
 * @brief Assertion macro for the MQTT library.
 *
 * Set @ref IOT_MQTT_ENABLE_ASSERTS to `1` to enable assertions in the MQTT
 * library.
 *
 * @param[in] expression Expression to be evaluated.
 */
#if IOT_MQTT_ENABLE_ASSERTS == 1
    #ifndef IotMqtt_Assert
        #ifdef Iot_DefaultAssert
            #define IotMqtt_Assert( expression )    Iot_DefaultAssert( expression )
        #else
            #error "Asserts are enabled for MQTT, but IotMqtt_Assert is not defined"
        #endif
    #endif
#else
    #define IotMqtt_Assert( expression )
#endif

/* Configure logs for MQTT functions. */
#ifdef IOT_LOG_LEVEL_MQTT
    #define LIBRARY_LOG_LEVEL        IOT_LOG_LEVEL_MQTT
#else
    #ifdef IOT_LOG_LEVEL_GLOBAL
        #define LIBRARY_LOG_LEVEL    IOT_LOG_LEVEL_GLOBAL
    #else
        #define LIBRARY_LOG_LEVEL    IOT_LOG_NONE
    #endif
#endif

#define LIBRARY_LOG_NAME    ( "MQTT" )
#include "iot_logging_setup.h"

/*
 * Provide default values for undefined memory allocation functions based on
 * the usage of dynamic memory allocation.
 */
#if IOT_STATIC_MEMORY_ONLY == 1
    #include "iot_static_memory.h"

/**
 * @brief Allocate an #_mqttConnection_t. This function should have the same
 * signature as [malloc]
 * (http://pubs.opengroup.org/onlinepubs/9699919799/functions/malloc.html).
 */
    void * IotMqtt_MallocConnection( size_t size );

/**
 * @brief Free an #_mqttConnection_t. This function should have the same
 * signature as [free]
 * (http://pubs.opengroup.org/onlinepubs/9699919799/functions/free.html).
 */
    void IotMqtt_FreeConnection( void * ptr );

/**
 * @brief Allocate memory for an MQTT packet. This function should have the
 * same signature as [malloc]
 * (http://pubs.opengroup.org/onlinepubs/9699919799/functions/malloc.html).
 */
    #define IotMqtt_MallocMessage    Iot_MallocMessageBuffer

/**
 * @brief Free an MQTT packet. This function should have the same signature
 * as [free]
 * (http://pubs.opengroup.org/onlinepubs/9699919799/functions/free.html).
 */
    #define IotMqtt_FreeMessage      Iot_FreeMessageBuffer

/**
 * @brief Allocate an #_mqttOperation_t. This function should have the same
 * signature as [malloc]
 * (http://pubs.opengroup.org/onlinepubs/9699919799/functions/malloc.html).
 */
    void * IotMqtt_MallocOperation( size_t size );

/**
 * @brief Free an #_mqttOperation_t. This function should have the same
 * signature as [free]
 * (http://pubs.opengroup.org/onlinepubs/9699919799/functions/free.html).
 */
    void IotMqtt_FreeOperation( void * ptr );

/**
 * @brief Allocate an #_mqttSubscription_t. This function should have the
 * same signature as [malloc]
 * (http://pubs.opengroup.org/onlinepubs/9699919799/functions/malloc.html).
 */
    void * IotMqtt_MallocSubscription( size_t size );

/**
 * @brief Free an #_mqttSubscription_t. This function should have the same
 * signature as [free]
 * (http://pubs.opengroup.org/onlinepubs/9699919799/functions/free.html).
 */
    void IotMqtt_FreeSubscription( void * ptr );
#else /* if IOT_STATIC_MEMORY_ONLY == 1 */
    #ifndef IotMqtt_MallocConnection
        #ifdef Iot_DefaultMalloc
            #define IotMqtt_MallocConnection    Iot_DefaultMalloc
        #else
            #error "No malloc function defined for IotMqtt_MallocConnection"
        #endif
    #endif

    #ifndef IotMqtt_FreeConnection
        #ifdef Iot_DefaultFree
            #define IotMqtt_FreeConnection    Iot_DefaultFree
        #else
            #error "No free function defined for IotMqtt_FreeConnection"
        #endif
    #endif

    #ifndef IotMqtt_MallocMessage
        #ifdef Iot_DefaultMalloc
            #define IotMqtt_MallocMessage    Iot_DefaultMalloc
        #else
            #error "No malloc function defined for IotMqtt_MallocMessage"
        #endif
    #endif

    #ifndef IotMqtt_FreeMessage
        #ifdef Iot_DefaultFree
            #define IotMqtt_FreeMessage    Iot_DefaultFree
        #else
            #error "No free function defined for IotMqtt_FreeMessage"
        #endif
    #endif

    #ifndef IotMqtt_MallocOperation
        #ifdef Iot_DefaultMalloc
            #define IotMqtt_MallocOperation    Iot_DefaultMalloc
        #else
            #error "No malloc function defined for IotMqtt_MallocOperation"
        #endif
    #endif

    #ifndef IotMqtt_FreeOperation
        #ifdef Iot_DefaultFree
            #define IotMqtt_FreeOperation    Iot_DefaultFree
        #else
            #error "No free function defined for IotMqtt_FreeOperation"
        #endif
    #endif

    #ifndef IotMqtt_MallocSubscription
        #ifdef Iot_DefaultMalloc
            #define IotMqtt_MallocSubscription    Iot_DefaultMalloc
        #else
            #error "No malloc function defined for IotMqtt_MallocSubscription"
        #endif
    #endif

    #ifndef IotMqtt_FreeSubscription
        #ifdef Iot_DefaultFree
            #define IotMqtt_FreeSubscription    Iot_DefaultFree
        #else
            #error "No free function defined for IotMqtt_FreeSubscription"
        #endif
    #endif
#endif /* if IOT_STATIC_MEMORY_ONLY == 1 */

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this section.
 *
 * Provide default values for undefined configuration constants.
 */
#ifndef AWS_IOT_MQTT_ENABLE_METRICS
    #define AWS_IOT_MQTT_ENABLE_METRICS             ( 1 )
#endif
#ifndef IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES
    #define IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES    ( 0 )
#endif
#ifndef IOT_MQTT_RESPONSE_WAIT_MS
    #define IOT_MQTT_RESPONSE_WAIT_MS               ( 1000 )
#endif
#ifndef IOT_MQTT_RETRY_MS_CEILING
    #define IOT_MQTT_RETRY_MS_CEILING               ( 60000 )
#endif
/** @endcond */

/**
 * @brief Marks the empty statement of an `else` branch.
 *
 * Does nothing, but allows test coverage to detect branches not taken. By default,
 * this is defined to nothing. When running code coverage testing, this is defined
 * to an assembly NOP.
 */
#ifndef EMPTY_ELSE_MARKER
    #define EMPTY_ELSE_MARKER
#endif

#define MQTT_SERVER_MAX_CLIENTID_LENGTH                        ( ( uint16_t ) 23 )          /**< @brief Optional maximum length of client identifier specified by MQTT 3.1.1. */
#define MQTT_SERVER_MAX_PUBLISH_PAYLOAD_LENGTH                 ( ( size_t ) ( 268435456 ) ) /**< @brief Maximum publish payload length supported by MQTT 3.1.1. */
#define MQTT_SERVER_MAX_LWT_PAYLOAD_LENGTH                     ( ( size_t ) UINT16_MAX )    /**< @brief Maximum LWT payload length supported by MQTT 3.1.1. */

/*
 * Constants related to limits defined in AWS Service Limits.
 *
 * For details, see
 * https://docs.aws.amazon.com/general/latest/gr/aws_service_limits.html
 *
 * Used to validate parameters if when connecting to an AWS IoT MQTT server.
 */
#define AWS_IOT_MQTT_SERVER_MAX_CLIENTID_LENGTH                ( ( uint16_t ) 128 )      /**< @brief Maximum length of client identifier accepted by AWS IoT. */
#define AWS_IOT_MQTT_SERVER_MAX_TOPIC_LENGTH                   ( ( uint16_t ) 256 )      /**< @brief Maximum length of topic names or filters accepted by AWS IoT. */
#define AWS_IOT_MQTT_SERVER_MAX_TOPIC_FILTERS_PER_SUBSCRIBE    ( ( size_t ) 8 )          /**< @brief Maximum number of topic filters in a single SUBSCRIBE packet. */
#define AWS_IOT_MQTT_SERVER_MAX_PUBLISH_PAYLOAD_LENGTH         ( ( size_t ) ( 131072 ) ) /**< @brief Maximum publish payload length accepted by AWS IoT. */

/*
 * MQTT control packet type and flags. Always the first byte of an MQTT
 * packet.
 *
 * For details, see
 * http://docs.oasis-open.org/mqtt/mqtt/v3.1.1/csprd02/mqtt-v3.1.1-csprd02.html#_Toc385349757
 */
#define MQTT_PACKET_TYPE_CONNECT                               ( ( uint8_t ) 0x10U ) /**< @brief CONNECT (client-to-server). */
#define MQTT_PACKET_TYPE_CONNACK                               ( ( uint8_t ) 0x20U ) /**< @brief CONNACK (server-to-client). */
#define MQTT_PACKET_TYPE_PUBLISH                               ( ( uint8_t ) 0x30U ) /**< @brief PUBLISH (bi-directional). */
#define MQTT_PACKET_TYPE_PUBACK                                ( ( uint8_t ) 0x40U ) /**< @brief PUBACK (server-to-client). */
#define MQTT_PACKET_TYPE_SUBSCRIBE                             ( ( uint8_t ) 0x82U ) /**< @brief SUBSCRIBE (client-to-server). */
#define MQTT_PACKET_TYPE_SUBACK                                ( ( uint8_t ) 0x90U ) /**< @brief SUBACK (server-to-client). */
#define MQTT_PACKET_TYPE_UNSUBSCRIBE                           ( ( uint8_t ) 0xa2U ) /**< @brief UNSUBSCRIBE (client-to-server). */
#define MQTT_PACKET_TYPE_UNSUBACK                              ( ( uint8_t ) 0xb0U ) /**< @brief UNSUBACK (server-to-client). */
#define MQTT_PACKET_TYPE_PINGREQ                               ( ( uint8_t ) 0xc0U ) /**< @brief PINGREQ (client-to-server). */
#define MQTT_PACKET_TYPE_PINGRESP                              ( ( uint8_t ) 0xd0U ) /**< @brief PINGRESP (server-to-client). */
#define MQTT_PACKET_TYPE_DISCONNECT                            ( ( uint8_t ) 0xe0U ) /**< @brief DISCONNECT (client-to-server). */

/**
 * @brief A value that represents an invalid remaining length.
 *
 * This value is greater than what is allowed by the MQTT specification.
 */
#define MQTT_REMAINING_LENGTH_INVALID                          ( ( size_t ) 268435456 )

/**
 * @brief When this flag is passed, MQTT functions will execute jobs on the calling
 * thread, bypassing the task pool.
 *
 * This flag is used along with @ref mqtt_constants_flags, but is intended for internal
 * use only. Nevertheless, its value must be bitwise exclusive of all conflicting
 * @ref mqtt_constants_flags.
 */
#define MQTT_INTERNAL_FLAG_BLOCK_ON_SEND                       ( 0x80000000 )

/**
 * @brief When calling #_IotMqtt_RemoveSubscriptionByPacket, use this value
 * for `order` to delete all subscriptions for the packet.
 *
 * This flag is used along with @ref mqtt_constants_flags, but is intended for internal
 * use only.
 *
 * @ref mqtt_constants_flags.
 */
#define MQTT_REMOVE_ALL_SUBSCRIPTIONS                          ( -1 )

/*---------------------- MQTT internal data structures ----------------------*/

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this section.
 *
 * Forward declaration of MQTT connection type.
 */
struct _mqttConnection;
/** @endcond */

/**
 * @brief Internal structure representing a single MQTT operation, such as
 * CONNECT, SUBSCRIBE, PUBLISH, etc.
 *
 * Queues of these structures keeps track of all in-progress MQTT operations.
 */
typedef struct _mqttOperation
{
    /* Pointers to neighboring queue elements. */
    IotLink_t link;                           /**< @brief List link member. */

    bool incomingPublish;                     /**< @brief Set to true if this operation is an incoming PUBLISH. */
    struct _mqttConnection * pMqttConnection; /**< @brief MQTT connection associated with this operation. */

    IotTaskPoolJobStorage_t jobStorage;       /**< @brief Task pool job storage associated with this operation. */
    IotTaskPoolJob_t job;                     /**< @brief Task pool job associated with this operation. */

    union
    {
        /* If incomingPublish is false, this struct is valid. */
        struct
        {
            /* Basic operation information. */
            int32_t jobReference;        /**< @brief Tracks if a job is using this operation. Must always be 0, 1, or 2. */
            IotMqttOperationType_t type; /**< @brief What operation this structure represents. */
            uint32_t flags;              /**< @brief Flags passed to the function that created this operation. */
            uint16_t packetIdentifier;   /**< @brief The packet identifier used with this operation. */

            /* Serialized packet and size. */
            uint8_t * pMqttPacket;           /**< @brief The MQTT packet to send over the network. */
            uint8_t * pPacketIdentifierHigh; /**< @brief The location of the high byte of the packet identifier in the MQTT packet. */
            size_t packetSize;               /**< @brief Size of `pMqttPacket`. */

            /* How to notify of an operation's completion. */
            union
            {
                IotSemaphore_t waitSemaphore;   /**< @brief Semaphore to be used with @ref mqtt_function_wait. */
                IotMqttCallbackInfo_t callback; /**< @brief User-provided callback function and parameter. */
            } notify;                           /**< @brief How to notify of this operation's completion. */
            IotMqttError_t status;              /**< @brief Result of this operation. This is reported once a response is received. */

            union
            {
                struct
                {
                    uint32_t count;        /**< @brief Current number of retries. */
                    uint32_t limit;        /**< @brief Maximum number of retries allowed. */
                    uint32_t nextPeriodMs; /**< @brief Next retry period. */
                } retry;                   /**< @brief Additional information for PUBLISH retry. */

                struct
                {
                    uint32_t failure;      /**< @brief Flag tracking keep-alive status. */
                    uint32_t keepAliveMs;  /**< @brief Keep-alive interval in milliseconds. Its max value (per spec) is 65,535,000. */
                    uint32_t nextPeriodMs; /**< @brief Relative delay for next keep-alive job. */
                } ping;                    /**< @brief Additional information for keep-alive pings. */
            } periodic;                    /**< @brief Additional information for periodic operations. */
        } operation;

        /* If incomingPublish is true, this struct is valid. */
        struct
        {
            IotMqttPublishInfo_t publishInfo; /**< @brief Deserialized PUBLISH. */
            const void * pReceivedData;       /**< @brief Any buffer associated with this PUBLISH that should be freed. */
        } publish;
    } u;                                      /**< @brief Valid member depends on _mqttOperation_t.incomingPublish. */
} _mqttOperation_t;

/**
 * @brief Represents an MQTT connection.
 */
typedef struct _mqttConnection
{
    bool awsIotMqttMode;                             /**< @brief Specifies if this connection is to an AWS IoT MQTT server. */
    bool ownNetworkConnection;                       /**< @brief Whether this MQTT connection owns its network connection. */
    void * pNetworkConnection;                       /**< @brief References the transport-layer network connection. */
    const IotNetworkInterface_t * pNetworkInterface; /**< @brief Network interface provided to @ref mqtt_function_connect. */
    IotMqttCallbackInfo_t disconnectCallback;        /**< @brief A function to invoke when this connection is disconnected. */

    const IotMqttSerializer_t * pSerializer;         /**< @brief MQTT packet serializer overrides. */

    bool disconnected;                               /**< @brief Tracks if this connection has been disconnected. */
    IotMutex_t referencesMutex;                      /**< @brief Recursive mutex. Grants access to connection state and operation lists. */
    int32_t references;                              /**< @brief Counts callbacks and operations using this connection. */
    IotListDouble_t pendingProcessing;               /**< @brief List of operations waiting to be processed by a task pool routine. */
    IotListDouble_t pendingResponse;                 /**< @brief List of processed operations awaiting a server response. */

    IotListDouble_t subscriptionList;                /**< @brief Holds subscriptions associated with this connection. */
    IotMutex_t subscriptionMutex;                    /**< @brief Grants exclusive access to the subscription list. */

    _mqttOperation_t pingreq;                        /**< @brief Operation used for MQTT keep-alive. */
} _mqttConnection_t;

/**
 * @brief Represents a subscription stored in an MQTT connection.
 */
typedef struct _mqttSubscription
{
    IotLink_t link;     /**< @brief List link member. */

    int32_t references; /**< @brief How many subscription callbacks are using this subscription. */

    /**
     * @brief Tracks whether an unsubscribe function has been called for
     * this subscription.
     *
     * If there are active subscription callbacks, this subscription cannot be removed.
     * Instead, this flag will be set, which schedules the removal of this subscription
     * once all subscription callbacks terminate.
     */
    bool unsubscribed;

    struct
    {
        uint16_t identifier;        /**< @brief Packet identifier. */
        size_t order;               /**< @brief Order in the packet's list of subscriptions. */
    } packetInfo;                   /**< @brief Information about the SUBSCRIBE packet that registered this subscription. */

    IotMqttCallbackInfo_t callback; /**< @brief Callback information for this subscription. */

    uint16_t topicFilterLength;     /**< @brief Length of #_mqttSubscription_t.pTopicFilter. */
    char pTopicFilter[];            /**< @brief The subscription topic filter. */
} _mqttSubscription_t;

/**
 * @brief Represents an MQTT packet received from the network.
 *
 * This struct is used to hold parameters for the deserializers so that all
 * deserializers have the same function signature.
 */
typedef struct _mqttPacket
{
    union
    {
        /**
         * @brief (Input) MQTT connection associated with this packet. Only used
         * when deserializing SUBACKs.
         */
        _mqttConnection_t * pMqttConnection;

        /**
         * @brief (Output) Operation representing an incoming PUBLISH. Only used
         * when deserializing PUBLISHes.
         */
        _mqttOperation_t * pIncomingPublish;
    } u;                       /**< @brief Valid member depends on packet being decoded. */

    uint8_t * pRemainingData;  /**< @brief (Input) The remaining data in MQTT packet. */
    size_t remainingLength;    /**< @brief (Input) Length of the remaining data in the MQTT packet. */
    uint16_t packetIdentifier; /**< @brief (Output) MQTT packet identifier. */
    uint8_t type;              /**< @brief (Input) A value identifying the packet type. */
} _mqttPacket_t;

/*-------------------- MQTT struct validation functions ---------------------*/

/**
 * @brief Check that an #IotMqttConnectInfo_t is valid.
 *
 * @param[in] pConnectInfo The #IotMqttConnectInfo_t to validate.
 *
 * @return `true` if `pConnectInfo` is valid; `false` otherwise.
 */
bool _IotMqtt_ValidateConnect( const IotMqttConnectInfo_t * pConnectInfo );

/**
 * @brief Check that an #IotMqttPublishInfo_t is valid.
 *
 * @param[in] awsIotMqttMode Specifies if this PUBLISH packet is being sent to
 * an AWS IoT MQTT server.
 * @param[in] pPublishInfo The #IotMqttPublishInfo_t to validate.
 *
 * @return `true` if `pPublishInfo` is valid; `false` otherwise.
 */
bool _IotMqtt_ValidatePublish( bool awsIotMqttMode,
                               const IotMqttPublishInfo_t * pPublishInfo );

/**
 * @brief Check that an #IotMqttPublishInfo_t is valid for an LWT publish
 *
 * @param[in] awsIotMqttMode Specifies if this PUBLISH packet is being sent to
 * an AWS IoT MQTT server.
 * @param[in] pLwtPublishInfo The #IotMqttPublishInfo_t to validate.
 *
 * @return `true` if `pLwtPublishInfo` is valid; `false` otherwise.
 */
bool _IotMqtt_ValidateLwtPublish( bool awsIotMqttMode,
                                  const IotMqttPublishInfo_t * pLwtPublishInfo );

/**
 * @brief Check that an #IotMqttOperation_t is valid and waitable.
 *
 * @param[in] operation The #IotMqttOperation_t to validate.
 *
 * @return `true` if `operation` is valid; `false` otherwise.
 */
bool _IotMqtt_ValidateOperation( IotMqttOperation_t operation );

/**
 * @brief Check that a list of #IotMqttSubscription_t is valid.
 *
 * @param[in] operation Either #IOT_MQTT_SUBSCRIBE or #IOT_MQTT_UNSUBSCRIBE.
 * Some parameters are not validated for #IOT_MQTT_UNSUBSCRIBE.
 * @param[in] awsIotMqttMode Specifies if this SUBSCRIBE packet is being sent to
 * an AWS IoT MQTT server.
 * @param[in] pListStart First element of the list to validate.
 * @param[in] listSize Number of elements in the subscription list.
 *
 * @return `true` if every element in the list is valid; `false` otherwise.
 */
bool _IotMqtt_ValidateSubscriptionList( IotMqttOperationType_t operation,
                                        bool awsIotMqttMode,
                                        const IotMqttSubscription_t * pListStart,
                                        size_t listSize );

/*-------------------- MQTT packet serializer functions ---------------------*/

/**
 * @brief Get the MQTT packet type from a stream of bytes off the network.
 *
 * @param[in] pNetworkConnection Reference to the network connection.
 * @param[in] pNetworkInterface Function pointers used to interact with the
 * network.
 *
 * @return One of the server-to-client MQTT packet types.
 *
 * @note This function is only used for incoming packets, and may not work
 * correctly for outgoing packets.
 */
uint8_t _IotMqtt_GetPacketType( void * pNetworkConnection,
                                const IotNetworkInterface_t * pNetworkInterface );

/**
 * @brief Get the remaining length from a stream of bytes off the network.
 *
 * @param[in] pNetworkConnection Reference to the network connection.
 * @param[in] pNetworkInterface Function pointers used to interact with the
 * network.
 *
 * @return The remaining length; #MQTT_REMAINING_LENGTH_INVALID on error.
 */
size_t _IotMqtt_GetRemainingLength( void * pNetworkConnection,
                                    const IotNetworkInterface_t * pNetworkInterface );

/**
 * @brief Get the remaining length from a stream of bytes off the network.
 *
 * @param[in] pNetworkConnection Reference to the network connection.
 * @param[in] getNextByte Function pointer used to interact with the
 * network to get next byte.
 *
 * @return The remaining length; #MQTT_REMAINING_LENGTH_INVALID on error.
 *
 * @note This function is similar to _IotMqtt_GetRemainingLength() but it uses
 * user provided getNextByte function to parse the stream instead of using
 * _IotMqtt_GetNextByte(). pNetworkConnection is implementation dependent and
 * user provided function makes use of it.
 *
 */
size_t _IotMqtt_GetRemainingLength_Generic( void * pNetworkConnection,
                                            IotMqttGetNextByte_t getNextByte );

/**
 * @brief Generate a CONNECT packet from the given parameters.
 *
 * @param[in] pConnectInfo User-provided CONNECT information.
 * @param[out] pConnectPacket Where the CONNECT packet is written.
 * @param[out] pPacketSize Size of the packet written to `pConnectPacket`.
 *
 * @return #IOT_MQTT_SUCCESS or #IOT_MQTT_NO_MEMORY.
 */
IotMqttError_t _IotMqtt_SerializeConnect( const IotMqttConnectInfo_t * pConnectInfo,
                                          uint8_t ** pConnectPacket,
                                          size_t * pPacketSize );

/**
 * @brief Deserialize a CONNACK packet.
 *
 * Converts the packet from a stream of bytes to an #IotMqttError_t. Also
 * prints out debug log messages about the packet.
 *
 * @param[in,out] pConnack Pointer to an MQTT packet struct representing a CONNACK.
 *
 * @return #IOT_MQTT_SUCCESS if CONNACK specifies that CONNECT was accepted;
 * #IOT_MQTT_SERVER_REFUSED if CONNACK specifies that CONNECT was rejected;
 * #IOT_MQTT_BAD_RESPONSE if the CONNACK packet doesn't follow MQTT spec.
 */
IotMqttError_t _IotMqtt_DeserializeConnack( _mqttPacket_t * pConnack );

/**
 * @brief Generate a PUBLISH packet from the given parameters.
 *
 * @param[in] pPublishInfo User-provided PUBLISH information.
 * @param[out] pPublishPacket Where the PUBLISH packet is written.
 * @param[out] pPacketSize Size of the packet written to `pPublishPacket`.
 * @param[out] pPacketIdentifier The packet identifier generated for this PUBLISH.
 * @param[out] pPacketIdentifierHigh Where the high byte of the packet identifier
 * is written.
 *
 * @return #IOT_MQTT_SUCCESS or #IOT_MQTT_NO_MEMORY.
 */
IotMqttError_t _IotMqtt_SerializePublish( const IotMqttPublishInfo_t * pPublishInfo,
                                          uint8_t ** pPublishPacket,
                                          size_t * pPacketSize,
                                          uint16_t * pPacketIdentifier,
                                          uint8_t ** pPacketIdentifierHigh );

/**
 * @brief Set the DUP bit in a QoS 1 PUBLISH packet.
 *
 * @param[in] pPublishPacket Pointer to the PUBLISH packet to modify.
 * @param[in] pPacketIdentifierHigh The high byte of any packet identifier to modify.
 * @param[out] pNewPacketIdentifier Since AWS IoT does not support the DUP flag,
 * a new packet identifier is generated and should be written here. This parameter
 * is only used when connected to an AWS IoT MQTT server.
 *
 * @note See #IotMqttPublishInfo_t for caveats with retransmission to the
 * AWS IoT MQTT server.
 */
void _IotMqtt_PublishSetDup( uint8_t * pPublishPacket,
                             uint8_t * pPacketIdentifierHigh,
                             uint16_t * pNewPacketIdentifier );

/**
 * @brief Deserialize a PUBLISH packet received from the server.
 *
 * Converts the packet from a stream of bytes to an #IotMqttPublishInfo_t and
 * extracts the packet identifier. Also prints out debug log messages about the
 * packet.
 *
 * @param[in,out] pPublish Pointer to an MQTT packet struct representing a PUBLISH.
 *
 * @return #IOT_MQTT_SUCCESS if PUBLISH is valid; #IOT_MQTT_BAD_RESPONSE
 * if the PUBLISH packet doesn't follow MQTT spec.
 */
IotMqttError_t _IotMqtt_DeserializePublish( _mqttPacket_t * pPublish );

/**
 * @brief Generate a PUBACK packet for the given packet identifier.
 *
 * @param[in] packetIdentifier The packet identifier to place in PUBACK.
 * @param[out] pPubackPacket Where the PUBACK packet is written.
 * @param[out] pPacketSize Size of the packet written to `pPubackPacket`.
 *
 * @return #IOT_MQTT_SUCCESS or #IOT_MQTT_NO_MEMORY.
 */
IotMqttError_t _IotMqtt_SerializePuback( uint16_t packetIdentifier,
                                         uint8_t ** pPubackPacket,
                                         size_t * pPacketSize );

/**
 * @brief Deserialize a PUBACK packet.
 *
 * Converts the packet from a stream of bytes to an #IotMqttError_t and extracts
 * the packet identifier. Also prints out debug log messages about the packet.
 *
 * @param[in,out] pPuback Pointer to an MQTT packet struct representing a PUBACK.
 *
 * @return #IOT_MQTT_SUCCESS if PUBACK is valid; #IOT_MQTT_BAD_RESPONSE
 * if the PUBACK packet doesn't follow MQTT spec.
 */
IotMqttError_t _IotMqtt_DeserializePuback( _mqttPacket_t * pPuback );

/**
 * @brief Generate a SUBSCRIBE packet from the given parameters.
 *
 * @param[in] pSubscriptionList User-provided array of subscriptions.
 * @param[in] subscriptionCount Size of `pSubscriptionList`.
 * @param[out] pSubscribePacket Where the SUBSCRIBE packet is written.
 * @param[out] pPacketSize Size of the packet written to `pSubscribePacket`.
 * @param[out] pPacketIdentifier The packet identifier generated for this SUBSCRIBE.
 *
 * @return #IOT_MQTT_SUCCESS or #IOT_MQTT_NO_MEMORY.
 */
IotMqttError_t _IotMqtt_SerializeSubscribe( const IotMqttSubscription_t * pSubscriptionList,
                                            size_t subscriptionCount,
                                            uint8_t ** pSubscribePacket,
                                            size_t * pPacketSize,
                                            uint16_t * pPacketIdentifier );

/**
 * @brief Deserialize a SUBACK packet.
 *
 * Converts the packet from a stream of bytes to an #IotMqttError_t and extracts
 * the packet identifier. Also prints out debug log messages about the packet.
 *
 * @param[in,out] pSuback Pointer to an MQTT packet struct representing a SUBACK.
 *
 * @return #IOT_MQTT_SUCCESS if SUBACK is valid; #IOT_MQTT_BAD_RESPONSE
 * if the SUBACK packet doesn't follow MQTT spec.
 */
IotMqttError_t _IotMqtt_DeserializeSuback( _mqttPacket_t * pSuback );

/**
 * @brief Generate an UNSUBSCRIBE packet from the given parameters.
 *
 * @param[in] pSubscriptionList User-provided array of subscriptions to remove.
 * @param[in] subscriptionCount Size of `pSubscriptionList`.
 * @param[out] pUnsubscribePacket Where the UNSUBSCRIBE packet is written.
 * @param[out] pPacketSize Size of the packet written to `pUnsubscribePacket`.
 * @param[out] pPacketIdentifier The packet identifier generated for this UNSUBSCRIBE.
 *
 * @return #IOT_MQTT_SUCCESS or #IOT_MQTT_NO_MEMORY.
 */
IotMqttError_t _IotMqtt_SerializeUnsubscribe( const IotMqttSubscription_t * pSubscriptionList,
                                              size_t subscriptionCount,
                                              uint8_t ** pUnsubscribePacket,
                                              size_t * pPacketSize,
                                              uint16_t * pPacketIdentifier );

/**
 * @brief Deserialize a UNSUBACK packet.
 *
 * Converts the packet from a stream of bytes to an #IotMqttError_t and extracts
 * the packet identifier. Also prints out debug log messages about the packet.
 *
 * @param[in,out] pUnsuback Pointer to an MQTT packet struct representing an UNSUBACK.
 *
 * @return #IOT_MQTT_SUCCESS if UNSUBACK is valid; #IOT_MQTT_BAD_RESPONSE
 * if the UNSUBACK packet doesn't follow MQTT spec.
 */
IotMqttError_t _IotMqtt_DeserializeUnsuback( _mqttPacket_t * pUnsuback );

/**
 * @brief Generate a PINGREQ packet.
 *
 * @param[out] pPingreqPacket Where the PINGREQ packet is written.
 * @param[out] pPacketSize Size of the packet written to `pPingreqPacket`.
 *
 * @return Always returns #IOT_MQTT_SUCCESS.
 */
IotMqttError_t _IotMqtt_SerializePingreq( uint8_t ** pPingreqPacket,
                                          size_t * pPacketSize );

/**
 * @brief Deserialize a PINGRESP packet.
 *
 * Converts the packet from a stream of bytes to an #IotMqttError_t. Also
 * prints out debug log messages about the packet.
 *
 * @param[in,out] pPingresp Pointer to an MQTT packet struct representing a PINGRESP.
 *
 * @return #IOT_MQTT_SUCCESS if PINGRESP is valid; #IOT_MQTT_BAD_RESPONSE
 * if the PINGRESP packet doesn't follow MQTT spec.
 */
IotMqttError_t _IotMqtt_DeserializePingresp( _mqttPacket_t * pPingresp );

/**
 * @brief Generate a DISCONNECT packet.
 *
 * @param[out] pDisconnectPacket Where the DISCONNECT packet is written.
 * @param[out] pPacketSize Size of the packet written to `pDisconnectPacket`.
 *
 * @return Always returns #IOT_MQTT_SUCCESS.
 */
IotMqttError_t _IotMqtt_SerializeDisconnect( uint8_t ** pDisconnectPacket,
                                             size_t * pPacketSize );

/**
 * @brief Free a packet generated by the serializer.
 *
 * @param[in] pPacket The packet to free.
 */
void _IotMqtt_FreePacket( uint8_t * pPacket );

/*-------------------- MQTT operation record functions ----------------------*/

/**
 * @brief Create a record for a new in-progress MQTT operation.
 *
 * @param[in] pMqttConnection The MQTT connection to associate with the operation.
 * @param[in] flags Flags variable passed to a user-facing MQTT function.
 * @param[in] pCallbackInfo User-provided callback function and parameter.
 * @param[out] pNewOperation Set to point to the new operation on success.
 *
 * @return #IOT_MQTT_SUCCESS, #IOT_MQTT_BAD_PARAMETER, or #IOT_MQTT_NO_MEMORY.
 */
IotMqttError_t _IotMqtt_CreateOperation( _mqttConnection_t * pMqttConnection,
                                         uint32_t flags,
                                         const IotMqttCallbackInfo_t * pCallbackInfo,
                                         _mqttOperation_t ** pNewOperation );

/**
 * @brief Decrement the job reference count of an MQTT operation and optionally
 * cancel its job.
 *
 * Checks if the operation may be destroyed afterwards.
 *
 * @param[in] pOperation The MQTT operation with the job to cancel.
 * @param[in] cancelJob Whether to attempt cancellation of the operation's job.
 *
 * @return `true` if the the operation may be safely destroyed; `false` otherwise.
 */
bool _IotMqtt_DecrementOperationReferences( _mqttOperation_t * pOperation,
                                            bool cancelJob );

/**
 * @brief Free resources used to record an MQTT operation. This is called when
 * the operation completes.
 *
 * @param[in] pOperation The operation which completed.
 */
void _IotMqtt_DestroyOperation( _mqttOperation_t * pOperation );

/**
 * @brief Task pool routine for processing an MQTT connection's keep-alive.
 *
 * @param[in] pTaskPool Pointer to the system task pool.
 * @param[in] pKeepAliveJob Pointer the an MQTT connection's keep-alive job.
 * @param[in] pContext Pointer to an MQTT connection, passed as an opaque context.
 */
void _IotMqtt_ProcessKeepAlive( IotTaskPool_t pTaskPool,
                                IotTaskPoolJob_t pKeepAliveJob,
                                void * pContext );

/**
 * @brief Task pool routine for processing an incoming PUBLISH message.
 *
 * @param[in] pTaskPool Pointer to the system task pool.
 * @param[in] pPublishJob Pointer to the incoming PUBLISH operation's job.
 * @param[in] pContext Pointer to the incoming PUBLISH operation, passed as an
 * opaque context.
 */
void _IotMqtt_ProcessIncomingPublish( IotTaskPool_t pTaskPool,
                                      IotTaskPoolJob_t pPublishJob,
                                      void * pContext );

/**
 * @brief Task pool routine for processing an MQTT operation to send.
 *
 * @param[in] pTaskPool Pointer to the system task pool.
 * @param[in] pSendJob Pointer to an operation's job.
 * @param[in] pContext Pointer to the operation to send, passed as an opaque
 * context.
 */
void _IotMqtt_ProcessSend( IotTaskPool_t pTaskPool,
                           IotTaskPoolJob_t pSendJob,
                           void * pContext );

/**
 * @brief Task pool routine for processing a completed MQTT operation.
 *
 * @param[in] pTaskPool Pointer to the system task pool.
 * @param[in] pOperationJob Pointer to the completed operation's job.
 * @param[in] pContext Pointer to the completed operation, passed as an opaque
 * context.
 */
void _IotMqtt_ProcessCompletedOperation( IotTaskPool_t pTaskPool,
                                         IotTaskPoolJob_t pOperationJob,
                                         void * pContext );

/**
 * @brief Schedule an operation for immediate processing.
 *
 * @param[in] pOperation The operation to schedule.
 * @param[in] jobRoutine The routine to run for the job. Must be either
 * #_IotMqtt_ProcessSend, #_IotMqtt_ProcessCompletedOperation, or
 * #_IotMqtt_ProcessIncomingPublish.
 * @param[in] delay A delay before the operation job should be executed. Pass
 * `0` to execute ASAP.
 *
 * @return #IOT_MQTT_SUCCESS or #IOT_MQTT_SCHEDULING_ERROR.
 */
IotMqttError_t _IotMqtt_ScheduleOperation( _mqttOperation_t * pOperation,
                                           IotTaskPoolRoutine_t jobRoutine,
                                           uint32_t delay );

/**
 * @brief Search a list of MQTT operations pending responses using an operation
 * name and packet identifier. Removes a matching operation from the list if found.
 *
 * @param[in] pMqttConnection The connection associated with the operation.
 * @param[in] type The operation type to look for.
 * @param[in] pPacketIdentifier A packet identifier to match. Pass `NULL` to ignore.
 *
 * @return Pointer to any matching operation; `NULL` if no match was found.
 */
_mqttOperation_t * _IotMqtt_FindOperation( _mqttConnection_t * pMqttConnection,
                                           IotMqttOperationType_t type,
                                           const uint16_t * pPacketIdentifier );

/**
 * @brief Notify of a completed MQTT operation.
 *
 * @param[in] pOperation The MQTT operation which completed.
 *
 * Depending on the parameters passed to a user-facing MQTT function, the
 * notification will cause @ref mqtt_function_wait to return or invoke a
 * user-provided callback.
 */
void _IotMqtt_Notify( _mqttOperation_t * pOperation );

/*----------------- MQTT subscription management functions ------------------*/

/**
 * @brief Add an array of subscriptions to the subscription manager.
 *
 * @param[in] pMqttConnection The MQTT connection associated with the subscriptions.
 * @param[in] subscribePacketIdentifier Packet identifier for the subscriptions'
 * SUBSCRIBE packet.
 * @param[in] pSubscriptionList The first element in the array.
 * @param[in] subscriptionCount Number of elements in `pSubscriptionList`.
 *
 * @return #IOT_MQTT_SUCCESS or #IOT_MQTT_NO_MEMORY.
 */
IotMqttError_t _IotMqtt_AddSubscriptions( _mqttConnection_t * pMqttConnection,
                                          uint16_t subscribePacketIdentifier,
                                          const IotMqttSubscription_t * pSubscriptionList,
                                          size_t subscriptionCount );

/**
 * @brief Process a received PUBLISH from the server, invoking any subscription
 * callbacks that have a matching topic filter.
 *
 * @param[in] pMqttConnection The MQTT connection associated with the received
 * PUBLISH.
 * @param[in] pCallbackParam The parameter to pass to a PUBLISH callback.
 */
void _IotMqtt_InvokeSubscriptionCallback( _mqttConnection_t * pMqttConnection,
                                          IotMqttCallbackParam_t * pCallbackParam );

/**
 * @brief Remove a single subscription from the subscription manager by
 * packetIdentifier and order.
 *
 * @param[in] pMqttConnection The MQTT connection associated with the subscriptions.
 * @param[in] packetIdentifier The packet identifier associated with the subscription's
 * SUBSCRIBE packet.
 * @param[in] order The order of the subscription in the SUBSCRIBE packet.
 * Pass #MQTT_REMOVE_ALL_SUBSCRIPTIONS to ignore order and remove all subscriptions for `packetIdentifier`.
 */
void _IotMqtt_RemoveSubscriptionByPacket( _mqttConnection_t * pMqttConnection,
                                          uint16_t packetIdentifier,
                                          int32_t order );

/**
 * @brief Remove an array of subscriptions from the subscription manager by
 * topic filter.
 *
 * @param[in] pMqttConnection The MQTT connection associated with the subscriptions.
 * @param[in] pSubscriptionList The first element in the array.
 * @param[in] subscriptionCount Number of elements in `pSubscriptionList`.
 */
void _IotMqtt_RemoveSubscriptionByTopicFilter( _mqttConnection_t * pMqttConnection,
                                               const IotMqttSubscription_t * pSubscriptionList,
                                               size_t subscriptionCount );

/*------------------ MQTT connection management functions -------------------*/

/**
 * @brief Attempt to increment the reference count of an MQTT connection.
 *
 * @param[in] pMqttConnection The referenced MQTT connection.
 *
 * @return `true` if the reference count was incremented; `false` otherwise. The
 * reference count will not be incremented for a disconnected connection.
 */
bool _IotMqtt_IncrementConnectionReferences( _mqttConnection_t * pMqttConnection );

/**
 * @brief Decrement the reference count of an MQTT connection.
 *
 * Also destroys an unreferenced MQTT connection.
 *
 * @param[in] pMqttConnection The referenced MQTT connection.
 */
void _IotMqtt_DecrementConnectionReferences( _mqttConnection_t * pMqttConnection );

/**
 * @brief Read the next available byte on a network connection.
 *
 * @param[in] pNetworkConnection Reference to the network connection.
 * @param[in] pNetworkInterface Function pointers used to interact with the
 * network.
 * @param[out] pIncomingByte The byte read from the network.
 *
 * @return `true` if a byte was successfully received from the network; `false`
 * otherwise.
 */
bool _IotMqtt_GetNextByte( void * pNetworkConnection,
                           const IotNetworkInterface_t * pNetworkInterface,
                           uint8_t * pIncomingByte );

/**
 * @brief Closes the network connection associated with an MQTT connection.
 *
 * A network disconnect function must be set in the network interface for the
 * network connection to be closed.
 *
 * @param[in] disconnectReason A reason to pass to the connection's disconnect
 * callback.
 * @param[in] pMqttConnection The MQTT connection with the network connection
 * to close.
 */
void _IotMqtt_CloseNetworkConnection( IotMqttDisconnectReason_t disconnectReason,
                                      _mqttConnection_t * pMqttConnection );

#if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1

/**
 * @brief Utility macro for creating serializer override selector functions
 */
    #define _SERIALIZER_OVERRIDE_SELECTOR( _funcType_t, _funcName, _defaultFunc, _serializerMember ) \
    static _funcType_t _funcName( const IotMqttSerializer_t * pSerializer );                         \
    static _funcType_t _funcName( const IotMqttSerializer_t * pSerializer )                          \
    {                                                                                                \
        _funcType_t _returnValue = _defaultFunc;                                                     \
        if( pSerializer != NULL )                                                                    \
        {                                                                                            \
            if( pSerializer->_serializerMember != NULL )                                             \
            {                                                                                        \
                _returnValue = pSerializer->_serializerMember;                                       \
            }                                                                                        \
            else                                                                                     \
            {                                                                                        \
                EMPTY_ELSE_MARKER;                                                                   \
            }                                                                                        \
        }                                                                                            \
        else                                                                                         \
        {                                                                                            \
            EMPTY_ELSE_MARKER;                                                                       \
        }                                                                                            \
        return _returnValue;                                                                         \
    }
#endif /* if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1 */

#endif /* ifndef IOT_MQTT_INTERNAL_H_ */
