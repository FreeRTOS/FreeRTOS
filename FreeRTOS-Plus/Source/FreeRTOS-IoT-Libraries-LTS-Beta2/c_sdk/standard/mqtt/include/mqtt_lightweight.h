/*
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
 */

/**
 * @file mqtt_lightweight.h
 * @brief User-facing functions for serializing and deserializing MQTT 3.1.1
 * packets. This header should be included for building a lightweight MQTT
 * client bypassing the managed CSDK MQTT library API in mqtt.h.
 */
#ifndef MQTT_LIGHTWEIGHT_H
#define MQTT_LIGHTWEIGHT_H

#include <stddef.h>
#include <stdint.h>

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this section.
 */

/* bool is defined in only C99+. */
#if defined( __cplusplus ) || ( defined( __STDC_VERSION__ ) && ( __STDC_VERSION__ >= 199901L ) )
    #include <stdbool.h>
#elif !defined( bool )
    #define bool     int8_t
    #define false    ( int8_t ) 0
    #define true     ( int8_t ) 1
#endif
/** @endcond */

/* Include config file before other headers. */
#include "mqtt_config.h"

#include "transport_interface.h"

/* MQTT packet types. */
#define MQTT_PACKET_TYPE_CONNECT        ( ( uint8_t ) 0x10U )  /**< @brief CONNECT (client-to-server). */
#define MQTT_PACKET_TYPE_CONNACK        ( ( uint8_t ) 0x20U )  /**< @brief CONNACK (server-to-client). */
#define MQTT_PACKET_TYPE_PUBLISH        ( ( uint8_t ) 0x30U )  /**< @brief PUBLISH (bidirectional). */
#define MQTT_PACKET_TYPE_PUBACK         ( ( uint8_t ) 0x40U )  /**< @brief PUBACK (bidirectional). */
#define MQTT_PACKET_TYPE_PUBREC         ( ( uint8_t ) 0x50U )  /**< @brief PUBREC (bidirectional). */
#define MQTT_PACKET_TYPE_PUBREL         ( ( uint8_t ) 0x62U )  /**< @brief PUBREL (bidirectional). */
#define MQTT_PACKET_TYPE_PUBCOMP        ( ( uint8_t ) 0x70U )  /**< @brief PUBCOMP (bidirectional). */
#define MQTT_PACKET_TYPE_SUBSCRIBE      ( ( uint8_t ) 0x82U )  /**< @brief SUBSCRIBE (client-to-server). */
#define MQTT_PACKET_TYPE_SUBACK         ( ( uint8_t ) 0x90U )  /**< @brief SUBACK (server-to-client). */
#define MQTT_PACKET_TYPE_UNSUBSCRIBE    ( ( uint8_t ) 0xA2U )  /**< @brief UNSUBSCRIBE (client-to-server). */
#define MQTT_PACKET_TYPE_UNSUBACK       ( ( uint8_t ) 0xB0U )  /**< @brief UNSUBACK (server-to-client). */
#define MQTT_PACKET_TYPE_PINGREQ        ( ( uint8_t ) 0xC0U )  /**< @brief PINGREQ (client-to-server). */
#define MQTT_PACKET_TYPE_PINGRESP       ( ( uint8_t ) 0xD0U )  /**< @brief PINGRESP (server-to-client). */
#define MQTT_PACKET_TYPE_DISCONNECT     ( ( uint8_t ) 0xE0U )  /**< @brief DISCONNECT (client-to-server). */

/**
 * @brief The size of MQTT PUBACK, PUBREC, PUBREL, and PUBCOMP packets, per MQTT spec.
 */
#define MQTT_PUBLISH_ACK_PACKET_SIZE    ( 4UL )

/* Structures defined in this file. */
struct MQTTFixedBuffer;
struct MQTTConnectInfo;
struct MQTTSubscribeInfo;
struct MQTTPublishInfo;
struct MQTTPacketInfo;

/**
 * @brief Return codes from MQTT functions.
 */
typedef enum MQTTStatus
{
    MQTTSuccess = 0,     /**< Function completed successfully. */
    MQTTBadParameter,    /**< At least one parameter was invalid. */
    MQTTNoMemory,        /**< A provided buffer was too small. */
    MQTTSendFailed,      /**< The transport send function failed. */
    MQTTRecvFailed,      /**< The transport receive function failed. */
    MQTTBadResponse,     /**< An invalid packet was received from the server. */
    MQTTServerRefused,   /**< The server refused a CONNECT or SUBSCRIBE. */
    MQTTNoDataAvailable, /**< No data available from the transport interface. */
    MQTTIllegalState,    /**< An illegal state in the state record. */
    MQTTStateCollision,  /**< A collision with an existing state record entry. */
    MQTTKeepAliveTimeout /**< Timeout while waiting for PINGRESP. */
} MQTTStatus_t;

/**
 * @brief MQTT Quality of Service values.
 */
typedef enum MQTTQoS
{
    MQTTQoS0 = 0, /**< Delivery at most once. */
    MQTTQoS1 = 1, /**< Delivery at least once. */
    MQTTQoS2 = 2  /**< Delivery exactly once. */
} MQTTQoS_t;

/**
 * @brief Buffer passed to MQTT library.
 *
 * These buffers are not copied and must remain in scope for the duration of the
 * MQTT operation.
 */
typedef struct MQTTFixedBuffer
{
    uint8_t * pBuffer; /**< @brief Pointer to buffer. */
    size_t size;       /**< @brief Size of buffer. */
} MQTTFixedBuffer_t;

/**
 * @brief MQTT CONNECT packet parameters.
 */
typedef struct MQTTConnectInfo
{
    /**
     * @brief Whether to establish a new, clean session or resume a previous session.
     */
    bool cleanSession;

    /**
     * @brief MQTT keep alive period.
     */
    uint16_t keepAliveSeconds;

    /**
     * @brief MQTT client identifier. Must be unique per client.
     */
    const char * pClientIdentifier;

    /**
     * @brief Length of the client identifier.
     */
    uint16_t clientIdentifierLength;

    /**
     * @brief MQTT user name. Set to NULL if not used.
     */
    const char * pUserName;

    /**
     * @brief Length of MQTT user name. Set to 0 if not used.
     */
    uint16_t userNameLength;

    /**
     * @brief MQTT password. Set to NULL if not used.
     */
    const char * pPassword;

    /**
     * @brief Length of MQTT password. Set to 0 if not used.
     */
    uint16_t passwordLength;
} MQTTConnectInfo_t;

/**
 * @brief MQTT SUBSCRIBE packet parameters.
 */
typedef struct MQTTSubscribeInfo
{
    /**
     * @brief Quality of Service for subscription.
     */
    MQTTQoS_t qos;

    /**
     * @brief Topic filter to subscribe to.
     */
    const char * pTopicFilter;

    /**
     * @brief Length of subscription topic filter.
     */
    uint16_t topicFilterLength;
} MQTTSubscribeInfo_t;

/**
 * @brief MQTT PUBLISH packet parameters.
 */
typedef struct MQTTPublishInfo
{
    /**
     * @brief Quality of Service for message.
     */
    MQTTQoS_t qos;

    /**
     * @brief Whether this is a retained message.
     */
    bool retain;

    /**
     * @brief Whether this is a duplicate publish message.
     */
    bool dup;

    /**
     * @brief Topic name on which the message is published.
     */
    const char * pTopicName;

    /**
     * @brief Length of topic name.
     */
    uint16_t topicNameLength;

    /**
     * @brief Message payload.
     */
    const void * pPayload;

    /**
     * @brief Message payload length.
     */
    size_t payloadLength;
} MQTTPublishInfo_t;

/**
 * @brief MQTT incoming packet parameters.
 */
typedef struct MQTTPacketInfo
{
    /**
     * @brief Type of incoming MQTT packet.
     */
    uint8_t type;

    /**
     * @brief Remaining serialized data in the MQTT packet.
     */
    uint8_t * pRemainingData;

    /**
     * @brief Length of remaining serialized data.
     */
    size_t remainingLength;
} MQTTPacketInfo_t;

/**
 * @brief Get the size and Remaining Length of an MQTT CONNECT packet.
 *
 * This function must be called before #MQTT_SerializeConnect in order to get
 * the size of the MQTT CONNECT packet that is generated from #MQTTConnectInfo_t
 * and optional #MQTTPublishInfo_t. The size of the #MQTTFixedBuffer_t supplied
 * to #MQTT_SerializeConnect must be at least @p pPacketSize. The provided
 * @p pConnectInfo and @p pWillInfo are valid for serialization with
 * #MQTT_SerializeConnect only if this function returns #MQTTSuccess. The
 * remaining length returned in @p pRemainingLength and the packet size returned
 * in @p pPacketSize are valid only if this function returns #MQTTSuccess.
 *
 * @param[in] pConnectInfo MQTT CONNECT packet parameters.
 * @param[in] pWillInfo Last Will and Testament. Pass NULL if not used.
 * @param[out] pRemainingLength The Remaining Length of the MQTT CONNECT packet.
 * @param[out] pPacketSize The total size of the MQTT CONNECT packet.
 *
 * @return #MQTTBadParameter if the packet would exceed the size allowed by the
 * MQTT spec; #MQTTSuccess otherwise.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * MQTTConnectInfo_t connectInfo = { 0 };
 * MQTTPublishInfo_t willInfo = { 0 };
 * size_t remainingLength = 0, packetSize = 0;
 *
 * // Initialize the connection info, the details are out of scope for this example.
 * initializeConnectInfo( &connectInfo );
 *
 * // Initialize the optional will info, the details are out of scope for this example.
 * initializeWillInfo( &willInfo );
 *
 * // Get the size requirement for the connect packet.
 * status = MQTT_GetConnectPacketSize(
 *      &connectInfo, &willInfo, &remainingLength, &packetSize
 * );
 *
 * if( status == MQTTSuccess )
 * {
 *      // The application should allocate or use a static #MQTTFixedBuffer_t
 *      // of size >= packetSize to serialize the connect request.
 * }
 * @endcode
 */
MQTTStatus_t MQTT_GetConnectPacketSize( const MQTTConnectInfo_t * pConnectInfo,
                                        const MQTTPublishInfo_t * pWillInfo,
                                        size_t * pRemainingLength,
                                        size_t * pPacketSize );

/**
 * @brief Serialize an MQTT CONNECT packet in the given fixed buffer @p pFixedBuffer.
 *
 * #MQTT_GetConnectPacketSize should be called with @p pConnectInfo and
 * @p pWillInfo before invoking this function to get the size of the required
 * #MQTTFixedBuffer_t and @p remainingLength. The @p remainingLength must be
 * the same as returned by #MQTT_GetConnectPacketSize. The #MQTTFixedBuffer_t
 * must be at least as large as the size returned by #MQTT_GetConnectPacketSize.
 *
 * @param[in] pConnectInfo MQTT CONNECT packet parameters.
 * @param[in] pWillInfo Last Will and Testament. Pass NULL if not used.
 * @param[in] remainingLength Remaining Length provided by #MQTT_GetConnectPacketSize.
 * @param[out] pFixedBuffer Buffer for packet serialization.
 *
 * @return #MQTTNoMemory if pFixedBuffer is too small to hold the MQTT packet;
 * #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSuccess otherwise.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * MQTTConnectInfo_t connectInfo = { 0 };
 * MQTTPublishInfo_t willInfo = { 0 };
 * MQTTFixedBuffer_t fixedBuffer;
 * uint8_t buffer[ BUFFER_SIZE ];
 * size_t remainingLength = 0, packetSize = 0;
 *
 * fixedBuffer.pBuffer = buffer;
 * fixedBuffer.size = BUFFER_SIZE;
 *
 * // Assume connectInfo and willInfo are initialized. Get the size requirement for
 * // the connect packet.
 * status = MQTT_GetConnectPacketSize(
 *      &connectInfo, &willInfo, &remainingLength, &packetSize
 * );
 * assert( status == MQTTSuccess );
 * assert( packetSize <= BUFFER_SIZE );
 *
 * // Serialize the connect packet into the fixed buffer.
 * status = MQTT_SerializeConnect( &connectInfo, &willInfo, remainingLength, &fixedBuffer );
 *
 * if( status == MQTTSuccess )
 * {
 *      // The connect packet can now be sent to the broker.
 * }
 * @endcode
 */
MQTTStatus_t MQTT_SerializeConnect( const MQTTConnectInfo_t * pConnectInfo,
                                    const MQTTPublishInfo_t * pWillInfo,
                                    size_t remainingLength,
                                    const MQTTFixedBuffer_t * pFixedBuffer );

/**
 * @brief Get packet size and Remaining Length of an MQTT SUBSCRIBE packet.
 *
 * This function must be called before #MQTT_SerializeSubscribe in order to get
 * the size of the MQTT SUBSCRIBE packet that is generated from the list of
 * #MQTTSubscribeInfo_t. The size of the #MQTTFixedBuffer_t supplied
 * to #MQTT_SerializeSubscribe must be at least @p pPacketSize. The provided
 * @p pSubscriptionList is valid for serialization with #MQTT_SerializeSubscribe
 * only if this function returns #MQTTSuccess. The remaining length returned in
 * @p pRemainingLength and the packet size returned in @p pPacketSize are valid
 * only if this function returns #MQTTSuccess.
 *
 * @param[in] pSubscriptionList List of MQTT subscription info.
 * @param[in] subscriptionCount The number of elements in pSubscriptionList.
 * @param[out] pRemainingLength The Remaining Length of the MQTT SUBSCRIBE packet.
 * @param[out] pPacketSize The total size of the MQTT SUBSCRIBE packet.
 *
 * @return #MQTTBadParameter if the packet would exceed the size allowed by the
 * MQTT spec; #MQTTSuccess otherwise.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * MQTTSubscribeInfo_t subscriptionList[ NUMBER_OF_SUBSCRIPTIONS ] = { 0 };
 * size_t remainingLength = 0, packetSize = 0;
 * // This is assumed to be a list of filters we want to subscribe to.
 * const char * filters[ NUMBER_OF_SUBSCRIPTIONS ];
 *
 * // Set each subscription.
 * for( int i = 0; i < NUMBER_OF_SUBSCRIPTIONS; i++ )
 * {
 *      subscriptionList[ i ].qos = MQTTQoS0;
 *      // Each subscription needs a topic filter.
 *      subscriptionList[ i ].pTopicFilter = filters[ i ];
 *      subscriptionList[ i ].topicFilterLength = strlen( filters[ i ] );
 * }
 *
 * // Get the size requirement for the subscribe packet.
 * status = MQTT_GetSubscribePacketSize(
 *      &subscriptionList[ 0 ], NUMBER_OF_SUBSCRIPTIONS, &remainingLength, &packetSize
 * );
 *
 * if( status == MQTTSuccess )
 * {
 *      // The application should allocate or use a static #MQTTFixedBuffer_t
 *      // of size >= packetSize to serialize the subscribe request.
 * }
 * @endcode
 */
MQTTStatus_t MQTT_GetSubscribePacketSize( const MQTTSubscribeInfo_t * pSubscriptionList,
                                          size_t subscriptionCount,
                                          size_t * pRemainingLength,
                                          size_t * pPacketSize );

/**
 * @brief Serialize an MQTT SUBSCRIBE packet in the given buffer.
 *
 * #MQTT_GetSubscribePacketSize should be called with @p pSubscriptionList
 * before invoking this function to get the size of the required
 * #MQTTFixedBuffer_t and @p remainingLength. The @p remainingLength must be
 * the same as returned by #MQTT_GetSubscribePacketSize. The #MQTTFixedBuffer_t
 * must be at least as large as the size returned by #MQTT_GetSubscribePacketSize.
 *
 * @param[in] pSubscriptionList List of MQTT subscription info.
 * @param[in] subscriptionCount The number of elements in pSubscriptionList.
 * @param[in] packetId packet ID generated by #MQTT_GetPacketId.
 * @param[in] remainingLength Remaining Length provided by #MQTT_GetSubscribePacketSize.
 * @param[out] pFixedBuffer Buffer for packet serialization.
 *
 * @return #MQTTNoMemory if pFixedBuffer is too small to hold the MQTT packet;
 * #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSuccess otherwise.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * MQTTSubscribeInfo_t subscriptionList[ NUMBER_OF_SUBSCRIPTIONS ] = { 0 };
 * MQTTFixedBuffer_t fixedBuffer;
 * uint8_t buffer[ BUFFER_SIZE ];
 * size_t remainingLength = 0, packetSize = 0;
 * uint16_t packetId;
 *
 * fixedBuffer.pBuffer = buffer;
 * fixedBuffer.size = BUFFER_SIZE;
 *
 * // Function to return a valid, unused packet identifier. The details are out of
 * // scope for this example.
 * packetId = getNewPacketId();
 *
 * // Assume subscriptionList has been initialized. Get the subscribe packet size.
 * status = MQTT_GetSubscribePacketSize(
 *      &subscriptionList[ 0 ], NUMBER_OF_SUBSCRIPTIONS, &remainingLength, &packetSize
 * );
 * assert( status == MQTTSuccess );
 * assert( packetSize <= BUFFER_SIZE );
 *
 * // Serialize the subscribe packet into the fixed buffer.
 * status = MQTT_SerializeSubscribe(
 *      &subscriptionList[ 0 ],
 *      NUMBER_OF_SUBSCRIPTIONS,
 *      packetId,
 *      remainingLength,
 *      &fixedBuffer
 * );
 *
 * if( status == MQTTSuccess )
 * {
 *      // The subscribe packet can now be sent to the broker.
 * }
 * @endcode
 */
MQTTStatus_t MQTT_SerializeSubscribe( const MQTTSubscribeInfo_t * pSubscriptionList,
                                      size_t subscriptionCount,
                                      uint16_t packetId,
                                      size_t remainingLength,
                                      const MQTTFixedBuffer_t * pFixedBuffer );

/**
 * @brief Get packet size and Remaining Length of an MQTT UNSUBSCRIBE packet.
 *
 * This function must be called before #MQTT_SerializeUnsubscribe in order to
 * get the size of the MQTT UNSUBSCRIBE packet that is generated from the list
 * of #MQTTSubscribeInfo_t. The size of the #MQTTFixedBuffer_t supplied
 * to #MQTT_SerializeUnsubscribe must be at least @p pPacketSize. The provided
 * @p pSubscriptionList is valid for serialization with #MQTT_SerializeUnsubscribe
 * only if this function returns #MQTTSuccess. The remaining length returned in
 * @p pRemainingLength and the packet size returned in @p pPacketSize are valid
 * only if this function returns #MQTTSuccess.
 *
 * @param[in] pSubscriptionList List of MQTT subscription info.
 * @param[in] subscriptionCount The number of elements in pSubscriptionList.
 * @param[out] pRemainingLength The Remaining Length of the MQTT UNSUBSCRIBE packet.
 * @param[out] pPacketSize The total size of the MQTT UNSUBSCRIBE packet.
 *
 * @return #MQTTBadParameter if the packet would exceed the size allowed by the
 * MQTT spec; #MQTTSuccess otherwise.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * MQTTSubscribeInfo_t subscriptionList[ NUMBER_OF_SUBSCRIPTIONS ] = { 0 };
 * size_t remainingLength = 0, packetSize = 0;
 *
 * // Initialize the subscribe info. The details are out of scope for this example.
 * initializeSubscribeInfo( &subscriptionList[ 0 ] );
 *
 * // Get the size requirement for the unsubscribe packet.
 * status = MQTT_GetUnsubscribePacketSize(
 *      &subscriptionList[ 0 ], NUMBER_OF_SUBSCRIPTIONS, &remainingLength, &packetSize
 * );
 *
 * if( status == MQTTSuccess )
 * {
 *      // The application should allocate or use a static #MQTTFixedBuffer_t
 *      // of size >= packetSize to serialize the unsubscribe request.
 * }
 * @endcode
 */
MQTTStatus_t MQTT_GetUnsubscribePacketSize( const MQTTSubscribeInfo_t * pSubscriptionList,
                                            size_t subscriptionCount,
                                            size_t * pRemainingLength,
                                            size_t * pPacketSize );

/**
 * @brief Serialize an MQTT UNSUBSCRIBE packet in the given buffer.
 *
 * #MQTT_GetUnsubscribePacketSize should be called with @p pSubscriptionList
 * before invoking this function to get the size of the required
 * #MQTTFixedBuffer_t and @p remainingLength. The @p remainingLength must be
 * the same as returned by #MQTT_GetUnsubscribePacketSize. The #MQTTFixedBuffer_t
 * must be at least as large as the size returned by #MQTT_GetUnsubscribePacketSize.
 *
 * @param[in] pSubscriptionList List of MQTT subscription info.
 * @param[in] subscriptionCount The number of elements in pSubscriptionList.
 * @param[in] packetId packet ID generated by #MQTT_GetPacketId.
 * @param[in] remainingLength Remaining Length provided by #MQTT_GetUnsubscribePacketSize.
 * @param[out] pFixedBuffer Buffer for packet serialization.
 *
 * @return #MQTTNoMemory if pFixedBuffer is too small to hold the MQTT packet;
 * #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSuccess otherwise.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * MQTTSubscribeInfo_t subscriptionList[ NUMBER_OF_SUBSCRIPTIONS ] = { 0 };
 * MQTTFixedBuffer_t fixedBuffer;
 * uint8_t buffer[ BUFFER_SIZE ];
 * size_t remainingLength = 0, packetSize = 0;
 * uint16_t packetId;
 *
 * fixedBuffer.pBuffer = buffer;
 * fixedBuffer.size = BUFFER_SIZE;
 *
 * // Function to return a valid, unused packet identifier. The details are out of
 * // scope for this example.
 * packetId = getNewPacketId();
 *
 * // Assume subscriptionList has been initialized. Get the unsubscribe packet size.
 * status = MQTT_GetUnsubscribePacketSize(
 *      &subscriptionList[ 0 ], NUMBER_OF_SUBSCRIPTIONS, &remainingLength, &packetSize
 * );
 * assert( status == MQTTSuccess );
 * assert( packetSize <= BUFFER_SIZE );
 *
 * // Serialize the unsubscribe packet into the fixed buffer.
 * status = MQTT_SerializeUnsubscribe(
 *      &subscriptionList[ 0 ],
 *      NUMBER_OF_SUBSCRIPTIONS,
 *      packetId,
 *      remainingLength,
 *      &fixedBuffer
 * );
 *
 * if( status == MQTTSuccess )
 * {
 *      // The unsubscribe packet can now be sent to the broker.
 * }
 * @endcode
 */
MQTTStatus_t MQTT_SerializeUnsubscribe( const MQTTSubscribeInfo_t * pSubscriptionList,
                                        size_t subscriptionCount,
                                        uint16_t packetId,
                                        size_t remainingLength,
                                        const MQTTFixedBuffer_t * pFixedBuffer );

/**
 * @brief Get the packet size and remaining length of an MQTT PUBLISH packet.
 *
 * This function must be called before #MQTT_SerializePublish in order to get
 * the size of the MQTT PUBLISH packet that is generated from #MQTTPublishInfo_t.
 * The size of the #MQTTFixedBuffer_t supplied to #MQTT_SerializePublish must be
 * at least @p pPacketSize. The provided @p pPublishInfo is valid for
 * serialization with #MQTT_SerializePublish only if this function returns
 * #MQTTSuccess. The remaining length returned in @p pRemainingLength and the
 * packet size returned in @p pPacketSize are valid only if this function
 * returns #MQTTSuccess.
 *
 * @param[in] pPublishInfo MQTT PUBLISH packet parameters.
 * @param[out] pRemainingLength The Remaining Length of the MQTT PUBLISH packet.
 * @param[out] pPacketSize The total size of the MQTT PUBLISH packet.
 *
 * @return #MQTTBadParameter if the packet would exceed the size allowed by the
 * MQTT spec or if invalid parameters are passed; #MQTTSuccess otherwise.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * MQTTPublishInfo_t publishInfo = { 0 };
 * size_t remainingLength = 0, packetSize = 0;
 *
 * // Initialize the publish info.
 * publishInfo.qos = MQTTQoS0;
 * publishInfo.pTopicName = "/some/topic/name";
 * publishInfo.topicNameLength = strlen( publishInfo.pTopicName );
 * publishInfo.pPayload = "Hello World!";
 * publishInfo.payloadLength = strlen( "Hello World!" );
 *
 * // Get the size requirement for the publish packet.
 * status = MQTT_GetPublishPacketSize(
 *      &publishInfo, &remainingLength, &packetSize
 * );
 *
 * if( status == MQTTSuccess )
 * {
 *      // The application should allocate or use a static #MQTTFixedBuffer_t
 *      // of size >= packetSize to serialize the publish.
 * }
 * @endcode
 */
MQTTStatus_t MQTT_GetPublishPacketSize( const MQTTPublishInfo_t * pPublishInfo,
                                        size_t * pRemainingLength,
                                        size_t * pPacketSize );

/**
 * @brief Serialize an MQTT PUBLISH packet in the given buffer.
 *
 * This function will serialize complete MQTT PUBLISH packet into
 * the given buffer. If the PUBLISH payload can be sent separately,
 * consider using #MQTT_SerializePublishHeader, which will serialize
 * only the PUBLISH header into the buffer.
 *
 * #MQTT_GetPublishPacketSize should be called with @p pPublishInfo before
 * invoking this function to get the size of the required #MQTTFixedBuffer_t and
 * @p remainingLength. The @p remainingLength must be the same as returned by
 * #MQTT_GetPublishPacketSize. The #MQTTFixedBuffer_t must be at least as large
 * as the size returned by #MQTT_GetPublishPacketSize.
 *
 * @param[in] pPublishInfo MQTT PUBLISH packet parameters.
 * @param[in] packetId packet ID generated by #MQTT_GetPacketId.
 * @param[in] remainingLength Remaining Length provided by #MQTT_GetPublishPacketSize.
 * @param[out] pFixedBuffer Buffer for packet serialization.
 *
 * @return #MQTTNoMemory if pFixedBuffer is too small to hold the MQTT packet;
 * #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSuccess otherwise.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * MQTTPublishInfo_t publishInfo = { 0 };
 * MQTTFixedBuffer_t fixedBuffer;
 * uint8_t buffer[ BUFFER_SIZE ];
 * size_t remainingLength = 0, packetSize = 0;
 * uint16_t packetId;
 *
 * fixedBuffer.pBuffer = buffer;
 * fixedBuffer.size = BUFFER_SIZE;
 *
 * // A packet identifier is unused for QoS 0 publishes. Otherwise, a valid, unused packet
 * // identifier must be used.
 * packetId = 0;
 *
 * // Assume publishInfo has been initialized. Get publish packet size.
 * status = MQTT_GetPublishPacketSize(
 *      &publishInfo, &remainingLength, &packetSize
 * );
 * assert( status == MQTTSuccess );
 * assert( packetSize <= BUFFER_SIZE );
 *
 * // Serialize the publish packet into the fixed buffer.
 * status = MQTT_SerializePublish(
 *      &publishInfo,
 *      packetId,
 *      remainingLength,
 *      &fixedBuffer
 * );
 *
 * if( status == MQTTSuccess )
 * {
 *      // The publish packet can now be sent to the broker.
 * }
 * @endcode
 */
MQTTStatus_t MQTT_SerializePublish( const MQTTPublishInfo_t * pPublishInfo,
                                    uint16_t packetId,
                                    size_t remainingLength,
                                    const MQTTFixedBuffer_t * pFixedBuffer );

/**
 * @brief Serialize an MQTT PUBLISH packet header in the given buffer.
 *
 * This function serializes PUBLISH header in to the given buffer. The payload
 * for PUBLISH will not be copied over to the buffer. This will help reduce
 * the memory needed for the buffer and avoid an unwanted copy operation of the
 * PUBLISH payload into the buffer. If the payload also would need to be part of
 * the serialized buffer, consider using #MQTT_SerializePublish.
 *
 * #MQTT_GetPublishPacketSize should be called with @p pPublishInfo before
 * invoking this function to get the size of the required #MQTTFixedBuffer_t and
 * @p remainingLength. The @p remainingLength must be the same as returned by
 * #MQTT_GetPublishPacketSize. The #MQTTFixedBuffer_t must be at least as large
 * as the size returned by #MQTT_GetPublishPacketSize.
 *
 * @param[in] pPublishInfo MQTT PUBLISH packet parameters.
 * @param[in] packetId packet ID generated by #MQTT_GetPacketId.
 * @param[in] remainingLength Remaining Length provided by #MQTT_GetPublishPacketSize.
 * @param[out] pFixedBuffer Buffer for packet serialization.
 * @param[out] pHeaderSize Size of the serialized MQTT PUBLISH header.
 *
 * @return #MQTTNoMemory if pFixedBuffer is too small to hold the MQTT packet;
 * #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSuccess otherwise.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * MQTTPublishInfo_t publishInfo = { 0 };
 * MQTTFixedBuffer_t fixedBuffer;
 * uint8_t buffer[ BUFFER_SIZE ];
 * size_t remainingLength = 0, packetSize = 0, headerSize = 0;
 * uint16_t packetId;
 * int32_t bytesSent;
 *
 * fixedBuffer.pBuffer = buffer;
 * fixedBuffer.size = BUFFER_SIZE;
 *
 * // A packet identifier is unused for QoS 0 publishes. Otherwise, a valid, unused packet
 * // identifier must be used.
 * packetId = 0;
 *
 * // Assume publishInfo has been initialized. Get the publish packet size.
 * status = MQTT_GetPublishPacketSize(
 *      &publishInfo, &remainingLength, &packetSize
 * );
 * assert( status == MQTTSuccess );
 * // The payload will not be serialized, so the the fixed buffer does not need to hold it.
 * assert( ( packetSize - publishInfo.payloadLength ) <= BUFFER_SIZE );
 *
 * // Serialize the publish packet header into the fixed buffer.
 * status = MQTT_SerializePublishHeader(
 *      &publishInfo,
 *      packetId,
 *      remainingLength,
 *      &fixedBuffer,
 *      &headerSize
 * );
 *
 * if( status == MQTTSuccess )
 * {
 *      // The publish header and payload can now be sent to the broker.
 *      // mqttSocket here is a socket descriptor created and connected to the MQTT
 *      // broker outside of this function.
 *      bytesSent = send( mqttSocket, ( void * ) fixedBuffer.pBuffer, headerSize, 0 );
 *      assert( bytesSent == headerSize );
 *      bytesSent = send( mqttSocket, publishInfo.pPayload, publishInfo.payloadLength, 0 );
 *      assert( bytesSent == publishInfo.payloadLength );
 * }
 * @endcode
 */
MQTTStatus_t MQTT_SerializePublishHeader( const MQTTPublishInfo_t * pPublishInfo,
                                          uint16_t packetId,
                                          size_t remainingLength,
                                          const MQTTFixedBuffer_t * pFixedBuffer,
                                          size_t * pHeaderSize );

/**
 * @brief Serialize an MQTT PUBACK, PUBREC, PUBREL, or PUBCOMP into the given
 * buffer.
 *
 * @param[out] pFixedBuffer Buffer for packet serialization.
 * @param[in] packetType Byte of the corresponding packet fixed header per the
 * MQTT spec.
 * @param[in] packetId Packet ID of the publish.
 *
 * @return #MQTTBadParameter, #MQTTNoMemory, or #MQTTSuccess.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * MQTTFixedBuffer_t fixedBuffer;
 * uint8_t buffer[ BUFFER_SIZE ];
 * uint16_t packetId;
 * uint8_t packetType;
 *
 * fixedBuffer.pBuffer = buffer;
 * fixedBuffer.size = BUFFER_SIZE;
 * // The fixed buffer must be large enough to hold 4 bytes.
 * assert( BUFFER_SIZE >= MQTT_PUBLISH_ACK_PACKET_SIZE );
 *
 * // The packet ID must be the same as the original publish packet.
 * packetId = publishPacketId;
 *
 * // The byte representing a packet of type ACK. This function accepts PUBACK, PUBREC, PUBREL, or PUBCOMP.
 * packetType = MQTT_PACKET_TYPE_PUBACK;
 *
 * // Serialize the publish acknowledgment into the fixed buffer.
 * status = MQTT_SerializeAck( &fixedBuffer, packetType, packetId );
 *
 * if( status == MQTTSuccess )
 * {
 *      // The publish acknowledgment can now be sent to the broker.
 * }
 * @endcode
 */
MQTTStatus_t MQTT_SerializeAck( const MQTTFixedBuffer_t * pFixedBuffer,
                                uint8_t packetType,
                                uint16_t packetId );

/**
 * @brief Get the size of an MQTT DISCONNECT packet.
 *
 * @param[out] pPacketSize The size of the MQTT DISCONNECT packet.
 *
 * @return #MQTTSuccess, or #MQTTBadParameter if @p pPacketSize is NULL.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * size_t packetSize = 0;
 *
 * // Get the size requirement for the disconnect packet.
 * status = MQTT_GetDisconnectPacketSize( &packetSize );
 * assert( status == MQTTSuccess );
 * assert( packetSize == 2 );
 *
 * // The application should allocate or use a static #MQTTFixedBuffer_t of
 * // size >= 2 to serialize the disconnect packet.
 *
 * @endcode
 */
MQTTStatus_t MQTT_GetDisconnectPacketSize( size_t * pPacketSize );

/**
 * @brief Serialize an MQTT DISCONNECT packet into the given buffer.
 *
 * The input #MQTTFixedBuffer_t.size must be at least as large as the size
 * returned by #MQTT_GetDisconnectPacketSize.
 *
 * @param[out] pFixedBuffer Buffer for packet serialization.
 *
 * @return #MQTTNoMemory if pFixedBuffer is too small to hold the MQTT packet;
 * #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSuccess otherwise.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * MQTTFixedBuffer_t fixedBuffer;
 * uint8_t buffer[ BUFFER_SIZE ];
 *
 * fixedBuffer.pBuffer = buffer;
 * fixedBuffer.size = BUFFER_SIZE;
 *
 * // Get the disconnect packet size.
 * status = MQTT_GetDisconnectPacketSize( &packetSize );
 * assert( status == MQTTSuccess );
 * assert( packetSize <= BUFFER_SIZE );
 *
 * // Serialize the disconnect into the fixed buffer.
 * status = MQTT_SerializeDisconnect( &fixedBuffer );
 *
 * if( status == MQTTSuccess )
 * {
 *      // The disconnect packet can now be sent to the broker.
 * }
 * @endcode
 */
MQTTStatus_t MQTT_SerializeDisconnect( const MQTTFixedBuffer_t * pFixedBuffer );

/**
 * @brief Get the size of an MQTT PINGREQ packet.
 *
 * @param[out] pPacketSize The size of the MQTT PINGREQ packet.
 *
 * @return  #MQTTSuccess or #MQTTBadParameter if pPacketSize is NULL.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * size_t packetSize = 0;
 *
 * // Get the size requirement for the ping request packet.
 * status = MQTT_GetPingreqPacketSize( &packetSize );
 * assert( status == MQTTSuccess );
 * assert( packetSize == 2 );
 *
 * // The application should allocate or use a static #MQTTFixedBuffer_t of
 * // size >= 2 to serialize the ping request.
 *
 * @endcode
 */
MQTTStatus_t MQTT_GetPingreqPacketSize( size_t * pPacketSize );

/**
 * @brief Serialize an MQTT PINGREQ packet into the given buffer.
 *
 * The input #MQTTFixedBuffer_t.size must be at least as large as the size
 * returned by #MQTT_GetPingreqPacketSize.
 *
 * @param[out] pFixedBuffer Buffer for packet serialization.
 *
 * @return #MQTTNoMemory if pFixedBuffer is too small to hold the MQTT packet;
 * #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSuccess otherwise.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * MQTTFixedBuffer_t fixedBuffer;
 * uint8_t buffer[ BUFFER_SIZE ];
 *
 * fixedBuffer.pBuffer = buffer;
 * fixedBuffer.size = BUFFER_SIZE;
 *
 * // Get the ping request packet size.
 * status = MQTT_GetPingreqPacketSize( &packetSize );
 * assert( status == MQTTSuccess );
 * assert( packetSize <= BUFFER_SIZE );
 *
 * // Serialize the ping request into the fixed buffer.
 * status = MQTT_SerializePingreq( &fixedBuffer );
 *
 * if( status == MQTTSuccess )
 * {
 *      // The ping request can now be sent to the broker.
 * }
 * @endcode
 */
MQTTStatus_t MQTT_SerializePingreq( const MQTTFixedBuffer_t * pFixedBuffer );

/**
 * @brief Deserialize an MQTT PUBLISH packet.
 *
 * @param[in] pIncomingPacket #MQTTPacketInfo_t containing the buffer.
 * @param[out] pPacketId The packet ID obtained from the buffer.
 * @param[out] pPublishInfo Struct containing information about the publish.
 *
 * @return #MQTTBadParameter, #MQTTBadResponse, or #MQTTSuccess.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // TransportRecv_t function for reading from the network.
 * int32_t socket_recv(
 *      NetworkContext_t * pNetworkContext,
 *      void * pBuffer,
 *      size_t bytesToRecv
 * );
 * // Some context to be used with the above transport receive function.
 * NetworkContext_t networkContext;
 *
 * // Other variables used in this example.
 * MQTTStatus_t status;
 * MQTTPacketInfo_t incomingPacket;
 * MQTTPublishInfo_t publishInfo = { 0 };
 * uint16_t packetId;
 *
 * int32_t bytesRecvd;
 * // A buffer to hold remaining data of the incoming packet.
 * uint8_t buffer[ BUFFER_SIZE ];
 *
 * // Populate all fields of the incoming packet.
 * status = MQTT_GetIncomingPacketTypeAndLength(
 *      socket_recv,
 *      &networkContext,
 *      &incomingPacket
 * );
 * assert( status == MQTTSuccess );
 * assert( incomingPacket.remainingLength <= BUFFER_SIZE );
 * bytesRecvd = socket_recv(
 *      &networkContext,
 *      ( void * ) buffer,
 *      incomingPacket.remainingLength
 * );
 * incomingPacket.pRemainingData = buffer;
 *
 * // Deserialize the publish information if the incoming packet is a publish.
 * if( ( incomingPacket.type & 0xF0 ) == MQTT_PACKET_TYPE_PUBLISH )
 * {
 *      status = MQTT_DeserializePublish( &incomingPacket, &packetId, &publishInfo );
 *      if( status == MQTTSuccess )
 *      {
 *          // The deserialized publish information can now be used from `publishInfo`.
 *      }
 * }
 * @endcode
 */
MQTTStatus_t MQTT_DeserializePublish( const MQTTPacketInfo_t * pIncomingPacket,
                                      uint16_t * pPacketId,
                                      MQTTPublishInfo_t * pPublishInfo );

/**
 * @brief Deserialize an MQTT CONNACK, SUBACK, UNSUBACK, PUBACK, PUBREC, PUBREL,
 * PUBCOMP, or PINGRESP.
 *
 * @param[in] pIncomingPacket #MQTTPacketInfo_t containing the buffer.
 * @param[out] pPacketId The packet ID of obtained from the buffer. Not used
 * in CONNACK or PINGRESP.
 * @param[out] pSessionPresent Boolean flag from a CONNACK indicating present session.
 *
 * @return #MQTTBadParameter, #MQTTBadResponse, #MQTTServerRefused, or #MQTTSuccess.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * MQTTPacketInfo_t incomingPacket;
 * // Used for SUBACK, UNSUBACK, PUBACK, PUBREC, PUBREL, and PUBCOMP.
 * uint16_t packetId;
 * // Used for CONNACK.
 * bool sessionPresent;
 *
 * // Receive an incoming packet and populate all fields. The details are out of scope
 * // for this example.
 * receiveIncomingPacket( &incomingPacket );
 *
 * // Deserialize ack information if the incoming packet is not a publish.
 * if( ( incomingPacket.type & 0xF0 ) != MQTT_PACKET_TYPE_PUBLISH )
 * {
 *      status = MQTT_DeserializeAck( &incomingPacket, &packetId, &sessionPresent );
 *      if( status == MQTTSuccess )
 *      {
 *          // The packet ID or session present flag information is available. For
 *          // ping response packets, the only information is the status code.
 *      }
 * }
 * @endcode
 */
MQTTStatus_t MQTT_DeserializeAck( const MQTTPacketInfo_t * pIncomingPacket,
                                  uint16_t * pPacketId,
                                  bool * pSessionPresent );

/**
 * @brief Extract the MQTT packet type and length from incoming packet.
 *
 * This function must be called for every incoming packet to retrieve the
 * #MQTTPacketInfo_t.type and #MQTTPacketInfo_t.remainingLength. A
 * #MQTTPacketInfo_t is not valid until this routine has been invoked.
 *
 * @param[in] readFunc Transport layer read function pointer.
 * @param[in] pNetworkContext The network context pointer provided by the application.
 * @param[out] pIncomingPacket Pointer to MQTTPacketInfo_t structure. This is
 * where type, remaining length and packet identifier are stored.
 *
 * @return #MQTTSuccess on successful extraction of type and length,
 * #MQTTBadParameter if @p pIncomingPacket is invalid,
 * #MQTTRecvFailed on transport receive failure,
 * #MQTTBadResponse if an invalid packet is read, and
 * #MQTTNoDataAvailable if there is nothing to read.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // TransportRecv_t function for reading from the network.
 * int32_t socket_recv(
 *      NetworkContext_t * pNetworkContext,
 *      void * pBuffer,
 *      size_t bytesToRecv
 * );
 * // Some context to be used with above transport receive function.
 * NetworkContext_t networkContext;
 *
 * // Struct to hold the incoming packet information.
 * MQTTPacketInfo_t incomingPacket;
 * MQTTStatus_t status = MQTTSuccess;
 * int32_t bytesRecvd;
 * // Buffer to hold the remaining data of the incoming packet.
 * uint8_t buffer[ BUFFER_SIZE ];
 *
 * // Loop until data is available to be received.
 * do{
 *      status = MQTT_GetIncomingPacketTypeAndLength(
 *          socket_recv,
 *          &networkContext,
 *          &incomingPacket
 *      );
 * } while( status == MQTTNoDataAvailable );
 *
 * assert( status == MQTTSuccess );
 *
 * // Receive the rest of the incoming packet.
 * assert( incomingPacket.remainingLength <= BUFFER_SIZE );
 * bytesRecvd = socket_recv(
 *      &networkContext,
 *      ( void * ) buffer,
 *      incomingPacket.remainingLength
 * );
 *
 * // Set the remaining data field.
 * incomingPacket.pRemainingData = buffer;
 * @endcode
 */
MQTTStatus_t MQTT_GetIncomingPacketTypeAndLength( TransportRecv_t readFunc,
                                                  NetworkContext_t * pNetworkContext,
                                                  MQTTPacketInfo_t * pIncomingPacket );

#endif /* ifndef MQTT_LIGHTWEIGHT_H */
