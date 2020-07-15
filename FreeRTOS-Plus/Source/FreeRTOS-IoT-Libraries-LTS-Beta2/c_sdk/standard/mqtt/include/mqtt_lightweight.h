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

#ifndef MQTT_LIGHTWEIGHT_H
#define MQTT_LIGHTWEIGHT_H

#include <stddef.h>
#include <stdint.h>

/* bool is defined in only C99+. */
#if defined( __cplusplus ) || ( defined( __STDC_VERSION__ ) && ( __STDC_VERSION__ >= 199901L ) )
    #include <stdbool.h>
#elif !defined( bool )
    #define bool     int8_t
    #define false    ( int8_t ) 0
    #define true     ( int8_t ) 1
#endif

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

struct MQTTFixedBuffer;
typedef struct MQTTFixedBuffer     MQTTFixedBuffer_t;

struct MQTTConnectInfo;
typedef struct MQTTConnectInfo     MQTTConnectInfo_t;

struct MQTTSubscribeInfo;
typedef struct MQTTSubscribeInfo   MQTTSubscribeInfo_t;

struct MqttPublishInfo;
typedef struct MqttPublishInfo     MQTTPublishInfo_t;

struct MQTTPacketInfo;
typedef struct MQTTPacketInfo      MQTTPacketInfo_t;

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
struct MQTTFixedBuffer
{
    uint8_t * pBuffer; /**< @brief Pointer to buffer. */
    size_t size;       /**< @brief Size of buffer. */
};

/**
 * @brief MQTT CONNECT packet parameters.
 */
struct MQTTConnectInfo
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
};

/**
 * @brief MQTT SUBSCRIBE packet parameters.
 */
struct MQTTSubscribeInfo
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
};

/**
 * @brief MQTT PUBLISH packet parameters.
 */
struct MqttPublishInfo
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
};

/**
 * @brief MQTT incoming packet parameters.
 */
struct MQTTPacketInfo
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
};

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
 */
MQTTStatus_t MQTT_SerializeAck( const MQTTFixedBuffer_t * pFixedBuffer,
                                uint8_t packetType,
                                uint16_t packetId );

/**
 * @brief Get the size of an MQTT DISCONNECT packet.
 *
 * @param[out] pPacketSize The size of the MQTT DISCONNECT packet.
 *
 * @return Always returns #MQTTSuccess.
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
 */
MQTTStatus_t MQTT_SerializeDisconnect( const MQTTFixedBuffer_t * pFixedBuffer );

/**
 * @brief Get the size of an MQTT PINGREQ packet.
 *
 * @param[out] pPacketSize The size of the MQTT PINGREQ packet.
 *
 * @return  #MQTTSuccess or #MQTTBadParameter if pPacketSize is NULL.
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
 * @return #MQTTBadParameter, #MQTTBadResponse, or #MQTTSuccess.
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
 */
MQTTStatus_t MQTT_GetIncomingPacketTypeAndLength( TransportRecv_t readFunc,
                                                  NetworkContext_t * pNetworkContext,
                                                  MQTTPacketInfo_t * pIncomingPacket );

#endif /* ifndef MQTT_LIGHTWEIGHT_H */
