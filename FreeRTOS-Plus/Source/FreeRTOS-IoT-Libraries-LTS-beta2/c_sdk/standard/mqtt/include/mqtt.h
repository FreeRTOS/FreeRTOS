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

#ifndef MQTT_H
#define MQTT_H

/* Include config file before other headers. */
#include "mqtt_config.h"
#include "mqtt_lightweight.h"

/**
 * @brief Invalid packet identifier.
 *
 * Zero is an invalid packet identifier as per MQTT v3.1.1 spec.
 */
#define MQTT_PACKET_ID_INVALID    ( ( uint16_t ) 0U )

struct MQTTApplicationCallbacks;
typedef struct MQTTApplicationCallbacks   MQTTApplicationCallbacks_t;

struct MQTTPubAckInfo;
typedef struct MQTTPubAckInfo             MQTTPubAckInfo_t;

struct MQTTContext;
typedef struct MQTTContext                MQTTContext_t;

struct MQTTTransportInterface;
typedef struct MQTTTransportInterface     MQTTTransportInterface_t;

typedef int32_t (* MQTTTransportSendFunc_t )( NetworkContext_t context,
                                              const void * pMessage,
                                              size_t bytesToSend );

typedef uint32_t (* MQTTGetCurrentTimeFunc_t )( void );

typedef void (* MQTTEventCallback_t )( MQTTContext_t * pContext,
                                       MQTTPacketInfo_t * pPacketInfo,
                                       uint16_t packetIdentifier,
                                       MQTTPublishInfo_t * pPublishInfo );

typedef enum MQTTConnectionStatus
{
    MQTTNotConnected,
    MQTTConnected
} MQTTConnectionStatus_t;

typedef enum MQTTPublishState
{
    MQTTStateNull = 0,
    MQTTPublishSend,
    MQTTPubAckSend,
    MQTTPubRecSend,
    MQTTPubRelSend,
    MQTTPubCompSend,
    MQTTPubAckPending,
    MQTTPubRelPending,
    MQTTPubRecPending,
    MQTTPubCompPending,
    MQTTPublishDone
} MQTTPublishState_t;

typedef enum MQTTPubAckType
{
    MQTTPuback,
    MQTTPubrec,
    MQTTPubrel,
    MQTTPubcomp
} MQTTPubAckType_t;

struct MQTTTransportInterface
{
    MQTTTransportSendFunc_t send;
    MQTTTransportRecvFunc_t recv;
    NetworkContext_t networkContext;
};

struct MQTTApplicationCallbacks
{
    MQTTGetCurrentTimeFunc_t getTime;
    MQTTEventCallback_t appCallback;
};

struct MQTTPubAckInfo
{
    uint16_t packetId;
    MQTTQoS_t qos;
    MQTTPublishState_t publishState;
};

struct MQTTContext
{
    MQTTPubAckInfo_t outgoingPublishRecords[ MQTT_STATE_ARRAY_MAX_COUNT ];
    size_t outgoingPublishCount;
    MQTTPubAckInfo_t incomingPublishRecords[ MQTT_STATE_ARRAY_MAX_COUNT ];
    size_t incomingPublishCount;

    MQTTTransportInterface_t transportInterface;
    MQTTFixedBuffer_t networkBuffer;

    uint16_t nextPacketId;
    MQTTConnectionStatus_t connectStatus;
    MQTTApplicationCallbacks_t callbacks;
    uint32_t lastPacketTime;
    bool controlPacketSent;

    /* Keep alive members. */
    uint16_t keepAliveIntervalSec;
    uint32_t pingReqSendTimeMs;
    uint32_t pingRespTimeoutMs;
    bool waitingForPingResp;
};

/**
 * @brief Initialize an MQTT context.
 *
 * This function must be called on an MQTT context before any other function.
 *
 * @note The getTime callback function must be defined. If there is no time
 * implementation, it is the responsibility of the application to provide a
 * dummy function to always return 0, and provide 0 timeouts for functions. This
 * will ensure all time based functions will run for a single iteration.
 *
 * @brief param[in] pContext The context to initialize.
 * @brief param[in] pTransportInterface The transport interface to use with the context.
 * @brief param[in] pCallbacks Callbacks to use with the context.
 * @brief param[in] pNetworkBuffer Network buffer provided for the context.
 *
 * @return #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSuccess otherwise.
 */
MQTTStatus_t MQTT_Init( MQTTContext_t * pContext,
                        const MQTTTransportInterface_t * pTransportInterface,
                        const MQTTApplicationCallbacks_t * pCallbacks,
                        const MQTTFixedBuffer_t * pNetworkBuffer );

/**
 * @brief Establish a MQTT session.
 *
 * @brief param[in] pContext Initialized MQTT context.
 * @brief param[in] pConnectInfo MQTT CONNECT packet parameters.
 * @brief param[in] pWillInfo Last Will and Testament. Pass NULL if not used.
 * @brief param[in] timeoutMs Timeout in milliseconds for receiving
 * CONNACK packet.
 * @brief param[out] pSessionPresent Whether a previous session was present.
 * Only relevant if not establishing a clean session.
 *
 * @return #MQTTNoMemory if the #MQTTContext_t.networkBuffer is too small to
 * hold the MQTT packet;
 * #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSendFailed if transport send failed;
 * #MQTTRecvFailed if transport receive failed for CONNACK;
 * #MQTTNoDataAvailable if no data available to receive in transport until
 * the #timeoutMs for CONNACK;
 * #MQTTSuccess otherwise.
 */
MQTTStatus_t MQTT_Connect( MQTTContext_t * pContext,
                           const MQTTConnectInfo_t * pConnectInfo,
                           const MQTTPublishInfo_t * pWillInfo,
                           uint32_t timeoutMs,
                           bool * pSessionPresent );

/**
 * @brief Sends MQTT SUBSCRIBE for the given list of topic filters to
 * the broker.
 *
 * @param[in] pContext Initialized MQTT context.
 * @param[in] pSubscriptionList List of MQTT subscription info.
 * @param[in] subscriptionCount The number of elements in pSubscriptionList.
 * @param[in] packetId packet ID generated by #MQTT_GetPacketId.
 *
 * @return #MQTTNoMemory if the #MQTTContext_t.networkBuffer is too small to
 * hold the MQTT packet;
 * #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSendFailed if transport write failed;
 * #MQTTSuccess otherwise.
 */
MQTTStatus_t MQTT_Subscribe( MQTTContext_t * pContext,
                             const MQTTSubscribeInfo_t * pSubscriptionList,
                             size_t subscriptionCount,
                             uint16_t packetId );

/**
 * @brief Publishes a message to the given topic name.
 *
 * @brief param[in] pContext Initialized MQTT context.
 * @brief param[in] pPublishInfo MQTT PUBLISH packet parameters.
 * @brief param[in] packetId packet ID generated by #MQTT_GetPacketId.
 *
 * @return #MQTTNoMemory if pBuffer is too small to hold the MQTT packet;
 * #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSendFailed if transport write failed;
 * #MQTTSuccess otherwise.
 */
MQTTStatus_t MQTT_Publish( MQTTContext_t * pContext,
                           const MQTTPublishInfo_t * pPublishInfo,
                           uint16_t packetId );

/**
 * @brief Sends an MQTT PINGREQ to broker.
 *
 * @param[in] pContext Initialized and connected MQTT context.
 *
 * @return #MQTTNoMemory if pBuffer is too small to hold the MQTT packet;
 * #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSendFailed if transport write failed;
 * #MQTTSuccess otherwise.
 */
MQTTStatus_t MQTT_Ping( MQTTContext_t * pContext );

/**
 * @brief Sends MQTT UNSUBSCRIBE for the given list of topic filters to
 * the broker.
 *
 * @param[in] pContext Initialized MQTT context.
 * @param[in] pSubscriptionList List of MQTT subscription info.
 * @param[in] subscriptionCount The number of elements in pSubscriptionList.
 * @param[in] packetId packet ID generated by #MQTT_GetPacketId.
 *
 * @return #MQTTNoMemory if the #MQTTContext_t.networkBuffer is too small to
 * hold the MQTT packet;
 * #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSendFailed if transport write failed;
 * #MQTTSuccess otherwise.
 */
MQTTStatus_t MQTT_Unsubscribe( MQTTContext_t * pContext,
                               const MQTTSubscribeInfo_t * pSubscriptionList,
                               size_t subscriptionCount,
                               uint16_t packetId );

/**
 * @brief Disconnect an MQTT session.
 *
 * @param[in] pContext Initialized and connected MQTT context.
 *
 * @return #MQTTNoMemory if the #MQTTContext_t.networkBuffer is too small to
 * hold the MQTT packet;
 * #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSendFailed if transport send failed;
 * #MQTTSuccess otherwise.
 */
MQTTStatus_t MQTT_Disconnect( MQTTContext_t * pContext );

/**
 * @brief Loop to receive packets from the transport interface. Handles keep
 * alive.
 *
 * @param[in] pContext Initialized and connected MQTT context.
 * @param[in] timeoutMs Minimum time in milliseconds that the receive loop will
 * run, unless an error occurs.
 *
 * @return #MQTTBadParameter if context is NULL;
 * #MQTTRecvFailed if a network error occurs during reception;
 * #MQTTSendFailed if a network error occurs while sending an ACK or PINGREQ;
 * #MQTTBadResponse if an invalid packet is received;
 * #MQTTKeepAliveTimeout if the server has not sent a PINGRESP before
 * pContext->pingRespTimeoutMs milliseconds;
 * #MQTTIllegalState if an incoming QoS 1/2 publish or ack causes an
 * invalid transition for the internal state machine;
 * #MQTTSuccess on success.
 */
MQTTStatus_t MQTT_ProcessLoop( MQTTContext_t * pContext,
                               uint32_t timeoutMs );

/**
 * @brief Loop to receive packets from the transport interface. Does not handle
 * keep alive.
 *
 * @note Passing a timeout value of 0 will run the loop for a single iteration.
 *
 * @param[in] pContext Initialized and connected MQTT context.
 * @param[in] timeoutMs Minimum time in milliseconds that the receive loop will
 * run, unless an error occurs.
 *
 * @return #MQTTBadParameter if context is NULL;
 * #MQTTRecvFailed if a network error occurs during reception;
 * #MQTTSendFailed if a network error occurs while sending an ACK or PINGREQ;
 * #MQTTBadResponse if an invalid packet is received;
 * #MQTTIllegalState if an incoming QoS 1/2 publish or ack causes an
 * invalid transition for the internal state machine;
 * #MQTTSuccess on success.
 */
MQTTStatus_t MQTT_ReceiveLoop( MQTTContext_t * pContext,
                               uint32_t timeoutMs );

/**
 * @brief Get a packet ID that is valid according to the MQTT 3.1.1 spec.
 *
 * @param[in] pContext Initialized MQTT context.
 *
 * @return A non-zero number.
 */
uint16_t MQTT_GetPacketId( MQTTContext_t * pContext );

/**
 * @brief Error code to string conversion for MQTT statuses.
 *
 * @param[in] status The status to convert to a string.
 *
 * @return The string representation of the status.
 */
const char * MQTT_Status_strerror( MQTTStatus_t status );

#endif /* ifndef MQTT_H */
