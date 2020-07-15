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

#include <string.h>
#include <assert.h>

#include "mqtt.h"
#include "mqtt_state.h"
#include "private/mqtt_internal.h"


/**
 * @brief The number of retries for receiving CONNACK.
 *
 * The MQTT_MAX_CONNACK_RECEIVE_RETRY_COUNT will be used only when the
 * timeoutMs parameter of #MQTT_Connect() is passed as 0 . The transport
 * receive for CONNACK will be retried MQTT_MAX_CONNACK_RECEIVE_RETRY_COUNT
 * times before timing out. A value of 0 for this config will cause the
 * transport receive for CONNACK  to be invoked only once.
 */
#ifndef MQTT_MAX_CONNACK_RECEIVE_RETRY_COUNT
    /* Default value for the CONNACK receive retries. */
    #define MQTT_MAX_CONNACK_RECEIVE_RETRY_COUNT    ( 5U )
#endif

/**
 * @brief A return code indicating an error from the transport interface.
 */
#define TRANSPORT_ERROR    ( -1 )

/*-----------------------------------------------------------*/

/**
 * @brief Sends provided buffer to network using transport send.
 *
 * @brief param[in] pContext Initialized MQTT context.
 * @brief param[in] pBufferToSend Buffer to be sent to network.
 * @brief param[in] bytesToSend Number of bytes to be sent.
 *
 * @return Total number of bytes sent; -1 if there is an error.
 */
static int32_t sendPacket( MQTTContext_t * pContext,
                           const uint8_t * pBufferToSend,
                           size_t bytesToSend );

/**
 * @brief Calculate the interval between two millisecond timestamps, including
 * when the later value has overflowed.
 *
 * @note In C, the operands are promoted to signed integers in subtraction.
 * Using this function avoids the need to cast the result of subtractions back
 * to uint32_t.
 *
 * @param[in] later The later time stamp, in milliseconds.
 * @param[in] start The earlier time stamp, in milliseconds.
 *
 * @return later - start.
 */
static uint32_t calculateElapsedTime( uint32_t later,
                                      uint32_t start );

/**
 * @brief Convert a byte indicating a publish ack type to an #MQTTPubAckType_t.
 *
 * @param[in] packetType First byte of fixed header.
 *
 * @return Type of ack.
 */
static MQTTPubAckType_t getAckFromPacketType( uint8_t packetType );

/**
 * @brief Receive bytes into the network buffer, with a timeout.
 *
 * @param[in] pContext Initialized MQTT Context.
 * @param[in] bytesToRecv Number of bytes to receive.
 * @param[in] timeoutMs Time remaining to receive the packet.
 *
 * @return Number of bytes received, or negative number on network error.
 */
static int32_t recvExact( const MQTTContext_t * pContext,
                          size_t bytesToRecv,
                          uint32_t timeoutMs );

/**
 * @brief Discard a packet from the transport interface.
 *
 * @param[in] PContext MQTT Connection context.
 * @param[in] remainingLength Remaining length of the packet to dump.
 * @param[in] timeoutMs Time remaining to discard the packet.
 *
 * @return #MQTTRecvFailed or #MQTTNoDataAvailable.
 */
static MQTTStatus_t discardPacket( const MQTTContext_t * pContext,
                                   size_t remainingLength,
                                   uint32_t timeoutMs );

/**
 * @brief Receive a packet from the transport interface.
 *
 * @param[in] pContext MQTT Connection context.
 * @param[in] incomingPacket packet struct with remaining length.
 * @param[in] remainingTimeMs Time remaining to receive the packet.
 *
 * @return #MQTTSuccess or #MQTTRecvFailed.
 */
static MQTTStatus_t receivePacket( const MQTTContext_t * pContext,
                                   MQTTPacketInfo_t incomingPacket,
                                   uint32_t remainingTimeMs );

/**
 * @brief Get the correct ack type to send.
 *
 * @param[in] state Current state of publish.
 *
 * @return Packet Type byte of PUBACK, PUBREC, PUBREL, or PUBCOMP if one of
 * those should be sent, else 0.
 */
static uint8_t getAckTypeToSend( MQTTPublishState_t state );

/**
 * @brief Send acks for received QoS 1/2 publishes.
 *
 * @param[in] pContext MQTT Connection context.
 * @param[in] packetId packet ID of original PUBLISH.
 * @param[in] publishState Current publish state in record.
 *
 * @return #MQTTSuccess, #MQTTIllegalState or #MQTTSendFailed.
 */
static MQTTStatus_t sendPublishAcks( MQTTContext_t * pContext,
                                     uint16_t packetId,
                                     MQTTPublishState_t publishState );

/**
 * @brief Send a keep alive PINGREQ if the keep alive interval has elapsed.
 *
 * @param[in] pContext Initialized MQTT Context.
 *
 * @return #MQTTKeepAliveTimeout if a PINGRESP is not received in time,
 * #MQTTSendFailed if the PINGREQ cannot be sent, or #MQTTSuccess.
 */
static MQTTStatus_t handleKeepAlive( MQTTContext_t * pContext );

/**
 * @brief Handle received MQTT PUBLISH packet.
 *
 * @param[in] pContext MQTT Connection context.
 * @param[in] pIncomingPacket Incoming packet.
 *
 * @return MQTTSuccess, MQTTIllegalState or deserialization error.
 */
static MQTTStatus_t handleIncomingPublish( MQTTContext_t * pContext,
                                           MQTTPacketInfo_t * pIncomingPacket );

/**
 * @brief Handle received MQTT publish acks.
 *
 * @param[in] pContext MQTT Connection context.
 * @param[in] pIncomingPacket Incoming packet.
 *
 * @return MQTTSuccess, MQTTIllegalState, or deserialization error.
 */
static MQTTStatus_t handlePublishAcks( MQTTContext_t * pContext,
                                       MQTTPacketInfo_t * pIncomingPacket );

/**
 * @brief Handle received MQTT ack.
 *
 * @param[in] pContext MQTT Connection context.
 * @param[in] pIncomingPacket Incoming packet.
 * @param[in] manageKeepAlive Flag indicating if PINGRESPs should not be given
 * to the application
 *
 * @return MQTTSuccess, MQTTIllegalState, or deserialization error.
 */
static MQTTStatus_t handleIncomingAck( MQTTContext_t * pContext,
                                       MQTTPacketInfo_t * pIncomingPacket,
                                       bool manageKeepAlive );

/**
 * @brief Run a single iteration of the receive loop.
 *
 * @param[in] pContext MQTT Connection context.
 * @param[in] remainingTimeMs Remaining time for the loop in milliseconds.
 * @param[in] manageKeepAlive Flag indicating if keep alive should be handled.
 *
 * @return #MQTTRecvFailed if a network error occurs during reception;
 * #MQTTSendFailed if a network error occurs while sending an ACK or PINGREQ;
 * #MQTTBadResponse if an invalid packet is received;
 * #MQTTKeepAliveTimeout if the server has not sent a PINGRESP before
 * pContext->pingRespTimeoutMs milliseconds;
 * #MQTTIllegalState if an incoming QoS 1/2 publish or ack causes an
 * invalid transition for the internal state machine;
 * #MQTTSuccess on success.
 */
static MQTTStatus_t receiveSingleIteration( MQTTContext_t * pContext,
                                            uint32_t remainingTimeMs,
                                            bool manageKeepAlive );

/**
 * @brief Validates parameters of #MQTT_Subscribe or #MQTT_Unsubscribe.
 *
 * @param[in] pContext Initialized MQTT context.
 * @param[in] pSubscriptionList List of MQTT subscription info.
 * @param[in] subscriptionCount The number of elements in pSubscriptionList.
 * @param[in] packetId Packet identifier.
 *
 * @return #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSuccess otherwise.
 */
static MQTTStatus_t validateSubscribeUnsubscribeParams( const MQTTContext_t * pContext,
                                                        const MQTTSubscribeInfo_t * pSubscriptionList,
                                                        size_t subscriptionCount,
                                                        uint16_t packetId );

/**
 * @brief Send serialized publish packet using transport send.
 *
 * @brief param[in] pContext Initialized MQTT context.
 * @brief param[in] pPublishInfo MQTT PUBLISH packet parameters.
 * @brief param[in] headerSize Header size of the PUBLISH packet.
 *
 * @return #MQTTSendFailed if transport write failed;
 * #MQTTSuccess otherwise.
 */
static MQTTStatus_t sendPublish( MQTTContext_t * pContext,
                                 const MQTTPublishInfo_t * pPublishInfo,
                                 size_t headerSize );

/**
 * @brief Receives a CONNACK MQTT packet.
 *
 * @param[in] pContext Initialized MQTT context.
 * @param[in] timeoutMs Timeout for waiting for CONNACK packet.
 * @param[in] cleanSession Clean session flag set by application.
 * @param[out] pIncomingPacket List of MQTT subscription info.
 * @param[out] pSessionPresent Whether a previous session was present.
 * Only relevant if not establishing a clean session.
 *
 * @return #MQTTBadResponse if a bad response is received;
 * #MQTTNoDataAvailable if no data available for transport recv;
 * ##MQTTRecvFailed if transport recv failed;
 * #MQTTSuccess otherwise.
 */
static MQTTStatus_t receiveConnack( const MQTTContext_t * pContext,
                                    uint32_t timeoutMs,
                                    bool cleanSession,
                                    MQTTPacketInfo_t * pIncomingPacket,
                                    bool * pSessionPresent );

/**
 * @brief Resends pending acks for a re-established MQTT session.
 *
 * @param[in] pContext Initialized MQTT context.
 *
 * @return #MQTTSendFailed if transport send failed;
 * #MQTTSuccess otherwise.
 */
static MQTTStatus_t resendPendingAcks( MQTTContext_t * pContext );

/**
 * @brief Serializes a PUBLISH message.
 *
 * @brief param[in] pContext Initialized MQTT context.
 * @brief param[in] pPublishInfo MQTT PUBLISH packet parameters.
 * @brief param[in] packetId Packet Id of the publish packet.
 * @brief param[out] pHeaderSize Size of the serialized PUBLISH header.
 *
 * @return #MQTTNoMemory if pBuffer is too small to hold the MQTT packet;
 * #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSuccess otherwise.
 */
static MQTTStatus_t serializePublish( const MQTTContext_t * pContext,
                                      const MQTTPublishInfo_t * pPublishInfo,
                                      uint16_t packetId,
                                      size_t * const pHeaderSize );

/**
 * @brief Function to validate #MQTT_Publish parameters.
 *
 * @brief param[in] pContext Initialized MQTT context.
 * @brief param[in] pPublishInfo MQTT PUBLISH packet parameters.
 * @brief param[in] packetId Packet Id for the MQTT PUBLISH packet.
 *
 * @return #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSuccess otherwise.
 */
static MQTTStatus_t validatePublishParams( const MQTTContext_t * pContext,
                                           const MQTTPublishInfo_t * pPublishInfo,
                                           uint16_t packetId );

/*-----------------------------------------------------------*/

static int32_t sendPacket( MQTTContext_t * pContext,
                           const uint8_t * pBufferToSend,
                           size_t bytesToSend )
{
    const uint8_t * pIndex = pBufferToSend;
    size_t bytesRemaining = bytesToSend;
    int32_t totalBytesSent = 0, bytesSent;
    uint32_t sendTime = 0U;

    assert( pContext != NULL );
    assert( pContext->callbacks.getTime != NULL );

    bytesRemaining = bytesToSend;

    /* Record the time of transmission. */
    sendTime = pContext->callbacks.getTime();

    /* Loop until the entire packet is sent. */
    while( bytesRemaining > 0UL )
    {
        bytesSent = pContext->transportInterface.send( pContext->transportInterface.pNetworkContext,
                                                       pIndex,
                                                       bytesRemaining );

        if( bytesSent > 0 )
        {
            bytesRemaining -= ( size_t ) bytesSent;
            totalBytesSent += bytesSent;
            pIndex += bytesSent;
            LogDebug( ( "Bytes sent=%d, bytes remaining=%ul,"
                        "total bytes sent=%d.",
                        bytesSent,
                        bytesRemaining,
                        totalBytesSent ) );
        }
        else
        {
            LogError( ( "Transport send failed. Error code=%d.", bytesSent ) );
            totalBytesSent = TRANSPORT_ERROR;
            break;
        }
    }

    /* Update time of last transmission if the entire packet is successfully sent. */
    if( totalBytesSent > 0 )
    {
        pContext->lastPacketTime = sendTime;
        LogDebug( ( "Successfully sent packet at time %u.",
                    sendTime ) );
    }

    return totalBytesSent;
}

/*-----------------------------------------------------------*/

static uint32_t calculateElapsedTime( uint32_t later,
                                      uint32_t start )
{
    return later - start;
}

/*-----------------------------------------------------------*/

static MQTTPubAckType_t getAckFromPacketType( uint8_t packetType )
{
    MQTTPubAckType_t ackType = MQTTPuback;

    switch( packetType )
    {
        case MQTT_PACKET_TYPE_PUBACK:
            ackType = MQTTPuback;
            break;

        case MQTT_PACKET_TYPE_PUBREC:
            ackType = MQTTPubrec;
            break;

        case MQTT_PACKET_TYPE_PUBREL:
            ackType = MQTTPubrel;
            break;

        case MQTT_PACKET_TYPE_PUBCOMP:
        default:

            /* This function is only called after checking the type is one of
             * the above four values, so packet type must be PUBCOMP here. */
            assert( packetType == MQTT_PACKET_TYPE_PUBCOMP );
            ackType = MQTTPubcomp;
            break;
    }

    return ackType;
}

/*-----------------------------------------------------------*/

static int32_t recvExact( const MQTTContext_t * pContext,
                          size_t bytesToRecv,
                          uint32_t timeoutMs )
{
    uint8_t * pIndex = NULL;
    size_t bytesRemaining = bytesToRecv;
    int32_t totalBytesRecvd = 0, bytesRecvd;
    uint32_t entryTimeMs = 0U, elapsedTimeMs = 0U;
    TransportRecv_t recvFunc = NULL;
    MQTTGetCurrentTimeFunc_t getTimeStampMs = NULL;
    bool receiveError = false;

    assert( pContext != NULL );
    assert( bytesToRecv <= pContext->networkBuffer.size );
    assert( pContext->callbacks.getTime != NULL );

    pIndex = pContext->networkBuffer.pBuffer;
    recvFunc = pContext->transportInterface.recv;
    getTimeStampMs = pContext->callbacks.getTime;

    entryTimeMs = getTimeStampMs();

    while( ( bytesRemaining > 0U ) && ( receiveError == false ) )
    {
        bytesRecvd = recvFunc( pContext->transportInterface.pNetworkContext,
                               pIndex,
                               bytesRemaining );

        if( bytesRecvd >= 0 )
        {
            bytesRemaining -= ( size_t ) bytesRecvd;
            totalBytesRecvd += ( int32_t ) bytesRecvd;
            pIndex += bytesRecvd;
        }
        else
        {
            LogError( ( "Network error while receiving packet: ReturnCode=%d",
                        bytesRecvd ) );
            totalBytesRecvd = bytesRecvd;
            receiveError = true;
        }

        elapsedTimeMs = calculateElapsedTime( getTimeStampMs(), entryTimeMs );

        if( ( bytesRemaining > 0U ) && ( elapsedTimeMs >= timeoutMs ) )
        {
            LogError( ( "Time expired while receiving packet." ) );
            receiveError = true;
        }
    }

    return totalBytesRecvd;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t discardPacket( const MQTTContext_t * pContext,
                                   size_t remainingLength,
                                   uint32_t timeoutMs )
{
    MQTTStatus_t status = MQTTRecvFailed;
    int32_t bytesReceived = 0;
    size_t bytesToReceive = 0U;
    uint32_t totalBytesReceived = 0U, entryTimeMs = 0U, elapsedTimeMs = 0U;
    uint32_t remainingTimeMs = timeoutMs;
    MQTTGetCurrentTimeFunc_t getTimeStampMs = NULL;
    bool receiveError = false;

    assert( pContext != NULL );
    assert( pContext->callbacks.getTime != NULL );
    bytesToReceive = pContext->networkBuffer.size;
    getTimeStampMs = pContext->callbacks.getTime;

    entryTimeMs = getTimeStampMs();

    while( ( totalBytesReceived < remainingLength ) && ( receiveError == false ) )
    {
        if( ( remainingLength - totalBytesReceived ) < bytesToReceive )
        {
            bytesToReceive = remainingLength - totalBytesReceived;
        }

        bytesReceived = recvExact( pContext, bytesToReceive, remainingTimeMs );

        if( bytesReceived != ( int32_t ) bytesToReceive )
        {
            LogError( ( "Receive error while discarding packet."
                        "ReceivedBytes=%d, ExpectedBytes=%lu.",
                        bytesReceived,
                        bytesToReceive ) );
            receiveError = true;
        }
        else
        {
            totalBytesReceived += ( uint32_t ) bytesReceived;

            elapsedTimeMs = calculateElapsedTime( getTimeStampMs(), entryTimeMs );

            /* Update remaining time and check for timeout. */
            if( elapsedTimeMs < timeoutMs )
            {
                remainingTimeMs = timeoutMs - elapsedTimeMs;
            }
            else
            {
                LogError( ( "Time expired while discarding packet." ) );
                receiveError = true;
            }
        }
    }

    if( totalBytesReceived == remainingLength )
    {
        LogError( ( "Dumped packet. DumpedBytes=%d.",
                    totalBytesReceived ) );
        /* Packet dumped, so no data is available. */
        status = MQTTNoDataAvailable;
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t receivePacket( const MQTTContext_t * pContext,
                                   MQTTPacketInfo_t incomingPacket,
                                   uint32_t remainingTimeMs )
{
    MQTTStatus_t status = MQTTSuccess;
    int32_t bytesReceived = 0;
    size_t bytesToReceive = 0U;

    assert( pContext != NULL );

    if( incomingPacket.remainingLength > pContext->networkBuffer.size )
    {
        LogError( ( "Incoming packet will be dumped: "
                    "Packet length exceeds network buffer size."
                    "PacketSize=%lu, NetworkBufferSize=%lu",
                    incomingPacket.remainingLength,
                    pContext->networkBuffer.size ) );
        status = discardPacket( pContext,
                                incomingPacket.remainingLength,
                                remainingTimeMs );
    }
    else
    {
        bytesToReceive = incomingPacket.remainingLength;
        bytesReceived = recvExact( pContext, bytesToReceive, remainingTimeMs );

        if( bytesReceived == ( int32_t ) bytesToReceive )
        {
            /* Receive successful, bytesReceived == bytesToReceive. */
            LogInfo( ( "Packet received. ReceivedBytes=%d.",
                       bytesReceived ) );
        }
        else
        {
            LogError( ( "Packet reception failed. ReceivedBytes=%d, "
                        "ExpectedBytes=%lu.",
                        bytesReceived,
                        bytesToReceive ) );
            status = MQTTRecvFailed;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static uint8_t getAckTypeToSend( MQTTPublishState_t state )
{
    uint8_t packetTypeByte = 0U;

    switch( state )
    {
        case MQTTPubAckSend:
            packetTypeByte = MQTT_PACKET_TYPE_PUBACK;
            break;

        case MQTTPubRecSend:
            packetTypeByte = MQTT_PACKET_TYPE_PUBREC;
            break;

        case MQTTPubRelSend:
            packetTypeByte = MQTT_PACKET_TYPE_PUBREL;
            break;

        case MQTTPubCompSend:
            packetTypeByte = MQTT_PACKET_TYPE_PUBCOMP;
            break;

        default:
            /* Take no action for states that do not require sending an ack. */
            break;
    }

    return packetTypeByte;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t sendPublishAcks( MQTTContext_t * pContext,
                                     uint16_t packetId,
                                     MQTTPublishState_t publishState )
{
    MQTTStatus_t status = MQTTSuccess;
    MQTTPublishState_t newState = MQTTStateNull;
    int32_t bytesSent = 0;
    uint8_t packetTypeByte = 0U;
    MQTTPubAckType_t packetType;

    assert( pContext != NULL );

    packetTypeByte = getAckTypeToSend( publishState );

    if( packetTypeByte != 0U )
    {
        packetType = getAckFromPacketType( packetTypeByte );

        status = MQTT_SerializeAck( &( pContext->networkBuffer ),
                                    packetTypeByte,
                                    packetId );

        if( status == MQTTSuccess )
        {
            bytesSent = sendPacket( pContext,
                                    pContext->networkBuffer.pBuffer,
                                    MQTT_PUBLISH_ACK_PACKET_SIZE );
        }

        if( bytesSent == ( int32_t ) MQTT_PUBLISH_ACK_PACKET_SIZE )
        {
            pContext->controlPacketSent = true;
            status = MQTT_UpdateStateAck( pContext,
                                          packetId,
                                          packetType,
                                          MQTT_SEND,
                                          &newState );

            if( status != MQTTSuccess )
            {
                LogError( ( "Failed to update state of publish %u.", packetId ) );
            }
        }
        else
        {
            LogError( ( "Failed to send ACK packet: PacketType=%02x, "
                        "SentBytes=%d, "
                        "PacketSize=%lu.",
                        packetTypeByte,
                        bytesSent,
                        MQTT_PUBLISH_ACK_PACKET_SIZE ) );
            status = MQTTSendFailed;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t handleKeepAlive( MQTTContext_t * pContext )
{
    MQTTStatus_t status = MQTTSuccess;
    uint32_t now = 0U, keepAliveMs = 0U;

    assert( pContext != NULL );
    now = pContext->callbacks.getTime();
    keepAliveMs = 1000U * ( uint32_t ) pContext->keepAliveIntervalSec;

    /* If keep alive interval is 0, it is disabled. */
    if( ( keepAliveMs != 0U ) &&
        ( calculateElapsedTime( now, pContext->lastPacketTime ) > keepAliveMs ) )
    {
        if( pContext->waitingForPingResp == true )
        {
            /* Has time expired? */
            if( calculateElapsedTime( now, pContext->pingReqSendTimeMs ) >
                pContext->pingRespTimeoutMs )
            {
                status = MQTTKeepAliveTimeout;
            }
        }
        else
        {
            status = MQTT_Ping( pContext );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t handleIncomingPublish( MQTTContext_t * pContext,
                                           MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTBadParameter;
    MQTTPublishState_t publishRecordState = MQTTStateNull;
    uint16_t packetIdentifier = 0U;
    MQTTPublishInfo_t publishInfo;
    bool duplicatePublish = false;

    assert( pContext != NULL );
    assert( pIncomingPacket != NULL );

    status = MQTT_DeserializePublish( pIncomingPacket, &packetIdentifier, &publishInfo );
    LogInfo( ( "De-serialized incoming PUBLISH packet: DeserializerResult=%d", status ) );

    if( status == MQTTSuccess )
    {
        status = MQTT_UpdateStatePublish( pContext,
                                          packetIdentifier,
                                          MQTT_RECEIVE,
                                          publishInfo.qos,
                                          &publishRecordState );

        if( status == MQTTSuccess )
        {
            LogInfo( ( "State record updated. New state=%s.",
                       MQTT_State_strerror( publishRecordState ) ) );
        }

        /* Different cases in which an incoming publish with duplicate flag is
         * handled are as listed below.
         * 1. No collision - This is the first instance of the incoming publish
         *    packet received or an earlier received packet state is lost. This
         *    will be handled as a new incoming publish for both QoS1 and QoS2
         *    publishes.
         * 2. Collision - The incoming packet was received before and a state
         *    record is present in the state engine. For QoS1 and QoS2 publishes
         *    this case can happen at 2 different cases and handling is
         *    different.
         *    a. QoS1 - If a PUBACK is not successfully sent for the incoming
         *       publish due to a connection issue, it can result in broker
         *       sending out a duplicate publish with dup flag set, when a
         *       session is reestablished. It can result in a collision in
         *       state engine. This will be handled by processing the incoming
         *       publish as a new publish ignoring the
         *       #MQTTStateCollision status from the state engine. The publish
         *       data is not passed to the application.
         *    b. QoS2 - If a PUBREC is not successfully sent for the incoming
         *       publish or the PUBREC sent is not successfully received by the
         *       broker due to a connection issue, it can result in broker
         *       sending out a duplicate publish with dup flag set, when a
         *       session is reestablished. It can result in a collision in
         *       state engine. This will be handled by ignoring the
         *       #MQTTStateCollision status from the state engine. The publish
         *       data is not passed to the application. */
        else if( ( status == MQTTStateCollision ) && ( publishInfo.dup == true ) )
        {
            status = MQTTSuccess;
            duplicatePublish = true;

            /* Calculate the state for the ack packet that needs to be sent out
             * for the duplicate incoming publish. */
            publishRecordState = MQTT_CalculateStatePublish( MQTT_RECEIVE,
                                                             publishInfo.qos );
            LogDebug( ( "Incoming publish packet with packet id %u already exists.",
                        packetIdentifier ) );
        }
        else
        {
            LogError( ( "Error in updating publish state for incoming publish with packet id %u."
                        " Error is %s",
                        packetIdentifier,
                        MQTT_Status_strerror( status ) ) );
        }
    }

    if( status == MQTTSuccess )
    {
        /* Invoke application callback to hand the buffer over to application
         * before sending acks.
         * Application callback will be invoked for all publishes, except for
         * duplicate incoming publishes. */
        if( duplicatePublish == false )
        {
            pContext->callbacks.appCallback( pContext,
                                             pIncomingPacket,
                                             packetIdentifier,
                                             &publishInfo );
        }

        /* Send PUBACK or PUBREC if necessary. */
        status = sendPublishAcks( pContext,
                                  packetIdentifier,
                                  publishRecordState );
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t handlePublishAcks( MQTTContext_t * pContext,
                                       MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTBadResponse;
    MQTTPublishState_t publishRecordState = MQTTStateNull;
    uint16_t packetIdentifier;
    MQTTPubAckType_t ackType;
    MQTTEventCallback_t appCallback;

    assert( pContext != NULL );
    assert( pIncomingPacket != NULL );
    assert( pContext->callbacks.appCallback != NULL );

    appCallback = pContext->callbacks.appCallback;

    ackType = getAckFromPacketType( pIncomingPacket->type );
    status = MQTT_DeserializeAck( pIncomingPacket, &packetIdentifier, NULL );
    LogInfo( ( "Ack packet deserialized with result: %s.",
               MQTT_Status_strerror( status ) ) );

    if( status == MQTTSuccess )
    {
        status = MQTT_UpdateStateAck( pContext,
                                      packetIdentifier,
                                      ackType,
                                      MQTT_RECEIVE,
                                      &publishRecordState );

        if( status == MQTTSuccess )
        {
            LogInfo( ( "State record updated. New state=%s.",
                       MQTT_State_strerror( publishRecordState ) ) );
        }
        else
        {
            LogError( ( "Updating the state engine for packet id %u"
                        " failed with error %s.",
                        packetIdentifier,
                        MQTT_Status_strerror( status ) ) );
        }
    }

    if( status == MQTTSuccess )
    {
        /* Invoke application callback to hand the buffer over to application
         * before sending acks. */
        appCallback( pContext, pIncomingPacket, packetIdentifier, NULL );

        /* Send PUBREL or PUBCOMP if necessary. */
        status = sendPublishAcks( pContext,
                                  packetIdentifier,
                                  publishRecordState );
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t handleIncomingAck( MQTTContext_t * pContext,
                                       MQTTPacketInfo_t * pIncomingPacket,
                                       bool manageKeepAlive )
{
    MQTTStatus_t status = MQTTBadResponse;
    uint16_t packetIdentifier = MQTT_PACKET_ID_INVALID;

    /* We should always invoke the app callback unless we receive a PINGRESP
     * and are managing keep alive, or if we receive an unknown packet. We
     * initialize this to false since the callback must be invoked before
     * sending any PUBREL or PUBCOMP. However, for other cases, we invoke it
     * at the end to reduce the complexity of this function. */
    bool invokeAppCallback = false;
    MQTTEventCallback_t appCallback = NULL;

    assert( pContext != NULL );
    assert( pIncomingPacket != NULL );

    appCallback = pContext->callbacks.appCallback;

    switch( pIncomingPacket->type )
    {
        case MQTT_PACKET_TYPE_PUBACK:
        case MQTT_PACKET_TYPE_PUBREC:
        case MQTT_PACKET_TYPE_PUBREL:
        case MQTT_PACKET_TYPE_PUBCOMP:

            /* Handle all the publish acks. The app callback is invoked here. */
            status = handlePublishAcks( pContext, pIncomingPacket );

            break;

        case MQTT_PACKET_TYPE_PINGRESP:
            status = MQTT_DeserializeAck( pIncomingPacket, &packetIdentifier, NULL );
            invokeAppCallback = ( manageKeepAlive == true ) ? false : true;

            if( ( status == MQTTSuccess ) && ( manageKeepAlive == true ) )
            {
                pContext->waitingForPingResp = false;
            }

            break;

        case MQTT_PACKET_TYPE_SUBACK:
        case MQTT_PACKET_TYPE_UNSUBACK:
            /* Deserialize and give these to the app provided callback. */
            status = MQTT_DeserializeAck( pIncomingPacket, &packetIdentifier, NULL );
            invokeAppCallback = true;
            break;

        default:
            /* Bad response from the server. */
            LogError( ( "Unexpected packet type from server: PacketType=%02x.",
                        pIncomingPacket->type ) );
            status = MQTTBadResponse;
            break;
    }

    if( ( status == MQTTSuccess ) && ( invokeAppCallback == true ) )
    {
        appCallback( pContext, pIncomingPacket, packetIdentifier, NULL );
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t receiveSingleIteration( MQTTContext_t * pContext,
                                            uint32_t remainingTimeMs,
                                            bool manageKeepAlive )
{
    MQTTStatus_t status = MQTTSuccess;
    MQTTPacketInfo_t incomingPacket;

    assert( pContext != NULL );

    status = MQTT_GetIncomingPacketTypeAndLength( pContext->transportInterface.recv,
                                                  pContext->transportInterface.pNetworkContext,
                                                  &incomingPacket );

    if( status == MQTTNoDataAvailable )
    {
        if( manageKeepAlive == true )
        {
            /* Assign status so an error can be bubbled up to application,
             * but reset it on success. */
            status = handleKeepAlive( pContext );
        }

        if( status == MQTTSuccess )
        {
            /* Reset the status to indicate that we should not try to read
             * a packet from the transport interface. */
            status = MQTTNoDataAvailable;
        }
    }
    else if( status != MQTTSuccess )
    {
        LogError( ( "Receiving incoming packet length failed. Status=%s",
                    MQTT_Status_strerror( status ) ) );
    }
    else
    {
        /* Receive packet. Remaining time is recalculated before calling this
         * function. */
        status = receivePacket( pContext, incomingPacket, remainingTimeMs );
    }

    /* Handle received packet. If no data was read then this will not execute. */
    if( status == MQTTSuccess )
    {
        incomingPacket.pRemainingData = pContext->networkBuffer.pBuffer;

        /* PUBLISH packets allow flags in the lower four bits. For other
         * packet types, they are reserved. */
        if( ( incomingPacket.type & 0xF0U ) == MQTT_PACKET_TYPE_PUBLISH )
        {
            status = handleIncomingPublish( pContext, &incomingPacket );
        }
        else
        {
            status = handleIncomingAck( pContext, &incomingPacket, manageKeepAlive );
        }
    }

    if( status == MQTTNoDataAvailable )
    {
        /* No data available is not an error. Reset to MQTTSuccess so the
         * return code will indicate success. */
        status = MQTTSuccess;
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t validateSubscribeUnsubscribeParams( const MQTTContext_t * pContext,
                                                        const MQTTSubscribeInfo_t * pSubscriptionList,
                                                        size_t subscriptionCount,
                                                        uint16_t packetId )
{
    MQTTStatus_t status = MQTTSuccess;

    /* Validate all the parameters. */
    if( ( pContext == NULL ) || ( pSubscriptionList == NULL ) )
    {
        LogError( ( "Argument cannot be NULL: pContext=%p, "
                    "pSubscriptionList=%p.",
                    pContext,
                    pSubscriptionList ) );
        status = MQTTBadParameter;
    }
    else if( subscriptionCount == 0UL )
    {
        LogError( ( "Subscription count is 0." ) );
        status = MQTTBadParameter;
    }
    else if( packetId == 0U )
    {
        LogError( ( "Packet Id for subscription packet is 0." ) );
        status = MQTTBadParameter;
    }
    else
    {
        /* Empty else MISRA 15.7 */
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t sendPublish( MQTTContext_t * pContext,
                                 const MQTTPublishInfo_t * pPublishInfo,
                                 size_t headerSize )
{
    MQTTStatus_t status = MQTTSuccess;
    int32_t bytesSent = 0;

    assert( pContext != NULL );
    assert( pPublishInfo != NULL );
    assert( headerSize > 0 );

    /* Send header first. */
    bytesSent = sendPacket( pContext,
                            pContext->networkBuffer.pBuffer,
                            headerSize );

    if( bytesSent < 0 )
    {
        LogError( ( "Transport send failed for PUBLISH header." ) );
        status = MQTTSendFailed;
    }
    else
    {
        LogDebug( ( "Sent %d bytes of PUBLISH header.",
                    bytesSent ) );

        /* Send Payload. */
        bytesSent = sendPacket( pContext,
                                pPublishInfo->pPayload,
                                pPublishInfo->payloadLength );

        if( bytesSent < 0 )
        {
            LogError( ( "Transport send failed for PUBLISH payload." ) );
            status = MQTTSendFailed;
        }
        else
        {
            LogDebug( ( "Sent %d bytes of PUBLISH payload.",
                        bytesSent ) );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t receiveConnack( const MQTTContext_t * pContext,
                                    uint32_t timeoutMs,
                                    bool cleanSession,
                                    MQTTPacketInfo_t * pIncomingPacket,
                                    bool * pSessionPresent )
{
    MQTTStatus_t status = MQTTSuccess;
    MQTTGetCurrentTimeFunc_t getTimeStamp = NULL;
    uint32_t entryTimeMs = 0U, remainingTimeMs = 0U, timeTakenMs = 0U;
    bool breakFromLoop = false;
    uint16_t loopCount = 0U;

    assert( pContext != NULL );
    assert( pIncomingPacket != NULL );
    assert( pContext->callbacks.getTime != NULL );

    getTimeStamp = pContext->callbacks.getTime;

    /* Get the entry time for the function. */
    entryTimeMs = getTimeStamp();

    do
    {
        /* Transport read for incoming CONNACK packet type and length.
         * MQTT_GetIncomingPacketTypeAndLength is a blocking call and it is
         * returned after a transport receive timeout, an error, or a successful
         * receive of packet type and length. */
        status = MQTT_GetIncomingPacketTypeAndLength( pContext->transportInterface.recv,
                                                      pContext->transportInterface.pNetworkContext,
                                                      pIncomingPacket );

        /* The loop times out based on 2 conditions.
         * 1. If timeoutMs is greater than 0:
         *    Loop times out based on the timeout calculated by getTime()
         *    function.
         * 2. If timeoutMs is 0:
         *    Loop times out based on the maximum number of retries config
         *    MQTT_MAX_CONNACK_RECEIVE_RETRY_COUNT. This config will control
         *    maximum the number of retry attempts to read the CONNACK packet.
         *    A value of 0 for the config will try once to read CONNACK. */
        if( timeoutMs > 0U )
        {
            breakFromLoop = ( calculateElapsedTime( getTimeStamp(), entryTimeMs ) >= timeoutMs ) ? true : false;
        }
        else
        {
            breakFromLoop = ( loopCount >= MQTT_MAX_CONNACK_RECEIVE_RETRY_COUNT ) ? true : false;
            loopCount++;
        }

        /* Loop until there is data to read or if we have exceeded the timeout/retries. */
    } while( ( status == MQTTNoDataAvailable ) && ( breakFromLoop == false ) );

    if( status == MQTTSuccess )
    {
        /* Time taken in this function so far. */
        timeTakenMs = calculateElapsedTime( getTimeStamp(), entryTimeMs );

        if( timeTakenMs < timeoutMs )
        {
            /* Calculate remaining time for receiving the remainder of
             * the packet. */
            remainingTimeMs = timeoutMs - timeTakenMs;
        }

        /* Reading the remainder of the packet by transport recv.
         * Attempt to read once even if the timeout has expired.
         * Invoking receivePacket with remainingTime as 0 would attempt to
         * recv from network once. If using retries, the remainder of the
         * CONNACK packet is tried to be read only once. Reading once would be
         * good as the packet type and remaining length was already read. Hence,
         * the probability of the remaining 2 bytes available to read is very high. */
        if( pIncomingPacket->type == MQTT_PACKET_TYPE_CONNACK )
        {
            status = receivePacket( pContext,
                                    *pIncomingPacket,
                                    remainingTimeMs );
        }
        else
        {
            LogError( ( "Incorrect packet type %X received while expecting"
                        " CONNACK(%X).",
                        pIncomingPacket->type,
                        MQTT_PACKET_TYPE_CONNACK ) );
            status = MQTTBadResponse;
        }
    }

    if( status == MQTTSuccess )
    {
        /* Update the packet info pointer to the buffer read. */
        pIncomingPacket->pRemainingData = pContext->networkBuffer.pBuffer;

        /* Deserialize CONNACK. */
        status = MQTT_DeserializeAck( pIncomingPacket, NULL, pSessionPresent );
    }

    /* If a clean session is requested, a session present should not be set by
     * broker. */
    if( status == MQTTSuccess )
    {
        if( ( cleanSession == true ) && ( *pSessionPresent == true ) )
        {
            LogError( ( "Unexpected session present flag in CONNACK response from broker."
                        " CONNECT request with clean session was made with broker." ) );
            status = MQTTBadResponse;
        }
    }

    if( status == MQTTSuccess )
    {
        LogInfo( ( "Received MQTT CONNACK successfully from broker." ) );
    }
    else
    {
        LogError( ( "CONNACK recv failed with status = %s.",
                    MQTT_Status_strerror( status ) ) );
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t resendPendingAcks( MQTTContext_t * pContext )
{
    MQTTStatus_t status = MQTTSuccess;
    MQTTStateCursor_t cursor = MQTT_STATE_CURSOR_INITIALIZER;
    uint16_t packetId = MQTT_PACKET_ID_INVALID;
    MQTTPublishState_t state = MQTTStateNull;

    assert( pContext != NULL );

    /* Get the next packet Id for which a PUBREL need to be resent. */
    packetId = MQTT_PubrelToResend( pContext, &cursor, &state );

    /* Resend all the PUBREL acks after session is reestablished. */
    while( ( packetId != MQTT_PACKET_ID_INVALID ) &&
           ( status == MQTTSuccess ) )
    {
        status = sendPublishAcks( pContext, packetId, state );

        packetId = MQTT_PubrelToResend( pContext, &cursor, &state );
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t serializePublish( const MQTTContext_t * pContext,
                                      const MQTTPublishInfo_t * pPublishInfo,
                                      uint16_t packetId,
                                      size_t * const pHeaderSize )
{
    MQTTStatus_t status = MQTTSuccess;
    size_t remainingLength = 0UL, packetSize = 0UL;

    assert( pContext != NULL );
    assert( pPublishInfo != NULL );
    assert( pHeaderSize != NULL );

    /* Get the remaining length and packet size.*/
    status = MQTT_GetPublishPacketSize( pPublishInfo,
                                        &remainingLength,
                                        &packetSize );
    LogDebug( ( "PUBLISH packet size is %lu and remaining length is %lu.",
                packetSize,
                remainingLength ) );

    if( status == MQTTSuccess )
    {
        status = MQTT_SerializePublishHeader( pPublishInfo,
                                              packetId,
                                              remainingLength,
                                              &( pContext->networkBuffer ),
                                              pHeaderSize );
        LogDebug( ( "Serialized PUBLISH header size is %lu.",
                    *pHeaderSize ) );
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t validatePublishParams( const MQTTContext_t * pContext,
                                           const MQTTPublishInfo_t * pPublishInfo,
                                           uint16_t packetId )
{
    MQTTStatus_t status = MQTTSuccess;

    /* Validate arguments. */
    if( ( pContext == NULL ) || ( pPublishInfo == NULL ) )
    {
        LogError( ( "Argument cannot be NULL: pContext=%p, "
                    "pPublishInfo=%p.",
                    pContext,
                    pPublishInfo ) );
        status = MQTTBadParameter;
    }
    else if( ( pPublishInfo->qos != MQTTQoS0 ) && ( packetId == 0U ) )
    {
        LogError( ( "Packet Id is 0 for PUBLISH with QoS=%u.",
                    pPublishInfo->qos ) );
        status = MQTTBadParameter;
    }
    else
    {
        /* Empty else MISRA 15.7 */
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_Init( MQTTContext_t * pContext,
                        const TransportInterface_t * pTransportInterface,
                        const MQTTApplicationCallbacks_t * pCallbacks,
                        const MQTTFixedBuffer_t * pNetworkBuffer )
{
    MQTTStatus_t status = MQTTSuccess;

    /* Validate arguments. */
    if( ( pContext == NULL ) || ( pTransportInterface == NULL ) ||
        ( pCallbacks == NULL ) || ( pNetworkBuffer == NULL ) )
    {
        LogError( ( "Argument cannot be NULL: pContext=%p, "
                    "pTransportInterface=%p, "
                    "pCallbacks=%p, "
                    "pNetworkBuffer=%p.",
                    pContext,
                    pTransportInterface,
                    pCallbacks,
                    pNetworkBuffer ) );
        status = MQTTBadParameter;
    }
    else if( ( pCallbacks->getTime == NULL ) || ( pCallbacks->appCallback == NULL ) ||
             ( pTransportInterface->recv == NULL ) || ( pTransportInterface->send == NULL ) )
    {
        LogError( ( "Functions cannot be NULL: getTime=%p, appCallback=%p, recv=%p, send=%p.",
                    pCallbacks->getTime,
                    pCallbacks->appCallback,
                    pTransportInterface->recv,
                    pTransportInterface->send ) );
        status = MQTTBadParameter;
    }
    else
    {
        ( void ) memset( pContext, 0x00, sizeof( MQTTContext_t ) );

        pContext->connectStatus = MQTTNotConnected;
        pContext->transportInterface = *pTransportInterface;
        pContext->callbacks = *pCallbacks;
        pContext->networkBuffer = *pNetworkBuffer;

        /* Zero is not a valid packet ID per MQTT spec. Start from 1. */
        pContext->nextPacketId = 1;
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_Connect( MQTTContext_t * pContext,
                           const MQTTConnectInfo_t * pConnectInfo,
                           const MQTTPublishInfo_t * pWillInfo,
                           uint32_t timeoutMs,
                           bool * pSessionPresent )
{
    size_t remainingLength = 0UL, packetSize = 0UL;
    int32_t bytesSent;
    MQTTStatus_t status = MQTTSuccess;
    MQTTPacketInfo_t incomingPacket = { 0 };

    incomingPacket.type = ( uint8_t ) 0;

    if( ( pContext == NULL ) || ( pConnectInfo == NULL ) || ( pSessionPresent == NULL ) )
    {
        LogError( ( "Argument cannot be NULL: pContext=%p, "
                    "pConnectInfo=%p, pSessionPresent=%p.",
                    pContext,
                    pConnectInfo,
                    pSessionPresent ) );
        status = MQTTBadParameter;
    }

    if( status == MQTTSuccess )
    {
        /* Get MQTT connect packet size and remaining length. */
        status = MQTT_GetConnectPacketSize( pConnectInfo,
                                            pWillInfo,
                                            &remainingLength,
                                            &packetSize );
        LogDebug( ( "CONNECT packet size is %lu and remaining length is %lu.",
                    packetSize,
                    remainingLength ) );
    }

    if( status == MQTTSuccess )
    {
        status = MQTT_SerializeConnect( pConnectInfo,
                                        pWillInfo,
                                        remainingLength,
                                        &( pContext->networkBuffer ) );
    }

    if( status == MQTTSuccess )
    {
        bytesSent = sendPacket( pContext,
                                pContext->networkBuffer.pBuffer,
                                packetSize );

        if( bytesSent < 0 )
        {
            LogError( ( "Transport send failed for CONNECT packet." ) );
            status = MQTTSendFailed;
        }
        else
        {
            LogDebug( ( "Sent %d bytes of CONNECT packet.",
                        bytesSent ) );
        }
    }

    /* Read CONNACK from transport layer. */
    if( status == MQTTSuccess )
    {
        status = receiveConnack( pContext,
                                 timeoutMs,
                                 pConnectInfo->cleanSession,
                                 &incomingPacket,
                                 pSessionPresent );
    }

    /* Resend all the PUBREL when reestablishing a session. */
    if( ( status == MQTTSuccess ) && ( *pSessionPresent == true ) )
    {
        status = resendPendingAcks( pContext );
    }

    if( status == MQTTSuccess )
    {
        LogInfo( ( "MQTT connection established with the broker." ) );
        pContext->connectStatus = MQTTConnected;
        pContext->keepAliveIntervalSec = pConnectInfo->keepAliveSeconds;
    }
    else
    {
        LogError( ( "MQTT connection failed with status = %s.",
                    MQTT_Status_strerror( status ) ) );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_Subscribe( MQTTContext_t * pContext,
                             const MQTTSubscribeInfo_t * pSubscriptionList,
                             size_t subscriptionCount,
                             uint16_t packetId )
{
    size_t remainingLength = 0UL, packetSize = 0UL;
    int32_t bytesSent = 0;

    /* Validate arguments. */
    MQTTStatus_t status = validateSubscribeUnsubscribeParams( pContext,
                                                              pSubscriptionList,
                                                              subscriptionCount,
                                                              packetId );

    if( status == MQTTSuccess )
    {
        /* Get the remaining length and packet size.*/
        status = MQTT_GetSubscribePacketSize( pSubscriptionList,
                                              subscriptionCount,
                                              &remainingLength,
                                              &packetSize );
        LogDebug( ( "SUBSCRIBE packet size is %lu and remaining length is %lu.",
                    packetSize,
                    remainingLength ) );
    }

    if( status == MQTTSuccess )
    {
        /* Serialize MQTT SUBSCRIBE packet. */
        status = MQTT_SerializeSubscribe( pSubscriptionList,
                                          subscriptionCount,
                                          packetId,
                                          remainingLength,
                                          &( pContext->networkBuffer ) );
    }

    if( status == MQTTSuccess )
    {
        /* Send serialized MQTT SUBSCRIBE packet to transport layer. */
        bytesSent = sendPacket( pContext,
                                pContext->networkBuffer.pBuffer,
                                packetSize );

        if( bytesSent < 0 )
        {
            LogError( ( "Transport send failed for SUBSCRIBE packet." ) );
            status = MQTTSendFailed;
        }
        else
        {
            LogDebug( ( "Sent %d bytes of SUBSCRIBE packet.",
                        bytesSent ) );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_Publish( MQTTContext_t * pContext,
                           const MQTTPublishInfo_t * pPublishInfo,
                           uint16_t packetId )
{
    size_t headerSize = 0UL;
    MQTTPublishState_t publishStatus = MQTTStateNull;

    /* Validate arguments. */
    MQTTStatus_t status = validatePublishParams( pContext, pPublishInfo, packetId );

    if( status == MQTTSuccess )
    {
        /* Serialize PUBLISH packet. */
        status = serializePublish( pContext,
                                   pPublishInfo,
                                   packetId,
                                   &headerSize );
    }

    if( ( status == MQTTSuccess ) && ( pPublishInfo->qos > MQTTQoS0 ) )
    {
        /* Reserve state for publish message. Only to be done for QoS1 or QoS2. */
        status = MQTT_ReserveState( pContext,
                                    packetId,
                                    pPublishInfo->qos );

        /* State already exists for a duplicate packet.
         * If a state doesn't exist, it will be handled as a new publish in
         * state engine. */
        if( ( status == MQTTStateCollision ) && ( pPublishInfo->dup == true ) )
        {
            status = MQTTSuccess;
        }
    }

    if( status == MQTTSuccess )
    {
        /* Sends the serialized publish packet over network. */
        status = sendPublish( pContext,
                              pPublishInfo,
                              headerSize );
    }

    if( ( status == MQTTSuccess ) && ( pPublishInfo->qos > MQTTQoS0 ) )
    {
        /* Update state machine after PUBLISH is sent.
         * Only to be done for QoS1 or QoS2. */
        status = MQTT_UpdateStatePublish( pContext,
                                          packetId,
                                          MQTT_SEND,
                                          pPublishInfo->qos,
                                          &publishStatus );

        if( status != MQTTSuccess )
        {
            LogError( ( "Update state for publish failed with status %s."
                        " However PUBLISH packet was sent to the broker."
                        " Any further handling of ACKs for the packet Id"
                        " will fail.",
                        MQTT_Status_strerror( status ) ) );
        }
    }

    if( status != MQTTSuccess )
    {
        LogError( ( "MQTT PUBLISH failed with status %s.",
                    MQTT_Status_strerror( status ) ) );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_Ping( MQTTContext_t * pContext )
{
    int32_t bytesSent = 0;
    MQTTStatus_t status = MQTTSuccess;
    size_t packetSize = 0U;

    if( pContext == NULL )
    {
        LogError( ( "pContext is NULL." ) );
        status = MQTTBadParameter;
    }

    if( status == MQTTSuccess )
    {
        /* Get MQTT PINGREQ packet size. */
        status = MQTT_GetPingreqPacketSize( &packetSize );

        if( status == MQTTSuccess )
        {
            LogDebug( ( "MQTT PINGREQ packet size is %lu.",
                        packetSize ) );
        }
        else
        {
            LogError( ( "Failed to get the PINGREQ packet size." ) );
        }
    }

    if( status == MQTTSuccess )
    {
        /* Serialize MQTT PINGREQ. */
        status = MQTT_SerializePingreq( &( pContext->networkBuffer ) );
    }

    if( status == MQTTSuccess )
    {
        /* Send the serialized PINGREQ packet to transport layer. */
        bytesSent = sendPacket( pContext,
                                pContext->networkBuffer.pBuffer,
                                packetSize );

        if( bytesSent < 0 )
        {
            LogError( ( "Transport send failed for PINGREQ packet." ) );
            status = MQTTSendFailed;
        }
        else
        {
            pContext->pingReqSendTimeMs = pContext->lastPacketTime;
            pContext->waitingForPingResp = true;
            LogDebug( ( "Sent %d bytes of PINGREQ packet.",
                        bytesSent ) );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_Unsubscribe( MQTTContext_t * pContext,
                               const MQTTSubscribeInfo_t * pSubscriptionList,
                               size_t subscriptionCount,
                               uint16_t packetId )
{
    size_t remainingLength = 0UL, packetSize = 0UL;
    int32_t bytesSent = 0;

    /* Validate arguments. */
    MQTTStatus_t status = validateSubscribeUnsubscribeParams( pContext,
                                                              pSubscriptionList,
                                                              subscriptionCount,
                                                              packetId );

    if( status == MQTTSuccess )
    {
        /* Get the remaining length and packet size.*/
        status = MQTT_GetUnsubscribePacketSize( pSubscriptionList,
                                                subscriptionCount,
                                                &remainingLength,
                                                &packetSize );
        LogDebug( ( "UNSUBSCRIBE packet size is %lu and remaining length is %lu.",
                    packetSize,
                    remainingLength ) );
    }

    if( status == MQTTSuccess )
    {
        /* Serialize MQTT UNSUBSCRIBE packet. */
        status = MQTT_SerializeUnsubscribe( pSubscriptionList,
                                            subscriptionCount,
                                            packetId,
                                            remainingLength,
                                            &( pContext->networkBuffer ) );
    }

    if( status == MQTTSuccess )
    {
        /* Send serialized MQTT UNSUBSCRIBE packet to transport layer. */
        bytesSent = sendPacket( pContext,
                                pContext->networkBuffer.pBuffer,
                                packetSize );

        if( bytesSent < 0 )
        {
            LogError( ( "Transport send failed for UNSUBSCRIBE packet." ) );
            status = MQTTSendFailed;
        }
        else
        {
            LogDebug( ( "Sent %d bytes of UNSUBSCRIBE packet.",
                        bytesSent ) );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_Disconnect( MQTTContext_t * pContext )
{
    size_t packetSize = 0U;
    int32_t bytesSent = 0;
    MQTTStatus_t status = MQTTSuccess;

    /* Validate arguments. */
    if( pContext == NULL )
    {
        LogError( ( "pContext cannot be NULL." ) );
        status = MQTTBadParameter;
    }

    if( status == MQTTSuccess )
    {
        /* Get MQTT DISCONNECT packet size. */
        status = MQTT_GetDisconnectPacketSize( &packetSize );
        LogDebug( ( "MQTT DISCONNECT packet size is %lu.",
                    packetSize ) );
    }

    if( status == MQTTSuccess )
    {
        /* Serialize MQTT DISCONNECT packet. */
        status = MQTT_SerializeDisconnect( &( pContext->networkBuffer ) );
    }

    if( status == MQTTSuccess )
    {
        bytesSent = sendPacket( pContext,
                                pContext->networkBuffer.pBuffer,
                                packetSize );

        if( bytesSent < 0 )
        {
            LogError( ( "Transport send failed for DISCONNECT packet." ) );
            status = MQTTSendFailed;
        }
        else
        {
            LogDebug( ( "Sent %d bytes of DISCONNECT packet.",
                        bytesSent ) );
        }
    }

    if( status == MQTTSuccess )
    {
        LogInfo( ( "Disconnected from the broker." ) );
        pContext->connectStatus = MQTTNotConnected;
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_ProcessLoop( MQTTContext_t * pContext,
                               uint32_t timeoutMs )
{
    MQTTStatus_t status = MQTTBadParameter;
    MQTTGetCurrentTimeFunc_t getTimeStampMs = NULL;
    uint32_t entryTimeMs = 0U, remainingTimeMs = timeoutMs, elapsedTimeMs = 0U;

    if( ( pContext != NULL ) && ( pContext->callbacks.getTime != NULL ) )
    {
        getTimeStampMs = pContext->callbacks.getTime;
        entryTimeMs = getTimeStampMs();
        status = MQTTSuccess;
        pContext->controlPacketSent = false;
    }
    else if( pContext == NULL )
    {
        LogError( ( "MQTT Context cannot be NULL." ) );
    }
    else
    {
        LogError( ( "MQTT Context must set callbacks.getTime." ) );
    }

    while( status == MQTTSuccess )
    {
        status = receiveSingleIteration( pContext, remainingTimeMs, true );

        /* We don't need to break here since the status is already checked in
         * the loop condition, and we do not want multiple breaks in a loop. */
        if( status != MQTTSuccess )
        {
            LogError( ( "Exiting process loop. Error status=%s",
                        MQTT_Status_strerror( status ) ) );
        }
        else
        {
            /* Recalculate remaining time and check if loop should exit. This is
             * done at the end so the loop will run at least a single iteration. */
            elapsedTimeMs = calculateElapsedTime( getTimeStampMs(), entryTimeMs );

            if( elapsedTimeMs > timeoutMs )
            {
                break;
            }

            remainingTimeMs = timeoutMs - elapsedTimeMs;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_ReceiveLoop( MQTTContext_t * pContext,
                               uint32_t timeoutMs )
{
    MQTTStatus_t status = MQTTBadParameter;
    MQTTGetCurrentTimeFunc_t getTimeStampMs = NULL;
    uint32_t entryTimeMs = 0U, remainingTimeMs = timeoutMs, elapsedTimeMs = 0U;

    if( ( pContext != NULL ) && ( pContext->callbacks.getTime != NULL ) )
    {
        getTimeStampMs = pContext->callbacks.getTime;
        entryTimeMs = getTimeStampMs();
        status = MQTTSuccess;
    }
    else if( pContext == NULL )
    {
        LogError( ( "MQTT Context cannot be NULL." ) );
    }
    else
    {
        LogError( ( "MQTT Context must set callbacks.getTime." ) );
    }

    while( status == MQTTSuccess )
    {
        status = receiveSingleIteration( pContext, remainingTimeMs, false );

        /* We don't need to break here since the status is already checked in
         * the loop condition, and we do not want multiple breaks in a loop. */
        if( status != MQTTSuccess )
        {
            LogError( ( "Exiting receive loop. Error status=%s",
                        MQTT_Status_strerror( status ) ) );
        }
        else
        {
            /* Recalculate remaining time and check if loop should exit. This is
             * done at the end so the loop will run at least a single iteration. */
            elapsedTimeMs = calculateElapsedTime( getTimeStampMs(), entryTimeMs );

            if( elapsedTimeMs >= timeoutMs )
            {
                break;
            }

            remainingTimeMs = timeoutMs - elapsedTimeMs;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

uint16_t MQTT_GetPacketId( MQTTContext_t * pContext )
{
    uint16_t packetId = 0U;

    if( pContext != NULL )
    {
        packetId = pContext->nextPacketId;

        /* A packet ID of zero is not a valid packet ID. When the max ID
         * is reached the next one should start at 1. */
        if( pContext->nextPacketId == ( uint16_t ) UINT16_MAX )
        {
            pContext->nextPacketId = 1;
        }
        else
        {
            pContext->nextPacketId++;
        }
    }

    return packetId;
}

/*-----------------------------------------------------------*/

const char * MQTT_Status_strerror( MQTTStatus_t status )
{
    const char * str = NULL;

    switch( status )
    {
        case MQTTSuccess:
            str = "MQTTSuccess";
            break;

        case MQTTBadParameter:
            str = "MQTTBadParameter";
            break;

        case MQTTNoMemory:
            str = "MQTTNoMemory";
            break;

        case MQTTSendFailed:
            str = "MQTTSendFailed";
            break;

        case MQTTRecvFailed:
            str = "MQTTRecvFailed";
            break;

        case MQTTBadResponse:
            str = "MQTTBadResponse";
            break;

        case MQTTServerRefused:
            str = "MQTTServerRefused";
            break;

        case MQTTNoDataAvailable:
            str = "MQTTNoDataAvailable";
            break;

        case MQTTIllegalState:
            str = "MQTTIllegalState";
            break;

        case MQTTStateCollision:
            str = "MQTTStateCollision";
            break;

        case MQTTKeepAliveTimeout:
            str = "MQTTKeepAliveTimeout";
            break;

        default:
            str = "Invalid MQTT Status code";
            break;
    }

    return str;
}

/*-----------------------------------------------------------*/
