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

#ifndef MQTT_STATE_H
#define MQTT_STATE_H

#include "mqtt.h"

#define MQTT_STATE_CURSOR_INITIALIZER    ( size_t ) 0

/**
 * @brief Value indicating either send or receive.
 */
typedef enum MQTTStateOperation
{
    MQTT_SEND,
    MQTT_RECEIVE
} MQTTStateOperation_t;

/**
 * @brief Cursor for iterating through state records.
 */
typedef size_t MQTTStateCursor_t;

/**
 * @brief Reserve an entry for an outgoing QoS 1/2 publish.
 *
 * @param[in] pMqttContext Initialized MQTT context.
 * @param[in] packetId The ID of the publish packet.
 * @param[in] qos 1 or 2.
 *
 * @return MQTTSuccess, MQTTNoMemory, or MQTTStateCollision.
 */
MQTTStatus_t MQTT_ReserveState( MQTTContext_t * pMqttContext,
                                uint16_t packetId,
                                MQTTQoS_t qos );

/**
 * @brief Calculate the new state for a publish from its qos and operation type.
 *
 * @param[in] opType Send or Receive.
 * @param[in] qos 0, 1, or 2.
 *
 * @return The calculated state.
 */
MQTTPublishState_t MQTT_CalculateStatePublish( MQTTStateOperation_t opType,
                                               MQTTQoS_t qos );

/**
 * @brief Update the state record for a PUBLISH packet.
 *
 * @param[in] pMqttContext Initialized MQTT context.
 * @param[in] packetId ID of the PUBLISH packet.
 * @param[in] opType Send or Receive.
 * @param[in] qos 0, 1, or 2.
 * @param[out] pNewState Updated state of the publish.
 *
 * @return #MQTTBadParameter, #MQTTIllegalState, #MQTTStateCollision or
 * #MQTTSuccess.
 */
MQTTStatus_t MQTT_UpdateStatePublish( MQTTContext_t * pMqttContext,
                                      uint16_t packetId,
                                      MQTTStateOperation_t opType,
                                      MQTTQoS_t qos,
                                      MQTTPublishState_t * pNewState );

/**
 * @brief Calculate the state from a PUBACK, PUBREC, PUBREL, or PUBCOMP.
 *
 * @param[in] packetType PUBACK, PUBREC, PUBREL, or PUBCOMP.
 * @param[in] opType Send or Receive.
 * @param[in] qos 1 or 2.
 *
 * @return The calculated state.
 */
MQTTPublishState_t MQTT_CalculateStateAck( MQTTPubAckType_t packetType,
                                           MQTTStateOperation_t opType,
                                           MQTTQoS_t qos );

/**
 * @brief Update the state record for an ACKed publish.
 *
 * @param[in] pMqttContext Initialized MQTT context.
 * @param[in] packetId ID of the ack packet.
 * @param[in] packetType PUBACK, PUBREC, PUBREL, or PUBCOMP.
 * @param[in] opType Send or Receive.
 * @param[out] pNewState Updated state of the publish.
 *
 * @return #MQTTBadParameter, #MQTTIllegalState, or #MQTTSuccess.
 */
MQTTStatus_t MQTT_UpdateStateAck( MQTTContext_t * pMqttContext,
                                  uint16_t packetId,
                                  MQTTPubAckType_t packetType,
                                  MQTTStateOperation_t opType,
                                  MQTTPublishState_t * pNewState );

/**
 * @brief Get the packet ID of next pending PUBREL ack to be resent.
 *
 * This function will need to be called to get the packet for which a PUBREL
 * need to be sent when a session is reestablished. Calling this function
 * repeatedly until packet id is 0 will give all the packets for which
 * a PUBREL need to be resent in the correct order.
 *
 * @param[in] pMqttContext Initialized MQTT context.
 * @param[in,out] pCursor Index at which to start searching.
 * @param[out] pState State indicating that PUBREL packet need to be sent.
 */
uint16_t MQTT_PubrelToResend( const MQTTContext_t * pMqttContext,
                              MQTTStateCursor_t * pCursor,
                              MQTTPublishState_t * pState );

/**
 * @brief Get the packet ID of next pending publish to be resent.
 *
 * This function will need to be called to get the packet for which a publish
 * need to be sent when a session is reestablished. Calling this function
 * repeatedly until packet id is 0 will give all the packets for which
 * a publish need to be resent in the correct order.
 *
 * @param[in] pMqttContext Initialized MQTT context.
 * @param[in,out] pCursor Index at which to start searching.
 */
uint16_t MQTT_PublishToResend( const MQTTContext_t * pMqttContext,
                               MQTTStateCursor_t * pCursor );

/**
 * @brief State to string conversion for state engine.
 *
 * @param[in] state The state to convert to a string.
 *
 * @return The string representation of the state.
 */
const char * MQTT_State_strerror( MQTTPublishState_t state );

#endif /* ifndef MQTT_STATE_H */
