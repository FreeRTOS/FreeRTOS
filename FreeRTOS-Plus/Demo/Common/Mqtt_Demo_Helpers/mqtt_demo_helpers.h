/*
 * FreeRTOS V202011.00
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

#ifndef MQTT_DEMO_HELPERS_H
#define MQTT_DEMO_HELPERS_H

/* MQTT API header. */
#include "core_mqtt.h"

/* Transport interface implementation include header for TLS. */
#include "using_mbedtls.h"

/**
 * @brief Establish a MQTT connection.
 *
 * @param[in, out] pxContext The memory for the MQTTContext_t that will be used for the
 * MQTT connection.
 * @param[out] pxNetworkContext The memory for the NetworkContext_t required for the
 * MQTT connection.
 * @param[in] pxNetworkBuffer The buffer space for initializing the @p pxContext MQTT
 * context used in the MQTT connection.
 * @param[in] appCallback The callback function used to receive incoming
 * publishes and incoming acks from MQTT library.
 *
 * @return The status of the final connection attempt.
 */
BaseType_t xEstablishMqttSession( MQTTContext_t * pxMqttContext,
                                  NetworkContext_t * pxNetContext,
                                  MQTTFixedBuffer_t * pxNetworkBuffer,
                                  MQTTEventCallback_t eventCallback );

/**
 * @brief Handle the incoming packet if it's not related to the device shadow.
 *
 * @param[in] pxPacketInfo Packet Info pointer for the incoming packet.
 * @param[in] usPacketIdentifier Packet identifier of the incoming packet.
 */
void vHandleOtherIncomingPacket( MQTTPacketInfo_t * pxPacketInfo,
                                 uint16_t usPacketIdentifier );

/**
 * @brief Close the MQTT connection.
 *
 * @param[in] pxContext The MQTT context for the MQTT connection to close.
 *
 * @return pdPASS if DISCONNECT was successfully sent;
 * pdFAIL otherwise.
 */
BaseType_t xDisconnectMqttSession( MQTTContext_t * pxContext,
                                   NetworkContext_t * pxNetContext );

/**
 * @brief Subscribe to a MQTT topic filter.
 *
 * @param[in] pxContext The MQTT context for the MQTT connection to close.
 * @param[in] pcTopicFilter Pointer to the shadow topic buffer.
 * @param[in] usTopicFilterLength Indicates the length of the shadow
 * topic buffer.
 *
 * @return pdPASS if SUBSCRIBE was successfully sent;
 * pdFAIL otherwise.
 */
BaseType_t xSubscribeToTopic( MQTTContext_t * pxContext,
                              const char * pcTopicFilter,
                              uint16_t usTopicFilterLength );

/**
 * @brief Sends an MQTT UNSUBSCRIBE to unsubscribe from the shadow
 * topic.
 *
 * @param[in] pxContext The MQTT context for the MQTT connection.
 * @param[in] pcTopicFilter Pointer to the shadow topic buffer.
 * @param[in] usTopicFilterLength Indicates the length of the shadow
 * topic buffer.
 *
 * @return pdPASS if UNSUBSCRIBE was successfully sent;
 * pdFAIL otherwise.
 */
BaseType_t xUnsubscribeFromTopic( MQTTContext_t * pxContext,
                                  const char * pcTopicFilter,
                                  uint16_t usTopicFilterLength );

/**
 * @brief Publish a message to a MQTT topic.
 *
 * @param[in] pxContext The MQTT context for the MQTT connection.
 * @param[in] pcTopicFilter Points to the topic.
 * @param[in] topicFilterLength The length of the topic.
 * @param[in] pcPayload Points to the payload.
 * @param[in] payloadLength The length of the payload.
 *
 * @return pdPASS if PUBLISH was successfully sent;
 * pdFAIL otherwise.
 */
BaseType_t xPublishToTopic( MQTTContext_t * pxContext,
                            const char * pcTopicFilter,
                            int32_t topicFilterLength,
                            const char * pcPayload,
                            size_t payloadLength );

#endif /* ifndef MQTT_DEMO_HELPERS_H */
