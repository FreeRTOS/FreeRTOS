/*
 * FreeRTOS V202112.00
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
 *
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

#ifndef MQTT_OPERATIONS_H_
#define MQTT_OPERATIONS_H_

/* MQTT API header. */
#include "core_mqtt.h"

/* corePKCS11 include. */
#include "core_pkcs11.h"

/**
 * @brief Application callback type to handle the incoming publishes.
 *
 * @param[in] pxPublishInfo Pointer to publish info of the incoming publish.
 * @param[in] usPacketIdentifier Packet identifier of the incoming publish.
 */
typedef void (* MQTTPublishCallback_t )( MQTTPublishInfo_t * pxPublishInfo,
                                         uint16_t usPacketIdentifier );

/**
 * @brief Establish a MQTT connection.
 *
 * @param[in] xPublishCallback The callback function to receive incoming
 * publishes from the MQTT broker.
 * @param[in] pcClientCertLabel The client certificate PKCS #11 label to use.
 * @param[in] pcPrivateKeyLabel The private key PKCS #11 label for the client certificate.
 *
 * @return true if an MQTT session is established;
 * false otherwise.
 */
bool xEstablishMqttSession( MQTTPublishCallback_t xPublishCallback,
                            char * pcClientCertLabel,
                            char * pcPrivateKeyLabel );

/**
 * @brief Disconnect the MQTT connection.
 *
 * @return true if the MQTT session was successfully disconnected;
 * false otherwise.
 */
bool xDisconnectMqttSession( void );

/**
 * @brief Subscribe to a MQTT topic filter.
 *
 * @param[in] pcTopicFilter The topic filter to subscribe to.
 * @param[in] usTopicFilterLength Length of the topic buffer.
 *
 * @return true if subscribe operation was successful;
 * false otherwise.
 */
bool xSubscribeToTopic( const char * pcTopicFilter,
                        uint16_t usTopicFilterLength );

/**
 * @brief Unsubscribe from a MQTT topic filter.
 *
 * @param[in] pcTopicFilter The topic filter to unsubscribe from.
 * @param[in] usTopicFilterLength Length of the topic buffer.
 *
 * @return true if unsubscribe operation was successful;
 * false otherwise.
 */
bool xUnsubscribeFromTopic( const char * pcTopicFilter,
                            uint16_t usTopicFilterLength );

/**
 * @brief Publish a message to a MQTT topic.
 *
 * @param[in] pcTopic The topic to publish the message on.
 * @param[in] usTopicLength Length of the topic.
 * @param[in] pcMessage The message to publish.
 * @param[in] xMessageLength Length of the message.
 *
 * @return true if PUBLISH was successfully sent;
 * false otherwise.
 */
bool xPublishToTopic( const char * pcTopic,
                      uint16_t usTopicLength,
                      const char * pcMessage,
                      size_t xMessageLength );

/**
 * @brief Invoke the core MQTT library's process loop function.
 *
 * @return true if process loop was successful;
 * false otherwise.
 */
bool xProcessLoop( void );

#endif /* ifndef MQTT_OPERATIONS_H_ */
