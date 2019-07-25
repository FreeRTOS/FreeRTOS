/*
 * Amazon FreeRTOS MQTT V2.0.0
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
 *
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

/**
 * @file iot_mqtt_lib.h
 * @brief MQTT Core Library interface.
 */

#ifndef _AWS_MQTT_LIB_H_
#define _AWS_MQTT_LIB_H_

/* This ifndef enables the core MQTT library to be used without
 * providing MQTTConfig.h. All the config values in this case are
 * taken from MQTTConfigDefaults.h. */
#ifndef mqttDO_NOT_USE_CUSTOM_CONFIG
    #include "aws_mqtt_config.h"
#endif
#include "iot_mqtt_config_defaults.h"

#include "iot_doubly_linked_list.h"

 /**
  * @brief Opaque handle to represent an MQTT buffer.
  */
typedef void * MQTTBufferHandle_t;

/**
 * @brief Boolean type.
 */
typedef enum
{
    eMQTTFalse = 0, /**< Boolean False. */
    eMQTTTrue = 1   /**< Boolean True. */
} MQTTBool_t;

/**
 * @brief Quality of Service (qos).
 */
typedef enum
{
    eMQTTQoS0 = 0, /**< Quality of Service 0 - Fire and Forget. No ACK. */
    eMQTTQoS1 = 1, /**< Quality of Service 1 - Wait till ACK or Timeout. */
    eMQTTQoS2 = 2  /**< Quality of Service 2 - Not supported. */
} MQTTQoS_t;

/**
 * @brief The data sent by the MQTT library in the user supplied callback
 * when a publish message from the broker is received.
 */
typedef struct MQTTPublishData
{
    MQTTQoS_t xQos;             /**< Quality of Service (qos). */
    const uint8_t * pucTopic;   /**< The topic on which the message is received. */
    uint16_t usTopicLength;     /**< Length of the topic. */
    const void * pvData;        /**< The received message. */
    uint32_t ulDataLength;      /**< Length of the message. */
    MQTTBufferHandle_t xBuffer; /**< The buffer containing the whole MQTT message. Both pcTopic and pvData are pointers to the locations in this buffer. */
} MQTTPublishData_t;

/**
 * @brief Signature of the user supplied topic specific publish callback which gets called
 * whenever a publish message is received on the topic this callback is registered for.
 *
 * The user can choose to register this optional topic specific callback while subscribing to
 * a topic. Whenever a publish message is received on the topic, this callback is invoked. If
 * the user chooses not to enable subscription management or chooses not to register a topic
 * specific callback, the generic callback supplied during Init is invoked.
 *
 * @param[in] pvPublishCallbackContext The callback context as supplied by the user in the
 * subscribe parameters.
 * @param[in] pxPublishData The publish data.
 *
 * @return The return value is interpreted as follows:
 * 1. If eMQTTTrue is returned - the ownership of the buffer passed in the callback (xBuffer
 * in MQTTPublishData_t) lies with the user.
 * 2. If eMQTTFalse is returned - the ownership of the buffer passed in the callback (xBuffer
 * in MQTTPublishData_t) remains with the library and it is recycled as soon as the callback
 * returns.<br>
 * The user should take the ownership of the buffer containing the received message from the
 * broker by returning eMQTTTrue from the callback if the user wants to use the buffer after
 * the callback is over. The user should return the buffer whenever done by calling the
 * MQTT_ReturnBuffer API.
 */
#if ( mqttconfigENABLE_SUBSCRIPTION_MANAGEMENT == 1 )

    typedef MQTTBool_t ( * MQTTPublishCallback_t )( void * pvPublishCallbackContext,
                                                    const MQTTPublishData_t * const pxPublishData );

#endif /* mqttconfigENABLE_SUBSCRIPTION_MANAGEMENT */

#endif /* _AWS_MQTT_LIB_H_ */
