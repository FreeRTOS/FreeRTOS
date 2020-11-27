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
 *
 * https://www.FreeRTOS.org
 * https://aws.amazon.com/freertos
 *
 */

/**
 * @file mqtt_agent.h
 * @brief Functions for running a coreMQTT client in a dedicated thread.
 */
#ifndef MQTT_AGENT_H
#define MQTT_AGENT_H

/* Demo Specific configs. */
#include "demo_config.h"

/* MQTT library includes. */
#include "core_mqtt.h"
#include "core_mqtt_state.h"

/**
 * @brief Timeout for MQTT_ProcessLoop function in milliseconds.
 *
 * This demo uses no delay for the process loop, so each invocation will run
 * one iteration, and will only receive a single packet. However, if there is
 * no data available on the socket, the entire socket timeout value will elapse.
 */
#define MQTT_AGENT_PROCESS_LOOP_TIMEOUT_MS     ( 0U )

/**
 * @brief The maximum number of MQTT connections that can be tracked.
 */
#define MAX_CONNECTIONS                        2

/**
 * @brief The maximum number of pending acknowledgments to track for a single
 * connection.
 */
#define PENDING_ACKS_MAX_SIZE                  20

/**
 * @brief The maximum number of subscriptions to track for a single connection.
 */
#define SUBSCRIPTIONS_MAX_COUNT                10

/**
 * @brief Size of statically allocated buffers for holding subscription filters.
 */
#define MQTT_AGENT_SUBSCRIPTION_BUFFER_SIZE    100

/**
 * @brief Ticks to wait for task notifications.
 */
#define MQTT_AGENT_QUEUE_WAIT_TIME             pdMS_TO_TICKS( 1000 )

/*-----------------------------------------------------------*/

/**
 * @brief Struct containing context for a specific command.
 *
 * @note An instance of this struct and any variables it points to MUST stay
 * in scope until the associated command is processed, and its callback called.
 */
struct CommandContext;
typedef struct CommandContext CommandContext_t;

/**
 * @brief Callback function called when a command completes.
 */
typedef void (* CommandCallback_t )( CommandContext_t *,
                                     MQTTStatus_t );

/**
 * @brief Callback function called when a publish is received.
 */
typedef void (* PublishCallback_t )( MQTTPublishInfo_t * pxPublishInfo,
                                     void * pxSubscriptionContext );

/*-----------------------------------------------------------*/

/**
 * @brief Dispatch incoming publishes and acks to response queues and
 * command callbacks.
 *
 * @param[in] pMqttContext MQTT Context
 * @param[in] pPacketInfo Pointer to incoming packet.
 * @param[in] pDeserializedInfo Pointer to deserialized information from
 * the incoming packet.
 */
void MQTTAgent_EventCallback( MQTTContext_t * pMqttContext,
                              MQTTPacketInfo_t * pPacketInfo,
                              MQTTDeserializedInfo_t * pDeserializedInfo );

/**
 * @brief Process commands from the command queue in a loop.
 *
 * This demo requires a process loop command to be enqueued before calling this
 * function, and will re-add a process loop command every time one is processed.
 * This demo will exit the loop after receiving an unsubscribe operation.
 *
 * @return pointer to MQTT context that caused error, or `NULL` if terminated
 * gracefully.
 */
MQTTContext_t * MQTTAgent_CommandLoop( void );

/**
 * @brief Resume a session by resending publishes if a session is present in
 * the broker, or reestablish subscriptions if not.
 *
 * @param[in] xSessionPresent The session present flag from the broker.
 *
 * @return `MQTTSuccess` if it succeeds in resending publishes, else an
 * appropriate error code from `MQTT_Publish()`
 */
MQTTStatus_t MQTTAgent_ResumeSession( MQTTContext_t * pMqttContext,
                                      bool xSessionPresent );

bool MQTTAgent_Subscribe( MQTTContext_t * pMqttContext,
                          MQTTSubscribeInfo_t * pSubscriptionList,
                          size_t subscriptionCount,
                          PublishCallback_t publishCallback,
                          void * pPublishCallbackContext,
                          CommandContext_t * pContext,
                          CommandCallback_t cmdCallback );

bool MQTTAgent_Unsubscribe( MQTTContext_t * pMqttContext,
                            MQTTSubscribeInfo_t * pSubscriptionList,
                            size_t subscriptionCount,
                            CommandContext_t * pContext,
                            CommandCallback_t cmdCallback );

bool MQTTAgent_Publish( MQTTContext_t * pMqttContext,
                        MQTTPublishInfo_t * pPublishInfo,
                        CommandContext_t * pContext,
                        CommandCallback_t cmdCallback );

bool MQTTAgent_ProcessLoop( MQTTContext_t * pMqttContext,
                            uint32_t timeoutMs,
                            CommandContext_t * pContext,
                            CommandCallback_t cmdCallback );

bool MQTTAgent_Ping( MQTTContext_t * pMqttContext,
                     CommandContext_t * pContext,
                     CommandCallback_t cmdCallback );

bool MQTTAgent_Disconnect( MQTTContext_t * pMqttContext,
                           CommandContext_t * pContext,
                           CommandCallback_t cmdCallback );

bool MQTTAgent_Register( MQTTContext_t * pMqttContext,
                         PublishCallback_t defaultPublishCallback,
                         void * pDefaultPublishContext,
                         CommandContext_t * pContext,
                         CommandCallback_t cmdCallback );

bool MQTTAgent_Free( MQTTContext_t * pMqttContext,
                     CommandContext_t * pContext,
                     CommandCallback_t cmdCallback );

bool MQTTAgent_Terminate( void );

uint32_t MQTTAgent_GetNumWaiting( void );

bool MQTTAgent_CreateCommandQueue( const uint32_t uxCommandQueueLength );

#endif /* MQTT_AGENT_H */
