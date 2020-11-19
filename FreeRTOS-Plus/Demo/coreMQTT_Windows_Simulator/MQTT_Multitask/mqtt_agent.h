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

/* Standard includes. */
#include <string.h>
#include <stdio.h>
#include <assert.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

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
#define mqttexamplePROCESS_LOOP_TIMEOUT_MS    ( 0U )

#define MAX_CONNECTIONS                       5

/**
 * @brief Size of statically allocated buffers for holding topic names and payloads in this demo.
 */
#define mqttexampleDEMO_BUFFER_SIZE           100

/**
 * @brief Ticks to wait for task notifications.
 */
#define mqttexampleDEMO_TICKS_TO_WAIT         pdMS_TO_TICKS( 1000 )

#define mqttexamplePOST_SUBSCRIBE_DELAY_MS    400U

/*-----------------------------------------------------------*/

struct MQTTAgentContext;

/**
 * @brief A type of command for interacting with the MQTT API.
 */
typedef enum CommandType
{
    PROCESSLOOP, /**< @brief Call MQTT_ProcessLoop(). */
    PUBLISH,     /**< @brief Call MQTT_Publish(). */
    SUBSCRIBE,   /**< @brief Call MQTT_Subscribe(). */
    UNSUBSCRIBE, /**< @brief Call MQTT_Unsubscribe(). */
    PING,        /**< @brief Call MQTT_Ping(). */
    DISCONNECT,  /**< @brief Call MQTT_Disconnect(). */
    TERMINATE    /**< @brief Exit the command loop and stop processing commands. */
} CommandType_t;

/**
 * @brief Struct containing context for a specific command.
 *
 * @note An instance of this struct and any variables it points to MUST stay
 * in scope until the associated command is processed, and its callback called.
 * The command callback will set the `xIsComplete` flag, and notify the calling task.
 */
typedef struct CommandContext
{
    MQTTPublishInfo_t * pxPublishInfo;
    MQTTSubscribeInfo_t * pxSubscribeInfo;
    size_t ulSubscriptionCount;
    MQTTStatus_t xReturnStatus;
    bool xIsComplete;

    /* The below fields are specific to this FreeRTOS implementation. */
    TaskHandle_t xTaskToNotify;
    uint32_t ulNotificationBit;
    QueueHandle_t pxResponseQueue;
} CommandContext_t;

/**
 * @brief Callback function called when a command completes.
 */
typedef void (* CommandCallback_t )( CommandContext_t * );

/**
 * @brief A command for interacting with the MQTT API.
 */
typedef struct Command
{
    CommandType_t xCommandType;
    CommandContext_t * pxCmdContext;
    CommandCallback_t vCallback;
    struct MQTTAgentContext * pAgentContext;
} Command_t;

/**
 * @brief Information for a pending MQTT ack packet expected by the demo.
 */
typedef struct ackInfo
{
    uint16_t usPacketId;
    Command_t xOriginalCommand;
} AckInfo_t;

/**
 * @brief An element in the list of subscriptions maintained in the demo.
 *
 * @note This demo allows multiple tasks to subscribe to the same topic.
 * In this case, another element is added to the subscription list, differing
 * in the destination response queue.
 */
typedef struct subscriptionElement
{
    char pcSubscriptionFilter[ mqttexampleDEMO_BUFFER_SIZE ];
    uint16_t usFilterLength;
    QueueHandle_t pxResponseQueue;
} SubscriptionElement_t;

/**
 * @brief An element for a task's response queue for received publishes.
 *
 * @note Since elements are copied to queues, this struct needs to hold
 * buffers for the payload and topic of incoming publishes, as the original
 * pointers are out of scope. When processing a publish from this struct,
 * the `pcTopicNameBuf` and `pcPayloadBuf` pointers need to be set to point to the
 * static buffers in this struct.
 */
typedef struct publishElement
{
    MQTTPublishInfo_t xPublishInfo;
    uint8_t pcPayloadBuf[ mqttexampleDEMO_BUFFER_SIZE ];
    uint8_t pcTopicNameBuf[ mqttexampleDEMO_BUFFER_SIZE ];
} PublishElement_t;

typedef struct MQTTAgentContext
{
    MQTTContext_t * pMQTTContext;
    AckInfo_t * pPendingAcks;
    size_t pendingAckSize;
    SubscriptionElement_t * pSubscriptionList;
    size_t maxSubscriptions;
    MQTTSubscribeInfo_t * pResendSubscriptions;
    CommandContext_t * pResubscribeContext;
    void * pDefaultResponseQueue;
} MQTTAgentContext_t;

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
 * @return `true` if the loop exited successfully, else `false`.
 */
bool MQTTAgent_CommandLoop( void );

/**
 * @brief Populate the parameters of a #Command_t
 *
 * @param[in] xCommandType Type of command.
 * @param[in] pxContext Context and necessary structs for command.
 * @param[in] xCallback Callback for when command completes.
 * @param[out] pxCommand Pointer to initialized command.
 *
 * @return `true` if all necessary structs for the command exist in pxContext,
 * else `false`
 */
bool MQTTAgent_CreateCommand( CommandType_t xCommandType,
                              CommandContext_t * pxContext,
                              CommandCallback_t xCallback,
                              Command_t * pxCommand,
                              MQTTAgentContext_t * pAgentContext );

/**
 * @brief Add a command to the global command queue.
 *
 * @param[in] pxCommand Pointer to command to copy to queue.
 *
 * @return true if the command was added to the queue, else false.
 */
BaseType_t MQTTAgent_AddCommandToQueue( Command_t * pxCommand );

/**
 * @brief Resume a session by resending publishes if a session is present in
 * the broker, or reestablish subscriptions if not.
 *
 * @param[in] xSessionPresent The session present flag from the broker.
 *
 * @return `MQTTSuccess` if it succeeds in resending publishes, else an
 * appropriate error code from `MQTT_Publish()`
 */
MQTTStatus_t MQTTAgent_ResumeSession( MQTTAgentContext_t * pAgentContext,
                                      bool xSessionPresent );

bool MQTTAgent_Subscribe( MQTTAgentContext_t * pAgentContext,
                          CommandContext_t * pContext,
                          CommandCallback_t cmdCallback,
                          const MQTTSubscribeInfo_t * pSubscriptionList,
                          size_t subscriptionCount );

bool MQTTAgent_Unsubscribe( MQTTAgentContext_t * pAgentContext,
                            CommandContext_t * pContext,
                            CommandCallback_t cmdCallback,
                            const MQTTSubscribeInfo_t * pSubscriptionList,
                            size_t subscriptionCount );

bool MQTTAgent_Publish( MQTTAgentContext_t * pAgentContext,
                        CommandContext_t * pContext,
                        CommandCallback_t cmdCallback,
                        const MQTTPublishInfo_t *pPublishInfo );

bool MQTTAgent_ProcessLoop( MQTTAgentContext_t * pAgentContext,
                            CommandContext_t * pContext,
                            CommandCallback_t cmdCallback,
                            uint32_t timeoutMs );

bool MQTTAgent_Ping( MQTTAgentContext_t * pAgentContext,
                     CommandContext_t * pContext,
                     CommandCallback_t cmdCallback );

bool MQTTAgent_Disconnect( MQTTAgentContext_t * pAgentContext,
                           CommandContext_t * pContext,
                           CommandCallback_t cmdCallback );

bool MQTTAgent_Terminate();

/* Not thread safe. */
void MQTTAgent_RegisterContexts( MQTTContext_t * pMQTTContext, MQTTAgentContext_t * pAgentContext );

/*-----------------------------------------------------------*/

/**
 * @brief Queue for main task to handle MQTT operations.
 */
QueueHandle_t xCommandQueue;

#endif /* MQTT_AGENT_H */
