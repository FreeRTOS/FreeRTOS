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

/*
 * This file demonstrates numerous tasks all of which use the MQTT agent API
 * to send unique MQTT payloads to unique topics over the same MQTT connection
 * to the same MQTT agent.  Some tasks use QoS0 and others QoS1.
 *
 * Each created task is a unique instance of the task implemented by
 * prvSimpleSubscribePublishTask().  prvSimpleSubscribePublishTask()
 * subscribes to a topic then periodically publishes a message to the same
 * topic to which it has subscribed.  The command context sent to
 * MQTTAgent_Publish() contains a unique number that is sent back to the task
 * as a task notification from the callback function that executes when the
 * PUBLISH operation is acknowledged (or just sent in the case of QoS 0).  The
 * task checks the number it receives from the callback equals the number it
 * previously set in the command context before printing out either a success
 * or failure message.
 */


/* Standard includes. */
#include <string.h>
#include <stdio.h>
#include <assert.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/* Demo Specific configs. */
#include "demo_config.h"

/* MQTT library includes. */
#include "core_mqtt.h"

/* MQTT agent include. */
#include "core_mqtt_agent.h"

/* Subscription manager header include. */
#include "subscription_manager.h"

/**
 * @brief This demo uses task notifications to signal tasks from MQTT callback
 * functions.  mqttexampleMS_TO_WAIT_FOR_NOTIFICATION defines the time, in ticks,
 * to wait for such a callback.
 */
#define mqttexampleMS_TO_WAIT_FOR_NOTIFICATION            ( 10000 )

/**
 * @brief Size of statically allocated buffers for holding topic names and
 * payloads.
 */
#define mqttexampleSTRING_BUFFER_LENGTH                   ( 100 )

/**
 * @brief Delay for each task between publishes.
 */
#define mqttexampleDELAY_BETWEEN_PUBLISH_OPERATIONS_MS    ( 1000U )

/**
 * @brief Number of publishes done by each task in this demo.
 */
#define mqttexamplePUBLISH_COUNT                          ( 0xffffffffUL )

/**
 * @brief The maximum amount of time in milliseconds to wait for the commands
 * to be posted to the MQTT agent should the MQTT agent's command queue be full.
 * Tasks wait in the Blocked state, so don't use any CPU time.
 */
#define mqttexampleMAX_COMMAND_SEND_BLOCK_TIME_MS         ( 500 )

/*-----------------------------------------------------------*/

/**
 * @brief Defines the structure to use as the command callback context in this
 * demo.
 */
struct MQTTAgentCommandContext
{
    MQTTStatus_t xReturnStatus;
    TaskHandle_t xTaskToNotify;
    uint32_t ulNotificationValue;
    void * pArgs;
};

/*-----------------------------------------------------------*/

/**
 * @brief Passed into MQTTAgent_Subscribe() as the callback to execute when the
 * broker ACKs the SUBSCRIBE message.  Its implementation sends a notification
 * to the task that called MQTTAgent_Subscribe() to let the task know the
 * SUBSCRIBE operation completed.  It also sets the xReturnStatus of the
 * structure passed in as the command's context to the value of the
 * xReturnStatus parameter - which enables the task to check the status of the
 * operation.
 *
 * See https://freertos.org/mqtt/mqtt-agent-demo.html#example_mqtt_api_call
 *
 * @param[in] pxCommandContext Context of the initial command.
 * @param[in].xReturnStatus The result of the command.
 */
static void prvSubscribeCommandCallback( void * pxCommandContext,
                                         MQTTAgentReturnInfo_t * pxReturnInfo );

/**
 * @brief Passed into MQTTAgent_Publish() as the callback to execute when the
 * broker ACKs the PUBLISH message.  Its implementation sends a notification
 * to the task that called MQTTAgent_Publish() to let the task know the
 * PUBLISH operation completed.  It also sets the xReturnStatus of the
 * structure passed in as the command's context to the value of the
 * xReturnStatus parameter - which enables the task to check the status of the
 * operation.
 *
 * See https://freertos.org/mqtt/mqtt-agent-demo.html#example_mqtt_api_call
 *
 * @param[in] pxCommandContext Context of the initial command.
 * @param[in].xReturnStatus The result of the command.
 */
static void prvPublishCommandCallback( MQTTAgentCommandContext_t * pxCommandContext,
                                       MQTTAgentReturnInfo_t * pxReturnInfo );

/**
 * @brief Called by the task to wait for a notification from a callback function
 * after the task first executes either MQTTAgent_Publish()* or
 * MQTTAgent_Subscribe().
 *
 * See https://freertos.org/mqtt/mqtt-agent-demo.html#example_mqtt_api_call
 *
 * @param[in] pxCommandContext Context of the initial command.
 * @param[out] pulNotifiedValue The task's notification value after it receives
 * a notification from the callback.
 *
 * @return pdTRUE if the task received a notification, otherwise pdFALSE.
 */
static BaseType_t prvWaitForCommandAcknowledgment( uint32_t * pulNotifiedValue );

/**
 * @brief Passed into MQTTAgent_Subscribe() as the callback to execute when
 * there is an incoming publish on the topic being subscribed to.  Its
 * implementation just logs information about the incoming publish including
 * the publish messages source topic and payload.
 *
 * See https://freertos.org/mqtt/mqtt-agent-demo.html#example_mqtt_api_call
 *
 * @param[in] pvIncomingPublishCallbackContext Context of the initial command.
 * @param[in] pxPublishInfo Deserialized publish.
 */
static void prvIncomingPublishCallback( void * pvIncomingPublishCallbackContext,
                                        MQTTPublishInfo_t * pxPublishInfo );

/**
 * @brief Subscribe to the topic the demo task will also publish to - that
 * results in all outgoing publishes being published back to the task
 * (effectively echoed back).
 *
 * @param[in] xQoS The quality of service (QoS) to use.  Can be zero or one
 * for all MQTT brokers.  Can also be QoS2 if supported by the broker.  AWS IoT
 * does not support QoS2.
 */
static bool prvSubscribeToTopic( MQTTQoS_t xQoS,
                                 char * pcTopicFilter );

/**
 * @brief The function that implements the task demonstrated by this file.
 */
static void prvSimpleSubscribePublishTask( void * pvParameters );

/*-----------------------------------------------------------*/

/**
 * @brief The MQTT agent manages the MQTT contexts.  This set the handle to the
 * context used by this demo.
 */
extern MQTTAgentContext_t xGlobalMqttAgentContext;

/*-----------------------------------------------------------*/

/**
 * @brief The buffer to hold the topic filter. The topic is generated at runtime
 * by adding the task names.
 *
 * @note The topic strings must persist until unsubscribed.
 */
static char topicBuf[ democonfigNUM_SIMPLE_SUB_PUB_TASKS_TO_CREATE ][ mqttexampleSTRING_BUFFER_LENGTH ];

/*-----------------------------------------------------------*/

void vStartSimpleSubscribePublishTask( uint32_t ulNumberToCreate,
                                       configSTACK_DEPTH_TYPE uxStackSize,
                                       UBaseType_t uxPriority )
{
    char pcTaskNameBuf[ 15 ];
    uint32_t ulTaskNumber;

    /* Each instance of prvSimpleSubscribePublishTask() generates a unique name
     * and topic filter for itself from the number passed in as the task
     * parameter. */
    /* Create a few instances of vSimpleSubscribePublishTask(). */
    for( ulTaskNumber = 0; ulTaskNumber < ulNumberToCreate; ulTaskNumber++ )
    {
        memset( pcTaskNameBuf, 0x00, sizeof( pcTaskNameBuf ) );
        snprintf( pcTaskNameBuf, 10, "SubPub%d", ( int ) ulTaskNumber );
        xTaskCreate( prvSimpleSubscribePublishTask,
                     pcTaskNameBuf,
                     uxStackSize,
                     ( void * ) ulTaskNumber,
                     uxPriority,
                     NULL );
    }
}

/*-----------------------------------------------------------*/

static void prvPublishCommandCallback( MQTTAgentCommandContext_t * pxCommandContext,
                                       MQTTAgentReturnInfo_t * pxReturnInfo )
{
    /* Store the result in the application defined context so the task that
     * initiated the publish can check the operation's status. */
    pxCommandContext->xReturnStatus = pxReturnInfo->returnCode;

    if( pxCommandContext->xTaskToNotify != NULL )
    {
        /* Send the context's ulNotificationValue as the notification value so
         * the receiving task can check the value it set in the context matches
         * the value it receives in the notification. */
        xTaskNotify( pxCommandContext->xTaskToNotify,
                     pxCommandContext->ulNotificationValue,
                     eSetValueWithOverwrite );
    }
}

/*-----------------------------------------------------------*/

static void prvSubscribeCommandCallback( void * pxCommandContext,
                                         MQTTAgentReturnInfo_t * pxReturnInfo )
{
    bool xSubscriptionAdded = false;
    MQTTAgentCommandContext_t * pxApplicationDefinedContext = ( MQTTAgentCommandContext_t * ) pxCommandContext;
    MQTTAgentSubscribeArgs_t * pxSubscribeArgs = ( MQTTAgentSubscribeArgs_t * ) pxApplicationDefinedContext->pArgs;

    /* Store the result in the application defined context so the task that
     * initiated the subscribe can check the operation's status.  Also send the
     * status as the notification value.  These things are just done for
     * demonstration purposes. */
    pxApplicationDefinedContext->xReturnStatus = pxReturnInfo->returnCode;

    /* Check if the subscribe operation is a success. Only one topic is
     * subscribed by this demo. */
    if( pxReturnInfo->returnCode == MQTTSuccess )
    {
        /* Add subscription so that incoming publishes are routed to the application
         * callback. */
        xSubscriptionAdded = addSubscription( ( SubscriptionElement_t * ) xGlobalMqttAgentContext.pIncomingCallbackContext,
                                              pxSubscribeArgs->pSubscribeInfo->pTopicFilter,
                                              pxSubscribeArgs->pSubscribeInfo->topicFilterLength,
                                              prvIncomingPublishCallback,
                                              NULL );

        if( xSubscriptionAdded == false )
        {
            LogError( ( "Failed to register an incoming publish callback for topic %.*s.",
                        pxSubscribeArgs->pSubscribeInfo->topicFilterLength,
                        pxSubscribeArgs->pSubscribeInfo->pTopicFilter ) );
        }
    }

    xTaskNotify( pxApplicationDefinedContext->xTaskToNotify,
                 ( uint32_t ) ( pxReturnInfo->returnCode ),
                 eSetValueWithOverwrite );
}

/*-----------------------------------------------------------*/

static BaseType_t prvWaitForCommandAcknowledgment( uint32_t * pulNotifiedValue )
{
    BaseType_t xReturn;

    /* Wait for this task to get notified, passing out the value it gets
     * notified with. */
    xReturn = xTaskNotifyWait( 0,
                               0,
                               pulNotifiedValue,
                               pdMS_TO_TICKS( mqttexampleMS_TO_WAIT_FOR_NOTIFICATION ) );
    return xReturn;
}

/*-----------------------------------------------------------*/

static void prvIncomingPublishCallback( void * pvIncomingPublishCallbackContext,
                                        MQTTPublishInfo_t * pxPublishInfo )
{
    static char cTerminatedString[ mqttexampleSTRING_BUFFER_LENGTH ];

    ( void ) pvIncomingPublishCallbackContext;

    /* Create a message that contains the incoming MQTT payload to the logger,
     * terminating the string first. */
    if( pxPublishInfo->payloadLength < mqttexampleSTRING_BUFFER_LENGTH )
    {
        memcpy( ( void * ) cTerminatedString, pxPublishInfo->pPayload, pxPublishInfo->payloadLength );
        cTerminatedString[ pxPublishInfo->payloadLength ] = 0x00;
    }
    else
    {
        memcpy( ( void * ) cTerminatedString, pxPublishInfo->pPayload, mqttexampleSTRING_BUFFER_LENGTH );
        cTerminatedString[ mqttexampleSTRING_BUFFER_LENGTH - 1 ] = 0x00;
    }

    LogInfo( ( "Received incoming publish message %s", cTerminatedString ) );
}

/*-----------------------------------------------------------*/

static bool prvSubscribeToTopic( MQTTQoS_t xQoS,
                                 char * pcTopicFilter )
{
    MQTTStatus_t xCommandAdded;
    BaseType_t xCommandAcknowledged = pdFALSE;
    uint32_t ulSubscribeMessageID;
    MQTTAgentSubscribeArgs_t xSubscribeArgs;
    MQTTSubscribeInfo_t xSubscribeInfo;
    static int32_t ulNextSubscribeMessageID = 0;
    MQTTAgentCommandContext_t xApplicationDefinedContext = { 0 };
    MQTTAgentCommandInfo_t xCommandParams = { 0 };

    /* Create a unique number of the subscribe that is about to be sent.  The number
     * is used as the command context and is sent back to this task as a notification
     * in the callback that executed upon receipt of the subscription acknowledgment.
     * That way this task can match an acknowledgment to a subscription. */
    xTaskNotifyStateClear( NULL );
    taskENTER_CRITICAL();
    {
        ulNextSubscribeMessageID++;
        ulSubscribeMessageID = ulNextSubscribeMessageID;
    }
    taskEXIT_CRITICAL();

    /* Complete the subscribe information.  The topic string must persist for
     * duration of subscription! */
    xSubscribeInfo.pTopicFilter = pcTopicFilter;
    xSubscribeInfo.topicFilterLength = ( uint16_t ) strlen( pcTopicFilter );
    xSubscribeInfo.qos = xQoS;
    xSubscribeArgs.pSubscribeInfo = &xSubscribeInfo;
    xSubscribeArgs.numSubscriptions = 1;

    /* Complete an application defined context associated with this subscribe message.
     * This gets updated in the callback function so the variable must persist until
     * the callback executes. */
    xApplicationDefinedContext.ulNotificationValue = ulNextSubscribeMessageID;
    xApplicationDefinedContext.xTaskToNotify = xTaskGetCurrentTaskHandle();
    xApplicationDefinedContext.pArgs = ( void * ) &xSubscribeArgs;

    xCommandParams.blockTimeMs = mqttexampleMAX_COMMAND_SEND_BLOCK_TIME_MS;
    xCommandParams.cmdCompleteCallback = prvSubscribeCommandCallback;
    xCommandParams.pCmdCompleteCallbackContext = ( void * ) &xApplicationDefinedContext;

    /* Loop in case the queue used to communicate with the MQTT agent is full and
     * attempts to post to it time out.  The queue will not become full if the
     * priority of the MQTT agent task is higher than the priority of the task
     * calling this function. */
    LogInfo( ( "Sending subscribe request to agent for topic filter: %s with id %d",
               pcTopicFilter,
               ( int ) ulSubscribeMessageID ) );

    do
    {
        /* TODO: prvIncomingPublish as publish callback. */
        xCommandAdded = MQTTAgent_Subscribe( &xGlobalMqttAgentContext,
                                             &xSubscribeArgs,
                                             &xCommandParams );
    } while( xCommandAdded != MQTTSuccess );

    /* Wait for acks to the subscribe message - this is optional but done here
     * so the code below can check the notification sent by the callback matches
     * the ulNextSubscribeMessageID value set in the context above. */
    xCommandAcknowledged = prvWaitForCommandAcknowledgment( NULL );

    /* Check both ways the status was passed back just for demonstration
     * purposes. */
    if( ( xCommandAcknowledged != pdTRUE ) ||
        ( xApplicationDefinedContext.xReturnStatus != MQTTSuccess ) )
    {
        LogInfo( ( "Error or timed out waiting for ack to subscribe message topic %s",
                   pcTopicFilter ) );
    }
    else
    {
        LogInfo( ( "Received subscribe ack for topic %s containing ID %d",
                   pcTopicFilter,
                   ( int ) xApplicationDefinedContext.ulNotificationValue ) );
    }

    return xCommandAcknowledged;
}

/*-----------------------------------------------------------*/

static void prvSimpleSubscribePublishTask( void * pvParameters )
{
    extern UBaseType_t uxRand( void );
    MQTTPublishInfo_t xPublishInfo = { 0 };
    char payloadBuf[ mqttexampleSTRING_BUFFER_LENGTH ];
    char taskName[ mqttexampleSTRING_BUFFER_LENGTH ];
    MQTTAgentCommandContext_t xCommandContext;
    uint32_t ulNotification = 0U, ulValueToNotify = 0UL;
    MQTTStatus_t xCommandAdded;
    uint32_t ulTaskNumber = ( uint32_t ) pvParameters;
    MQTTQoS_t xQoS;
    TickType_t xTicksToDelay;
    MQTTAgentCommandInfo_t xCommandParams = { 0 };
    char * pcTopicBuffer = topicBuf[ ulTaskNumber ];

    /* Have different tasks use different QoS.  0 and 1.  2 can also be used
     * if supported by the broker. */
    xQoS = ( MQTTQoS_t ) ( ulTaskNumber % 2UL );

    /* Create a unique name for this task from the task number that is passed into
     * the task using the task's parameter. */
    snprintf( taskName, mqttexampleSTRING_BUFFER_LENGTH, "Publisher%d", ( int ) ulTaskNumber );

    /* Create a topic name for this task to publish to. */
    snprintf( pcTopicBuffer, mqttexampleSTRING_BUFFER_LENGTH, "/filter/%s", taskName );

    /* Subscribe to the same topic to which this task will publish.  That will
     * result in each published message being published from the server back to
     * the target. */
    prvSubscribeToTopic( xQoS, pcTopicBuffer );

    /* Configure the publish operation. */
    memset( ( void * ) &xPublishInfo, 0x00, sizeof( xPublishInfo ) );
    xPublishInfo.qos = xQoS;
    xPublishInfo.pTopicName = pcTopicBuffer;
    xPublishInfo.topicNameLength = ( uint16_t ) strlen( pcTopicBuffer );
    xPublishInfo.pPayload = payloadBuf;

    /* Store the handler to this task in the command context so the callback
     * that executes when the command is acknowledged can send a notification
     * back to this task. */
    memset( ( void * ) &xCommandContext, 0x00, sizeof( xCommandContext ) );
    xCommandContext.xTaskToNotify = xTaskGetCurrentTaskHandle();

    xCommandParams.blockTimeMs = mqttexampleMAX_COMMAND_SEND_BLOCK_TIME_MS;
    xCommandParams.cmdCompleteCallback = prvPublishCommandCallback;
    xCommandParams.pCmdCompleteCallbackContext = &xCommandContext;

    /* For a finite number of publishes... */
    for( ulValueToNotify = 0UL; ulValueToNotify < mqttexamplePUBLISH_COUNT; ulValueToNotify++ )
    {
        /* Create a payload to send with the publish message.  This contains
         * the task name and an incrementing number. */
        snprintf( payloadBuf,
                  mqttexampleSTRING_BUFFER_LENGTH,
                  "%s publishing message %d",
                  taskName,
                  ( int ) ulValueToNotify );

        xPublishInfo.payloadLength = ( uint16_t ) strlen( payloadBuf );

        /* Also store the incrementing number in the command context so it can
         * be accessed by the callback that executes when the publish operation
         * is acknowledged. */
        xCommandContext.ulNotificationValue = ulValueToNotify;

        LogInfo( ( "Sending publish request to agent with message \"%s\" on topic \"%s\"",
                   payloadBuf,
                   pcTopicBuffer ) );

        /* To ensure ulNotification doesn't accidentally hold the expected value
         * as it is to be checked against the value sent from the callback.. */
        ulNotification = ~ulValueToNotify;

        xCommandAdded = MQTTAgent_Publish( &xGlobalMqttAgentContext,
                                           &xPublishInfo,
                                           &xCommandParams );
        configASSERT( xCommandAdded == MQTTSuccess );

        /* For QoS 1 and 2, wait for the publish acknowledgment.  For QoS0,
         * wait for the publish to be sent. */
        LogInfo( ( "Task %s waiting for publish %d to complete.",
                   taskName,
                   ulValueToNotify ) );
        prvWaitForCommandAcknowledgment( &ulNotification );

        /* The value received by the callback that executed when the publish was
         * completed came from the context passed into MQTTAgent_Publish() above,
         * so should match the value set in the context above. */
        configASSERT( ulNotification == ulValueToNotify );

        /* Log statement to indicate successful reception of publish. */
        LogInfo( ( "Demo completed successfully.\r\n" ) );
        LogInfo( ( "Short delay before next publish... \r\n\r\n" ) );

        /* Add a little randomness into the delay so the tasks don't remain
         * in lockstep. */
        xTicksToDelay = pdMS_TO_TICKS( mqttexampleDELAY_BETWEEN_PUBLISH_OPERATIONS_MS ) +
                        ( uxRand() % 0xff );
        vTaskDelay( xTicksToDelay );
    }

    /* Delete the task if it is complete. */
    LogInfo( ( "Task %s completed.", taskName ) );
    vTaskDelete( NULL );
}
