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
 * @file mqtt_agent.c
 * @brief Implements functions in mqtt_agent.h.
 */

/* Standard includes. */
#include <string.h>
#include <stdio.h>
#include <assert.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/* MQTT agent include. */
#include "mqtt_agent.h"

/*-----------------------------------------------------------*/

/**
 * @brief A type of command for interacting with the MQTT API.
 */
typedef enum CommandType
{
    NONE = 0,    /**< @brief No command received.  Must be zero (its memset() value). */
    PROCESSLOOP, /**< @brief Call MQTT_ProcessLoop(). */
    PUBLISH,     /**< @brief Call MQTT_Publish(). */
    SUBSCRIBE,   /**< @brief Call MQTT_Subscribe(). */
    UNSUBSCRIBE, /**< @brief Call MQTT_Unsubscribe(). */
    PING,        /**< @brief Call MQTT_Ping(). */
    DISCONNECT,  /**< @brief Call MQTT_Disconnect(). */
    INITIALIZE,  /**< @brief Assign an agent to an MQTT Context. */
    FREE,        /**< @brief Remove a mapping from an MQTT Context to the agent. */
    TERMINATE    /**< @brief Exit the command loop and stop processing commands. */
} CommandType_t;

/**
 * @brief A command for interacting with the MQTT API.
 */
typedef struct Command
{
    CommandType_t xCommandType;
    CommandContext_t * pxCmdContext;
    CommandCallback_t vCallback;
    MQTTContext_t * pMqttContext;
    void * pMqttInfoParam;
    uint32_t uintParam;
    PublishCallback_t vPublishCallback;
    void * pPublishCallbackContext;
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
    char pcSubscriptionFilter[ MQTT_AGENT_SUBSCRIPTION_BUFFER_SIZE ];
    uint16_t usFilterLength;
    PublishCallback_t vPublishCallback;
    void * pSubscriptionContext;
} SubscriptionElement_t;

/**
 * @brief Associated information for a single MQTT connection.
 */
typedef struct MQTTAgentContext
{
    MQTTContext_t * pMQTTContext;
    AckInfo_t pPendingAcks[ PENDING_ACKS_MAX_SIZE ];
    size_t pendingAckSize;
    SubscriptionElement_t pSubscriptionList[ SUBSCRIPTIONS_MAX_COUNT ];
    size_t maxSubscriptions;
    MQTTSubscribeInfo_t pResendSubscriptions[ SUBSCRIPTIONS_MAX_COUNT ];
    PublishCallback_t vDefaultPublishCallback;
    void * pDefaultSubscriptionContext;
} MQTTAgentContext_t;

/*-----------------------------------------------------------*/

/**
 * @brief Track an operation by adding it to a list, indicating it is anticipating
 * an acknowledgment.
 *
 * @param[in] pAgentContext Agent context for the MQTT connection.
 * @param[in] usPacketId Packet ID of pending ack.
 * @param[in] pxCommand Copy of command that is expecting an ack.
 *
 * @return `true` if the operation was added; else `false`
 */
static bool prvAddAwaitingOperation( MQTTAgentContext_t * pAgentContext,
                                     uint16_t usPacketId,
                                     Command_t * pxCommand );

/**
 * @brief Retrieve an operation from the list of pending acks, and optionally
 * remove it.
 *
 * @param[in] pAgentContext Agent context for the MQTT connection.
 * @param[in] usPacketId Packet ID of incoming ack.
 * @param[in] xRemove Flag indicating if the operation should be removed.
 *
 * @return Stored information about the operation awaiting the ack.
 */
static AckInfo_t prvGetAwaitingOperation( MQTTAgentContext_t * pAgentContext,
                                          uint16_t usPacketId,
                                          bool xRemove );

/**
 * @brief Add a subscription to the subscription list.
 *
 * @note Multiple tasks can be subscribed to the same topic with different
 * context-callback pairs. However, a single context-callback pair may only be
 * associated to the same topic filter once.
 *
 * @param[in] pAgentContext Agent context for the MQTT connection.
 * @param[in] pcTopicFilter Topic filter of subscription.
 * @param[in] usTopicFilterLength Length of topic filter.
 * @param[in] vPublishCallback Callback function for the subscription.
 * @param[in] pvSubscriptionContext Context for the subscription callback.
 *
 * @return `true` if subscription added or exists, `false` if insufficient memory.
 */
static bool prvAddSubscription( MQTTAgentContext_t * pAgentContext,
                                const char * pcTopicFilter,
                                uint16_t usTopicFilterLength,
                                PublishCallback_t vPublishCallback,
                                void * pvSubscriptionContext );

/**
 * @brief Remove a subscription from the subscription list.
 *
 * @note If the topic filter exists multiple times in the subscription list,
 * then every instance of the subscription will be removed.
 *
 * @param[in] pAgentContext Agent context for the MQTT connection.
 * @param[in] pcTopicFilter Topic filter of subscription.
 * @param[in] usTopicFilterLength Length of topic filter.
 */
static void prvRemoveSubscription( MQTTAgentContext_t * pAgentContext,
                                   const char * pcTopicFilter,
                                   uint16_t usTopicFilterLength );

/**
 * @brief Populate the parameters of a #Command_t
 *
 * @param[in] xCommandType Type of command.
 * @param[in] pMqttContext Pointer to MQTT context to use for command.
 * @param[in] pMqttInfoParam Pointer to MQTTPublishInfo_t or MQTTSubscribeInfo_t.
 * @param[in] uintParam Subscription count or process loop timeout, if applicable.
 * @param[in] publishCallback Subscription callback function for incomingin publishes.
 * @param[in] pSubscriptionContext Subscription callback context.
 * @param[in] pxContext Context and necessary structs for command.
 * @param[in] xCallback Callback for when command completes.
 * @param[out] pxCommand Pointer to initialized command.
 *
 * @return `true` if all necessary structs for the command exist in pxContext,
 * else `false`
 */
static bool prvCreateCommand( CommandType_t xCommandType,
                              MQTTContext_t * pMqttContext,
                              void * pMqttInfoParam,
                              uint32_t uintParam,
                              PublishCallback_t publishCallback,
                              void * pSubscriptionContext,
                              CommandContext_t * pxContext,
                              CommandCallback_t xCallback,
                              Command_t * pxCommand );

/**
 * @brief Add a command to the global command queue.
 *
 * @param[in] pxCommand Pointer to command to copy to queue.
 *
 * @return true if the command was added to the queue, else false.
 */
static bool prvAddCommandToQueue( Command_t * pxCommand );

/**
 * @brief Process a #Command_t.
 *
 * @note This agent does not check existing subscriptions before sending a
 * SUBSCRIBE or UNSUBSCRIBE packet. If a subscription already exists, then
 * a SUBSCRIBE packet will be sent anyway, and if multiple tasks are subscribed
 * to a topic filter, then they will all be unsubscribed after an UNSUBSCRIBE.
 *
 * @param[in] pxCommand Pointer to command to process.
 *
 * @return status of MQTT library API call.
 */
static MQTTStatus_t prvProcessCommand( Command_t * pxCommand );

/**
 * @brief Dispatch an incoming publish to the appropriate publish callback.
 *
 * @param[in] pAgentContext Agent context for the MQTT connection.
 * @param[in] pxPublishInfo Incoming publish information.
 */
static void prvHandleIncomingPublish( MQTTAgentContext_t * pAgentContext,
                                      MQTTPublishInfo_t * pxPublishInfo );

/**
 * @brief Add or delete subscription information from a SUBACK or UNSUBACK.
 *
 * @param[in] pAgentContext Agent context for the MQTT connection.
 * @param[in] pxPacketInfo Pointer to incoming packet.
 * @param[in] pxDeserializedInfo Pointer to deserialized information from
 * the incoming packet.
 * @param[in] pxAckInfo Pointer to stored information for the original subscribe
 * or unsubscribe operation resulting in the received packet.
 * @param[in] ucPacketType The type of the incoming packet, either SUBACK or UNSUBACK.
 */
static void prvHandleSubscriptionAcks( MQTTAgentContext_t * pAgentContext,
                                       MQTTPacketInfo_t * pxPacketInfo,
                                       MQTTDeserializedInfo_t * pxDeserializedInfo,
                                       AckInfo_t * pxAckInfo,
                                       uint8_t ucPacketType );

/**
 * @brief Retrieve an MQTT context for an empty command's process loop.
 *
 * @note Successive calls to this function will loop through the contexts stored
 * from MQTTAgent_Register(), ensuring that connections will not remain idle too
 * long when the queue is empty.
 *
 * @return Pointer to MQTT context, or NULL.
 */
static MQTTContext_t * getContextForProcessLoop( void );

/**
 * @brief Retrieve a pointer to an agent context given an MQTT context.
 *
 * @param[in] pMQTTContext MQTT Context to search for.
 *
 * @return Pointer to agent context, or NULL.
 */
static MQTTAgentContext_t * getAgentFromContext( MQTTContext_t * pMQTTContext );

/**
 * @brief Helper function for creating a command and adding it to the command
 * queue.
 *
 * @param[in] xCommandType Type of command.
 * @param[in] pMqttContext Pointer to MQTT context to use for command.
 * @param[in] pCommandContext Context and necessary structs for command.
 * @param[in] cmdCallback Callback for when command completes.
 * @param[in] pMqttInfoParam Pointer to MQTTPublishInfo_t or MQTTSubscribeInfo_t.
 * @param[in] uintParam Subscription count or process loop timeout, if applicable.
 * @param[in] publishCallback Subscription callback function for incomingin publishes.
 * @param[in] pSubscriptionContext Subscription callback context.
 *
 * @return `true` if the command was added to the queue, `false` if not.
 */
static bool createAndAddCommand( CommandType_t commandType,
                                 MQTTContext_t * pMqttContext,
                                 CommandContext_t * pCommandContext,
                                 CommandCallback_t cmdCallback,
                                 void * pMqttInfoParam,
                                 uint32_t uintParam,
                                 PublishCallback_t publishCallback,
                                 void * pSubscriptionContext );

/*-----------------------------------------------------------*/

/**
 * @brief Queue for main task to handle MQTT operations.
 *
 * This is a private variable initialized by #MQTTAgent_CreateCommandQueue.
 */
QueueHandle_t xCommandQueue;

/**
 * @brief Array of contexts, one for each potential MQTT connection.
 */
static MQTTAgentContext_t pAgentContexts[ MAX_CONNECTIONS ];

/*-----------------------------------------------------------*/

static bool prvAddAwaitingOperation( MQTTAgentContext_t * pAgentContext,
                                     uint16_t usPacketId,
                                     Command_t * pxCommand )
{
    size_t i = 0;
    bool xAckAdded = false;
    AckInfo_t * pxPendingAcks = pAgentContext->pPendingAcks;

    for( i = 0; i < pAgentContext->pendingAckSize; i++ )
    {
        if( pxPendingAcks[ i ].usPacketId == MQTT_PACKET_ID_INVALID )
        {
            pxPendingAcks[ i ].usPacketId = usPacketId;
            pxPendingAcks[ i ].xOriginalCommand = *pxCommand;
            xAckAdded = true;
            break;
        }
    }

    return xAckAdded;
}

/*-----------------------------------------------------------*/

static AckInfo_t prvGetAwaitingOperation( MQTTAgentContext_t * pAgentContext,
                                          uint16_t usPacketId,
                                          bool xRemove )
{
    size_t i = 0;
    AckInfo_t xFoundAck = { 0 };
    AckInfo_t * pxPendingAcks = pAgentContext->pPendingAcks;

    for( i = 0; i < pAgentContext->pendingAckSize; i++ )
    {
        if( pxPendingAcks[ i ].usPacketId == usPacketId )
        {
            xFoundAck = pxPendingAcks[ i ];

            if( xRemove )
            {
                pxPendingAcks[ i ].usPacketId = MQTT_PACKET_ID_INVALID;
                memset( &( pxPendingAcks[ i ].xOriginalCommand ), 0x00, sizeof( Command_t ) );
            }

            break;
        }
    }

    if( xFoundAck.usPacketId == MQTT_PACKET_ID_INVALID )
    {
        LogError( ( "No ack found for packet id %u.\n", usPacketId ) );
    }

    return xFoundAck;
}

/*-----------------------------------------------------------*/

static bool prvAddSubscription( MQTTAgentContext_t * pAgentContext,
                                const char * pcTopicFilter,
                                uint16_t usTopicFilterLength,
                                PublishCallback_t vPublishCallback,
                                void * pvSubscriptionContext )
{
    int32_t i = 0;
    size_t ulAvailableIndex = pAgentContext->maxSubscriptions;
    SubscriptionElement_t * pxSubscriptions = pAgentContext->pSubscriptionList;
    bool ret = false;

    /* Start at end of array, so that we will insert at the first available index. */
    for( i = ( int32_t ) pAgentContext->maxSubscriptions - 1; i >= 0; i-- )
    {
        if( pxSubscriptions[ i ].usFilterLength == 0 )
        {
            ulAvailableIndex = i;
        }
        else if( ( pxSubscriptions[ i ].usFilterLength == usTopicFilterLength ) &&
                 ( strncmp( pcTopicFilter, pxSubscriptions[ i ].pcSubscriptionFilter, usTopicFilterLength ) == 0 ) )
        {
            /* If a subscription already exists, don't do anything. */
            if( ( pxSubscriptions[ i ].vPublishCallback == vPublishCallback ) &&
                ( pxSubscriptions[ i ].pSubscriptionContext == pvSubscriptionContext ) )
            {
                LogWarn( ( "Subscription already exists.\n" ) );
                ulAvailableIndex = pAgentContext->maxSubscriptions;
                ret = true;
                break;
            }
        }
    }

    if( ( ulAvailableIndex < pAgentContext->maxSubscriptions ) && ( vPublishCallback != NULL ) )
    {
        pxSubscriptions[ ulAvailableIndex ].usFilterLength = usTopicFilterLength;
        pxSubscriptions[ ulAvailableIndex ].vPublishCallback = vPublishCallback;
        pxSubscriptions[ ulAvailableIndex ].pSubscriptionContext = pvSubscriptionContext;
        memcpy( pxSubscriptions[ ulAvailableIndex ].pcSubscriptionFilter, pcTopicFilter, usTopicFilterLength );
        ret = true;
    }

    return ret;
}

/*-----------------------------------------------------------*/

static void prvRemoveSubscription( MQTTAgentContext_t * pAgentContext,
                                   const char * pcTopicFilter,
                                   uint16_t usTopicFilterLength )
{
    size_t i = 0;
    SubscriptionElement_t * pxSubscriptions = pAgentContext->pSubscriptionList;

    for( i = 0; i < pAgentContext->maxSubscriptions; i++ )
    {
        if( pxSubscriptions[ i ].usFilterLength == usTopicFilterLength )
        {
            if( strncmp( pxSubscriptions[ i ].pcSubscriptionFilter, pcTopicFilter, usTopicFilterLength ) == 0 )
            {
                pxSubscriptions[ i ].usFilterLength = 0;
                pxSubscriptions[ i ].vPublishCallback = NULL;
                pxSubscriptions[ i ].pSubscriptionContext = NULL;
                memset( pxSubscriptions[ i ].pcSubscriptionFilter, 0x00, MQTT_AGENT_SUBSCRIPTION_BUFFER_SIZE );
            }
        }
    }
}

/*-----------------------------------------------------------*/

static bool prvCreateCommand( CommandType_t xCommandType,
                              MQTTContext_t * pMqttContext,
                              void * pMqttInfoParam,
                              uint32_t uintParam,
                              PublishCallback_t publishCallback,
                              void * pSubscriptionContext,
                              CommandContext_t * pxContext,
                              CommandCallback_t xCallback,
                              Command_t * pxCommand )
{
    bool xIsValid = true;

    /* Determine if required parameters are present in context. */
    switch( xCommandType )
    {
        case SUBSCRIBE:
            xIsValid = ( pMqttContext != NULL ) && ( pMqttInfoParam != NULL ) && ( uintParam > 0U ) && ( publishCallback != NULL );
            break;

        case UNSUBSCRIBE:
            xIsValid = ( pMqttContext != NULL ) && ( pMqttInfoParam != NULL ) && ( uintParam > 0U );
            break;

        case PUBLISH:
            xIsValid = ( pMqttContext != NULL ) && ( pMqttInfoParam != NULL );
            break;

        case PROCESSLOOP:
        case PING:
        case DISCONNECT:
        case INITIALIZE:
        case FREE:
            xIsValid = ( pMqttContext != NULL );
            break;

        default:
            /* Other operations don't need the MQTT context. */
            break;
    }

    if( xIsValid )
    {
        memset( pxCommand, 0x00, sizeof( Command_t ) );
        pxCommand->xCommandType = xCommandType;
        pxCommand->pMqttContext = pMqttContext;
        pxCommand->pMqttInfoParam = pMqttInfoParam;
        pxCommand->uintParam = uintParam;
        pxCommand->vPublishCallback = publishCallback;
        pxCommand->pPublishCallbackContext = pSubscriptionContext;
        pxCommand->pxCmdContext = pxContext;
        pxCommand->vCallback = xCallback;
    }

    return xIsValid;
}

/*-----------------------------------------------------------*/

static bool prvAddCommandToQueue( Command_t * pxCommand )
{
    return xQueueSendToBack( xCommandQueue, pxCommand, MQTT_AGENT_QUEUE_WAIT_TIME );
}

/*-----------------------------------------------------------*/

static MQTTStatus_t prvProcessCommand( Command_t * pxCommand )
{
    MQTTStatus_t xStatus = MQTTSuccess;
    uint16_t usPacketId = MQTT_PACKET_ID_INVALID;
    bool xAddAckToList = false, xAckAdded = false;
    MQTTPublishInfo_t * pxPublishInfo;
    MQTTSubscribeInfo_t * pxSubscribeInfo;
    MQTTContext_t * pMQTTContext = pxCommand->pMqttContext;
    MQTTAgentContext_t * pAgentContext = NULL;
    uint32_t i;
    uint32_t processLoopTimeoutMs = MQTT_AGENT_PROCESS_LOOP_TIMEOUT_MS;

    switch( pxCommand->xCommandType )
    {
        case PROCESSLOOP:

            /* The process loop will run at the end of every command, so we don't
             * need to call it again here. */
            LogDebug( ( "Running Process Loop.\n" ) );
            processLoopTimeoutMs = pxCommand->uintParam;
            break;

        case PUBLISH:
            configASSERT( pxCommand->pMqttInfoParam != NULL );
            pxPublishInfo = ( MQTTPublishInfo_t * ) pxCommand->pMqttInfoParam;

            if( pxPublishInfo->qos != MQTTQoS0 )
            {
                usPacketId = MQTT_GetPacketId( pMQTTContext );
            }

            LogDebug( ( "Publishing message to %.*s.\n", ( int ) pxPublishInfo->topicNameLength, pxPublishInfo->pTopicName ) );
            xStatus = MQTT_Publish( pMQTTContext, pxPublishInfo, usPacketId );

            /* Add to pending ack list, or call callback if QoS 0. */
            xAddAckToList = ( pxPublishInfo->qos != MQTTQoS0 ) && ( xStatus == MQTTSuccess );
            break;

        case SUBSCRIBE:
        case UNSUBSCRIBE:
            pxSubscribeInfo = ( MQTTSubscribeInfo_t * ) pxCommand->pMqttInfoParam;
            configASSERT( pxSubscribeInfo != NULL );
            configASSERT( pxSubscribeInfo->pTopicFilter != NULL );
            usPacketId = MQTT_GetPacketId( pMQTTContext );

            if( pxCommand->xCommandType == SUBSCRIBE )
            {
                /* Even if some subscriptions already exist in the subscription list,
                 * it is fine to send another subscription request. A valid use case
                 * for this is changing the maximum QoS of the subscription. */
                xStatus = MQTT_Subscribe( pMQTTContext,
                                          pxSubscribeInfo,
                                          pxCommand->uintParam,
                                          usPacketId );
            }
            else
            {
                xStatus = MQTT_Unsubscribe( pMQTTContext,
                                            pxSubscribeInfo,
                                            pxCommand->uintParam,
                                            usPacketId );
            }

            xAddAckToList = ( xStatus == MQTTSuccess );
            break;

        case PING:
            xStatus = MQTT_Ping( pMQTTContext );

            break;

        case DISCONNECT:
            xStatus = MQTT_Disconnect( pMQTTContext );

            break;

        case INITIALIZE:

            for( i = 0; i < MAX_CONNECTIONS; i++ )
            {
                if( pAgentContexts[ i ].pMQTTContext == NULL )
                {
                    pAgentContexts[ i ].pMQTTContext = pMQTTContext;
                    pAgentContexts[ i ].pendingAckSize = PENDING_ACKS_MAX_SIZE;
                    pAgentContexts[ i ].maxSubscriptions = SUBSCRIPTIONS_MAX_COUNT;
                    pAgentContexts[ i ].vDefaultPublishCallback = pxCommand->vPublishCallback;
                    pAgentContexts[ i ].pDefaultSubscriptionContext = pxCommand->pPublishCallbackContext;
                    break;
                }
            }

            if( i == MAX_CONNECTIONS )
            {
                xStatus = MQTTNoMemory;
            }

            break;

        case FREE:

            for( i = 0; i < MAX_CONNECTIONS; i++ )
            {
                if( pAgentContexts[ i ].pMQTTContext == pMQTTContext )
                {
                    memset( &pAgentContexts[ i ], 0x00, sizeof( MQTTAgentContext_t ) );
                    break;
                }
            }

            break;

        case TERMINATE:
            LogInfo( ( "Terminating command loop.\n" ) );

        default:
            break;
    }

    if( xAddAckToList )
    {
        pAgentContext = getAgentFromContext( pxCommand->pMqttContext );
        xAckAdded = prvAddAwaitingOperation( pAgentContext, usPacketId, pxCommand );

        /* Set the return status if no memory was available to store the operation
         * information. */
        if( !xAckAdded )
        {
            LogError( ( "No memory to wait for acknowledgment for packet %u\n", usPacketId ) );

            /* All operations that can wait for acks (publish, subscribe, unsubscribe)
             * require a context. */
            xStatus = MQTTNoMemory;
        }
    }

    if( !xAckAdded )
    {
        /* The command is complete, call the callback. */
        if( pxCommand->vCallback != NULL )
        {
            pxCommand->vCallback( pxCommand->pxCmdContext, xStatus );
        }
    }

    /* If empty command, iterate through stored contexts so that all MQTT
     * connections are used equally across the empty commands. */
    if( pxCommand->xCommandType == NONE )
    {
        pMQTTContext = getContextForProcessLoop();
        /* Set context for original command in case this results in a network error. */
        pxCommand->pMqttContext = pMQTTContext;
    }

    /* Run a single iteration of the process loop if there were no errors and
     * the MQTT connection still exists. */
    if( ( xStatus == MQTTSuccess ) && ( pMQTTContext != NULL ) && ( pMQTTContext->connectStatus == MQTTConnected ) )
    {
        xStatus = MQTT_ProcessLoop( pMQTTContext, processLoopTimeoutMs );
    }

    return xStatus;
}

/*-----------------------------------------------------------*/

static void prvHandleIncomingPublish( MQTTAgentContext_t * pAgentContext,
                                      MQTTPublishInfo_t * pxPublishInfo )
{
    bool xIsMatched = false, xRelayedPublish = false;
    MQTTStatus_t xStatus;
    size_t i;
    SubscriptionElement_t * pxSubscriptions = pAgentContext->pSubscriptionList;

    configASSERT( pxPublishInfo != NULL );

    for( i = 0; i < pAgentContext->maxSubscriptions; i++ )
    {
        if( pxSubscriptions[ i ].usFilterLength > 0 )
        {
            xStatus = MQTT_MatchTopic( pxPublishInfo->pTopicName,
                                       pxPublishInfo->topicNameLength,
                                       pxSubscriptions[ i ].pcSubscriptionFilter,
                                       pxSubscriptions[ i ].usFilterLength,
                                       &xIsMatched );
            /* The call can't fail if the topic name and filter is valid. */
            configASSERT( xStatus == MQTTSuccess );

            if( xIsMatched )
            {
                LogDebug( ( "Adding publish to response queue for %.*s\n",
                            pxSubscriptions[ i ].usFilterLength,
                            pxSubscriptions[ i ].pcSubscriptionFilter ) );
                pxSubscriptions[ i ].vPublishCallback( pxPublishInfo, pxSubscriptions[ i ].pSubscriptionContext );
                xRelayedPublish = true;
            }
        }
    }

    /* It is possible a publish was sent on an unsubscribed topic. This is
     * possible on topics reserved by the broker, e.g. those beginning with
     * '$'. In this case, we copy the publish to a queue we configured to
     * receive these publishes. */
    if( !xRelayedPublish )
    {
        LogWarn( ( "Publish received on topic %.*s with no subscription.\n",
                   pxPublishInfo->topicNameLength,
                   pxPublishInfo->pTopicName ) );

        if( pAgentContext->vDefaultPublishCallback != NULL )
        {
            pAgentContext->vDefaultPublishCallback( pxPublishInfo, pAgentContext->pDefaultSubscriptionContext );
        }
    }
}

/*-----------------------------------------------------------*/

static void prvHandleSubscriptionAcks( MQTTAgentContext_t * pAgentContext,
                                       MQTTPacketInfo_t * pxPacketInfo,
                                       MQTTDeserializedInfo_t * pxDeserializedInfo,
                                       AckInfo_t * pxAckInfo,
                                       uint8_t ucPacketType )
{
    size_t i;
    CommandContext_t * pxAckContext = NULL;
    CommandCallback_t vAckCallback = NULL;
    uint8_t * pcSubackCodes = NULL;
    MQTTSubscribeInfo_t * pxSubscribeInfo = NULL;

    configASSERT( pxAckInfo != NULL );

    pxAckContext = pxAckInfo->xOriginalCommand.pxCmdContext;
    vAckCallback = pxAckInfo->xOriginalCommand.vCallback;
    pxSubscribeInfo = ( MQTTSubscribeInfo_t * ) pxAckInfo->xOriginalCommand.pMqttInfoParam;
    pcSubackCodes = pxPacketInfo->pRemainingData + 2U;

    for( i = 0; i < pxAckInfo->xOriginalCommand.uintParam; i++ )
    {
        if( ucPacketType == MQTT_PACKET_TYPE_SUBACK )
        {
            if( pcSubackCodes[ i ] != MQTTSubAckFailure )
            {
                LogInfo( ( "Adding subscription to %.*s\n",
                           pxSubscribeInfo[ i ].topicFilterLength,
                           pxSubscribeInfo[ i ].pTopicFilter ) );
                prvAddSubscription( pAgentContext,
                                    pxSubscribeInfo[ i ].pTopicFilter,
                                    pxSubscribeInfo[ i ].topicFilterLength,
                                    pxAckInfo->xOriginalCommand.vPublishCallback,
                                    pxAckInfo->xOriginalCommand.pPublishCallbackContext );
            }
            else
            {
                LogError( ( "Subscription to %.*s failed.\n",
                            pxSubscribeInfo[ i ].topicFilterLength,
                            pxSubscribeInfo[ i ].pTopicFilter ) );
            }
        }
        else
        {
            LogInfo( ( "Removing subscription to %.*s\n",
                       pxSubscribeInfo[ i ].topicFilterLength,
                       pxSubscribeInfo[ i ].pTopicFilter ) );
            prvRemoveSubscription( pAgentContext,
                                   pxSubscribeInfo[ i ].pTopicFilter,
                                   pxSubscribeInfo[ i ].topicFilterLength );
        }
    }

    if( vAckCallback != NULL )
    {
        vAckCallback( pxAckContext, pxDeserializedInfo->deserializationResult );
    }
}

/*-----------------------------------------------------------*/

static MQTTContext_t * getContextForProcessLoop( void )
{
    static uint32_t contextIndex = 0U;
    uint32_t oldIndex = 0U;
    MQTTContext_t * ret = NULL;

    oldIndex = contextIndex;

    do
    {
        ret = pAgentContexts[ contextIndex ].pMQTTContext;

        if( ++contextIndex >= MAX_CONNECTIONS )
        {
            contextIndex = 0U;
        }
    } while( ( ret == NULL ) && ( oldIndex != contextIndex ) );

    return ret;
}

/*-----------------------------------------------------------*/

static MQTTAgentContext_t * getAgentFromContext( MQTTContext_t * pMQTTContext )
{
    MQTTAgentContext_t * ret = NULL;
    int i = 0;

    configASSERT( pMQTTContext );

    for( i = 0; i < MAX_CONNECTIONS; i++ )
    {
        if( pAgentContexts[ i ].pMQTTContext == pMQTTContext )
        {
            ret = &pAgentContexts[ i ];
            break;
        }
    }

    return ret;
}

/*-----------------------------------------------------------*/

void MQTTAgent_EventCallback( MQTTContext_t * pMqttContext,
                              MQTTPacketInfo_t * pPacketInfo,
                              MQTTDeserializedInfo_t * pDeserializedInfo )
{
    configASSERT( pMqttContext != NULL );
    configASSERT( pPacketInfo != NULL );
    AckInfo_t xAckInfo;
    uint16_t packetIdentifier = pDeserializedInfo->packetIdentifier;
    CommandCallback_t vAckCallback = NULL;
    MQTTAgentContext_t * pAgentContext = getAgentFromContext( pMqttContext );

    /* Handle incoming publish. The lower 4 bits of the publish packet
     * type is used for the dup, QoS, and retain flags. Hence masking
     * out the lower bits to check if the packet is publish. */
    if( ( pPacketInfo->type & 0xF0U ) == MQTT_PACKET_TYPE_PUBLISH )
    {
        prvHandleIncomingPublish( pAgentContext, pDeserializedInfo->pPublishInfo );
    }
    else
    {
        /* Handle other packets. */
        switch( pPacketInfo->type )
        {
            case MQTT_PACKET_TYPE_PUBACK:
            case MQTT_PACKET_TYPE_PUBCOMP:
                xAckInfo = prvGetAwaitingOperation( pAgentContext, packetIdentifier, true );

                if( xAckInfo.usPacketId == packetIdentifier )
                {
                    vAckCallback = xAckInfo.xOriginalCommand.vCallback;

                    if( vAckCallback != NULL )
                    {
                        vAckCallback( xAckInfo.xOriginalCommand.pxCmdContext, pDeserializedInfo->deserializationResult );
                    }
                }

                break;

            case MQTT_PACKET_TYPE_SUBACK:
            case MQTT_PACKET_TYPE_UNSUBACK:
                xAckInfo = prvGetAwaitingOperation( pAgentContext, packetIdentifier, true );

                if( xAckInfo.usPacketId == packetIdentifier )
                {
                    prvHandleSubscriptionAcks( pAgentContext, pPacketInfo, pDeserializedInfo, &xAckInfo, pPacketInfo->type );
                }
                else
                {
                    LogError( ( "No subscription or unsubscribe operation found matching packet id %u.\n", packetIdentifier ) );
                }

                break;

            /* Nothing to do for these packets since they don't indicate command completion. */
            case MQTT_PACKET_TYPE_PUBREC:
            case MQTT_PACKET_TYPE_PUBREL:
                break;

            case MQTT_PACKET_TYPE_PINGRESP:

                /* Nothing to be done from application as library handles
                 * PINGRESP with the use of MQTT_ProcessLoop API function. */
                LogWarn( ( "PINGRESP should not be handled by the application "
                           "callback when using MQTT_ProcessLoop.\n" ) );
                break;

            /* Any other packet type is invalid. */
            default:
                LogError( ( "Unknown packet type received:(%02x).\n",
                            pPacketInfo->type ) );
        }
    }
}

/*-----------------------------------------------------------*/

MQTTContext_t * MQTTAgent_CommandLoop( void )
{
    Command_t xCommand;
    MQTTStatus_t xStatus = MQTTSuccess;
    static int lNumProcessed = 0;
    MQTTContext_t * ret = NULL;

    /* Loop until we receive a terminate command. */
    for( ; ; )
    {
        /* Set command type to NONE. */
        memset( ( void * ) &xCommand, 0x00, sizeof( xCommand ) );

        /* If there is no command in the queue, try again. */
        if( xQueueReceive( xCommandQueue, &xCommand, MQTT_AGENT_QUEUE_WAIT_TIME ) != pdFALSE )
        {
            /* Keep a count of processed operations, for debug logs. */
            lNumProcessed++;
        }

        xStatus = prvProcessCommand( &xCommand );

        /* Return the current MQTT context if status was not successful. */
        if( xStatus != MQTTSuccess )
        {
            LogError( ( "MQTT operation failed with status %s\n",
                        MQTT_Status_strerror( xStatus ) ) );
            ret = xCommand.pMqttContext;
            break;
        }

        /* Terminate the loop if we receive the termination command. */
        if( xCommand.xCommandType == TERMINATE )
        {
            ret = NULL;
            break;
        }

        LogDebug( ( "Processed %d operations.", lNumProcessed ) );
    }

    return ret;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTTAgent_ResumeSession( MQTTContext_t * pMqttContext,
                                      bool xSessionPresent )
{
    MQTTStatus_t xResult = MQTTSuccess;
    MQTTAgentContext_t * pAgentContext = getAgentFromContext( pMqttContext );
    AckInfo_t * pxPendingAcks = pAgentContext->pPendingAcks;
    SubscriptionElement_t * pxSubscriptions = pAgentContext->pSubscriptionList;
    MQTTSubscribeInfo_t * pxResendSubscriptions = pAgentContext->pResendSubscriptions;
    MQTTPublishInfo_t * pxOriginalPublish = NULL;

    /* Resend publishes if session is present. NOTE: It's possible that some
     * of the operations that were in progress during the network interruption
     * were subscribes. In that case, we would want to mark those operations
     * as completing with error and remove them from the list of operations, so
     * that the calling task can try subscribing again. We do not handle that
     * case in this demo for simplicity, since only one subscription packet is
     * sent per iteration of this demo. */
    if( xSessionPresent )
    {
        MQTTStateCursor_t cursor = MQTT_STATE_CURSOR_INITIALIZER;
        uint16_t packetId = MQTT_PACKET_ID_INVALID;
        AckInfo_t xFoundAck;

        packetId = MQTT_PublishToResend( pAgentContext->pMQTTContext, &cursor );

        while( packetId != MQTT_PACKET_ID_INVALID )
        {
            /* Retrieve the operation but do not remove it from the list. */
            xFoundAck = prvGetAwaitingOperation( pAgentContext, packetId, false );

            if( xFoundAck.usPacketId == packetId )
            {
                /* Set the DUP flag. */
                pxOriginalPublish = ( MQTTPublishInfo_t * ) xFoundAck.xOriginalCommand.pMqttInfoParam;
                pxOriginalPublish->dup = true;
                xResult = MQTT_Publish( pAgentContext->pMQTTContext, pxOriginalPublish, packetId );

                if( xResult != MQTTSuccess )
                {
                    LogError( ( "Error in resending publishes. Error code=%s\n", MQTT_Status_strerror( xResult ) ) );
                    break;
                }
            }

            packetId = MQTT_PublishToResend( pAgentContext->pMQTTContext, &cursor );
        }
    }

    /* If we wanted to resume a session but none existed with the broker, we
     * should mark all in progress operations as errors so that the tasks that
     * created them can try again. Also, we will resubscribe to the filters in
     * the subscription list, so tasks do not unexpectedly lose their subscriptions. */
    else
    {
        size_t i = 0, j = 0;
        Command_t xNewCommand;
        bool xCommandCreated = false;
        BaseType_t xCommandAdded;

        /* We have a clean session, so clear all operations pending acknowledgments. */
        for( i = 0; i < pAgentContext->pendingAckSize; i++ )
        {
            if( pxPendingAcks[ i ].usPacketId != MQTT_PACKET_ID_INVALID )
            {
                if( pxPendingAcks[ i ].xOriginalCommand.vCallback != NULL )
                {
                    /* Bad response to indicate network error. */
                    pxPendingAcks[ i ].xOriginalCommand.vCallback( pxPendingAcks[ i ].xOriginalCommand.pxCmdContext, MQTTBadResponse );
                }

                /* Now remove it from the list. */
                prvGetAwaitingOperation( pAgentContext, pxPendingAcks[ i ].usPacketId, true );
            }
        }

        /* Populate the array of MQTTSubscribeInfo_t. It's possible there may be
         * repeated subscriptions in the list. This is fine, since clients
         * are able to subscribe to a topic with an existing subscription. */
        for( i = 0; i < pAgentContext->maxSubscriptions; i++ )
        {
            if( pxSubscriptions[ i ].usFilterLength != 0 )
            {
                pxResendSubscriptions[ j ].pTopicFilter = pxSubscriptions[ i ].pcSubscriptionFilter;
                pxResendSubscriptions[ j ].topicFilterLength = pxSubscriptions[ i ].usFilterLength;
                pxResendSubscriptions[ j ].qos = MQTTQoS1;
                j++;
            }
        }

        /* Resubscribe if needed. */
        if( j > 0 )
        {
            xCommandCreated = prvCreateCommand( SUBSCRIBE, pMqttContext, pxResendSubscriptions, j, NULL, NULL, NULL, NULL, &xNewCommand );
            configASSERT( xCommandCreated == true );
            xNewCommand.pMqttInfoParam = pxResendSubscriptions;
            xNewCommand.uintParam = j;
            xNewCommand.pPublishCallbackContext = NULL;
            /* Send to the front of the queue so we will resubscribe as soon as possible. */
            xCommandAdded = xQueueSendToFront( xCommandQueue, &xNewCommand, MQTT_AGENT_QUEUE_WAIT_TIME );
            configASSERT( xCommandAdded == pdTRUE );
        }
    }

    return xResult;
}

/*-----------------------------------------------------------*/

static bool createAndAddCommand( CommandType_t commandType,
                                 MQTTContext_t * pMqttContext,
                                 CommandContext_t * pCommandContext,
                                 CommandCallback_t cmdCallback,
                                 void * pMqttInfoParam,
                                 uint32_t uintParam,
                                 PublishCallback_t publishCallback,
                                 void * pSubscriptionContext )
{
    bool ret = false;
    Command_t newCommand = { 0 };

    ret = prvCreateCommand( commandType,
                            pMqttContext,
                            pMqttInfoParam,
                            uintParam,
                            publishCallback,
                            pSubscriptionContext,
                            pCommandContext,
                            cmdCallback,
                            &newCommand );

    if( ret )
    {
        ret = prvAddCommandToQueue( &newCommand );
    }

    return ret;
}

/*-----------------------------------------------------------*/

bool MQTTAgent_Subscribe( MQTTContext_t * pMqttContext,
                          MQTTSubscribeInfo_t * pSubscriptionList,
                          size_t subscriptionCount,
                          PublishCallback_t publishCallback,
                          void * pPublishCallbackContext,
                          CommandContext_t * pCommandContext,
                          CommandCallback_t cmdCallback )
{
    configASSERT( pMqttContext != NULL );
    return createAndAddCommand( SUBSCRIBE,
                                pMqttContext,
                                pCommandContext,
                                cmdCallback,
                                pSubscriptionList,
                                subscriptionCount,
                                publishCallback,
                                pPublishCallbackContext );
}

/*-----------------------------------------------------------*/

bool MQTTAgent_Unsubscribe( MQTTContext_t * pMqttContext,
                            MQTTSubscribeInfo_t * pSubscriptionList,
                            size_t subscriptionCount,
                            CommandContext_t * pCommandContext,
                            CommandCallback_t cmdCallback )
{
    configASSERT( pMqttContext != NULL );
    return createAndAddCommand( UNSUBSCRIBE, pMqttContext, pCommandContext, cmdCallback, pSubscriptionList, subscriptionCount, NULL, NULL );
}

/*-----------------------------------------------------------*/

bool MQTTAgent_Publish( MQTTContext_t * pMqttContext,
                        MQTTPublishInfo_t * pPublishInfo,
                        CommandContext_t * pCommandContext,
                        CommandCallback_t cmdCallback )
{
    configASSERT( pMqttContext != NULL );
    return createAndAddCommand( PUBLISH, pMqttContext, pCommandContext, cmdCallback, pPublishInfo, 0, NULL, NULL );
}

/*-----------------------------------------------------------*/

bool MQTTAgent_ProcessLoop( MQTTContext_t * pMqttContext,
                            uint32_t timeoutMs,
                            CommandContext_t * pCommandContext,
                            CommandCallback_t cmdCallback )
{
    configASSERT( pMqttContext != NULL );
    return createAndAddCommand( PROCESSLOOP, pMqttContext, pCommandContext, cmdCallback, NULL, timeoutMs, NULL, NULL );
}

/*-----------------------------------------------------------*/

bool MQTTAgent_Ping( MQTTContext_t * pMqttContext,
                     CommandContext_t * pCommandContext,
                     CommandCallback_t cmdCallback )
{
    configASSERT( pMqttContext != NULL );
    return createAndAddCommand( PING, pMqttContext, pCommandContext, cmdCallback, NULL, 0, NULL, NULL );
}

/*-----------------------------------------------------------*/

bool MQTTAgent_Disconnect( MQTTContext_t * pMqttContext,
                           CommandContext_t * pCommandContext,
                           CommandCallback_t cmdCallback )
{
    configASSERT( pMqttContext != NULL );
    return createAndAddCommand( DISCONNECT, pMqttContext, pCommandContext, cmdCallback, NULL, 0, NULL, NULL );
}

/*-----------------------------------------------------------*/

bool MQTTAgent_Register( MQTTContext_t * pMqttContext,
                         PublishCallback_t defaultPublishCallback,
                         void * pDefaultPublishContext,
                         CommandContext_t * pCommandContext,
                         CommandCallback_t cmdCallback )
{
    configASSERT( pMqttContext != NULL );
    configASSERT( pCommandContext != NULL );
    return createAndAddCommand( INITIALIZE, pMqttContext, pCommandContext, cmdCallback, NULL, 0, defaultPublishCallback, pDefaultPublishContext );
}

/*-----------------------------------------------------------*/

bool MQTTAgent_Free( MQTTContext_t * pMqttContext,
                     CommandContext_t * pCommandContext,
                     CommandCallback_t cmdCallback )
{
    configASSERT( pMqttContext != NULL );
    return createAndAddCommand( FREE, pMqttContext, pCommandContext, cmdCallback, NULL, 0, NULL, NULL );
}

/*-----------------------------------------------------------*/

bool MQTTAgent_Terminate( void )
{
    return createAndAddCommand( TERMINATE, NULL, NULL, NULL, NULL, 0, NULL, NULL );
}

/*-----------------------------------------------------------*/

uint32_t MQTTAgent_GetNumWaiting( void )
{
    return uxQueueMessagesWaiting( xCommandQueue );
}

/*-----------------------------------------------------------*/

bool MQTTAgent_CreateCommandQueue( const uint32_t uxCommandQueueLength )
{
    static BaseType_t xQueueCreated = pdFALSE;
    BaseType_t xCreateAgent;

    taskENTER_CRITICAL();
    {
        if( xQueueCreated == pdFALSE )
        {
            /* The agent has not been created yet, so try and create it. */
            xCreateAgent = pdTRUE;
            xQueueCreated = pdTRUE;
        }
        else
        {
            xCreateAgent = pdFALSE;
        }
    }
    taskEXIT_CRITICAL();

    if( xCreateAgent != pdFALSE )
    {
        /* The command queue should not have been created yet. */
        configASSERT( xCommandQueue == NULL );
        xCommandQueue = xQueueCreate( uxCommandQueueLength, sizeof( Command_t ) );

        if( xCommandQueue == NULL )
        {
            xQueueCreated = pdFALSE;
            LogDebug( ( "Could not create queue.\n" ) );
        }
        else
        {
            LogInfo( ( "Successfully created MQTT agent queue.\n" ) );
        }
    }

    return xQueueCreated;
}

/*-----------------------------------------------------------*/
