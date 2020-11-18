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

/* MQTT library includes. */
#include "mqtt_agent.h"

/**
 * @brief Timeout for MQTT_ProcessLoop function in milliseconds.
 *
 * This demo uses no delay for the process loop, so each invocation will run
 * one iteration, and will only receive a single packet. However, if there is
 * no data available on the socket, the entire socket timeout value will elapse.
 */
#define mqttexamplePROCESS_LOOP_TIMEOUT_MS           ( 0U )

/**
 * @brief Ticks to wait for task notifications.
 */
#define mqttexampleDEMO_TICKS_TO_WAIT                pdMS_TO_TICKS( 1000 )

#define mqttexamplePOST_SUBSCRIBE_DELAY_MS			 400U

/*-----------------------------------------------------------*/

/**
 * @brief Track an operation by adding it to a list, indicating it is anticipating
 * an acknowledgment.
 *
 * @param[in] usPacketId Packet ID of pending ack.
 * @param[in] pxCommand Copy of command that is expecting an ack.
 *
 * @return `true` if the operation was added; else `false`
 */
static bool prvAddAwaitingOperation( uint16_t usPacketId,
                                     Command_t * pxCommand );

/**
 * @brief Retrieve an operation from the list of pending acks, and optionally
 * remove it.
 *
 * @param[in] usPacketId Packet ID of incoming ack.
 * @param[in] xRemove Flag indicating if the operation should be removed.
 *
 * @return Stored information about the operation awaiting the ack.
 */
static AckInfo_t prvGetAwaitingOperation( uint16_t usPacketId,
                                          bool xRemove );

/**
 * @brief Add a subscription to the subscription list.
 *
 * @note Multiple tasks can be subscribed to the same topic. However, a single
 * task may only subscribe to the same topic filter once.
 *
 * @param[in] pcTopicFilter Topic filter of subscription.
 * @param[in] usTopicFilterLength Length of topic filter.
 * @param[in] pxQueue Response queue in which to enqueue received publishes.
 */
static void prvAddSubscription( const char * pcTopicFilter,
                                uint16_t usTopicFilterLength,
                                QueueHandle_t pxQueue );

/**
 * @brief Remove a subscription from the subscription list.
 *
 * @note If the topic filter exists multiple times in the subscription list,
 * then every instance of the subscription will be removed.
 *
 * @param[in] pcTopicFilter Topic filter of subscription.
 * @param[in] usTopicFilterLength Length of topic filter.
 */
static void prvRemoveSubscription( const char * pcTopicFilter,
                                   uint16_t usTopicFilterLength );

/**
 * @brief Copy an incoming publish to a response queue.
 *
 * @param[in] pxPublishInfo Info of incoming publish.
 * @param[in] pxResponseQueue Queue to which the publish is copied.
 *
 * @return true if the publish was copied to the queue, else false.
 */
static BaseType_t prvCopyPublishToQueue( MQTTPublishInfo_t * pxPublishInfo,
                                         QueueHandle_t pxResponseQueue );

/**
 * @brief Process a #Command_t.
 *
 * @note This demo does not check existing subscriptions before sending a
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
 * @brief Dispatch an incoming publish to the appropriate response queues.
 *
 * @param[in] pxPublishInfo Incoming publish information.
 */
static void prvHandleIncomingPublish( MQTTPublishInfo_t * pxPublishInfo );

/**
 * @brief Add or delete subscription information from a SUBACK or UNSUBACK.
 *
 * @param[in] pxPacketInfo Pointer to incoming packet.
 * @param[in] pxDeserializedInfo Pointer to deserialized information from
 * the incoming packet.
 * @param[in] pxAckInfo Pointer to stored information for the original subscribe
 * or unsubscribe operation resulting in the received packet.
 * @param[in] ucPacketType The type of the incoming packet, either SUBACK or UNSUBACK.
 */
static void prvHandleSubscriptionAcks( MQTTPacketInfo_t * pxPacketInfo,
                                       MQTTDeserializedInfo_t * pxDeserializedInfo,
                                       AckInfo_t * pxAckInfo,
                                       uint8_t ucPacketType );

/*-----------------------------------------------------------*/

// /**
//  * @brief List of operations that are awaiting an ack from the broker.
//  */
// static AckInfo_t pxPendingAcks[ mqttexamplePENDING_ACKS_MAX_SIZE ];

// /**
//  * @brief List of active subscriptions.
//  */
// static SubscriptionElement_t pxSubscriptions[ mqttexampleSUBSCRIPTIONS_MAX_COUNT ];

// /**
//  * @brief Array of subscriptions to resubscribe to.
//  */
// static MQTTSubscribeInfo_t pxResendSubscriptions[ mqttexampleSUBSCRIPTIONS_MAX_COUNT ];

// /**
//  * @brief Context to use for a resubscription after a reconnect.
//  */
// static CommandContext_t xResubscribeContext;

// /**
//  * @brief Queue for main task to handle MQTT operations.
//  */
// QueueHandle_t xCommandQueue;

// /**
//  * @brief Response queue for publishes received on non-subscribed topics.
//  */
// QueueHandle_t xDefaultResponseQueue;

// /**
//  * @brief Global MQTT context.
//  */
// MQTTContext_t globalMqttContext;

/*-----------------------------------------------------------*/

static bool prvAddAwaitingOperation( uint16_t usPacketId,
                                     Command_t * pxCommand )
{
    int32_t i = 0;
    bool xAckAdded = false;

    for( i = 0; i < mqttexamplePENDING_ACKS_MAX_SIZE; i++ )
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

static AckInfo_t prvGetAwaitingOperation( uint16_t usPacketId,
                                          bool xRemove )
{
    int32_t i = 0;
    AckInfo_t xFoundAck = { 0 };

    for( i = 0; i < mqttexamplePENDING_ACKS_MAX_SIZE; i++ )
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

static void prvAddSubscription( const char * pcTopicFilter,
                                uint16_t usTopicFilterLength,
                                QueueHandle_t pxQueue )
{
    int32_t i = 0, ulAvailableIndex = mqttexampleSUBSCRIPTIONS_MAX_COUNT;

    /* Start at end of array, so that we will insert at the first available index. */
    for( i = mqttexampleSUBSCRIPTIONS_MAX_COUNT - 1; i >= 0; i-- )
    {
        if( pxSubscriptions[ i ].usFilterLength == 0 )
        {
            ulAvailableIndex = i;
        }
        else if( ( pxSubscriptions[ i ].usFilterLength == usTopicFilterLength ) &&
                 ( strncmp( pcTopicFilter, pxSubscriptions[ i ].pcSubscriptionFilter, usTopicFilterLength ) == 0 ) )
        {
            /* If a subscription already exists, don't do anything. */
            if( pxSubscriptions[ i ].pxResponseQueue == pxQueue )
            {
                LogWarn( ( "Subscription already exists.\n" ) );
                ulAvailableIndex = mqttexampleSUBSCRIPTIONS_MAX_COUNT;
                break;
            }
        }
    }

    if( ( ulAvailableIndex < mqttexampleSUBSCRIPTIONS_MAX_COUNT ) && ( pxQueue != NULL ) )
    {
        pxSubscriptions[ ulAvailableIndex ].usFilterLength = usTopicFilterLength;
        pxSubscriptions[ ulAvailableIndex ].pxResponseQueue = pxQueue;
        memcpy( pxSubscriptions[ ulAvailableIndex ].pcSubscriptionFilter, pcTopicFilter, usTopicFilterLength );
    }
}

/*-----------------------------------------------------------*/

static void prvRemoveSubscription( const char * pcTopicFilter,
                                   uint16_t usTopicFilterLength )
{
    int32_t i = 0;

    for( i = 0; i < mqttexampleSUBSCRIPTIONS_MAX_COUNT; i++ )
    {
        if( pxSubscriptions[ i ].usFilterLength == usTopicFilterLength )
        {
            if( strncmp( pxSubscriptions[ i ].pcSubscriptionFilter, pcTopicFilter, usTopicFilterLength ) == 0 )
            {
                pxSubscriptions[ i ].usFilterLength = 0;
                pxSubscriptions[ i ].pxResponseQueue = NULL;
                memset( pxSubscriptions[ i ].pcSubscriptionFilter, 0x00, mqttexampleDEMO_BUFFER_SIZE );
            }
        }
    }
}

/*-----------------------------------------------------------*/

static BaseType_t prvCopyPublishToQueue( MQTTPublishInfo_t * pxPublishInfo,
                                         QueueHandle_t pxResponseQueue )
{
    PublishElement_t xCopiedPublish;

    memset( &xCopiedPublish, 0x00, sizeof( xCopiedPublish ) );
    memcpy( &( xCopiedPublish.xPublishInfo ), pxPublishInfo, sizeof( MQTTPublishInfo_t ) );

    /* Since adding an MQTTPublishInfo_t to a queue will not copy its string buffers,
     * we need to add buffers to a struct and copy the entire structure. We don't
     * need to set xCopiedPublish.xPublishInfo's pointers yet since the actual address
     * will change after the struct is copied into the queue. */
    memcpy( xCopiedPublish.pcTopicNameBuf, pxPublishInfo->pTopicName, pxPublishInfo->topicNameLength );
    memcpy( xCopiedPublish.pcPayloadBuf, pxPublishInfo->pPayload, pxPublishInfo->payloadLength );

    /* Add to response queue. */
    return xQueueSendToBack( pxResponseQueue, ( void * ) &xCopiedPublish, mqttexampleDEMO_TICKS_TO_WAIT );
}

/*-----------------------------------------------------------*/

static MQTTStatus_t prvProcessCommand( Command_t * pxCommand )
{
    MQTTStatus_t xStatus = MQTTSuccess;
    uint16_t usPacketId = MQTT_PACKET_ID_INVALID;
    bool xAddAckToList = false, xAckAdded = false;
    BaseType_t xNetworkResult = pdFAIL;
    MQTTPublishInfo_t * pxPublishInfo;
    MQTTSubscribeInfo_t * pxSubscribeInfo;

    switch( pxCommand->xCommandType )
    {
        case PROCESSLOOP:

            /* The process loop will run at the end of every command, so we don't
             * need to call it again here. */
            LogDebug( ( "Running Process Loop." ) );
            break;

        case PUBLISH:
            configASSERT( pxCommand->pxCmdContext != NULL );
            pxPublishInfo = pxCommand->pxCmdContext->pxPublishInfo;
            configASSERT( pxPublishInfo != NULL );

            if( pxPublishInfo->qos != MQTTQoS0 )
            {
                usPacketId = MQTT_GetPacketId( &globalMqttContext );
            }

            LogDebug( ( "Publishing message to %.*s.", ( int ) pxPublishInfo->topicNameLength, pxPublishInfo->pTopicName ) );
            xStatus = MQTT_Publish( &globalMqttContext, pxPublishInfo, usPacketId );
            pxCommand->pxCmdContext->xReturnStatus = xStatus;

            /* Add to pending ack list, or call callback if QoS 0. */
            xAddAckToList = ( pxPublishInfo->qos != MQTTQoS0 ) && ( xStatus == MQTTSuccess );
            break;

        case SUBSCRIBE:
        case UNSUBSCRIBE:
            configASSERT( pxCommand->pxCmdContext != NULL );
            pxSubscribeInfo = pxCommand->pxCmdContext->pxSubscribeInfo;
            configASSERT( pxSubscribeInfo != NULL );
            configASSERT( pxSubscribeInfo->pTopicFilter != NULL );
            usPacketId = MQTT_GetPacketId( &globalMqttContext );

            if( pxCommand->xCommandType == SUBSCRIBE )
            {
                /* Even if some subscriptions already exist in the subscription list,
                 * it is fine to send another subscription request. A valid use case
                 * for this is changing the maximum QoS of the subscription. */
                xStatus = MQTT_Subscribe( &globalMqttContext,
                                          pxSubscribeInfo,
                                          pxCommand->pxCmdContext->ulSubscriptionCount,
                                          usPacketId );
            }
            else
            {
                xStatus = MQTT_Unsubscribe( &globalMqttContext,
                                            pxSubscribeInfo,
                                            pxCommand->pxCmdContext->ulSubscriptionCount,
                                            usPacketId );
            }

            pxCommand->pxCmdContext->xReturnStatus = xStatus;
            xAddAckToList = ( xStatus == MQTTSuccess );
            break;

        case PING:
            xStatus = MQTT_Ping( &globalMqttContext );

            if( pxCommand->pxCmdContext != NULL )
            {
                pxCommand->pxCmdContext->xReturnStatus = xStatus;
            }

            break;

        case DISCONNECT:
            xStatus = MQTT_Disconnect( &globalMqttContext );

            if( pxCommand->pxCmdContext != NULL )
            {
                pxCommand->pxCmdContext->xReturnStatus = xStatus;
            }

            break;

        case RECONNECT:
            // /* Reconnect TCP. */
            // xNetworkResult = prvSocketDisconnect( &xNetworkContext );
            // configASSERT( xNetworkResult == pdPASS );
            // xNetworkResult = prvSocketConnect( &xNetworkContext );
            // configASSERT( xNetworkResult == pdPASS );
            // /* MQTT Connect with a persistent session. */
            // xStatus = prvMQTTConnect( &globalMqttContext, false );
            break;

        case TERMINATE:
            LogInfo( ( "Terminating command loop." ) );

        default:
            break;
    }

    if( xAddAckToList )
    {
        xAckAdded = prvAddAwaitingOperation( usPacketId, pxCommand );

        /* Set the return status if no memory was available to store the operation
         * information. */
        if( !xAckAdded )
        {
            LogError( ( "No memory to wait for acknowledgment for packet %u\n", usPacketId ) );

            /* All operations that can wait for acks (publish, subscribe, unsubscribe)
             * require a context. */
            configASSERT( pxCommand->pxCmdContext != NULL );
            pxCommand->pxCmdContext->xReturnStatus = MQTTNoMemory;
        }
    }

    if( !xAckAdded )
    {
        /* The command is complete, call the callback. */
        if( pxCommand->vCallback != NULL )
        {
            pxCommand->vCallback( pxCommand->pxCmdContext );
        }
    }

    /* Run a single iteration of the process loop if there were no errors and
     * the MQTT connection still exists. */
    if( ( xStatus == MQTTSuccess ) && ( globalMqttContext.connectStatus == MQTTConnected ) )
    {
        xStatus = MQTT_ProcessLoop( &globalMqttContext, mqttexamplePROCESS_LOOP_TIMEOUT_MS );
    }

    return xStatus;
}

/*-----------------------------------------------------------*/

static void prvHandleIncomingPublish( MQTTPublishInfo_t * pxPublishInfo )
{
    bool xIsMatched = false, xRelayedPublish = false;
    MQTTStatus_t xStatus;
    size_t i;
    BaseType_t xPublishCopied = pdFALSE;

    configASSERT( pxPublishInfo != NULL );

    for( i = 0; i < mqttexampleSUBSCRIPTIONS_MAX_COUNT; i++ )
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
                xPublishCopied = prvCopyPublishToQueue( pxPublishInfo, pxSubscriptions[ i ].pxResponseQueue );
                /* Ensure the publish was copied to the queue. */
                configASSERT( xPublishCopied == pdTRUE );
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
        xPublishCopied = prvCopyPublishToQueue( pxPublishInfo, xDefaultResponseQueue );
        /* Ensure the publish was copied to the queue. */
        configASSERT( xPublishCopied == pdTRUE );
    }
}

/*-----------------------------------------------------------*/

static void prvHandleSubscriptionAcks( MQTTPacketInfo_t * pxPacketInfo,
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
    pxSubscribeInfo = pxAckContext->pxSubscribeInfo;
    pcSubackCodes = pxPacketInfo->pRemainingData + 2U;

    for( i = 0; i < pxAckContext->ulSubscriptionCount; i++ )
    {
        if( ucPacketType == MQTT_PACKET_TYPE_SUBACK )
        {
            if( pcSubackCodes[ i ] != MQTTSubAckFailure )
            {
                LogInfo( ( "Adding subscription to %.*s",
                           pxSubscribeInfo[ i ].topicFilterLength,
                           pxSubscribeInfo[ i ].pTopicFilter ) );
                prvAddSubscription( pxSubscribeInfo[ i ].pTopicFilter,
                                    pxSubscribeInfo[ i ].topicFilterLength,
                                    pxAckContext->pxResponseQueue );
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
            LogInfo( ( "Removing subscription to %.*s",
                       pxSubscribeInfo[ i ].topicFilterLength,
                       pxSubscribeInfo[ i ].pTopicFilter ) );
            prvRemoveSubscription( pxSubscribeInfo[ i ].pTopicFilter,
                                   pxSubscribeInfo[ i ].topicFilterLength );
        }
    }

    pxAckContext->xReturnStatus = pxDeserializedInfo->deserializationResult;

    if( vAckCallback != NULL )
    {
        vAckCallback( pxAckContext );
    }
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
    CommandContext_t * pxAckContext = NULL;
    CommandCallback_t vAckCallback = NULL;

    /* Handle incoming publish. The lower 4 bits of the publish packet
     * type is used for the dup, QoS, and retain flags. Hence masking
     * out the lower bits to check if the packet is publish. */
    if( ( pPacketInfo->type & 0xF0U ) == MQTT_PACKET_TYPE_PUBLISH )
    {
        prvHandleIncomingPublish( pDeserializedInfo->pPublishInfo );
    }
    else
    {
        /* Handle other packets. */
        switch( pPacketInfo->type )
        {
            case MQTT_PACKET_TYPE_PUBACK:
            case MQTT_PACKET_TYPE_PUBCOMP:
                xAckInfo = prvGetAwaitingOperation( packetIdentifier, true );

                if( xAckInfo.usPacketId == packetIdentifier )
                {
                    pxAckContext = xAckInfo.xOriginalCommand.pxCmdContext;
                    vAckCallback = xAckInfo.xOriginalCommand.vCallback;
                    pxAckContext->xReturnStatus = pDeserializedInfo->deserializationResult;

                    if( vAckCallback != NULL )
                    {
                        vAckCallback( pxAckContext );
                    }
                }

                break;

            case MQTT_PACKET_TYPE_SUBACK:
            case MQTT_PACKET_TYPE_UNSUBACK:
                xAckInfo = prvGetAwaitingOperation( packetIdentifier, true );

                if( xAckInfo.usPacketId == packetIdentifier )
                {
                    prvHandleSubscriptionAcks( pPacketInfo, pDeserializedInfo, &xAckInfo, pPacketInfo->type );
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

bool MQTTAgent_CommandLoop( void )
{
    Command_t xCommand;
    Command_t xNewCommand;
    MQTTStatus_t xStatus = MQTTSuccess;
    static int lNumProcessed = 0;
    bool xTerminateReceived = false;
    BaseType_t xCommandAdded = pdTRUE;

    /* Loop until we receive a terminate command. */
    for( ; ; )
    {
        /* If there is no command in the queue, try again. */
        if( xQueueReceive( xCommandQueue, &xCommand, mqttexampleDEMO_TICKS_TO_WAIT ) == pdFALSE )
        {
            LogInfo( ( "No commands in the queue. Trying again." ) );
            continue;
        }

        xStatus = prvProcessCommand( &xCommand );

        /* Add connect operation to front of queue if status was not successful. */
        if( xStatus != MQTTSuccess )
        {
            LogError( ( "MQTT operation failed with status %s\n",
                        MQTT_Status_strerror( xStatus ) ) );
            break;
        }

        /* Keep a count of processed operations, for debug logs. */
        lNumProcessed++;

        /* Delay after sending a subscribe. This is to so that the broker
         * creates a subscription for us before processing our next publish,
         * which should be immediately after this.  Only required because the
         * subscribe and publish commands are coming from separate tasks, which
         * would not normally be the case. */
        if( xCommand.xCommandType == SUBSCRIBE )
        {
            LogDebug( ( "Sleeping for %d ms after sending SUBSCRIBE packet.", mqttexamplePOST_SUBSCRIBE_DELAY_MS ) );
            vTaskDelay( mqttexamplePOST_SUBSCRIBE_DELAY_MS );
        }

        /* Terminate the loop if we receive the termination command. */
        if( xCommand.xCommandType == TERMINATE )
        {
            xTerminateReceived = true;
            break;
        }

        LogDebug( ( "Processed %d operations.", lNumProcessed ) );
    }

    return xTerminateReceived;
}

/*-----------------------------------------------------------*/

bool MQTTAgent_CreateCommand( CommandType_t xCommandType,
                              CommandContext_t * pxContext,
                              CommandCallback_t xCallback,
                              Command_t * pxCommand )
{
    bool xIsValid = true;

    /* Determine if required parameters are present in context. */
    switch( xCommandType )
    {
        case PUBLISH:
            xIsValid = ( pxContext != NULL ) ? ( pxContext->pxPublishInfo != NULL ) : false;
            break;

        case SUBSCRIBE:
        case UNSUBSCRIBE:
            xIsValid = ( pxContext != NULL ) ? ( ( pxContext->pxSubscribeInfo != NULL ) && ( pxContext->ulSubscriptionCount > 0 ) ) : false;
            break;

        default:
            /* Other operations don't need a context. */
            break;
    }

    if( xIsValid )
    {
        memset( pxCommand, 0x00, sizeof( Command_t ) );
        pxCommand->xCommandType = xCommandType;
        pxCommand->pxCmdContext = pxContext;
        pxCommand->vCallback = xCallback;
    }

    return xIsValid;
}

/*-----------------------------------------------------------*/

BaseType_t MQTTAgent_AddCommandToQueue( Command_t * pxCommand )
{
    return xQueueSendToBack( xCommandQueue, pxCommand, mqttexampleDEMO_TICKS_TO_WAIT );
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTTAgent_ResumeSession( bool xSessionPresent )
{
    MQTTStatus_t xResult = MQTTSuccess;

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

        packetId = MQTT_PublishToResend( &globalMqttContext, &cursor );

        while( packetId != MQTT_PACKET_ID_INVALID )
        {
            /* Retrieve the operation but do not remove it from the list. */
            xFoundAck = prvGetAwaitingOperation( packetId, false );

            if( xFoundAck.usPacketId == packetId )
            {
                /* Set the DUP flag. */
                xFoundAck.xOriginalCommand.pxCmdContext->pxPublishInfo->dup = true;
                xResult = MQTT_Publish( &globalMqttContext, xFoundAck.xOriginalCommand.pxCmdContext->pxPublishInfo, packetId );

                if( xResult != MQTTSuccess )
                {
                    LogError( ( "Error in resending publishes. Error code=%s\n", MQTT_Status_strerror( xResult ) ) );
                    break;
                }
            }

            packetId = MQTT_PublishToResend( &globalMqttContext, &cursor );
        }
    }

    /* If we wanted to resume a session but none existed with the broker, we
     * should mark all in progress operations as errors so that the tasks that
     * created them can try again. Also, we will resubscribe to the filters in
     * the subscription list, so tasks do not unexpectedly lose their subscriptions. */
    else
    {
        int32_t i = 0, j = 0;
        Command_t xNewCommand;
        bool xCommandCreated = false;
        BaseType_t xCommandAdded;

        /* We have a clean session, so clear all operations pending acknowledgments. */
        for( i = 0; i < mqttexamplePENDING_ACKS_MAX_SIZE; i++ )
        {
            if( pxPendingAcks[ i ].usPacketId != MQTT_PACKET_ID_INVALID )
            {
                if( pxPendingAcks[ i ].xOriginalCommand.vCallback != NULL )
                {
                    /* Bad response to indicate network error. */
                    pxPendingAcks[ i ].xOriginalCommand.pxCmdContext->xReturnStatus = MQTTBadResponse;
                    pxPendingAcks[ i ].xOriginalCommand.vCallback( pxPendingAcks[ i ].xOriginalCommand.pxCmdContext );
                }

                /* Now remove it from the list. */
                prvGetAwaitingOperation( pxPendingAcks[ i ].usPacketId, true );
            }
        }

        /* Populate the array of MQTTSubscribeInfo_t. It's possible there may be
         * repeated subscriptions in the list. This is fine, since clients
         * are able to subscribe to a topic with an existing subscription. */
        for( i = 0; i < mqttexampleSUBSCRIPTIONS_MAX_COUNT; i++ )
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
            memset( ( void * ) &xResubscribeContext, 0x00, sizeof( xResubscribeContext ) );
            xResubscribeContext.pxSubscribeInfo = pxResendSubscriptions;
            xResubscribeContext.ulSubscriptionCount = j;
            /* Set to NULL so existing queues will not be overwritten. */
            xResubscribeContext.pxResponseQueue = NULL;
            xResubscribeContext.xTaskToNotify = NULL;
            //xCommandCreated = MQTTAgent_CreateCommand( SUBSCRIBE, &xResubscribeContext, prvCommandCallback, &xNewCommand );
            xCommandCreated = MQTTAgent_CreateCommand( SUBSCRIBE, &xResubscribeContext, NULL, &xNewCommand );
            configASSERT( xCommandCreated == true );
            /* Send to the front of the queue so we will resubscribe as soon as possible. */
            xCommandAdded = xQueueSendToFront( xCommandQueue, &xNewCommand, mqttexampleDEMO_TICKS_TO_WAIT );
            configASSERT( xCommandAdded == pdTRUE );
        }
    }

    return xResult;
}

/*-----------------------------------------------------------*/
