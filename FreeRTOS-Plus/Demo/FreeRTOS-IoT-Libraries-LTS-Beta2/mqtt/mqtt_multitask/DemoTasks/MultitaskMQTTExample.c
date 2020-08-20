/*
 * FreeRTOS Kernel V10.3.0
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
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 */

/*
 * Demo for showing use of the managed MQTT API shared between multiple tasks.
 * This demo uses a thread safe queue to hold commands for interacting with the
 * MQTT API. A command task processes commands from the queue while other tasks
 * enqueue them. In addition to the command task, this demo uses one task for
 * publishing messages to the MQTT broker and another for receiving them via
 * an MQTT subscription. Each task has a queue to hold received publish messages,
 * and the command task pushes incoming publishes to the queue of each task
 * that is subscribed to the incoming topic.
 *
 * !!! NOTE !!!
 * This MQTT demo does not authenticate the server nor the client.
 * Hence, this demo should not be used as production ready code.
 */

/* Standard includes. */
#include <string.h>
#include <stdio.h>
#include <assert.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"

/* Demo Specific configs. */
#include "demo_config.h"

/* MQTT library includes. */
#include "mqtt.h"

/* Transport interface include. */
#include "plaintext_freertos.h"

/**
 * These configuration settings are required to run the demo.
 * Throw compilation error if the below configs are not defined.
 */
#ifndef CLIENT_IDENTIFIER
    #error "Please define a unique CLIENT_IDENTIFIER."
#endif
#ifndef BROKER_ENDPOINT
    #error "Please define BROKER_ENDPOINT."
#endif

/**
 * Provide default values for undefined configuration settings.
 */
#ifndef BROKER_PORT
    #define BROKER_PORT    ( 1883 )
#endif

#ifndef NETWORK_BUFFER_SIZE
    #define NETWORK_BUFFER_SIZE    ( 1024U )
#endif

/**
 * @brief Length of client identifier.
 */
#define CLIENT_IDENTIFIER_LENGTH            ( ( uint16_t ) ( sizeof( CLIENT_IDENTIFIER ) - 1 ) )

/**
 * @brief Length of MQTT server host name.
 */
#define BROKER_ENDPOINT_LENGTH              ( ( uint16_t ) ( sizeof( BROKER_ENDPOINT ) - 1 ) )

/**
 * @brief Timeout for receiving CONNACK packet in milliseconds.
 */
#define CONNACK_RECV_TIMEOUT_MS             ( 1000U )

/**
 * @brief Timeout for MQTT_ProcessLoop function in milliseconds.
 */
#define MQTT_PROCESS_LOOP_TIMEOUT_MS        ( 200U )

/**
 * @brief The maximum time interval in seconds which is allowed to elapse
 *  between two Control Packets.
 *
 *  It is the responsibility of the Client to ensure that the interval between
 *  Control Packets being sent does not exceed the this Keep Alive value. In the
 *  absence of sending any other Control Packets, the Client MUST send a
 *  PINGREQ Packet.
 */
#define MQTT_KEEP_ALIVE_INTERVAL_SECONDS    ( 60U )

/**
 * @brief Transport timeout in milliseconds for transport send and receive.
 */
#define TRANSPORT_SEND_RECV_TIMEOUT_MS      ( 20 )

#define _MILLISECONDS_PER_SECOND            ( 1000U )                                                 /**< @brief Milliseconds per second. */
#define _MILLISECONDS_PER_TICK              ( _MILLISECONDS_PER_SECOND / configTICK_RATE_HZ )         /**< Milliseconds per FreeRTOS tick. */

/**
 * @brief Ticks to wait for task notifications.
 */
#define DEMO_TICKS_TO_WAIT                  pdMS_TO_TICKS( 1000 )

/**
 * @brief Maximum number of operations awaiting an ack packet from the broker.
 */
#define PENDING_ACKS_MAX_SIZE               20

/**
 * @brief Maximum number of subscriptions to store in the subscription list.
 */
#define SUBSCRIPTIONS_MAX_COUNT             10

/**
 * @brief Number of publishes done by the publisher in this demo.
 */
#define PUBLISH_COUNT                       16

/**
 * @brief Size of statically allocated buffers for holding topic names and payloads in this demo.
 */
#define DEMO_BUFFER_SIZE                    100

/**
 * @brief Size of dynamically allocated buffers for holding topic names and payloads in this demo.
 */
#define DYNAMIC_BUFFER_SIZE                 25

/**
 * @brief Max number of commands that can be enqueued.
 */
#define COMMAND_QUEUE_SIZE                  25

/**
 * @brief Max number of received publishes that can be enqueued for a task.
 */
#define PUBLISH_QUEUE_SIZE                  20

/**
 * @brief Delay for the subscriber task when no publishes are waiting in the queue.
 */
#define SUBSCRIBE_TASK_DELAY_MS             400U

/**
 * @brief Delay for the publisher task between synchronous publishes.
 */
#define PUBLISH_DELAY_SYNC_MS               500U

/**
 * @brief Delay for the publisher task between asynchronous publishes.
 */
#define PUBLISH_DELAY_ASYNC_MS              50U

/**
 * @brief Notification bit indicating completion of publisher task.
 */
#define PUBLISHER_TASK_COMPLETE_BIT         ( 1U << 1 )

/**
 * @brief Notification bit indicating completion of subscriber task.
 */
#define SUBSCRIBE_TASK_COMPLETE_BIT         ( 1U << 2 )

/**
 * @brief Notification bit used by subscriber task for subscribe operation.
 */
#define SUBSCRIBE_COMPLETE_BIT              ( 1U << 0 )

/**
 * @brief Notification bit used by subscriber task for unsubscribe operation.
 */
#define UNSUBSCRIBE_COMPLETE_BIT            ( 1U << 1 )

/**
 * @brief Maximum number of loop iterations to wait for a task notification.
 */
#define MAX_WAIT_ITERATIONS                 5

/**
 * @brief Topic filter used by the subscriber task.
 */
#define SUBSCRIBE_TOPIC_FILTER              "publish/+/filter"

/**
 * @brief Format string used by the publisher task for topic names.
 */
#define PUBLISH_TOPIC_FORMAT_STRING         "publish/%i/filter"

/**
 * @brief Format string used by the publisher task for payloads.
 */
#define PUBLISH_PAYLOAD_FORMAT              "Hello World! %d"

/*-----------------------------------------------------------*/

/**
 * @brief A type of command for interacting with the MQTT API.
 */
typedef enum CommandType
{
    PROCESSLOOP, /**< @brief Call MQTT_ProcessLoop(). */
    PUBLISH,     /**< @brief Call MQTT_Publish(). */
    SUBSCRIBE,   /**< @brief Call MQTT_Subscribe(). */
    UNSUBSCRIBE, /**< @brief Call MQTT_Unsubscribe(). */
    PING,        /**< @brief Call MQTT_Pint(). */
    DISCONNECT,  /**< @brief Call MQTT_Disconnect(). */
    CONNECT,     /**< @brief Placeholder command for reconnecting a broken connection. */
    TERMINATE    /**< @brief Exit the command loop and stop processing commands. */
} CommandType_t;

/**
 * @brief Struct containing context for a specific command.
 *
 * @note An instance of this struct and any variables it points to MUST stay
 * in scope until the associated command is processed, and its callback called.
 * The command callback will set the `complete` flag, and notify the calling task.
 */
typedef struct CommandContext
{
    MQTTPublishInfo_t * pPublishInfo;
    MQTTSubscribeInfo_t * pSubscribeInfo;
    size_t subscriptionCount;
    MQTTStatus_t returnStatus;
    bool complete;

    /* The below fields are specific to this FreeRTOS implementation. */
    TaskHandle_t taskToNotify;
    uint32_t notificationBit;
    QueueHandle_t pResponseQueue;
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
    CommandType_t commandType;
    CommandContext_t * pContext;
    CommandCallback_t callback;
} Command_t;

/**
 * @brief Information for a pending MQTT ack packet expected by the demo.
 */
typedef struct ackInfo
{
    uint16_t packetId;
    CommandContext_t * pCommandContext;
    CommandCallback_t callback;
} AckInfo_t;

/**
 * @brief An element in the list of subscriptions maintained in the demo.
 *
 * @note This demo allows multiple tasks to subscribe to the same topic.
 */
typedef struct subscriptionElement
{
    char pTopicFilter[ DEMO_BUFFER_SIZE ];
    uint16_t topicFilterLength;
    QueueHandle_t pResponseQueue;
} SubscriptionElement_t;

/**
 * @brief An element for a task's response queue for received publishes.
 *
 * @note Since elements are copied to queues, this struct needs to hold
 * buffers for the payload and topic of incoming publishes, as the original
 * pointers are out of scope. When processing a publish from this struct,
 * the `pTopicName` and `pPayload` pointers need to be set to point to the
 * static buffers in this struct.
 */
typedef struct publishElement
{
    MQTTPublishInfo_t publishInfo;
    uint8_t pPayload[ DEMO_BUFFER_SIZE ];
    uint8_t pTopicName[ DEMO_BUFFER_SIZE ];
} PublishElement_t;

/*-----------------------------------------------------------*/

/**
 * @brief Sends an MQTT Connect packet over the already connected TCP socket.
 *
 * @param[in] pxMQTTContext MQTT context pointer.
 * @param[in] xNetworkContext network context.
 */
static void prvCreateMQTTConnectionWithBroker( MQTTContext_t * pxMQTTContext,
                                               NetworkContext_t * pxNetworkContext );

/**
 * @brief Initialize context for a command.
 *
 * @param[in] pxContext Context to initialize.
 */
static void prvInitializeCommandContext( CommandContext_t * pxContext );

/**
 * @brief Add an operation to the list of pending acks.
 *
 * @param[in] usPacketId Packet ID of pending ack.
 * @param[in] pxContext Command context of operation.
 * @param[in] xCallback Callback from command.
 */
static void prvAddAck( uint16_t usPacketId,
                       CommandContext_t * pxContext,
                       CommandCallback_t xCallback );

/**
 * @brief Remove an operation from the list of pending acks and return it.
 *
 * @param[in] usPacketId Packet ID of incoming ack.
 *
 * @return Stored information about the operation awaiting the ack.
 */
static AckInfo_t prvRemoveAck( uint16_t usPacketId );

/**
 * @brief Add a subscription to the subscription list.
 *
 * @note This demo does not check existing subscriptions before adding a new
 * one. Therefore, multiple tasks can be subscribed to the same topic.
 *
 * @param[in] pTopicFilter Topic filter of subscription.
 * @param[in] topicFilterLength Length of topic filter.
 * @param[in] pxQueue Response queue in which to enqueue received publishes.
 */
static void prvAddSubscription( const char * pTopicFilter,
                                uint16_t topicFilterLength,
                                QueueHandle_t pxQueue );

/**
 * @brief Remove a subscription from the subscription list.
 *
 * @note If the topic filter exists multiple times in the subscription list,
 * then every instance of the subscription will be removed.
 *
 * @param[in] pTopicFilter Topic filter of subscription.
 * @param[in] topicFilterLength Length of topic filter.
 */
static void prvRemoveSubscription( const char * pTopicFilter,
                                   size_t topicFilterLength );

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
static bool prvCreateCommand( CommandType_t xCommandType,
                              CommandContext_t * pxContext,
                              CommandCallback_t xCallback,
                              Command_t * pxCommand );

/**
 * @brief Add a command to the global command queue.
 *
 * @param[in] pxCommand Pointer to command to copy to queue.
 */
static void prvAddCommandToQueue( Command_t * pxCommand );

/**
 * @brief Copy an incoming publish to a response queue.
 *
 * @param[in] pPublishInfo Info of incoming publish.
 * @param[in] pResponseQueue Queue to which the publish is copied.
 */
static void prvCopyPublishToQueue( MQTTPublishInfo_t * pPublishInfo,
                                   QueueHandle_t pResponseQueue );

/**
 * @brief Process a #Command_t.
 *
 * @note This demo does not check existing subscriptions before sending a
 * SUBSCRIBE or UNSUBSCRIBE packet. If a subscription already exists, then
 * a SUBSCRIBE packet will be sent anyway, and if multiple tasks are subscribed
 * to a topic filter, then they will all be unsubscribed after an UNSUBSCRIBE.
 * TODO: check for existing subscriptions before subscribing.
 *
 * @param[in] pxCommand Pointer to command to process.
 *
 * @return status of MQTT library API call.
 */
static MQTTStatus_t prvProcessCommand( Command_t * pxCommand );

/**
 * @brief Dispatch incoming publishes and acks to response queues and
 * command callbacks.
 *
 * @param[in] pMqttContext MQTT Context
 * @param[in] pPacketInfo Pointer to incoming packet.
 * @param[in] pDeserializedInfo Pointer to deserialized information from
 * the incoming packet.
 */
static void prvSubscriptionManager( MQTTContext_t * pMqttContext,
                                    MQTTPacketInfo_t * pPacketInfo,
                                    MQTTDeserializedInfo_t * pDeserializedInfo );

/**
 * @brief Process commands from the command queue in a loop.
 *
 * This demo requires a process loop command to be enqueued before calling this
 * function, and will re-add a process loop command every time one is processed.
 * This demo will exit the loop after receiving an unsubscribe operation.
 */
static void prvCommandLoop();

/**
 * @brief Common callback for commands in this demo.
 *
 * This callback marks the command as complete and notifies the calling task.
 *
 * @param[in] pxContext Context of the initial command.
 */
static void prvCommandCallback( CommandContext_t * pxContext );

/**
 * @brief The task used to create various publish operations.
 *
 * @param[in] pvParameters Parameters as passed at the time of task creation. Not
 * used in this example.
 */
void prvPublishTask( void * pvParameters );

/**
 * @brief The task used to wait for incoming publishes.
 *
 * @param[in] pvParameters Parameters as passed at the time of task creation. Not
 * used in this example.
 */
void prvSubscribeTask( void * pvParameters );

/**
 * @brief The main task used in the MQTT demo.
 *
 * @param[in] pvParameters Parameters as passed at the time of task creation. Not
 * used in this example.
 */
static void prvMQTTDemoTask( void * pvParameters );

/**
 * @brief The timer query function provided to the MQTT context.
 *
 * @return Time in milliseconds.
 */
static uint32_t prvGetTimeMs( void );

/*-----------------------------------------------------------*/

/**
 * @brief Global MQTT context.
 */
static MQTTContext_t globalMqttContext;

/**
 * @brief List of operations that are awaiting an ack from the broker.
 */
static AckInfo_t pxPendingAcks[ PENDING_ACKS_MAX_SIZE ];

/**
 * @brief List of active subscriptions.
 */
static SubscriptionElement_t pxSubscriptions[ SUBSCRIPTIONS_MAX_COUNT ];

/**
 * @brief Queue for main task to handle MQTT operations.
 */
static QueueHandle_t xCommandQueue;

/**
 * @brief Response queue for prvPublishTask.
 */
static QueueHandle_t xPublisherResponseQueue;

/**
 * @brief Response queue for prvSubscribeTask.
 */
static QueueHandle_t xSubscriberResponseQueue;

/**
 * @brief Response queue for publishes received on non-subscribed topics.
 */
static QueueHandle_t xDefaultResponseQueue;

/**
 * @brief Handle for prvMQTTDemoTask.
 */
static TaskHandle_t xMainTask;

/**
 * @brief Handle for prvPublishTask.
 */
static TaskHandle_t xPublisherTask;

/**
 * @brief Handle for prvSubscribeTask.
 */
static TaskHandle_t xSubscribeTask;

/**
 * @brief The network buffer must remain valid for the lifetime of the MQTT context.
 */
static uint8_t buffer[ NETWORK_BUFFER_SIZE ];

/**
 * @brief Global entry time into the application to use as a reference timestamp
 * in the #prvGetTimeMs function. #prvGetTimeMs will always return the difference
 * between the current time and the global entry time. This will reduce the chances
 * of overflow for the 32 bit unsigned integer used for holding the timestamp.
 */
static uint32_t ulGlobalEntryTimeMs;

/*-----------------------------------------------------------*/

/*
 * @brief Create the task that demonstrates the MQTT Connection sharing demo.
 */
void vStartSimpleMQTTDemo( void )
{
    /* This example uses a single application task, which in turn is used to
     * connect, subscribe, publish, unsubscribe and disconnect from the MQTT
     * broker. */
    xTaskCreate( prvMQTTDemoTask,          /* Function that implements the task. */
                 "MQTTDemo",               /* Text name for the task - only used for debugging. */
                 democonfigDEMO_STACKSIZE, /* Size of stack (in words, not bytes) to allocate for the task. */
                 NULL,                     /* Task parameter - not used in this case. */
                 tskIDLE_PRIORITY,         /* Task priority, must be between 0 and configMAX_PRIORITIES - 1. */
                 &xMainTask );             /* Used to pass out a handle to the created task. */
}
/*-----------------------------------------------------------*/

static void prvCreateMQTTConnectionWithBroker( MQTTContext_t * pxMQTTContext,
                                               NetworkContext_t * pxNetworkContext )
{
    MQTTStatus_t xResult;
    MQTTConnectInfo_t xConnectInfo;
    bool xSessionPresent;
    TransportInterface_t xTransport;
    MQTTFixedBuffer_t xNetworkBuffer;

    /* Fill the values for network buffer. */
    xNetworkBuffer.pBuffer = buffer;
    xNetworkBuffer.size = NETWORK_BUFFER_SIZE;

    /***
     * For readability, error handling in this function is restricted to the use of
     * configASSERT().
     ***/

    /* Fill in Transport Interface send and receive function pointers. */
    xTransport.pNetworkContext = pxNetworkContext;
    xTransport.send = Plaintext_FreeRTOS_send;
    xTransport.recv = Plaintext_FreeRTOS_recv;

    /* Initialize MQTT library. */
    xResult = MQTT_Init( pxMQTTContext, &xTransport, prvGetTimeMs, prvSubscriptionManager, &xNetworkBuffer );
    configASSERT( xResult == MQTTSuccess );

    /* Many fields are not used in this demo so start with everything at 0. */
    memset( ( void * ) &xConnectInfo, 0x00, sizeof( xConnectInfo ) );

    /* Start with a clean session i.e. direct the MQTT broker to discard any
     * previous session data. Also, establishing a connection with clean session
     * will ensure that the broker does not store any data when this client
     * gets disconnected. */
    xConnectInfo.cleanSession = true;

    /* The client identifier is used to uniquely identify this MQTT client to
     * the MQTT broker. In a production device the identifier can be something
     * unique, such as a device serial number. */
    xConnectInfo.pClientIdentifier = CLIENT_IDENTIFIER;
    xConnectInfo.clientIdentifierLength = ( uint16_t ) strlen( CLIENT_IDENTIFIER );

    /* Set MQTT keep-alive period. It is the responsibility of the application to ensure
     * that the interval between Control Packets being sent does not exceed the Keep Alive value.
     * In the absence of sending any other Control Packets, the Client MUST send a PINGREQ Packet. */
    xConnectInfo.keepAliveSeconds = MQTT_KEEP_ALIVE_INTERVAL_SECONDS;

    /* Send MQTT CONNECT packet to broker. LWT is not used in this demo, so it
     * is passed as NULL. */
    xResult = MQTT_Connect( pxMQTTContext,
                            &xConnectInfo,
                            NULL,
                            CONNACK_RECV_TIMEOUT_MS,
                            &xSessionPresent );

    configASSERT( xResult == MQTTSuccess );
}

/*-----------------------------------------------------------*/

static void prvInitializeCommandContext( CommandContext_t * pxContext )
{
    pxContext->complete = false;
    pxContext->pResponseQueue = NULL;
    pxContext->returnStatus = MQTTSuccess;
    pxContext->pPublishInfo = NULL;
    pxContext->pSubscribeInfo = NULL;
}

/*-----------------------------------------------------------*/

static void prvDestroyCommandContext( CommandContext_t * pxContext )
{
    ( void ) pxContext;
}

/*-----------------------------------------------------------*/

static void prvAddAck( uint16_t usPacketId,
                       CommandContext_t * pxContext,
                       CommandCallback_t xCallback )
{
    int32_t i = 0;

    for( i = 0; i < PENDING_ACKS_MAX_SIZE; i++ )
    {
        if( pxPendingAcks[ i ].packetId == MQTT_PACKET_ID_INVALID )
        {
            pxPendingAcks[ i ].packetId = usPacketId;
            pxPendingAcks[ i ].pCommandContext = pxContext;
            pxPendingAcks[ i ].callback = xCallback;
            break;
        }
    }
}

/*-----------------------------------------------------------*/

static AckInfo_t prvRemoveAck( uint16_t usPacketId )
{
    int32_t i = 0;
    AckInfo_t xFoundAck = { 0 };

    for( i = 0; i < PENDING_ACKS_MAX_SIZE; i++ )
    {
        if( pxPendingAcks[ i ].packetId == usPacketId )
        {
            xFoundAck = pxPendingAcks[ i ];
            pxPendingAcks[ i ].packetId = MQTT_PACKET_ID_INVALID;
            pxPendingAcks[ i ].pCommandContext = NULL;
            pxPendingAcks[ i ].callback = NULL;
            break;
        }
    }

    if( xFoundAck.packetId == MQTT_PACKET_ID_INVALID )
    {
        LogError( ( "No ack found for packet id %u.", usPacketId ) );
    }

    return xFoundAck;
}

/*-----------------------------------------------------------*/

static void prvAddSubscription( const char * pTopicFilter,
                                uint16_t topicFilterLength,
                                QueueHandle_t pxQueue )
{
    int32_t i = 0;

    for( i = 0; i < SUBSCRIPTIONS_MAX_COUNT; i++ )
    {
        if( pxSubscriptions[ i ].topicFilterLength == 0 )
        {
            pxSubscriptions[ i ].topicFilterLength = topicFilterLength;
            pxSubscriptions[ i ].pResponseQueue = pxQueue;
            memcpy( pxSubscriptions[ i ].pTopicFilter, pTopicFilter, topicFilterLength );
            break;
        }
    }
}

/*-----------------------------------------------------------*/

static void prvRemoveSubscription( const char * pTopicFilter,
                                   size_t topicFilterLength )
{
    int32_t i = 0;

    for( i = 0; i < SUBSCRIPTIONS_MAX_COUNT; i++ )
    {
        if( pxSubscriptions[ i ].topicFilterLength == topicFilterLength )
        {
            if( strncmp( pxSubscriptions[ i ].pTopicFilter, pTopicFilter, topicFilterLength ) == 0 )
            {
                pxSubscriptions[ i ].topicFilterLength = 0;
                pxSubscriptions[ i ].pResponseQueue = NULL;
                memset( ( void * ) pxSubscriptions[ i ].pTopicFilter, 0x00, sizeof( pxSubscriptions[ i ].pTopicFilter ) );
            }
        }
    }
}

/*-----------------------------------------------------------*/

static bool prvCreateCommand( CommandType_t xCommandType,
                              CommandContext_t * pxContext,
                              CommandCallback_t xCallback,
                              Command_t * pxCommand )
{
    bool xIsValid = true;

    /* Determine if required parameters are present in context. */
    switch( xCommandType )
    {
        case PUBLISH:
            xIsValid = ( pxContext != NULL ) ? ( pxContext->pPublishInfo != NULL ) : false;
            break;

        case SUBSCRIBE:
        case UNSUBSCRIBE:
            xIsValid = ( pxContext != NULL ) ? ( pxContext->pSubscribeInfo != NULL ) : false;
            break;

        default:
            /* Other operations don't need a context. */
            break;
    }

    if( xIsValid )
    {
        memset( ( void * ) pxCommand, 0x00, sizeof( Command_t ) );
        pxCommand->commandType = xCommandType;
        pxCommand->pContext = pxContext;
        pxCommand->callback = xCallback;
    }

    return xIsValid;
}

/*-----------------------------------------------------------*/

static void prvAddCommandToQueue( Command_t * pxCommand )
{
    xQueueSendToBack( xCommandQueue, pxCommand, DEMO_TICKS_TO_WAIT );
}

/*-----------------------------------------------------------*/

static void prvCopyPublishToQueue( MQTTPublishInfo_t * pPublishInfo,
                                   QueueHandle_t pResponseQueue )
{
    PublishElement_t xCopiedPublish;

    memset( ( void * ) &xCopiedPublish, 0x00, sizeof( xCopiedPublish ) );
    memcpy( &( xCopiedPublish.publishInfo ), pPublishInfo, sizeof( MQTTPublishInfo_t ) );

    /* Since adding an MQTTPublishInfo_t to a queue will not copy its string buffers,
     * we need to add buffers to a struct and copy the entire structure. We don't
     * need to set xCopiedPublish.publishInfo's pointers yet since the actual address
     * will change after the struct is copied into the queue. */
    memcpy( xCopiedPublish.pTopicName, pPublishInfo->pTopicName, pPublishInfo->topicNameLength );
    memcpy( xCopiedPublish.pPayload, pPublishInfo->pPayload, pPublishInfo->payloadLength );

    /* Add to response queue. */
    xQueueSendToBack( pResponseQueue, ( void * ) &xCopiedPublish, DEMO_TICKS_TO_WAIT );
}

/*-----------------------------------------------------------*/

static MQTTStatus_t prvProcessCommand( Command_t * pxCommand )
{
    MQTTStatus_t xStatus = MQTTSuccess;
    uint16_t usPacketId = MQTT_PACKET_ID_INVALID;
    bool xAddAckToList = false;
    MQTTPublishInfo_t * pxPublishInfo;
    MQTTSubscribeInfo_t * pxSubscribeInfo;

    switch( pxCommand->commandType )
    {
        case PROCESSLOOP:
            LogInfo( ( "Running Process Loop." ) );
            xStatus = MQTT_ProcessLoop( &globalMqttContext, MQTT_PROCESS_LOOP_TIMEOUT_MS );
            break;

        case PUBLISH:
            configASSERT( pxCommand->pContext != NULL );
            pxPublishInfo = pxCommand->pContext->pPublishInfo;
            configASSERT( pxPublishInfo != NULL );

            if( pxPublishInfo->qos != MQTTQoS0 )
            {
                usPacketId = MQTT_GetPacketId( &globalMqttContext );
            }

            LogInfo( ( "Publishing message to %.*s.", ( int ) pxPublishInfo->topicNameLength, pxPublishInfo->pTopicName ) );
            xStatus = MQTT_Publish( &globalMqttContext, pxPublishInfo, usPacketId );
            pxCommand->pContext->returnStatus = xStatus;

            /* Add to pending ack list, or call callback if QoS 0. */
            xAddAckToList = ( pxPublishInfo->qos != MQTTQoS0 ) && ( xStatus == MQTTSuccess );
            break;

        case SUBSCRIBE:
        case UNSUBSCRIBE:
            configASSERT( pxCommand->pContext != NULL );
            pxSubscribeInfo = pxCommand->pContext->pSubscribeInfo;
            configASSERT( pxSubscribeInfo != NULL );
            configASSERT( pxSubscribeInfo->pTopicFilter != NULL );
            usPacketId = MQTT_GetPacketId( &globalMqttContext );

            /* TODO: search for existing subscriptions before removing. */
            if( pxCommand->commandType == SUBSCRIBE )
            {
                LogInfo( ( "Sending SUBSCRIBE packet for %.*s",
                           pxSubscribeInfo->topicFilterLength,
                           pxSubscribeInfo->pTopicFilter ) );
                xStatus = MQTT_Subscribe( &globalMqttContext,
                                          pxSubscribeInfo,
                                          pxCommand->pContext->subscriptionCount,
                                          usPacketId );
            }
            else
            {
                LogInfo( ( "Sending UNSUBSCRIBE packet for %.*s",
                           pxSubscribeInfo->topicFilterLength,
                           pxSubscribeInfo->pTopicFilter ) );
                xStatus = MQTT_Unsubscribe( &globalMqttContext,
                                            pxSubscribeInfo,
                                            pxCommand->pContext->subscriptionCount,
                                            usPacketId );
            }

            pxCommand->pContext->returnStatus = xStatus;
            xAddAckToList = ( xStatus == MQTTSuccess );
            break;

        case PING:
            xStatus = MQTT_Ping( &globalMqttContext );

            if( pxCommand->pContext != NULL )
            {
                pxCommand->pContext->returnStatus = xStatus;
            }

            break;

        case DISCONNECT:
            xStatus = MQTT_Disconnect( &globalMqttContext );

            if( pxCommand->pContext != NULL )
            {
                pxCommand->pContext->returnStatus = xStatus;
            }

            break;

        case CONNECT:
            /* TODO: Reconnect. */
            LogInfo( ( "Processed Connect Command" ) );
            break;

        case TERMINATE:
            LogInfo( ( "Terminating command loop." ) );

        default:
            break;
    }

    if( xAddAckToList )
    {
        prvAddAck( usPacketId, pxCommand->pContext, pxCommand->callback );
    }
    else
    {
        /* The command is complete, call the callback. */
        if( pxCommand->callback != NULL )
        {
            pxCommand->callback( pxCommand->pContext );
        }
    }

    return xStatus;
}

/*-----------------------------------------------------------*/

static void prvSubscriptionManager( MQTTContext_t * pMqttContext,
                                    MQTTPacketInfo_t * pPacketInfo,
                                    MQTTDeserializedInfo_t * pDeserializedInfo )
{
    configASSERT( pMqttContext != NULL );
    configASSERT( pPacketInfo != NULL );
    AckInfo_t xAckInfo;
    MQTTStatus_t xStatus = MQTTSuccess;
    bool xIsMatched = false, xRelayedPublish = false;
    size_t i;
    MQTTSubscribeInfo_t * pxSubscribeInfo = NULL;
    MQTTPublishInfo_t * pPublishInfo = pDeserializedInfo->pPublishInfo;
    uint16_t packetIdentifier = pDeserializedInfo->packetIdentifier;

    /* Handle incoming publish. The lower 4 bits of the publish packet
     * type is used for the dup, QoS, and retain flags. Hence masking
     * out the lower bits to check if the packet is publish. */
    if( ( pPacketInfo->type & 0xF0U ) == MQTT_PACKET_TYPE_PUBLISH )
    {
        configASSERT( pPublishInfo != NULL );

        for( i = 0; i < SUBSCRIPTIONS_MAX_COUNT; i++ )
        {
            if( pxSubscriptions[ i ].topicFilterLength > 0 )
            {
                xStatus = MQTT_MatchTopic( pPublishInfo->pTopicName,
                                           pPublishInfo->topicNameLength,
                                           pxSubscriptions[ i ].pTopicFilter,
                                           pxSubscriptions[ i ].topicFilterLength,
                                           &xIsMatched );
                /* The call can't fail if the topic name and filter is valid. */
                configASSERT( xStatus == MQTTSuccess );

                if( xIsMatched )
                {
                    LogInfo( ( "Adding publish to response queue for %.*s",
                               pxSubscriptions[ i ].topicFilterLength,
                               pxSubscriptions[ i ].pTopicFilter ) );
                    prvCopyPublishToQueue( pPublishInfo, pxSubscriptions[ i ].pResponseQueue );
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
            LogWarn( ( "Publish received on topic %.*s with no subscription.",
                       pPublishInfo->topicNameLength,
                       pPublishInfo->pTopicName ) );
            prvCopyPublishToQueue( pPublishInfo, xDefaultResponseQueue );
        }
    }
    else
    {
        /* Handle other packets. */
        switch( pPacketInfo->type )
        {
            case MQTT_PACKET_TYPE_PUBACK:
            case MQTT_PACKET_TYPE_PUBCOMP:
                xAckInfo = prvRemoveAck( packetIdentifier );

                if( xAckInfo.packetId == packetIdentifier )
                {
                    xAckInfo.pCommandContext->returnStatus = pDeserializedInfo->deserializationResult;

                    if( xAckInfo.callback != NULL )
                    {
                        xAckInfo.callback( xAckInfo.pCommandContext );
                    }
                }

                break;

            case MQTT_PACKET_TYPE_SUBACK:
                xAckInfo = prvRemoveAck( packetIdentifier );

                if( xAckInfo.packetId == packetIdentifier )
                {
                    pxSubscribeInfo = xAckInfo.pCommandContext->pSubscribeInfo;

                    for( i = 0; i < xAckInfo.pCommandContext->subscriptionCount; i++ )
                    {
                        LogInfo( ( "Adding subscription to %.*s",
                                   pxSubscribeInfo[ i ].topicFilterLength,
                                   pxSubscribeInfo[ i ].pTopicFilter ) );
                        LogInfo( ( "Filter length: %u", pxSubscribeInfo[ i ].topicFilterLength ) );
                        prvAddSubscription( pxSubscribeInfo[ i ].pTopicFilter,
                                            pxSubscribeInfo[ i ].topicFilterLength,
                                            xAckInfo.pCommandContext->pResponseQueue );
                    }

                    xAckInfo.pCommandContext->returnStatus = pDeserializedInfo->deserializationResult;

                    if( xAckInfo.callback != NULL )
                    {
                        xAckInfo.callback( xAckInfo.pCommandContext );
                    }
                }
                else
                {
                    LogError( ( "No subscription operation found matching packet id %u.", packetIdentifier ) );
                }

                break;

            case MQTT_PACKET_TYPE_UNSUBACK:
                xAckInfo = prvRemoveAck( packetIdentifier );

                if( xAckInfo.packetId == packetIdentifier )
                {
                    pxSubscribeInfo = xAckInfo.pCommandContext->pSubscribeInfo;

                    for( i = 0; i < xAckInfo.pCommandContext->subscriptionCount; i++ )
                    {
                        LogInfo( ( "Removing subscription to %.*s",
                                   pxSubscribeInfo[ i ].topicFilterLength,
                                   pxSubscribeInfo[ i ].pTopicFilter ) );
                        prvRemoveSubscription( pxSubscribeInfo[ i ].pTopicFilter,
                                               pxSubscribeInfo[ i ].topicFilterLength );
                    }

                    xAckInfo.pCommandContext->returnStatus = pDeserializedInfo->deserializationResult;

                    if( xAckInfo.callback != NULL )
                    {
                        xAckInfo.callback( xAckInfo.pCommandContext );
                    }
                }
                else
                {
                    LogError( ( "No unsubscribe operation found matching packet id %u.", packetIdentifier ) );
                }

                break;

            /* Nothing to do for these packets since they don't indicate command completion. */
            case MQTT_PACKET_TYPE_PUBREC:
            case MQTT_PACKET_TYPE_PUBREL:
                break;

            case MQTT_PACKET_TYPE_PINGRESP:

                /* Nothing to be done from application as library handles
                 * PINGRESP. */
                LogWarn( ( "PINGRESP should not be handled by the application "
                           "callback when using MQTT_ProcessLoop.\n\n" ) );
                break;

            /* Any other packet type is invalid. */
            default:
                LogError( ( "Unknown packet type received:(%02x).\n\n",
                            pPacketInfo->type ) );
        }
    }
}

/*-----------------------------------------------------------*/

static void prvCommandLoop()
{
    Command_t xCommand;
    Command_t xNewCommand;
    Command_t * pxCommand;
    MQTTStatus_t xStatus = MQTTSuccess;
    static int lNumProcessed = 0;
    bool xSubscribeProcessed = false;

    while( xQueueReceive( xCommandQueue, &xCommand, DEMO_TICKS_TO_WAIT ) )
    {
        pxCommand = &xCommand;

        /* This demo requires the subscription to be present before the first publish. */
        if( pxCommand->commandType == PUBLISH )
        {
            if( !xSubscribeProcessed )
            {
                LogInfo( ( "Publish in queue before subscribe. Sending to back of queue." ) );
                prvAddCommandToQueue( pxCommand );
                continue;
            }
        }

        xStatus = prvProcessCommand( pxCommand );

        /* TODO: After reconnect implemented, add connect operation to front
         * of queue if status was not successful. */
        configASSERT( xStatus == MQTTSuccess );
        lNumProcessed++;

        if( pxCommand->commandType == PROCESSLOOP )
        {
            /* Add process loop back to end of queue. */
            prvCreateCommand( PROCESSLOOP, NULL, NULL, &xNewCommand );
            prvAddCommandToQueue( &xNewCommand );
            lNumProcessed--;
        }

        /* Mark subscribed as being processed. */
        if( pxCommand->commandType == SUBSCRIBE )
        {
            xSubscribeProcessed = true;
        }

        if( pxCommand->commandType == TERMINATE )
        {
            break;
        }

        LogInfo( ( "Processed %d non-Process Loop operations.", lNumProcessed ) );
    }

    LogInfo( ( "Creating Disconnect operation." ) );
    prvCreateCommand( DISCONNECT, NULL, NULL, &xNewCommand );
    prvProcessCommand( &xNewCommand );
    LogInfo( ( "Disconnected from broker." ) );
}

static void prvCommandCallback( CommandContext_t * pxContext )
{
    pxContext->complete = true;
    xTaskNotify( pxContext->taskToNotify, pxContext->notificationBit, eSetBits );
}

/*-----------------------------------------------------------*/

void prvPublishTask( void * pvParameters )
{
    ( void ) pvParameters;
    Command_t xCommand;
    MQTTPublishInfo_t xPublishInfo = { 0 };
    MQTTPublishInfo_t pxPublishes[ PUBLISH_COUNT ];
    char payloadBuf[ DEMO_BUFFER_SIZE ];
    char topicBuf[ DEMO_BUFFER_SIZE ];
    CommandContext_t xContext;
    uint32_t ulNotification = 0U;
    /* The following arrays are used to hold pointers to dynamically allocated memory. */
    char * payloadBuffers[ PUBLISH_COUNT ];
    char * topicBuffers[ PUBLISH_COUNT ];
    CommandContext_t * pxContexts[ PUBLISH_COUNT ] = { 0 };

    /* We use QoS 1 so that the operation won't be counted as complete until we
     * receive the publish acknowledgment. */
    xPublishInfo.qos = MQTTQoS1;
    xPublishInfo.pTopicName = topicBuf;
    xPublishInfo.pPayload = payloadBuf;

    /* Do synchronous publishes for first half. */
    for( int i = 0; i < PUBLISH_COUNT / 2; i++ )
    {
        snprintf( payloadBuf, DEMO_BUFFER_SIZE, PUBLISH_PAYLOAD_FORMAT, i + 1 );
        xPublishInfo.payloadLength = ( uint16_t ) strlen( payloadBuf );
        snprintf( topicBuf, DEMO_BUFFER_SIZE, PUBLISH_TOPIC_FORMAT_STRING, i + 1 );
        xPublishInfo.topicNameLength = ( uint16_t ) strlen( topicBuf );

        prvInitializeCommandContext( &xContext );
        xContext.pResponseQueue = xPublisherResponseQueue;
        xContext.taskToNotify = xTaskGetCurrentTaskHandle();
        xContext.notificationBit = 1 << i;
        xContext.pPublishInfo = &xPublishInfo;
        LogInfo( ( "Adding publish operation for message %s \non topic %.*s\n", payloadBuf, xPublishInfo.topicNameLength, xPublishInfo.pTopicName ) );
        prvCreateCommand( PUBLISH, &xContext, prvCommandCallback, &xCommand );
        prvAddCommandToQueue( &xCommand );

        while( ( ulNotification & ( 1U << i ) ) != ( 1U << i ) )
        {
            LogInfo( ( "Waiting for publish %d to complete.\n", i + 1 ) );
            xTaskNotifyWait( 0, ( 1U << i ), &ulNotification, DEMO_TICKS_TO_WAIT );
        }

        prvDestroyCommandContext( &xContext );
        LogInfo( ( "Publish operation complete.\n" ) );
        LogInfo( ( "Publish operation complete. Sleeping for %d ms.\n", PUBLISH_DELAY_SYNC_MS ) );
        vTaskDelay( pdMS_TO_TICKS( PUBLISH_DELAY_SYNC_MS ) );
    }

    /* Asynchronous publishes for second half. Although not necessary, we use dynamic
     * memory here to avoid declaring many static buffers. */
    for( int i = PUBLISH_COUNT >> 1; i < PUBLISH_COUNT; i++ )
    {
        pxContexts[ i ] = ( CommandContext_t * ) pvPortMalloc( sizeof( CommandContext_t ) );
        prvInitializeCommandContext( pxContexts[ i ] );
        pxContexts[ i ]->pResponseQueue = xPublisherResponseQueue;
        pxContexts[ i ]->taskToNotify = xTaskGetCurrentTaskHandle();

        /* Set the notification bit to be the publish number. This prevents this demo
         * from having more than 32 publishes. If many publishes are desired, semaphores
         * can be used instead of task notifications. */
        pxContexts[ i ]->notificationBit = 1U << i;
        payloadBuffers[ i ] = ( char * ) pvPortMalloc( DYNAMIC_BUFFER_SIZE );
        topicBuffers[ i ] = ( char * ) pvPortMalloc( DYNAMIC_BUFFER_SIZE );
        snprintf( payloadBuffers[ i ], DYNAMIC_BUFFER_SIZE, PUBLISH_PAYLOAD_FORMAT, i + 1 );
        snprintf( topicBuffers[ i ], DYNAMIC_BUFFER_SIZE, PUBLISH_TOPIC_FORMAT_STRING, i + 1 );
        /* Set publish info. */
        memset( ( void * ) &( pxPublishes[ i ] ), 0x00, sizeof( MQTTPublishInfo_t ) );
        pxPublishes[ i ].pPayload = payloadBuffers[ i ];
        pxPublishes[ i ].payloadLength = strlen( payloadBuffers[ i ] );
        pxPublishes[ i ].pTopicName = topicBuffers[ i ];
        pxPublishes[ i ].topicNameLength = ( uint16_t ) strlen( topicBuffers[ i ] );
        pxPublishes[ i ].qos = MQTTQoS1;
        pxContexts[ i ]->pPublishInfo = &( pxPublishes[ i ] );
        LogInfo( ( "Adding publish operation for message %s \non topic %.*s\n",
                   payloadBuffers[ i ],
                   pxPublishes[ i ].topicNameLength,
                   pxPublishes[ i ].pTopicName ) );
        prvCreateCommand( PUBLISH, pxContexts[ i ], prvCommandCallback, &xCommand );
        prvAddCommandToQueue( &xCommand );
        LogInfo( ( "Publish operation queued. Sleeping for %d ms.\n", PUBLISH_DELAY_ASYNC_MS ) );
        vTaskDelay( pdMS_TO_TICKS( PUBLISH_DELAY_ASYNC_MS ) );
    }

    LogInfo( ( "Finished publishing\n" ) );

    for( int i = 0; i < PUBLISH_COUNT; i++ )
    {
        if( pxContexts[ i ] == NULL )
        {
            /* Don't try to free anything that wasn't initialized. */
            continue;
        }

        while( ( ulNotification & ( 1U << i ) ) != ( 1U << i ) )
        {
            LogInfo( ( "Waiting to free publish context %d.", i ) );
            xTaskNotifyWait( 0, ( 1U << i ), &ulNotification, DEMO_TICKS_TO_WAIT );
        }

        prvDestroyCommandContext( pxContexts[ i ] );
        vPortFree( pxContexts[ i ] );
        vPortFree( topicBuffers[ i ] );
        vPortFree( payloadBuffers[ i ] );
        LogInfo( ( "Publish context %d freed.", i ) );
        pxContexts[ i ] = NULL;
    }

    /* Clear this task's notifications. */
    xTaskNotifyStateClear( NULL );

    /* Notify main task this task can be deleted. */
    xTaskNotify( xMainTask, PUBLISHER_TASK_COMPLETE_BIT, eSetBits );
}

/*-----------------------------------------------------------*/

void prvSubscribeTask( void * pvParameters )
{
    ( void ) pvParameters;
    MQTTSubscribeInfo_t xSubscribeInfo;
    Command_t xCommand;
    MQTTPublishInfo_t * pxReceivedPublish = NULL;
    static uint16_t usNumReceived = 0;
    uint32_t ulNotification = 0;
    CommandContext_t xContext;
    PublishElement_t xReceivedPublish;
    uint16_t usWaitCounter = 0;

    /* QoS 0 is simplest, so use that. */
    xSubscribeInfo.qos = MQTTQoS0;
    xSubscribeInfo.pTopicFilter = SUBSCRIBE_TOPIC_FILTER;
    xSubscribeInfo.topicFilterLength = ( uint16_t ) strlen( xSubscribeInfo.pTopicFilter );
    LogInfo( ( "Topic filter: %.*s", xSubscribeInfo.topicFilterLength, xSubscribeInfo.pTopicFilter ) );
    LogInfo( ( "Filter length: %d", xSubscribeInfo.topicFilterLength ) );

    /* Create the context and subscribe command. */
    prvInitializeCommandContext( &xContext );
    xContext.pResponseQueue = xSubscriberResponseQueue;
    xContext.taskToNotify = xTaskGetCurrentTaskHandle();
    xContext.notificationBit = 1;
    xContext.subscriptionCount = 1;
    xContext.pSubscribeInfo = &xSubscribeInfo;
    LogInfo( ( "Adding subscribe operation" ) );
    prvCreateCommand( SUBSCRIBE, &xContext, prvCommandCallback, &xCommand );
    prvAddCommandToQueue( &xCommand );

    while( ( ulNotification & SUBSCRIBE_COMPLETE_BIT ) != SUBSCRIBE_COMPLETE_BIT )
    {
        LogInfo( ( "Waiting for subscribe operation to complete." ) );
        xTaskNotifyWait( 0, SUBSCRIBE_COMPLETE_BIT, &ulNotification, DEMO_TICKS_TO_WAIT );
    }

    prvDestroyCommandContext( &xContext );
    LogInfo( ( "Operation wait complete.\n" ) );

    while( 1 )
    {
        while( xQueueReceive( xSubscriberResponseQueue, &xReceivedPublish, DEMO_TICKS_TO_WAIT ) )
        {
            pxReceivedPublish = &( xReceivedPublish.publishInfo );
            pxReceivedPublish->pTopicName = ( const char * ) xReceivedPublish.pTopicName;
            pxReceivedPublish->pPayload = xReceivedPublish.pPayload;
            LogInfo( ( "Received publish on topic %.*s\n", pxReceivedPublish->topicNameLength, pxReceivedPublish->pTopicName ) );
            LogInfo( ( "Message payload: %.*s\n", ( int ) pxReceivedPublish->payloadLength, ( const char * ) pxReceivedPublish->pPayload ) );
            usNumReceived++;
        }

        /* Break if all publishes have been received. */
        if( usNumReceived >= PUBLISH_COUNT )
        {
            break;
        }

        LogInfo( ( "No messages queued, received %u publishes, sleeping for %d ms\n",
                   usNumReceived,
                   SUBSCRIBE_TASK_DELAY_MS ) );
        vTaskDelay( pdMS_TO_TICKS( SUBSCRIBE_TASK_DELAY_MS ) );
    }

    LogInfo( ( "Finished receiving\n" ) );
    prvCreateCommand( UNSUBSCRIBE, &xContext, prvCommandCallback, &xCommand );
    prvInitializeCommandContext( &xContext );
    xContext.pResponseQueue = xSubscriberResponseQueue;
    xContext.taskToNotify = xTaskGetCurrentTaskHandle();
    xContext.notificationBit = UNSUBSCRIBE_COMPLETE_BIT;
    xContext.pSubscribeInfo = &xSubscribeInfo;
    LogInfo( ( "Adding unsubscribe operation\n" ) );
    prvAddCommandToQueue( &xCommand );
    LogInfo( ( "Starting wait on operation\n" ) );

    while( ( ulNotification & UNSUBSCRIBE_COMPLETE_BIT ) != UNSUBSCRIBE_COMPLETE_BIT )
    {
        LogInfo( ( "Waiting for unsubscribe operation to complete." ) );
        xTaskNotifyWait( 0, UNSUBSCRIBE_COMPLETE_BIT, &ulNotification, DEMO_TICKS_TO_WAIT );

        if( ++usWaitCounter > MAX_WAIT_ITERATIONS )
        {
            break;
        }
    }

    prvDestroyCommandContext( &xContext );
    LogInfo( ( "Operation wait complete.\n" ) );

    /* Create command to stop command loop. */
    LogInfo( ( "Beginning command queue termination." ) );
    prvCreateCommand( TERMINATE, NULL, NULL, &xCommand );
    prvAddCommandToQueue( &xCommand );

    /* Notify main task this task can be deleted. */
    xTaskNotify( xMainTask, SUBSCRIBE_TASK_COMPLETE_BIT, eSetBits );
}

/*-----------------------------------------------------------*/

static void prvMQTTDemoTask( void * pvParameters )
{
    NetworkContext_t xNetworkContext = { 0 };
    PlaintextTransportStatus_t xNetworkStatus;
    BaseType_t xResult;
    uint32_t ulNotification = 0;
    Command_t xCommand;

    ( void ) pvParameters;

    ulGlobalEntryTimeMs = prvGetTimeMs();

    xCommandQueue = xQueueCreate( COMMAND_QUEUE_SIZE, sizeof( Command_t ) );
    xSubscriberResponseQueue = xQueueCreate( PUBLISH_QUEUE_SIZE, sizeof( PublishElement_t ) );
    /* Publish task doesn't receive anything in this demo, so it doesn't need a large queue. */
    xPublisherResponseQueue = xQueueCreate( 1, sizeof( PublishElement_t ) );
    /* In this demo, send publishes on non-subscribed topics to this queue. */
    xDefaultResponseQueue = xPublisherResponseQueue;

    memset( ( void * ) pxPendingAcks, 0x00, PENDING_ACKS_MAX_SIZE * sizeof( AckInfo_t ) );
    memset( ( void * ) pxSubscriptions, 0x00, SUBSCRIPTIONS_MAX_COUNT * sizeof( SubscriptionElement_t ) );

    /* Create inital process loop command. */
    prvCreateCommand( PROCESSLOOP, NULL, NULL, &xCommand );
    prvAddCommandToQueue( &xCommand );

    LogInfo( ( "Creating a TCP connection to %s.\r\n", BROKER_ENDPOINT ) );

    /* TODO: Use TLS to connect to the broker. */
    xNetworkStatus = Plaintext_FreeRTOS_Connect( &xNetworkContext,
                                                 BROKER_ENDPOINT,
                                                 BROKER_PORT,
                                                 TRANSPORT_SEND_RECV_TIMEOUT_MS,
                                                 TRANSPORT_SEND_RECV_TIMEOUT_MS );
    configASSERT( xNetworkStatus == PLAINTEXT_TRANSPORT_SUCCESS );
    prvCreateMQTTConnectionWithBroker( &globalMqttContext, &xNetworkContext );
    configASSERT( globalMqttContext.connectStatus = MQTTConnected );

    xResult = xTaskCreate( prvSubscribeTask, "Subscriber", democonfigDEMO_STACKSIZE, NULL, tskIDLE_PRIORITY, &xSubscribeTask );
    xResult = xTaskCreate( prvPublishTask, "Publisher", democonfigDEMO_STACKSIZE, NULL, tskIDLE_PRIORITY, &xPublisherTask );

    LogInfo( ( "Running command loop" ) );
    prvCommandLoop();

    /* Delete created tasks and queues. */
    while( ( ulNotification & SUBSCRIBE_TASK_COMPLETE_BIT ) != SUBSCRIBE_TASK_COMPLETE_BIT )
    {
        LogInfo( ( "Waiting for subscribe task to exit." ) );
        xTaskNotifyWait( 0, SUBSCRIBE_TASK_COMPLETE_BIT, &ulNotification, DEMO_TICKS_TO_WAIT );
    }

    configASSERT( ( ulNotification & SUBSCRIBE_TASK_COMPLETE_BIT ) == SUBSCRIBE_TASK_COMPLETE_BIT );
    vTaskDelete( xSubscribeTask );
    LogInfo( ( "Subscribe task Deleted." ) );

    while( ( ulNotification & PUBLISHER_TASK_COMPLETE_BIT ) != PUBLISHER_TASK_COMPLETE_BIT )
    {
        LogInfo( ( "Waiting for publish task to exit." ) );
        xTaskNotifyWait( 0, PUBLISHER_TASK_COMPLETE_BIT, &ulNotification, DEMO_TICKS_TO_WAIT );
    }

    configASSERT( ( ulNotification & PUBLISHER_TASK_COMPLETE_BIT ) == PUBLISHER_TASK_COMPLETE_BIT );
    vTaskDelete( xPublisherTask );
    LogInfo( ( "Publish task Deleted." ) );

    /* Clean up queues. */
    vQueueDelete( xCommandQueue );
    vQueueDelete( xPublisherResponseQueue );
    vQueueDelete( xSubscriberResponseQueue );

    LogInfo( ( "Disconnecting TCP connection." ) );
    xNetworkStatus = Plaintext_FreeRTOS_Disconnect( &xNetworkContext );
    configASSERT( xNetworkStatus == PLAINTEXT_TRANSPORT_SUCCESS );

    LogInfo( ( "Demo completed successfully.\r\n" ) );
}

/*-----------------------------------------------------------*/

static uint32_t prvGetTimeMs( void )
{
    TickType_t xTickCount = 0;
    uint32_t ulTimeMs = 0UL;

    /* Get the current tick count. */
    xTickCount = xTaskGetTickCount();

    /* Convert the ticks to milliseconds. */
    ulTimeMs = ( uint32_t ) xTickCount * _MILLISECONDS_PER_TICK;

    /* Reduce ulGlobalEntryTimeMs from obtained time so as to always return the
     * elapsed time in the application. */
    ulTimeMs = ( uint32_t ) ( ulTimeMs - ulGlobalEntryTimeMs );

    return ulTimeMs;
}

/*-----------------------------------------------------------*/
