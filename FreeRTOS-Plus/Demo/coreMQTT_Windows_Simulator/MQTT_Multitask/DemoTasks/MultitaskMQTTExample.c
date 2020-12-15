/*
 * FreeRTOS V202012.00
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
 * This demo shows how to use coreMQTT in a multithreaded environment - it does not
 * yet go as far as encapsulating the MQTT library within its own agent (or daemon)
 * task - although the prvCommandLoop() function demonstrates how that might be done.
 * Also see https://www.freertos.org/mqtt/mqtt-agent-demo.html? for an
 * example that does use an agent task.  Executing the MQTT protocol in an agent
 * task removes the need for the application writer to explicitly manage any MQTT
 * state or call the MQTT_ProcessLoop() API function. Using an agent task
 * also enables multiple application tasks to more easily share a single
 * MQTT connection.
 *
 * In this task prvCommandLoop() is only executed from a single thread and is the
 * only function that is allowed to use the coreMQTT API directly.  Anything else
 * needing to interact with the coreMQTT API does so by posting commands to
 * prvCommandLoop() via a queue.  Future coreMQTT releases will build an agent into
 * the library itself, and then encapsulate the queues into the implementation of a
 * thread safe coreMQTT API.
 *
 * To use this demo with TLS set democonfigUSE_TLS to 1.  To use this demo without
 * TLS (so plain text) set democonfigUSE_TLS to 0.  democonfigUSE_TLS is defined
 * in demo_config.h.
 *
 *!!! Plain text connections are only used for ease of demonstration.  Do not send
 *!!! sensitive data on unencrypted connections.  Production devices should used
 *!!! mutually authenticated and encrypted connections.
 *
 * There are four tasks to note in this demo:
 *  - prvMQTTDemoTask() manages multiple iterations of the demo.  Each iteration
 *    creates the other tasks, calls prvCommandLoop() to handle the MQTT traffic,
 *    then cleans up ready for the next iteration.
 *  - prvSyncPublishTask() which demonstrates synchronous publishes. The task creates
 *    a series of publish operations that are sent over the command queue to be
 *    processed by prvCommandLoop(), waiting for each publish to complete before
 *    sending the next.
 *  - prvAsyncPublishTask() which demonstrates asynchronous publishes. Like
 *    prvSyncPublishTask(), the task creates a series of publish operations that are
 *    sent over the command queue to be processed by prvCommandLoop(), but unlike
 *    prvSyncPublishTask() this task does not wait for each publish to be complete
 *    until after all the publish commands are sent.  Note that the distinction
 *    between synchronous and asynchronous publishes is only in the behavior of the
 *    task, not in the actual publish command.
 *  - prvSubscribeTask() which creates an MQTT subscription to a topic filter
 *    matching the topics published on by the two publishing tasks, and in doing so,
 *    ensures the demo received a publish command back for each publish command it
 *    sends. It loops while waiting for publish messages to be received.
 *
 * Tasks can have queues to hold received publish messages, and the command task
 * will push incoming publishes to the queue of each task that is subscribed to
 * the incoming topic.
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
#include "core_mqtt.h"
#include "core_mqtt_state.h"

/* Exponential backoff retry include. */
#include "backoff_algorithm.h"

/* Transport interface include. */
#if defined( democonfigUSE_TLS ) && ( democonfigUSE_TLS == 1 )
    #include "using_mbedtls.h"
#else
    #include "using_plaintext.h"
#endif

/**
 * These configuration settings are required to run the demo.
 */

/**
 * @brief The size to use for the network buffer.
 */
#ifndef mqttexampleNETWORK_BUFFER_SIZE
    #define mqttexampleNETWORK_BUFFER_SIZE    ( 1024U )
#endif

/**
 * @brief The maximum number of retries for network operation with server.
 */
#define mqttexampleRETRY_MAX_ATTEMPTS                ( 5U )

/**
 * @brief The maximum back-off delay (in milliseconds) for retrying failed operation
 *  with server.
 */
#define mqttexampleRETRY_MAX_BACKOFF_DELAY_MS        ( 5000U )

/**
 * @brief The base back-off delay (in milliseconds) to use for network operation retry
 * attempts.
 */
#define mqttexampleRETRY_BACKOFF_BASE_MS             ( 500U )

/**
 * @brief Timeout for receiving CONNACK packet in milliseconds.
 */
#define mqttexampleCONNACK_RECV_TIMEOUT_MS           ( 1000U )

/**
 * @brief Time to wait between each cycle of the demo implemented by prvMQTTDemoTask().
 */
#define mqttexampleDELAY_BETWEEN_DEMO_ITERATIONS     ( pdMS_TO_TICKS( 5000U ) )

/**
 * @brief Timeout for MQTT_ProcessLoop function in milliseconds.
 *
 * This demo uses no delay for the process loop, so each invocation will run
 * one iteration, and will only receive a single packet. However, if there is
 * no data available on the socket, the entire socket timeout value will elapse.
 */
#define mqttexamplePROCESS_LOOP_TIMEOUT_MS           ( 0U )

/**
 * @brief The maximum time interval in seconds which is allowed to elapse
 *  between two Control Packets.
 *
 *  It is the responsibility of the Client to ensure that the interval between
 *  Control Packets being sent does not exceed the this Keep Alive value. In the
 *  absence of sending any other Control Packets, the Client MUST send a
 *  PINGREQ Packet.
 */
#define mqttexampleKEEP_ALIVE_INTERVAL_SECONDS       ( 60U )

/**
 * @brief Transport timeout in milliseconds for transport send and receive.
 */
#define mqttexampleTRANSPORT_SEND_RECV_TIMEOUT_MS    ( 200 )

/**
 * @brief Milliseconds per second.
 */
#define mqttexampleMILLISECONDS_PER_SECOND           ( 1000U )

/**
 * @brief Milliseconds per FreeRTOS tick.
 */
#define mqttexampleMILLISECONDS_PER_TICK             ( mqttexampleMILLISECONDS_PER_SECOND / configTICK_RATE_HZ )

/**
 * @brief Ticks to wait for task notifications.
 */
#define mqttexampleDEMO_TICKS_TO_WAIT                pdMS_TO_TICKS( 1000 )

/**
 * @brief Maximum number of operations awaiting an ack packet from the broker.
 */
#define mqttexamplePENDING_ACKS_MAX_SIZE             20

/**
 * @brief Maximum number of subscriptions to store in the subscription list.
 */
#define mqttexampleSUBSCRIPTIONS_MAX_COUNT           10

/**
 * @brief Number of publishes done by the publisher in this demo.
 */
#define mqttexamplePUBLISH_COUNT                     16

/**
 * @brief Size of statically allocated buffers for holding topic names and payloads in this demo.
 */
#define mqttexampleDEMO_BUFFER_SIZE                  100

/**
 * @brief Size of dynamically allocated buffers for holding topic names and payloads in this demo.
 */
#define mqttexampleDYNAMIC_BUFFER_SIZE               25

/**
 * @brief Max number of commands that can be enqueued.
 */
#define mqttexampleCOMMAND_QUEUE_SIZE                25

/**
 * @brief Max number of received publishes that can be enqueued for a task.
 */
#define mqttexamplePUBLISH_QUEUE_SIZE                20

/**
 * @brief Delay for the subscriber task. If no publishes are waiting in the
 * task's message queue, it will wait this many milliseconds before checking
 * it again.
 */
#define mqttexampleSUBSCRIBE_TASK_DELAY_MS           400U

/**
 * @brief Delay for the synchronous publisher task between publishes.
 */
#define mqttexamplePUBLISH_DELAY_SYNC_MS             100U

/**
 * @brief Delay for the asynchronous publisher task between publishes.
 */
#define mqttexamplePUBLISH_DELAY_ASYNC_MS            100U

/**
 * @brief Notification bit indicating completion of publisher task.
 */
#define mqttexamplePUBLISHER_SYNC_COMPLETE_BIT       ( 1U << 1 )

/**
 * @brief Notification bit indicating completion of second publisher task.
 */
#define mqttexamplePUBLISHER_ASYNC_COMPLETE_BIT      ( 1U << 2 )

/**
 * @brief Notification bit indicating completion of subscriber task.
 */
#define mqttexampleSUBSCRIBE_TASK_COMPLETE_BIT       ( 1U << 3 )

/**
 * @brief Notification bit used by subscriber task for subscribe operation.
 */
#define mqttexampleSUBSCRIBE_COMPLETE_BIT            ( 1U << 0 )

/**
 * @brief Notification bit used by subscriber task for unsubscribe operation.
 */
#define mqttexampleUNSUBSCRIBE_COMPLETE_BIT          ( 1U << 1 )

/**
 * @brief The maximum number of loop iterations to wait before declaring failure.
 *
 * Each `while` loop waiting for a task notification will wait for a total
 * number of ticks equal to `mqttexampleDEMO_TICKS_TO_WAIT` * this number of
 * iterations before the loop exits.
 *
 * @note This value should not be too small, as the reason for a long loop
 * may be a loss of network connection.
 */
#define mqttexampleMAX_WAIT_ITERATIONS               ( 20 )

/**
 * @brief Topic filter used by the subscriber task.
 */
#define mqttexampleSUBSCRIBE_TOPIC_FILTER            "filter/+/+"

/**
 * @brief Format string used by the publisher task for topic names.
 */
#define mqttexamplePUBLISH_TOPIC_FORMAT_STRING       "filter/%s/%i"

/**
 * @brief Format string used by the publisher task for payloads.
 */
#define mqttexamplePUBLISH_PAYLOAD_FORMAT            "Hello World! %s: %d"

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
    PING,        /**< @brief Call MQTT_Ping(). */
    DISCONNECT,  /**< @brief Call MQTT_Disconnect(). */
    RECONNECT,   /**< @brief Reconnect a broken connection. */
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

/*-----------------------------------------------------------*/

/**
 * @brief Each compilation unit that consumes the NetworkContext must define it.
 * It should contain a single pointer to the type of your desired transport.
 * When using multiple transports in the same compilation unit, define this pointer as void *.
 *
 * @note Transport stacks are defined in FreeRTOS-Plus/Source/Application-Protocols/network_transport.
 */
struct NetworkContext
{
    #if defined( democonfigUSE_TLS ) && ( democonfigUSE_TLS == 1 )
        TlsTransportParams_t * pParams;
    #else
        PlaintextTransportParams_t * pParams;
    #endif
};

/*-----------------------------------------------------------*/

/**
 * @brief Initializes an MQTT context, including transport interface and
 * network buffer.
 *
 * @param[in] pxMQTTContext MQTT Context to initialize.
 * @param[in] pxNetworkContext Network context.
 *
 * @return `MQTTSuccess` if the initialization succeeds, else `MQTTBadParameter`.
 */
static MQTTStatus_t prvMQTTInit( MQTTContext_t * pxMQTTContext,
                                 NetworkContext_t * pxNetworkContext );

/**
 * @brief Sends an MQTT Connect packet over the already connected TCP socket.
 *
 * @param[in] pxMQTTContext MQTT context pointer.
 * @param[in] xCleanSession If a clean session should be established.
 *
 * @return `MQTTSuccess` if connection succeeds, else appropriate error code
 * from MQTT_Connect.
 */
static MQTTStatus_t prvMQTTConnect( MQTTContext_t * pxMQTTContext,
                                    bool xCleanSession );

/**
 * @brief Resume a session by resending publishes if a session is present in
 * the broker, or reestablish subscriptions if not.
 *
 * @param[in] xSessionPresent The session present flag from the broker.
 *
 * @return `MQTTSuccess` if it succeeds in resending publishes, else an
 * appropriate error code from `MQTT_Publish()`
 */
static MQTTStatus_t prvResumeSession( bool xSessionPresent );


/**
 * @brief Form a TCP connection to a server.
 *
 * @param[in] pxNetworkContext Network context.
 *
 * @return `pdPASS` if connection succeeds, else `pdFAIL`.
 */
static BaseType_t prvSocketConnect( NetworkContext_t * pxNetworkContext );

/**
 * @brief Disconnect a TCP connection.
 *
 * @param[in] pxNetworkContext Network context.
 *
 * @return `pdPASS` if disconnect succeeds, else `pdFAIL`.
 */
static BaseType_t prvSocketDisconnect( NetworkContext_t * pxNetworkContext );

/**
 * @brief Callback for adding a process loop call to a command queue, when data
 * is available on a socket.
 *
 * @param[in] pxSocket Socket with data, unused.
 */
static void prvMQTTClientSocketWakeupCallback( Socket_t pxSocket );

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
 *
 * @return true if the command was added to the queue, else false.
 */
static BaseType_t prvAddCommandToQueue( Command_t * pxCommand );

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

/**
 * @brief Dispatch incoming publishes and acks to response queues and
 * command callbacks.
 *
 * @param[in] pMqttContext MQTT Context
 * @param[in] pPacketInfo Pointer to incoming packet.
 * @param[in] pDeserializedInfo Pointer to deserialized information from
 * the incoming packet.
 */
static void prvEventCallback( MQTTContext_t * pMqttContext,
                              MQTTPacketInfo_t * pPacketInfo,
                              MQTTDeserializedInfo_t * pDeserializedInfo );

/**
 * @brief Process commands from the command queue in a loop.
 *
 * This demo requires a process loop command to be enqueued before calling this
 * function, and will re-add a process loop command every time one is processed.
 * This demo will exit the loop after receiving an unsubscribe operation.
 */
static void prvCommandLoop( void );

/**
 * @brief Common callback for commands in this demo.
 *
 * This callback marks the command as complete and notifies the calling task.
 *
 * @param[in] pxContext Context of the initial command.
 */
static void prvCommandCallback( CommandContext_t * pxContext );

/**
 * @brief Wait for a task notification in a loop.
 *
 * @param[in] pulNotification pointer holding notification value.
 * @param[in] ulExpectedBits Bits to wait for.
 * @param[in] xClearBits If bits should be cleared.
 *
 * @return `true` if notification received without exceeding the timeout,
 * else `false`.
 */
static bool prvNotificationWaitLoop( uint32_t * pulNotification,
                                     uint32_t ulExpectedBits,
                                     bool xClearBits );

/**
 * @brief A task used to create publish operations, waiting for each to complete
 * before creating the next one.
 *
 * This task creates a series of publish operations to push to a command queue,
 * which are in turn executed serially by the main task. This task demonstrates
 * synchronous execution, waiting for each publish delivery to complete before
 * proceeding.
 *
 * @param[in] pvParameters Parameters as passed at the time of task creation. Not
 * used in this example.
 */
void prvSyncPublishTask( void * pvParameters );

/**
 * @brief A task used to create publish operations, without waiting for
 * completion between each new publish.
 *
 * This task creates publish operations asynchronously, meaning it will not
 * wait for a publish to complete before scheduling the next one. Note there
 * is no difference in the actual publish operation, only in the behavior of
 * this task.
 *
 * @param[in] pvParameters Parameters as passed at the time of task creation. Not
 * used in this example.
 */
void prvAsyncPublishTask( void * pvParameters );

/**
 * @brief The task used to wait for incoming publishes.
 *
 * This task subscribes to a topic filter that matches the topics on which the
 * publisher task publishes. It then enters a loop waiting for publish messages
 * from a message queue, to which the main loop will be pushing when publishes
 * are received from the broker. After `mqttexamplePUBLISH_COUNT` messages have been received,
 * this task will unsubscribe, and then tell the main loop to terminate.
 *
 * @param[in] pvParameters Parameters as passed at the time of task creation. Not
 * used in this example.
 */
void prvSubscribeTask( void * pvParameters );

/**
 * @brief The main task used in the MQTT demo.
 *
 * After creating the publisher and subscriber tasks, this task will enter a
 * loop, processing commands from the command queue and calling the MQTT API.
 * After the termination command is received on the command queue, the task
 * will break from the loop.
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

/**
 * @brief Cleans any persistent sessions that may already exist
 * This demo uses a persistent session that can be re-connected if disconnected.
 * Clean any lingering sessions that may exist from previous executions of the
 * demo.
 */
static void prvCleanExistingPersistentSession( void );

/*-----------------------------------------------------------*/

/**
 * @brief Global MQTT context.
 */
static MQTTContext_t globalMqttContext;

/**
 * @brief Global Network context.
 */
static NetworkContext_t xNetworkContext;

#if defined( democonfigUSE_TLS ) && ( democonfigUSE_TLS == 1 )

/**
 * @brief The parameters for the network context using a TLS channel.
 */
    static TlsTransportParams_t xTlsTransportParams;
#else

/**
 * @brief The parameters for the network context using a non-encrypted channel.
 */
    static PlaintextTransportParams_t xPlaintextTransportParams;
#endif

/**
 * @brief List of operations that are awaiting an ack from the broker.
 */
static AckInfo_t pxPendingAcks[ mqttexamplePENDING_ACKS_MAX_SIZE ];

/**
 * @brief List of active subscriptions.
 */
static SubscriptionElement_t pxSubscriptions[ mqttexampleSUBSCRIPTIONS_MAX_COUNT ];

/**
 * @brief Array of subscriptions to resubscribe to.
 */
static MQTTSubscribeInfo_t pxResendSubscriptions[ mqttexampleSUBSCRIPTIONS_MAX_COUNT ];

/**
 * @brief Context to use for a resubscription after a reconnect.
 */
static CommandContext_t xResubscribeContext;

/**
 * @brief Queue for main task to handle MQTT operations.
 */
static QueueHandle_t xCommandQueue;

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
 * @brief Handle for prvSyncPublishTask.
 */
static TaskHandle_t xSyncPublisherTask;

/**
 * @brief Handle of prvAsyncPublishTask.
 */
static TaskHandle_t xAsyncPublisherTask;

/**
 * @brief Handle for prvSubscribeTask.
 */
static TaskHandle_t xSubscribeTask;

/**
 * @brief The network buffer must remain valid for the lifetime of the MQTT context.
 */
static uint8_t pcNetworkBuffer[ mqttexampleNETWORK_BUFFER_SIZE ];

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
    /* This example uses one application task to process the command queue for
     * MQTT operations, and creates additional tasks to add operations to that
     * queue. */
    xTaskCreate( prvMQTTDemoTask,          /* Function that implements the task. */
                 "DemoTask",               /* Text name for the task - only used for debugging. */
                 democonfigDEMO_STACKSIZE, /* Size of stack (in words, not bytes) to allocate for the task. */
                 NULL,                     /* Task parameter - not used in this case. */
                 tskIDLE_PRIORITY + 1,     /* Task priority, must be between 0 and configMAX_PRIORITIES - 1. */
                 &xMainTask );             /* Used to pass out a handle to the created task. */
}
/*-----------------------------------------------------------*/

static MQTTStatus_t prvMQTTInit( MQTTContext_t * pxMQTTContext,
                                 NetworkContext_t * pxNetworkContext )
{
    TransportInterface_t xTransport;
    MQTTFixedBuffer_t xNetworkBuffer;

    /* Fill the values for network buffer. */
    xNetworkBuffer.pBuffer = pcNetworkBuffer;
    xNetworkBuffer.size = mqttexampleNETWORK_BUFFER_SIZE;

    /* Fill in Transport Interface send and receive function pointers. */
    xTransport.pNetworkContext = pxNetworkContext;
    #if defined( democonfigUSE_TLS ) && ( democonfigUSE_TLS == 1 )
        xTransport.send = TLS_FreeRTOS_send;
        xTransport.recv = TLS_FreeRTOS_recv;
    #else
        xTransport.send = Plaintext_FreeRTOS_send;
        xTransport.recv = Plaintext_FreeRTOS_recv;
    #endif

    /* Initialize MQTT library. */
    return MQTT_Init( pxMQTTContext, &xTransport, prvGetTimeMs, prvEventCallback, &xNetworkBuffer );
}

static MQTTStatus_t prvMQTTConnect( MQTTContext_t * pxMQTTContext,
                                    bool xCleanSession )
{
    MQTTStatus_t xResult;
    MQTTConnectInfo_t xConnectInfo;
    bool xSessionPresent = false;

    /* Many fields are not used in this demo so start with everything at 0. */
    memset( &xConnectInfo, 0x00, sizeof( xConnectInfo ) );

    /* Start with a clean session i.e. direct the MQTT broker to discard any
     * previous session data. Also, establishing a connection with clean session
     * will ensure that the broker does not store any data when this client
     * gets disconnected. */
    xConnectInfo.cleanSession = xCleanSession;

    /* The client identifier is used to uniquely identify this MQTT client to
     * the MQTT broker. In a production device the identifier can be something
     * unique, such as a device serial number. */
    xConnectInfo.pClientIdentifier = democonfigCLIENT_IDENTIFIER;
    xConnectInfo.clientIdentifierLength = ( uint16_t ) strlen( democonfigCLIENT_IDENTIFIER );

    /* Set MQTT keep-alive period. It is the responsibility of the application
     * to ensure that the interval between Control Packets being sent does not
     * exceed the Keep Alive value. In the absence of sending any other Control
     * Packets, the Client MUST send a PINGREQ Packet. */
    xConnectInfo.keepAliveSeconds = mqttexampleKEEP_ALIVE_INTERVAL_SECONDS;

    /* Append metrics when connecting to the AWS IoT Core broker. */
    #ifdef democonfigUSE_AWS_IOT_CORE_BROKER
        #ifdef democonfigCLIENT_USERNAME
            xConnectInfo.pUserName = CLIENT_USERNAME_WITH_METRICS;
            xConnectInfo.userNameLength = ( uint16_t ) strlen( CLIENT_USERNAME_WITH_METRICS );
            xConnectInfo.pPassword = democonfigCLIENT_PASSWORD;
            xConnectInfo.passwordLength = ( uint16_t ) strlen( democonfigCLIENT_PASSWORD );
        #else
            xConnectInfo.pUserName = AWS_IOT_METRICS_STRING;
            xConnectInfo.userNameLength = AWS_IOT_METRICS_STRING_LENGTH;
            /* Password for authentication is not used. */
            xConnectInfo.pPassword = NULL;
            xConnectInfo.passwordLength = 0U;
        #endif
    #else /* ifdef democonfigUSE_AWS_IOT_CORE_BROKER */
        #ifdef democonfigCLIENT_USERNAME
            xConnectInfo.pUserName = democonfigCLIENT_USERNAME;
            xConnectInfo.userNameLength = ( uint16_t ) strlen( democonfigCLIENT_USERNAME );
            xConnectInfo.pPassword = democonfigCLIENT_PASSWORD;
            xConnectInfo.passwordLength = ( uint16_t ) strlen( democonfigCLIENT_PASSWORD );
        #endif /* ifdef democonfigCLIENT_USERNAME */
    #endif /* ifdef democonfigUSE_AWS_IOT_CORE_BROKER */

    /* Send MQTT CONNECT packet to broker. MQTT's Last Will and Testament feature
     * is not used in this demo, so it is passed as NULL. */
    xResult = MQTT_Connect( pxMQTTContext,
                            &xConnectInfo,
                            NULL,
                            mqttexampleCONNACK_RECV_TIMEOUT_MS,
                            &xSessionPresent );

    LogInfo( ( "Session present: %d\n", xSessionPresent ) );

    /* Resume a session if desired. */
    if( ( xResult == MQTTSuccess ) && !xCleanSession )
    {
        xResult = prvResumeSession( xSessionPresent );
    }

    return xResult;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t prvResumeSession( bool xSessionPresent )
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
            xCommandCreated = prvCreateCommand( SUBSCRIBE, &xResubscribeContext, prvCommandCallback, &xNewCommand );
            configASSERT( xCommandCreated == true );
            /* Send to the front of the queue so we will resubscribe as soon as possible. */
            xCommandAdded = xQueueSendToFront( xCommandQueue, &xNewCommand, mqttexampleDEMO_TICKS_TO_WAIT );
            configASSERT( xCommandAdded == pdTRUE );
        }
    }

    return xResult;
}

/*-----------------------------------------------------------*/

static BaseType_t prvSocketConnect( NetworkContext_t * pxNetworkContext )
{
    BaseType_t xConnected = pdFAIL;
    BackoffAlgorithmStatus_t xBackoffAlgStatus = BackoffAlgorithmSuccess;
    BackoffAlgorithmContext_t xReconnectParams;
    uint16_t usNextRetryBackOff = 0U;

    configASSERT( pxNetworkContext != NULL && pxNetworkContext->pParams != NULL );

    #if defined( democonfigUSE_TLS ) && ( democonfigUSE_TLS == 1 )
        TlsTransportStatus_t xNetworkStatus = TLS_TRANSPORT_CONNECT_FAILURE;
        NetworkCredentials_t xNetworkCredentials = { 0 };

        #ifdef democonfigUSE_AWS_IOT_CORE_BROKER

            /* ALPN protocols must be a NULL-terminated list of strings. Therefore,
             * the first entry will contain the actual ALPN protocol string while the
             * second entry must remain NULL. */
            char * pcAlpnProtocols[] = { NULL, NULL };

            /* The ALPN string changes depending on whether username/password authentication is used. */
            #ifdef democonfigCLIENT_USERNAME
                pcAlpnProtocols[ 0 ] = AWS_IOT_CUSTOM_AUTH_ALPN;
            #else
                pcAlpnProtocols[ 0 ] = AWS_IOT_MQTT_ALPN;
            #endif
            xNetworkCredentials.pAlpnProtos = pcAlpnProtocols;
        #endif /* ifdef democonfigUSE_AWS_IOT_CORE_BROKER */

        /* Set the credentials for establishing a TLS connection. */
        xNetworkCredentials.pRootCa = ( const unsigned char * ) democonfigROOT_CA_PEM;
        xNetworkCredentials.rootCaSize = sizeof( democonfigROOT_CA_PEM );
        #ifdef democonfigCLIENT_CERTIFICATE_PEM
            xNetworkCredentials.pClientCert = ( const unsigned char * ) democonfigCLIENT_CERTIFICATE_PEM;
            xNetworkCredentials.clientCertSize = sizeof( democonfigCLIENT_CERTIFICATE_PEM );
            xNetworkCredentials.pPrivateKey = ( const unsigned char * ) democonfigCLIENT_PRIVATE_KEY_PEM;
            xNetworkCredentials.privateKeySize = sizeof( democonfigCLIENT_PRIVATE_KEY_PEM );
        #endif
        xNetworkCredentials.disableSni = democonfigDISABLE_SNI;
    #else /* if defined( democonfigUSE_TLS ) && ( democonfigUSE_TLS == 1 ) */
        PlaintextTransportStatus_t xNetworkStatus = PLAINTEXT_TRANSPORT_CONNECT_FAILURE;
    #endif /* if defined( democonfigUSE_TLS ) && ( democonfigUSE_TLS == 1 ) */

    /* We will use a retry mechanism with an exponential backoff mechanism and
     * jitter. We initialize the context required for backoff period calculation here. */
    BackoffAlgorithm_InitializeParams( &xReconnectParams,
                                       mqttexampleRETRY_BACKOFF_BASE_MS,
                                       mqttexampleRETRY_MAX_BACKOFF_DELAY_MS,
                                       mqttexampleRETRY_MAX_ATTEMPTS );

    /* Attempt to connect to MQTT broker. If connection fails, retry after a
     * timeout. Timeout value will exponentially increase until the maximum
     * number of attempts are reached.
     */
    do
    {
        /* Establish a TCP connection with the MQTT broker. This example connects to
         * the MQTT broker as specified in democonfigMQTT_BROKER_ENDPOINT and
         * democonfigMQTT_BROKER_PORT at the top of this file. */
        #if defined( democonfigUSE_TLS ) && ( democonfigUSE_TLS == 1 )
            LogInfo( ( "Creating a TLS connection to %s:%d.",
                       democonfigMQTT_BROKER_ENDPOINT,
                       democonfigMQTT_BROKER_PORT ) );
            xNetworkStatus = TLS_FreeRTOS_Connect( pxNetworkContext,
                                                   democonfigMQTT_BROKER_ENDPOINT,
                                                   democonfigMQTT_BROKER_PORT,
                                                   &xNetworkCredentials,
                                                   mqttexampleTRANSPORT_SEND_RECV_TIMEOUT_MS,
                                                   mqttexampleTRANSPORT_SEND_RECV_TIMEOUT_MS );
            xConnected = ( xNetworkStatus == TLS_TRANSPORT_SUCCESS ) ? pdPASS : pdFAIL;
        #else /* if defined( democonfigUSE_TLS ) && ( democonfigUSE_TLS == 1 ) */
            LogInfo( ( "Creating a TCP connection to %s:%d.",
                       democonfigMQTT_BROKER_ENDPOINT,
                       democonfigMQTT_BROKER_PORT ) );
            xNetworkStatus = Plaintext_FreeRTOS_Connect( pxNetworkContext,
                                                         democonfigMQTT_BROKER_ENDPOINT,
                                                         democonfigMQTT_BROKER_PORT,
                                                         mqttexampleTRANSPORT_SEND_RECV_TIMEOUT_MS,
                                                         mqttexampleTRANSPORT_SEND_RECV_TIMEOUT_MS );
            xConnected = ( xNetworkStatus == PLAINTEXT_TRANSPORT_SUCCESS ) ? pdPASS : pdFAIL;
        #endif /* if defined( democonfigUSE_TLS ) && ( democonfigUSE_TLS == 1 ) */

        if( !xConnected )
        {
            /* Generate a random number and calculate backoff value (in milliseconds) for
             * the next connection retry.
             * Note: It is recommended to seed the random number generator with a device-specific
             * entropy source so that possibility of multiple devices retrying failed network operations
             * at similar intervals can be avoided. */
            xBackoffAlgStatus = BackoffAlgorithm_GetNextBackoff( &xReconnectParams, uxRand(), &usNextRetryBackOff );

            if( xBackoffAlgStatus == BackoffAlgorithmRetriesExhausted )
            {
                LogError( ( "Connection to the broker failed, all attempts exhausted." ) );
            }
            else if( xBackoffAlgStatus == BackoffAlgorithmSuccess )
            {
                LogWarn( ( "Connection to the broker failed. "
                           "Retrying connection with backoff and jitter." ) );
                vTaskDelay( pdMS_TO_TICKS( usNextRetryBackOff ) );
            }
        }
    } while( ( xConnected != pdPASS ) && ( xBackoffAlgStatus == BackoffAlgorithmSuccess ) );

    /* Set the socket wakeup callback. */
    if( xConnected )
    {
        ( void ) FreeRTOS_setsockopt( pxNetworkContext->pParams->tcpSocket,
                                      0, /* Level - Unused. */
                                      FREERTOS_SO_WAKEUP_CALLBACK,
                                      ( void * ) prvMQTTClientSocketWakeupCallback,
                                      sizeof( &( prvMQTTClientSocketWakeupCallback ) ) );
    }

    return xConnected;
}

/*-----------------------------------------------------------*/

static BaseType_t prvSocketDisconnect( NetworkContext_t * pxNetworkContext )
{
    BaseType_t xDisconnected = pdFAIL;

    configASSERT( pxNetworkContext != NULL && pxNetworkContext->pParams != NULL );

    /* Set the wakeup callback to NULL since the socket will disconnect. */
    ( void ) FreeRTOS_setsockopt( pxNetworkContext->pParams->tcpSocket,
                                  0, /* Level - Unused. */
                                  FREERTOS_SO_WAKEUP_CALLBACK,
                                  ( void * ) NULL,
                                  sizeof( void * ) );

    #if defined( democonfigUSE_TLS ) && ( democonfigUSE_TLS == 1 )
        LogInfo( ( "Disconnecting TLS connection.\n" ) );
        TLS_FreeRTOS_Disconnect( pxNetworkContext );
        xDisconnected = pdPASS;
    #else
        LogInfo( ( "Disconnecting TCP connection.\n" ) );
        PlaintextTransportStatus_t xNetworkStatus = PLAINTEXT_TRANSPORT_CONNECT_FAILURE;
        xNetworkStatus = Plaintext_FreeRTOS_Disconnect( pxNetworkContext );
        xDisconnected = ( xNetworkStatus == PLAINTEXT_TRANSPORT_SUCCESS ) ? pdPASS : pdFAIL;
    #endif
    return xDisconnected;
}

/*-----------------------------------------------------------*/

static void prvMQTTClientSocketWakeupCallback( Socket_t pxSocket )
{
    BaseType_t xResult;
    Command_t xCommand;

    /* Just to avoid compiler warnings.  The socket is not used but the function
     * prototype cannot be changed because this is a callback function. */
    ( void ) pxSocket;

    configASSERT( xCommandQueue );

    /* A socket used by the MQTT task may need attention.  Send an event
     * to the MQTT task to make sure the task is not blocked on xCommandQueue. */
    if( uxQueueMessagesWaiting( xCommandQueue ) == ( UBaseType_t ) 0 )
    {
        prvCreateCommand( PROCESSLOOP, NULL, NULL, &xCommand );
        xResult = prvAddCommandToQueue( &xCommand );
        configASSERT( xResult == pdTRUE );
    }
}

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

static BaseType_t prvAddCommandToQueue( Command_t * pxCommand )
{
    return xQueueSendToBack( xCommandQueue, pxCommand, mqttexampleDEMO_TICKS_TO_WAIT );
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
            /* Reconnect TCP. */
            xNetworkResult = prvSocketDisconnect( &xNetworkContext );
            configASSERT( xNetworkResult == pdPASS );
            xNetworkResult = prvSocketConnect( &xNetworkContext );
            configASSERT( xNetworkResult == pdPASS );
            /* MQTT Connect with a persistent session. */
            xStatus = prvMQTTConnect( &globalMqttContext, false );
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

static void prvEventCallback( MQTTContext_t * pMqttContext,
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

static void prvCommandLoop( void )
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
            prvCreateCommand( RECONNECT, NULL, NULL, &xNewCommand );
            xCommandAdded = xQueueSendToFront( xCommandQueue, &xNewCommand, mqttexampleDEMO_TICKS_TO_WAIT );
            /* Ensure the command was added to the queue. */
            configASSERT( xCommandAdded == pdTRUE );
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
            LogDebug( ( "Sleeping for %d ms after sending SUBSCRIBE packet.", mqttexampleSUBSCRIBE_TASK_DELAY_MS ) );
            vTaskDelay( mqttexampleSUBSCRIBE_TASK_DELAY_MS );
        }

        /* Terminate the loop if we receive the termination command. */
        if( xCommand.xCommandType == TERMINATE )
        {
            xTerminateReceived = true;
            break;
        }

        LogDebug( ( "Processed %d operations.", lNumProcessed ) );
    }

    /* Make sure we exited the loop due to receiving a terminate command and not
     * due to the queue being empty. */
    configASSERT( xTerminateReceived == true );

    LogInfo( ( "Creating Disconnect operation." ) );
    MQTT_Disconnect( &globalMqttContext );
    LogInfo( ( "Disconnected from broker." ) );
}

/*-----------------------------------------------------------*/

static void prvCommandCallback( CommandContext_t * pxContext )
{
    pxContext->xIsComplete = true;

    if( pxContext->xTaskToNotify != NULL )
    {
        xTaskNotify( pxContext->xTaskToNotify, pxContext->ulNotificationBit, eSetBits );
    }
}

/*-----------------------------------------------------------*/

static bool prvNotificationWaitLoop( uint32_t * pulNotification,
                                     uint32_t ulExpectedBits,
                                     bool xClearBits )
{
    uint32_t ulWaitCounter = 0U;
    bool ret = true;

    configASSERT( pulNotification != NULL );

    while( ( *pulNotification & ulExpectedBits ) != ulExpectedBits )
    {
        xTaskNotifyWait( 0,
                         ( xClearBits ) ? ulExpectedBits : 0,
                         pulNotification,
                         mqttexampleDEMO_TICKS_TO_WAIT );

        if( ++ulWaitCounter > mqttexampleMAX_WAIT_ITERATIONS )
        {
            LogError( ( "Loop exceeded maximum wait time.\n" ) );
            ret = false;
            break;
        }
    }

    return ret;
}

/*-----------------------------------------------------------*/

void prvSyncPublishTask( void * pvParameters )
{
    ( void ) pvParameters;
    Command_t xCommand;
    MQTTPublishInfo_t xPublishInfo = { 0 };
    char payloadBuf[ mqttexampleDEMO_BUFFER_SIZE ];
    char topicBuf[ mqttexampleDEMO_BUFFER_SIZE ];
    CommandContext_t xContext;
    uint32_t ulNotification = 0U;
    BaseType_t xCommandAdded = pdTRUE;

    /* We use QoS 1 so that the operation won't be counted as complete until we
     * receive the publish acknowledgment. */
    xPublishInfo.qos = MQTTQoS1;
    xPublishInfo.pTopicName = topicBuf;
    xPublishInfo.pPayload = payloadBuf;

    /* Synchronous publishes. In case mqttexamplePUBLISH_COUNT is odd, round up. */
    for( int i = 0; i < ( ( mqttexamplePUBLISH_COUNT + 1 ) / 2 ); i++ )
    {
        snprintf( payloadBuf, mqttexampleDEMO_BUFFER_SIZE, mqttexamplePUBLISH_PAYLOAD_FORMAT, "Sync", i + 1 );
        xPublishInfo.payloadLength = ( uint16_t ) strlen( payloadBuf );
        snprintf( topicBuf, mqttexampleDEMO_BUFFER_SIZE, mqttexamplePUBLISH_TOPIC_FORMAT_STRING, "sync", i + 1 );
        xPublishInfo.topicNameLength = ( uint16_t ) strlen( topicBuf );

        memset( ( void * ) &xContext, 0x00, sizeof( xContext ) );
        xContext.xTaskToNotify = xTaskGetCurrentTaskHandle();
        xContext.ulNotificationBit = 1 << i;
        xContext.pxPublishInfo = &xPublishInfo;
        LogInfo( ( "Adding publish operation for message %s \non topic %.*s", payloadBuf, xPublishInfo.topicNameLength, xPublishInfo.pTopicName ) );
        prvCreateCommand( PUBLISH, &xContext, prvCommandCallback, &xCommand );
        xCommandAdded = prvAddCommandToQueue( &xCommand );
        /* Ensure command was added to queue. */
        configASSERT( xCommandAdded == pdTRUE );
        LogInfo( ( "Waiting for publish %d to complete.", i + 1 ) );

        if( prvNotificationWaitLoop( &ulNotification, ( 1U << i ), true ) != true )
        {
            LogError( ( "Synchronous publish loop iteration %d"
                        " exceeded maximum wait time.\n", ( i + 1 ) ) );
        }

        configASSERT( ( ulNotification & ( 1U << i ) ) == ( 1U << i ) );

        LogInfo( ( "Publish operation complete. Sleeping for %d ms.\n", mqttexamplePUBLISH_DELAY_SYNC_MS ) );
        vTaskDelay( pdMS_TO_TICKS( mqttexamplePUBLISH_DELAY_SYNC_MS ) );
    }

    LogInfo( ( "Finished sync publishes.\n" ) );

    /* Clear this task's notifications. */
    xTaskNotifyStateClear( NULL );
    ulNotification = ulTaskNotifyValueClear( NULL, ~( 0U ) );

    /* Notify main task this task has completed. */
    xTaskNotify( xMainTask, mqttexamplePUBLISHER_SYNC_COMPLETE_BIT, eSetBits );

    /* Delete this task. */
    LogInfo( ( "Deleting Sync Publisher task." ) );
    vTaskDelete( NULL );
}

/*-----------------------------------------------------------*/

void prvAsyncPublishTask( void * pvParameters )
{
    ( void ) pvParameters;
    Command_t xCommand;
    MQTTPublishInfo_t pxPublishes[ mqttexamplePUBLISH_COUNT / 2 ];
    uint32_t ulNotification = 0U;
    uint32_t ulExpectedNotifications = 0U;
    BaseType_t xCommandAdded = pdTRUE;
    /* The following arrays are used to hold pointers to dynamically allocated memory. */
    char * payloadBuffers[ mqttexamplePUBLISH_COUNT / 2 ];
    char * topicBuffers[ mqttexamplePUBLISH_COUNT / 2 ];
    CommandContext_t * pxContexts[ mqttexamplePUBLISH_COUNT / 2 ] = { 0 };

    /* Add a delay. The main task will not be sending publishes for this interval
     * anyway, as we want to give the broker ample time to process the
     * subscription. */
    vTaskDelay( mqttexampleSUBSCRIBE_TASK_DELAY_MS );

    /* Asynchronous publishes. Although not necessary, we use dynamic
     * memory here to avoid declaring many static buffers. */
    for( int i = 0; i < mqttexamplePUBLISH_COUNT / 2; i++ )
    {
        pxContexts[ i ] = ( CommandContext_t * ) pvPortMalloc( sizeof( CommandContext_t ) );
        memset( ( void * ) pxContexts[ i ], 0x00, sizeof( CommandContext_t ) );
        pxContexts[ i ]->xTaskToNotify = xTaskGetCurrentTaskHandle();

        /* Set the notification bit to be the publish number. This prevents this demo
         * from having more than 32 publishes. If many publishes are desired, semaphores
         * can be used instead of task notifications. */
        pxContexts[ i ]->ulNotificationBit = 1U << i;
        ulExpectedNotifications |= 1U << i;
        payloadBuffers[ i ] = ( char * ) pvPortMalloc( mqttexampleDYNAMIC_BUFFER_SIZE );
        topicBuffers[ i ] = ( char * ) pvPortMalloc( mqttexampleDYNAMIC_BUFFER_SIZE );
        snprintf( payloadBuffers[ i ], mqttexampleDYNAMIC_BUFFER_SIZE, mqttexamplePUBLISH_PAYLOAD_FORMAT, "Async", i + 1 );
        snprintf( topicBuffers[ i ], mqttexampleDYNAMIC_BUFFER_SIZE, mqttexamplePUBLISH_TOPIC_FORMAT_STRING, "async", i + 1 );
        /* Set publish info. */
        memset( &( pxPublishes[ i ] ), 0x00, sizeof( MQTTPublishInfo_t ) );
        pxPublishes[ i ].pPayload = payloadBuffers[ i ];
        pxPublishes[ i ].payloadLength = strlen( payloadBuffers[ i ] );
        pxPublishes[ i ].pTopicName = topicBuffers[ i ];
        pxPublishes[ i ].topicNameLength = ( uint16_t ) strlen( topicBuffers[ i ] );
        pxPublishes[ i ].qos = MQTTQoS1;
        pxContexts[ i ]->pxPublishInfo = &( pxPublishes[ i ] );
        LogInfo( ( "Adding publish operation for message %s \non topic %.*s",
                   payloadBuffers[ i ],
                   pxPublishes[ i ].topicNameLength,
                   pxPublishes[ i ].pTopicName ) );
        prvCreateCommand( PUBLISH, pxContexts[ i ], prvCommandCallback, &xCommand );
        xCommandAdded = prvAddCommandToQueue( &xCommand );
        /* Ensure command was added to queue. */
        configASSERT( xCommandAdded == pdTRUE );
        /* Short delay so we do not bombard the broker with publishes. */
        LogInfo( ( "Publish operation queued. Sleeping for %d ms.\n", mqttexamplePUBLISH_DELAY_ASYNC_MS ) );
        vTaskDelay( pdMS_TO_TICKS( mqttexamplePUBLISH_DELAY_ASYNC_MS ) );
    }

    LogInfo( ( "Finished async publishes.\n" ) );

    /* Receive all task notifications. We may receive notifications in a
     * different order, so we have two loops. If all notifications have been
     * received, we can break early. */
    ( void ) prvNotificationWaitLoop( &ulNotification, ulExpectedNotifications, false );

    for( int i = 0; i < mqttexamplePUBLISH_COUNT / 2; i++ )
    {
        configASSERT( ( ulNotification & ( 1U << i ) ) == ( 1U << i ) );

        LogInfo( ( "Freeing publish context %d.", i + 1 ) );
        vPortFree( pxContexts[ i ] );
        vPortFree( topicBuffers[ i ] );
        vPortFree( payloadBuffers[ i ] );
        LogInfo( ( "Publish context %d freed.", i + 1 ) );
        pxContexts[ i ] = NULL;
    }

    /* Clear this task's notifications. */
    xTaskNotifyStateClear( NULL );
    ulNotification = ulTaskNotifyValueClear( NULL, ~( 0U ) );

    /* Notify main task this task has completed. */
    xTaskNotify( xMainTask, mqttexamplePUBLISHER_ASYNC_COMPLETE_BIT, eSetBits );

    /* Delete this task. */
    LogInfo( ( "Deleting Async Publisher task." ) );
    vTaskDelete( NULL );
}

/*-----------------------------------------------------------*/

void prvSubscribeTask( void * pvParameters )
{
    ( void ) pvParameters;
    MQTTSubscribeInfo_t xSubscribeInfo;
    Command_t xCommand;
    BaseType_t xCommandAdded = pdTRUE;
    MQTTPublishInfo_t * pxReceivedPublish = NULL;
    uint16_t usNumReceived = 0;
    uint32_t ulNotification = 0;
    CommandContext_t xContext;
    PublishElement_t xReceivedPublish;
    uint32_t ulWaitCounter = 0;

    /* The QoS does not affect when subscribe operations are marked completed
     * as it does for publishes. However, we still use QoS 1 here so that the
     * broker will resend publishes if there is a network disconnect. */
    xSubscribeInfo.qos = MQTTQoS1;
    xSubscribeInfo.pTopicFilter = mqttexampleSUBSCRIBE_TOPIC_FILTER;
    xSubscribeInfo.topicFilterLength = ( uint16_t ) strlen( xSubscribeInfo.pTopicFilter );
    LogInfo( ( "Topic filter: %.*s", xSubscribeInfo.topicFilterLength, xSubscribeInfo.pTopicFilter ) );

    /* Create the context and subscribe command. */
    memset( &xContext, 0x00, sizeof( xContext ) );
    xContext.pxResponseQueue = xSubscriberResponseQueue;
    xContext.xTaskToNotify = xTaskGetCurrentTaskHandle();
    xContext.ulNotificationBit = mqttexampleSUBSCRIBE_COMPLETE_BIT;
    xContext.pxSubscribeInfo = &xSubscribeInfo;
    xContext.ulSubscriptionCount = 1;
    LogInfo( ( "Adding subscribe operation" ) );
    prvCreateCommand( SUBSCRIBE, &xContext, prvCommandCallback, &xCommand );
    xCommandAdded = prvAddCommandToQueue( &xCommand );
    /* Ensure command was added to queue. */
    configASSERT( xCommandAdded == pdTRUE );

    /* This demo relies on the server processing our subscription before any publishes.
     * Since this demo uses multiple tasks, we do not retry failed subscriptions, as the
     * server has likely already processed our first publish, and so this demo will not
     * complete successfully. */
    LogInfo( ( "Waiting for subscribe operation to complete." ) );
    ( void ) prvNotificationWaitLoop( &ulNotification, mqttexampleSUBSCRIBE_COMPLETE_BIT, true );

    configASSERT( ( ulNotification & mqttexampleSUBSCRIBE_COMPLETE_BIT ) == mqttexampleSUBSCRIBE_COMPLETE_BIT );
    configASSERT( xContext.xReturnStatus == MQTTSuccess );

    LogInfo( ( "Operation wait complete.\n" ) );

    for( ; ; )
    {
        /* It is possible that there is nothing to receive from the queue, and
         * this is expected, as there are delays between each publish. For this
         * reason, we keep track of the number of publishes received, and break
         * from the outermost while loop when we have received all of them. If
         * the queue is empty, we add a delay before checking it again. */
        while( xQueueReceive( xSubscriberResponseQueue, &xReceivedPublish, mqttexampleDEMO_TICKS_TO_WAIT ) != pdFALSE )
        {
            pxReceivedPublish = &( xReceivedPublish.xPublishInfo );
            pxReceivedPublish->pTopicName = ( const char * ) xReceivedPublish.pcTopicNameBuf;
            pxReceivedPublish->pPayload = xReceivedPublish.pcPayloadBuf;
            LogInfo( ( "Received publish on topic %.*s\nMessage payload: %.*s\n",
                       pxReceivedPublish->topicNameLength,
                       pxReceivedPublish->pTopicName,
                       ( int ) pxReceivedPublish->payloadLength,
                       ( const char * ) pxReceivedPublish->pPayload ) );
            usNumReceived++;
            /* Reset the wait counter every time a publish is received. */
            ulWaitCounter = 0;
        }

        /* Since this is an infinite loop, we want to break if all publishes have
         * been received. */
        if( usNumReceived >= mqttexamplePUBLISH_COUNT )
        {
            break;
        }

        /* Break if we have been stuck in this loop for too long. The total wait
         * here will be ( (loop delay + queue check delay) * `mqttexampleMAX_WAIT_ITERATIONS` ).
         * For example, with a 1000 ms queue delay, a 400 ms loop delay, and a
         * maximum iteration of 20, this will wait 28 seconds after receiving
         * the last publish. */
        if( ++ulWaitCounter > mqttexampleMAX_WAIT_ITERATIONS )
        {
            LogError( ( "Publish receive loop exceeded maximum wait time.\n" ) );
            break;
        }

        /* Delay a bit to give more time for publish messages to be received. */
        LogInfo( ( "No messages queued, received %u publish%s, sleeping for %d ms\n",
                   usNumReceived,
                   ( usNumReceived == 1 ) ? "" : "es",
                   mqttexampleSUBSCRIBE_TASK_DELAY_MS ) );
        vTaskDelay( pdMS_TO_TICKS( mqttexampleSUBSCRIBE_TASK_DELAY_MS ) );
    }

    LogInfo( ( "Finished receiving\n" ) );
    prvCreateCommand( UNSUBSCRIBE, &xContext, prvCommandCallback, &xCommand );
    memset( ( void * ) &xContext, 0x00, sizeof( xContext ) );
    xContext.pxResponseQueue = xSubscriberResponseQueue;
    xContext.xTaskToNotify = xTaskGetCurrentTaskHandle();
    xContext.ulNotificationBit = mqttexampleUNSUBSCRIBE_COMPLETE_BIT;
    xContext.pxSubscribeInfo = &xSubscribeInfo;
    xContext.ulSubscriptionCount = 1;
    LogInfo( ( "Adding unsubscribe operation\n" ) );
    xCommandAdded = prvAddCommandToQueue( &xCommand );
    /* Ensure command was added to queue. */
    configASSERT( xCommandAdded == pdTRUE );

    LogInfo( ( "Waiting for unsubscribe operation to complete." ) );
    ( void ) prvNotificationWaitLoop( &ulNotification, mqttexampleUNSUBSCRIBE_COMPLETE_BIT, true );

    configASSERT( ( ulNotification & mqttexampleUNSUBSCRIBE_COMPLETE_BIT ) == mqttexampleUNSUBSCRIBE_COMPLETE_BIT );
    LogInfo( ( "Operation wait complete.\n" ) );

    /* Create command to stop command loop. */
    LogInfo( ( "Beginning command queue termination." ) );
    prvCreateCommand( TERMINATE, NULL, NULL, &xCommand );
    xCommandAdded = prvAddCommandToQueue( &xCommand );
    /* Ensure command was added to queue. */
    configASSERT( xCommandAdded == pdTRUE );

    /* Notify main task this task has completed. */
    xTaskNotify( xMainTask, mqttexampleSUBSCRIBE_TASK_COMPLETE_BIT, eSetBits );

    /* Delete this task. */
    LogInfo( ( "Deleting Subscriber task." ) );
    vTaskDelete( NULL );
}

/*-----------------------------------------------------------*/

static void prvCleanExistingPersistentSession( void )
{
    BaseType_t xNetworkStatus = pdFAIL;
    MQTTStatus_t xMQTTStatus;

    /* Connect to the broker. We connect here with the "clean session" flag set
     * to true in order to clear any prior state in the broker. We will disconnect
     * and later form a persistent session, so that it may be resumed if the
     * network suddenly disconnects. */
    xNetworkStatus = prvSocketConnect( &xNetworkContext );
    configASSERT( xNetworkStatus == pdPASS );
    LogInfo( ( "Creating a clean session to clear any broker state information." ) );
    xMQTTStatus = prvMQTTInit( &globalMqttContext, &xNetworkContext );
    configASSERT( xMQTTStatus == MQTTSuccess );
    xMQTTStatus = prvMQTTConnect( &globalMqttContext, true );
    configASSERT( xMQTTStatus == MQTTSuccess );

    /* Disconnect. */
    xMQTTStatus = MQTT_Disconnect( &globalMqttContext );
    configASSERT( xMQTTStatus == MQTTSuccess );
    xNetworkStatus = prvSocketDisconnect( &xNetworkContext );
    configASSERT( xNetworkStatus == pdPASS );
}

/*-----------------------------------------------------------*/

 /* Also see https://www.freertos.org/mqtt/mqtt-agent-demo.html? for an
  * alternative run time model whereby coreMQTT runs in an autonomous
  * background agent task.  Executing the MQTT protocol in an agent task
  * removes the need for the application writer to explicitly manage any MQTT
  * state or call the MQTT_ProcessLoop() API function. Using an agent task
  * also enables multiple application tasks to more easily share a single
  * MQTT connection. */
static void prvMQTTDemoTask( void * pvParameters )
{
    BaseType_t xNetworkStatus = pdFAIL;
    MQTTStatus_t xMQTTStatus;
    BaseType_t xResult = pdFALSE;
    uint32_t ulNotification = 0;
    uint32_t ulExpectedNotifications = mqttexamplePUBLISHER_SYNC_COMPLETE_BIT |
                                       mqttexampleSUBSCRIBE_TASK_COMPLETE_BIT |
                                       mqttexamplePUBLISHER_ASYNC_COMPLETE_BIT;

    ( void ) pvParameters;

    /* Set the pParams member of the network context with desired transport. */
    #if defined( democonfigUSE_TLS ) && ( democonfigUSE_TLS == 1 )
        xNetworkContext.pParams = &xTlsTransportParams;
    #else
        xNetworkContext.pParams = &xPlaintextTransportParams;
    #endif

    ulGlobalEntryTimeMs = prvGetTimeMs();

    /* Create command queue for processing MQTT commands. */
    xCommandQueue = xQueueCreate( mqttexampleCOMMAND_QUEUE_SIZE, sizeof( Command_t ) );
    /* Create response queues for each task. */
    xSubscriberResponseQueue = xQueueCreate( mqttexamplePUBLISH_QUEUE_SIZE, sizeof( PublishElement_t ) );

    /* In this demo, send publishes on non-subscribed topics to this queue.
     * Note that this value is not meant to be changed after `prvCommandLoop` has
     * been called, since access to this variable is not protected by thread
     * synchronization primitives. */
    xDefaultResponseQueue = xQueueCreate( 1, sizeof( PublishElement_t ) );

    /* This demo uses a persistent session that can be re-connected if disconnected.
     * Clean any lingering sessions that may exist from previous executions of the
     * demo. */
    prvCleanExistingPersistentSession();

    for( ; ; )
    {
        /* Clear the lists of subscriptions and pending acknowledgments. */
        memset( pxPendingAcks, 0x00, mqttexamplePENDING_ACKS_MAX_SIZE * sizeof( AckInfo_t ) );
        memset( pxSubscriptions, 0x00, mqttexampleSUBSCRIPTIONS_MAX_COUNT * sizeof( SubscriptionElement_t ) );

        /* Connect to the broker. */
        xNetworkStatus = prvSocketConnect( &xNetworkContext );
        configASSERT( xNetworkStatus == pdPASS );
        /* Form an MQTT connection with a persistent session. */
        xMQTTStatus = prvMQTTConnect( &globalMqttContext, false );
        configASSERT( xMQTTStatus == MQTTSuccess );
        configASSERT( globalMqttContext.connectStatus == MQTTConnected );

        /* Give subscriber task higher priority so the subscribe will be processed
         * before the first publish.  This must be less than or equal to the priority of
         * the main task. */
        xResult = xTaskCreate( prvSubscribeTask, "Subscriber", democonfigDEMO_STACKSIZE, NULL, tskIDLE_PRIORITY + 1, &xSubscribeTask );
        configASSERT( xResult == pdPASS );
        xResult = xTaskCreate( prvSyncPublishTask, "SyncPublisher", democonfigDEMO_STACKSIZE, NULL, tskIDLE_PRIORITY, &xSyncPublisherTask );
        configASSERT( xResult == pdPASS );
        xResult = xTaskCreate( prvAsyncPublishTask, "AsyncPublisher", democonfigDEMO_STACKSIZE, NULL, tskIDLE_PRIORITY, &xAsyncPublisherTask );
        configASSERT( xResult == pdPASS );

        LogInfo( ( "Running command loop" ) );
        prvCommandLoop();

        /* Delete created queues. Wait for tasks to exit before cleaning up. */
        LogInfo( ( "Waiting for tasks to exit." ) );
        ( void ) prvNotificationWaitLoop( &ulNotification, ulExpectedNotifications, false );

        configASSERT( ( ulNotification & ulExpectedNotifications ) == ulExpectedNotifications );

        /* Reset queues. */
        xQueueReset( xCommandQueue );
        xQueueReset( xDefaultResponseQueue );
        xQueueReset( xSubscriberResponseQueue );

        /* Clear task notifications. */
        ulNotification = ulTaskNotifyValueClear( NULL, ~( 0U ) );

        /* Disconnect. */
        xNetworkStatus = prvSocketDisconnect( &xNetworkContext );
        configASSERT( xNetworkStatus == pdPASS );

        LogInfo( ( "\r\n\r\nprvMQTTDemoTask() completed an iteration successfully. Total free heap is %u.\r\n", xPortGetFreeHeapSize() ) );
        LogInfo( ( "Demo completed successfully.\r\n" ) );
        LogInfo( ( "Short delay before starting the next iteration.... \r\n\r\n" ) );
        vTaskDelay( mqttexampleDELAY_BETWEEN_DEMO_ITERATIONS );
    }
}

/*-----------------------------------------------------------*/

static uint32_t prvGetTimeMs( void )
{
    TickType_t xTickCount = 0;
    uint32_t ulTimeMs = 0UL;

    /* Get the current tick count. */
    xTickCount = xTaskGetTickCount();

    /* Convert the ticks to milliseconds. */
    ulTimeMs = ( uint32_t ) xTickCount * mqttexampleMILLISECONDS_PER_TICK;

    /* Reduce ulGlobalEntryTimeMs from obtained time so as to always return the
     * elapsed time in the application. */
    ulTimeMs = ( uint32_t ) ( ulTimeMs - ulGlobalEntryTimeMs );

    return ulTimeMs;
}

/*-----------------------------------------------------------*/
