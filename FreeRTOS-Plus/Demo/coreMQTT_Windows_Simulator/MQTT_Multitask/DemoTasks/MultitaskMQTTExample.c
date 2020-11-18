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
 * This demo shows how to use coreMQTT in a multithreaded environment - it does not
 * yet go as far as encapsulating the MQTT library within its own agent (or daemon)
 * task - although the MQTTAgent_CommandLoop() function demonstrates how that might be done.
 * In this task MQTTAgent_CommandLoop() is only executed from a single thread and is the
 * only function that is allowed to use the coreMQTT API directly.  Anything else
 * needing to interact with the coreMQTT API does so by posting commands to
 * MQTTAgent_CommandLoop() via a queue.  Future coreMQTT releases will build an agent into
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
 *    creates the other tasks, calls MQTTAgent_CommandLoop() to handle the MQTT traffic,
 *    then cleans up ready for the next iteration.
 *  - prvSyncPublishTask() which demonstrates synchronous publishes. The task creates
 *    a series of publish operations that are sent over the command queue to be
 *    processed by MQTTAgent_CommandLoop(), waiting for each publish to complete before
 *    sending the next.
 *  - prvAsyncPublishTask() which demonstrates asynchronous publishes. Like
 *    prvSyncPublishTask(), the task creates a series of publish operations that are
 *    sent over the command queue to be processed by MQTTAgent_CommandLoop(), but unlike
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

#include "mqtt_agent.h"

/* Exponential backoff retry include. */
#include "exponential_backoff.h"

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
 * @brief Timeout for receiving CONNACK packet in milliseconds.
 */
#define mqttexampleCONNACK_RECV_TIMEOUT_MS           ( 1000U )

/**
 * @brief Time to wait between each cycle of the demo implemented by prvMQTTDemoTask().
 */
#define mqttexampleDELAY_BETWEEN_DEMO_ITERATIONS     ( pdMS_TO_TICKS( 5000U ) )

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
 * @brief Number of publishes done by the publisher in this demo.
 */
#define mqttexamplePUBLISH_COUNT                     16

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
extern MQTTContext_t globalMqttContext;

/**
 * @brief Global Network context.
 */
static NetworkContext_t xNetworkContext;

/**
 * @brief Queue for main task to handle MQTT operations.
 */
extern QueueHandle_t xCommandQueue;

/**
 * @brief Response queue for prvSubscribeTask.
 */
static QueueHandle_t xSubscriberResponseQueue;

/**
 * @brief Response queue for publishes received on non-subscribed topics.
 */
extern QueueHandle_t xDefaultResponseQueue;

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
    return MQTT_Init( pxMQTTContext, &xTransport, prvGetTimeMs, MQTTAgent_EventCallback, &xNetworkBuffer );
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
        xResult = MQTTAgent_ResumeSession( xSessionPresent );
    }

    return xResult;
}

/*-----------------------------------------------------------*/

static BaseType_t prvSocketConnect( NetworkContext_t * pxNetworkContext )
{
    BaseType_t xConnected = pdFAIL;
    RetryUtilsStatus_t xRetryUtilsStatus = RetryUtilsSuccess;
    RetryUtilsParams_t xReconnectParams;

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
     * jitter. We initialize reconnect attempts and interval here. */
    xReconnectParams.maxRetryAttempts = MAX_RETRY_ATTEMPTS;
    RetryUtils_ParamsReset( &xReconnectParams );

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
            LogWarn( ( "Connection to the broker failed. Retrying connection with backoff and jitter." ) );
            xRetryUtilsStatus = RetryUtils_BackoffAndSleep( &xReconnectParams );
        }

        if( xRetryUtilsStatus == RetryUtilsRetriesExhausted )
        {
            LogError( ( "Connection to the broker failed. All attempts exhausted." ) );
        }
    } while( ( xConnected != pdPASS ) && ( xRetryUtilsStatus == RetryUtilsSuccess ) );

    /* Set the socket wakeup callback. */
    if( xConnected )
    {
        ( void ) FreeRTOS_setsockopt( pxNetworkContext->tcpSocket,
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

    /* Set the wakeup callback to NULL since the socket will disconnect. */
    ( void ) FreeRTOS_setsockopt( pxNetworkContext->tcpSocket,
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
        MQTTAgent_CreateCommand( PROCESSLOOP, NULL, NULL, &xCommand );
        xResult = MQTTAgent_AddCommandToQueue( &xCommand );
        configASSERT( xResult == pdTRUE );
    }
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
        MQTTAgent_CreateCommand( PUBLISH, &xContext, prvCommandCallback, &xCommand );
        xCommandAdded = MQTTAgent_AddCommandToQueue( &xCommand );
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
        MQTTAgent_CreateCommand( PUBLISH, pxContexts[ i ], prvCommandCallback, &xCommand );
        xCommandAdded = MQTTAgent_AddCommandToQueue( &xCommand );
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
    MQTTAgent_CreateCommand( SUBSCRIBE, &xContext, prvCommandCallback, &xCommand );
    xCommandAdded = MQTTAgent_AddCommandToQueue( &xCommand );
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
    MQTTAgent_CreateCommand( UNSUBSCRIBE, &xContext, prvCommandCallback, &xCommand );
    memset( ( void * ) &xContext, 0x00, sizeof( xContext ) );
    xContext.pxResponseQueue = xSubscriberResponseQueue;
    xContext.xTaskToNotify = xTaskGetCurrentTaskHandle();
    xContext.ulNotificationBit = mqttexampleUNSUBSCRIBE_COMPLETE_BIT;
    xContext.pxSubscribeInfo = &xSubscribeInfo;
    xContext.ulSubscriptionCount = 1;
    LogInfo( ( "Adding unsubscribe operation\n" ) );
    xCommandAdded = MQTTAgent_AddCommandToQueue( &xCommand );
    /* Ensure command was added to queue. */
    configASSERT( xCommandAdded == pdTRUE );

    LogInfo( ( "Waiting for unsubscribe operation to complete." ) );
    ( void ) prvNotificationWaitLoop( &ulNotification, mqttexampleUNSUBSCRIBE_COMPLETE_BIT, true );

    configASSERT( ( ulNotification & mqttexampleUNSUBSCRIBE_COMPLETE_BIT ) == mqttexampleUNSUBSCRIBE_COMPLETE_BIT );
    LogInfo( ( "Operation wait complete.\n" ) );

    /* Create command to stop command loop. */
    LogInfo( ( "Beginning command queue termination." ) );
    MQTTAgent_CreateCommand( TERMINATE, NULL, NULL, &xCommand );
    xCommandAdded = MQTTAgent_AddCommandToQueue( &xCommand );
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

static void prvMQTTAgentTask( void * pvParameters )
{
    bool xTerminateReceived = false;
    BaseType_t xNetworkResult = pdFAIL;
    MQTTStatus_t xMQTTStatus = MQTTSuccess;

    ( void ) pvParameters;

    do
    {
        xTerminateReceived = MQTTAgent_CommandLoop();

        if( xTerminateReceived != true )
        {
            /* Reconnect TCP. */
            xNetworkResult = prvSocketDisconnect( &xNetworkContext );
            configASSERT( xNetworkResult == pdPASS );
            xNetworkResult = prvSocketConnect( &xNetworkContext );
            configASSERT( xNetworkResult == pdPASS );
            /* MQTT Connect with a persistent session. */
            xMQTTStatus = prvMQTTConnect( &globalMqttContext, false );
        }
    } while( !xTerminateReceived );

    LogInfo( ( "Creating Disconnect operation." ) );
    MQTT_Disconnect( &globalMqttContext );
    LogInfo( ( "Disconnected from broker." ) );
}

/*-----------------------------------------------------------*/

static void prvMQTTDemoTask( void * pvParameters )
{
    BaseType_t xNetworkStatus = pdFAIL;
    MQTTStatus_t xMQTTStatus;
    BaseType_t xResult = pdFALSE;
    uint32_t ulNotification = 0;
    uint32_t ulExpectedNotifications = mqttexamplePUBLISHER_SYNC_COMPLETE_BIT |
                                       mqttexampleSUBSCRIBE_TASK_COMPLETE_BIT |
                                       mqttexamplePUBLISHER_ASYNC_COMPLETE_BIT;
    bool xTerminateReceived = false;
    uint32_t ulWaitCounter = 0UL;

    ( void ) pvParameters;

    ulGlobalEntryTimeMs = prvGetTimeMs();

    /* Create command queue for processing MQTT commands. */
    xCommandQueue = xQueueCreate( mqttexampleCOMMAND_QUEUE_SIZE, sizeof( Command_t ) );
    /* Create response queues for each task. */
    xSubscriberResponseQueue = xQueueCreate( mqttexamplePUBLISH_QUEUE_SIZE, sizeof( PublishElement_t ) );

    /* In this demo, send publishes on non-subscribed topics to this queue.
     * Note that this value is not meant to be changed after `MQTTAgent_CommandLoop` has
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

        do
        {
            xTerminateReceived = MQTTAgent_CommandLoop();

            if( xTerminateReceived != true )
            {
                /* Reconnect TCP. */
                xNetworkStatus = prvSocketDisconnect( &xNetworkContext );
                configASSERT( xNetworkStatus == pdPASS );
                xNetworkStatus = prvSocketConnect( &xNetworkContext );
                configASSERT( xNetworkStatus == pdPASS );
                /* MQTT Connect with a persistent session. */
                xMQTTStatus = prvMQTTConnect( &globalMqttContext, false );
            }
        } while( !xTerminateReceived && ( ++ulWaitCounter < mqttexampleMAX_WAIT_ITERATIONS ) );

        configASSERT( xTerminateReceived );
        LogInfo( ( "Creating Disconnect operation." ) );
        MQTT_Disconnect( &globalMqttContext );
        LogInfo( ( "Disconnected from broker." ) );

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
