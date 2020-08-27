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
 *
 * 1 tab == 4 spaces!
 */

/*
 * Demo for showing use of the managed MQTT API.
 *
 * The Example shown below uses this API to create MQTT messages and
 * send them over the connection established using FreeRTOS sockets.
 * The example is single threaded and uses statically allocated memory;
 * it uses QOS0 and therefore does not implement any retransmission
 * mechanism for Publish messages.
 *
 * !!! NOTE !!!
 * This MQTT demo does not authenticate the server nor the client.
 * Hence, this demo should not be used as production ready code.
 */

/* Standard includes. */
#include <string.h>
#include <stdio.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"

/* Demo Specific configs. */
#include "demo_config.h"

/* MQTT library includes. */
#include "mqtt.h"

/* Transport interface include. */
#include "plaintext_freertos.h"

/*-----------------------------------------------------------*/

/* Compile time error for undefined configs. */
#ifndef democonfigMQTT_BROKER_ENDPOINT
    #error "Define the config democonfigMQTT_BROKER_ENDPOINT by following the instructions in file demo_config.h."
#endif

/*-----------------------------------------------------------*/

/* Default values for configs. */
#ifndef democonfigCLIENT_IDENTIFIER

/**
 * @brief The MQTT client identifier used in this example.  Each client identifier
 * must be unique so edit as required to ensure no two clients connecting to the
 * same broker use the same client identifier.
 *
 * @note Appending __TIME__ to the client id string will reduce the possibility of a
 * client id collision in the broker. Note that the appended time is the compilation
 * time. This client id can cause collision, if more than one instance of the same
 * binary is used at the same time to connect to the broker.
 */
    #define democonfigCLIENT_IDENTIFIER    "testClient"__TIME__
#endif

#ifndef democonfigMQTT_BROKER_PORT

/**
 * @brief The port to use for the demo.
 */
    #define democonfigMQTT_BROKER_PORT    ( 1883 )
#endif

/*-----------------------------------------------------------*/

/**
 * @brief Timeout for receiving CONNACK packet in milliseconds.
 */
#define mqttexampleCONNACK_RECV_TIMEOUT_MS          ( 1000U )

/**
 * @brief The topic to subscribe and publish to in the example.
 *
 * The topic name starts with the client identifier to ensure that each demo
 * interacts with a unique topic name.
 */
#define mqttexampleTOPIC                            democonfigCLIENT_IDENTIFIER "/example/topic"

/**
 * @brief The MQTT message published in this example.
 */
#define mqttexampleMESSAGE                          "Hello World!"

/**
 * @brief Dimensions a file scope buffer currently used to send and receive MQTT data
 * from a socket.
 */
#define mqttexampleSHARED_BUFFER_SIZE               ( 500U )

/**
 * @brief Time to wait between each cycle of the demo implemented by prvMQTTDemoTask().
 */
#define mqttexampleDELAY_BETWEEN_DEMO_ITERATIONS    ( pdMS_TO_TICKS( 5000U ) )

/**
 * @brief Timeout for MQTT_ReceiveLoop in milliseconds.
 */
#define mqttexampleRECEIVE_LOOP_TIMEOUT_MS          ( 500U )

/**
 * @brief Keep alive time reported to the broker while establishing an MQTT connection.
 *
 * It is the responsibility of the Client to ensure that the interval between
 * Control Packets being sent does not exceed the this Keep Alive value. In the
 * absence of sending any other Control Packets, the Client MUST send a
 * PINGREQ Packet.
 */
#define mqttexampleKEEP_ALIVE_TIMEOUT_SECONDS       ( 60U )

/**
 * @brief Time to wait before sending ping request to keep MQTT connection alive.
 *
 * A PINGREQ is attempted to be sent at every ( #mqttexampleKEEP_ALIVE_TIMEOUT_SECONDS / 4 )
 * seconds. This is to make sure that a PINGREQ is always sent before the timeout
 * expires in broker.
 */
#define mqttexampleKEEP_ALIVE_DELAY                 ( pdMS_TO_TICKS( ( ( mqttexampleKEEP_ALIVE_TIMEOUT_SECONDS / 4 ) * 1000 ) ) )

/**
 * @brief Delay between MQTT publishes. Note that the receive loop also has a
 * timeout, so the total time between publishes is the sum of the two delays. The
 * keep-alive delay is added here so the keep-alive timer callback executes.
 */
#define mqttexampleDELAY_BETWEEN_PUBLISHES          ( mqttexampleKEEP_ALIVE_DELAY + pdMS_TO_TICKS( 500U ) )

/**
 * @brief Transport timeout in milliseconds for transport send and receive.
 */
#define TRANSPORT_SEND_RECV_TIMEOUT_MS              ( 200U )

/*-----------------------------------------------------------*/

/**
 * @brief A PINGREQ packet is always 2 bytes in size, defined by MQTT 3.1.1 spec.
 */
#define MQTT_PACKET_PINGREQ_SIZE    ( 2U )

/*-----------------------------------------------------------*/

#define _MILLISECONDS_PER_SECOND    ( 1000U )                                                         /**< @brief Milliseconds per second. */
#define _MILLISECONDS_PER_TICK      ( _MILLISECONDS_PER_SECOND / configTICK_RATE_HZ )                 /**< Milliseconds per FreeRTOS tick. */

/*-----------------------------------------------------------*/

/**
 * @brief The task used to demonstrate the MQTT API.
 *
 * @param[in] pvParameters Parameters as passed at the time of task creation. Not
 * used in this example.
 */
static void prvMQTTDemoTask( void * pvParameters );

/**
 * @brief Sends an MQTT Connect packet over the already connected TCP socket.
 *
 * @param pxMQTTContext MQTT context pointer.
 * @param xNetworkContext network context.
 *
 */
static void prvCreateMQTTConnectionWithBroker( MQTTContext_t * pxMQTTContext,
                                               NetworkContext_t * pxNetworkContext );

/**
 * @brief Subscribes to the topic as specified in mqttexampleTOPIC at the top of
 * this file.
 *
 * @param pxMQTTContext MQTT context pointer.
 */
static void prvMQTTSubscribeToTopic( MQTTContext_t * pxMQTTContext );

/**
 * @brief  Publishes a message mqttexampleMESSAGE on mqttexampleTOPIC topic.
 *
 * @param pxMQTTContext MQTT context pointer.
 */
static void prvMQTTPublishToTopic( MQTTContext_t * pxMQTTContext );

/**
 * @brief Unsubscribes from the previously subscribed topic as specified
 * in mqttexampleTOPIC.
 *
 * @param pxMQTTContext MQTT context pointer.
 */
static void prvMQTTUnsubscribeFromTopic( MQTTContext_t * pxMQTTContext );

/**
 * @brief The timer query function provided to the MQTT context.
 *
 * @return Time in milliseconds.
 */
static uint32_t prvGetTimeMs( void );

/**
 * @brief Process a response or ack to an MQTT request (PING, SUBSCRIBE
 * or UNSUBSCRIBE). This function processes PINGRESP, SUBACK, UNSUBACK
 *
 * @param pxIncomingPacket is a pointer to structure containing deserialized
 * MQTT response.
 * @param usPacketId is the packet identifier from the ack received.
 */
static void prvMQTTProcessResponse( MQTTPacketInfo_t * pxIncomingPacket,
                                    uint16_t usPacketId );

/**
 * @brief Process incoming Publish message.
 *
 * @param pxPublishInfo is a pointer to structure containing deserialized
 * Publish message.
 */
static void prvMQTTProcessIncomingPublish( MQTTPublishInfo_t * pxPublishInfo );

/**
 * @brief Check if the amount of time waiting for PINGRESP has exceeded
 * the specified timeout, then reset the keep-alive timer.
 *
 * This should only be called after a control packet has been sent.
 *
 * @param pxTimer The auto-reload software timer for handling keep alive.
 *
 * @return The status returned by #xTimerReset.
 */
static BaseType_t prvCheckTimeoutThenResetTimer( TimerHandle_t pxTimer );

/**
 * @brief This callback is invoked through an auto-reload software timer.
 *
 * Its responsibility is to send a PINGREQ packet if a PINGRESP is not pending
 * and no control packets have been sent after some given interval.
 *
 * @param pxTimer The auto-reload software timer for handling keep alive.
 */
static void prvKeepAliveTimerCallback( TimerHandle_t pxTimer );

/**
 * @brief The application callback function for getting the incoming publish
 * and incoming acks reported from the MQTT library.
 *
 * @param pxMQTTContext MQTT context pointer.
 * @param pxPacketInfo Packet Info pointer for the incoming packet.
 * @param usPacketIdentifier Packet identifier of the incoming packet.
 * @param pxPublishInfo Deserialized publish info pointer for the incoming
 * packet.
 */
static void prvEventCallback( MQTTContext_t * pxMQTTContext,
                              MQTTPacketInfo_t * pxPacketInfo,
                              uint16_t usPacketIdentifier,
                              MQTTPublishInfo_t * pxPublishInfo );

/*-----------------------------------------------------------*/

/**
 * @brief Static buffer used to hold MQTT messages being sent and received.
 */
static uint8_t ucSharedBuffer[ mqttexampleSHARED_BUFFER_SIZE ];

/**
 * @brief Static buffer used to hold PINGREQ messages to be sent.
 */
static uint8_t ucPingReqBuffer[ MQTT_PACKET_PINGREQ_SIZE ];

/**
 * @brief Global entry time into the application to use as a reference timestamp
 * in the #prvGetTimeMs function. #prvGetTimeMs will always return the difference
 * between the current time and the global entry time. This will reduce the chances
 * of overflow for the 32 bit unsigned integer used for holding the timestamp.
 */
static uint32_t ulGlobalEntryTimeMs;

/**
 * @brief Packet Identifier generated when Subscribe request was sent to the broker;
 * it is used to match received Subscribe ACK to the transmitted ACK.
 */
static uint16_t usSubscribePacketIdentifier;

/**
 * @brief Packet Identifier generated when Unsubscribe request was sent to the broker;
 * it is used to match received Unsubscribe response to the transmitted unsubscribe
 * request.
 */
static uint16_t usUnsubscribePacketIdentifier;

/**
 * @brief Timer to handle the MQTT keep-alive mechanism.
 */
static TimerHandle_t xKeepAliveTimer;

/**
 * @brief Storage space for xKeepAliveTimer.
 */
static StaticTimer_t xKeepAliveTimerBuffer;

/**
 * @brief Set to true when PINGREQ is sent then false when PINGRESP is received.
 */
static volatile bool xWaitingForPingResp = false;

/**
 * @brief The last time when a PINGREQ was sent over the network.
 */
static uint32_t ulPingReqSendTimeMs;

/**
 * @brief Timeout for a pending PINGRESP from the MQTT broker.
 */
static uint32_t ulPingRespTimeoutMs = ( mqttexampleKEEP_ALIVE_TIMEOUT_SECONDS / 4 ) * _MILLISECONDS_PER_SECOND;

/**
 * @brief Static buffer used to hold an MQTT PINGREQ packet for keep-alive mechanism.
 */
const static MQTTFixedBuffer_t xPingReqBuffer =
{
    .pBuffer = ucPingReqBuffer,
    .size    = MQTT_PACKET_PINGREQ_SIZE
};

/** @brief Static buffer used to hold MQTT messages being sent and received. */
static MQTTFixedBuffer_t xBuffer =
{
    .pBuffer = ucSharedBuffer,
    .size    = mqttexampleSHARED_BUFFER_SIZE
};

/*-----------------------------------------------------------*/

/**
 * @brief Create the task that demonstrates the Plain text MQTT API Demo.
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
                 NULL );                   /* Used to pass out a handle to the created task - not used in this case. */
}
/*-----------------------------------------------------------*/

static void prvMQTTDemoTask( void * pvParameters )
{
    uint32_t ulPublishCount = 0U;
    const uint32_t ulMaxPublishCount = 5UL;
    NetworkContext_t xNetworkContext = { 0 };
    MQTTContext_t xMQTTContext;
    MQTTStatus_t xMQTTStatus;
    BaseType_t xTimerStatus;
    BaseType_t xNetworkStatus;

    /* Remove compiler warnings about unused parameters. */
    ( void ) pvParameters;

    ulGlobalEntryTimeMs = prvGetTimeMs();

    /* Create a mutex to lock the MQTT Context in case of . */

    /* Serialize a PINGREQ packet to send upon invoking the keep-alive timer callback. */
    xMQTTStatus = MQTT_SerializePingreq( &xPingReqBuffer );
    configASSERT( xMQTTStatus == MQTTSuccess );

    for( ; ; )
    {
        /****************************** Connect. ******************************/

        /* Establish a TCP connection with the MQTT broker. This example connects to
         * the MQTT broker as specified in democonfigMQTT_BROKER_ENDPOINT and
         * democonfigMQTT_BROKER_PORT at the top of this file. */
        LogInfo( ( "Create a TCP connection to %s.\r\n", democonfigMQTT_BROKER_ENDPOINT ) );
        xNetworkStatus = Plaintext_FreeRTOS_Connect( &xNetworkContext,
                                                     democonfigMQTT_BROKER_ENDPOINT,
                                                     democonfigMQTT_BROKER_PORT,
                                                     TRANSPORT_SEND_RECV_TIMEOUT_MS,
                                                     TRANSPORT_SEND_RECV_TIMEOUT_MS );
        configASSERT( xNetworkStatus == 0 );

        /* Sends an MQTT Connect packet over the already connected TCP socket,
         * and waits for connection acknowledgment (CONNACK) packet. */
        LogInfo( ( "Creating an MQTT connection to %s.\r\n", democonfigMQTT_BROKER_ENDPOINT ) );
        prvCreateMQTTConnectionWithBroker( &xMQTTContext, &xNetworkContext );

        /* Create an auto-reload timer to handle keep-alive. */
        xKeepAliveTimer = xTimerCreateStatic( "KeepAliveTimer",
                                              mqttexampleKEEP_ALIVE_DELAY,
                                              pdTRUE,
                                              ( void * ) &xMQTTContext.transportInterface,
                                              prvKeepAliveTimerCallback,
                                              &xKeepAliveTimerBuffer );
        configASSERT( xKeepAliveTimer );

        /* Start the timer for keep alive. */
        xTimerStatus = xTimerStart( xKeepAliveTimer, 0 );
        configASSERT( xTimerStatus == pdPASS );

        /**************************** Subscribe. ******************************/

        /* The client is now connected to the broker. Subscribe to the topic
         * as specified in mqttexampleTOPIC at the top of this file by sending a
         * subscribe packet then waiting for a subscribe acknowledgment (SUBACK).
         * This client will then publish to the same topic it subscribed to, so it
         * will expect all the messages it sends to the broker to be sent back to it
         * from the broker. This demo uses QOS0 in Subscribe, therefore, the Publish
         * messages received from the broker will have QOS0. */
        LogInfo( ( "Attempt to subscribe to the MQTT topic %s.\r\n", mqttexampleTOPIC ) );
        prvMQTTSubscribeToTopic( &xMQTTContext );

        /* Process incoming packet from the broker. After sending the subscribe, the
         * client may receive a publish before it receives a subscribe ack. Therefore,
         * call generic incoming packet processing function. Since this demo is
         * subscribing to the topic to which no one is publishing, probability of
         * receiving Publish message before subscribe ack is zero; but application
         * must be ready to receive any packet.  This demo uses the generic packet
         * processing function everywhere to highlight this fact. */
        xMQTTStatus = MQTT_ReceiveLoop( &xMQTTContext, mqttexampleRECEIVE_LOOP_TIMEOUT_MS );
        configASSERT( xMQTTStatus == MQTTSuccess );

        /**************************** Publish and Receive Loop. ******************************/
        /* Publish messages with QOS0, send and process Keep alive messages. */
        for( ulPublishCount = 0; ulPublishCount < ulMaxPublishCount; ulPublishCount++ )
        {
            LogInfo( ( "Publish to the MQTT topic %s.\r\n", mqttexampleTOPIC ) );
            prvMQTTPublishToTopic( &xMQTTContext );

            /* Process incoming publish echo, since application subscribed to the same
             * topic the broker will send publish message back to the application. */
            LogInfo( ( "Attempt to receive publish message from broker.\r\n" ) );
            xMQTTStatus = MQTT_ReceiveLoop( &xMQTTContext, mqttexampleRECEIVE_LOOP_TIMEOUT_MS );
            configASSERT( xMQTTStatus == MQTTSuccess );

            /* Leave Connection Idle for some time. */
            LogInfo( ( "Keeping Connection Idle...\r\n\r\n" ) );
            vTaskDelay( mqttexampleDELAY_BETWEEN_PUBLISHES );
        }

        /************************ Unsubscribe from the topic. **************************/
        LogInfo( ( "Unsubscribe from the MQTT topic %s.\r\n", mqttexampleTOPIC ) );
        prvMQTTUnsubscribeFromTopic( &xMQTTContext );

        /* Process Incoming packet from the broker. */
        xMQTTStatus = MQTT_ReceiveLoop( &xMQTTContext, mqttexampleRECEIVE_LOOP_TIMEOUT_MS );
        configASSERT( xMQTTStatus == MQTTSuccess );

        /**************************** Disconnect. ******************************/

        /* Send an MQTT Disconnect packet over the already connected TCP socket.
         * There is no corresponding response for the disconnect packet. After sending
         * disconnect, client must close the network connection. */
        LogInfo( ( "Disconnecting the MQTT connection with %s.\r\n", democonfigMQTT_BROKER_ENDPOINT ) );
        MQTT_Disconnect( &xMQTTContext );

        /* Stop the keep-alive timer for the next iteration. */
        xTimerStatus = xTimerStop( xKeepAliveTimer, 0 );
        configASSERT( xTimerStatus == pdPASS );

        /* Close the network connection.  */
        Plaintext_FreeRTOS_Disconnect( &xNetworkContext );

        /* Wait for some time between two iterations to ensure that we do not
         * bombard the public test mosquitto broker. */
        LogInfo( ( "prvMQTTDemoTask() completed an iteration successfully. Total free heap is %u.\r\n", xPortGetFreeHeapSize() ) );
        LogInfo( ( "Demo completed successfully.\r\n" ) );
        LogInfo( ( "Short delay before starting the next iteration.... \r\n\r\n" ) );
        vTaskDelay( mqttexampleDELAY_BETWEEN_DEMO_ITERATIONS );
    }
}
/*-----------------------------------------------------------*/

static void prvCreateMQTTConnectionWithBroker( MQTTContext_t * pxMQTTContext,
                                               NetworkContext_t * pxNetworkContext )
{
    MQTTStatus_t xResult;
    MQTTConnectInfo_t xConnectInfo;
    bool xSessionPresent;
    TransportInterface_t xTransport;
    MQTTApplicationCallbacks_t xCallbacks;

    /***
     * For readability, error handling in this function is restricted to the use of
     * asserts().
     ***/

    /* Fill in Transport Interface send and receive function pointers. */
    xTransport.pNetworkContext = pxNetworkContext;
    xTransport.send = Plaintext_FreeRTOS_send;
    xTransport.recv = Plaintext_FreeRTOS_recv;

    /* Application callbacks for receiving incoming published and incoming acks
     * from MQTT library. */
    xCallbacks.appCallback = prvEventCallback;
    xCallbacks.getTime = prvGetTimeMs;

    /* Initialize MQTT library. */
    xResult = MQTT_Init( pxMQTTContext, &xTransport, &xCallbacks, &xBuffer );
    configASSERT( xResult == MQTTSuccess );

    /* Many fields not used in this demo so start with everything at 0. */
    memset( ( void * ) &xConnectInfo, 0x00, sizeof( xConnectInfo ) );

    /* Start with a clean session i.e. direct the MQTT broker to discard any
     * previous session data. Also, establishing a connection with clean session
     * will ensure that the broker does not store any data when this client
     * gets disconnected. */
    xConnectInfo.cleanSession = true;

    /* The client identifier is used to uniquely identify this MQTT client to
     * the MQTT broker. In a production device the identifier can be something
     * unique, such as a device serial number. */
    xConnectInfo.pClientIdentifier = democonfigCLIENT_IDENTIFIER;
    xConnectInfo.clientIdentifierLength = ( uint16_t ) strlen( democonfigCLIENT_IDENTIFIER );

    /* Set MQTT keep-alive period. It is the responsibility of the application to ensure
     * that the interval between Control Packets being sent does not exceed the Keep Alive value.
     * In the absence of sending any other Control Packets, the Client MUST send a PINGREQ Packet. */
    xConnectInfo.keepAliveSeconds = mqttexampleKEEP_ALIVE_TIMEOUT_SECONDS;

    /* Send MQTT CONNECT packet to broker. LWT is not used in this demo, so it
     * is passed as NULL. */
    xResult = MQTT_Connect( pxMQTTContext,
                            &xConnectInfo,
                            NULL,
                            mqttexampleCONNACK_RECV_TIMEOUT_MS,
                            &xSessionPresent );
    configASSERT( xResult == MQTTSuccess );
}
/*-----------------------------------------------------------*/

static void prvMQTTSubscribeToTopic( MQTTContext_t * pxMQTTContext )
{
    MQTTStatus_t xResult;
    MQTTSubscribeInfo_t xMQTTSubscription[ 1 ];
    BaseType_t xTimerStatus;

    /***
     * For readability, error handling in this function is restricted to the use of
     * asserts().
     ***/

    /* Some fields not used by this demo so start with everything at 0. */
    ( void ) memset( ( void * ) &xMQTTSubscription, 0x00, sizeof( xMQTTSubscription ) );

    /* Subscribe to the mqttexampleTOPIC topic filter. This example subscribes to
     * only one topic and uses QOS0. */
    xMQTTSubscription[ 0 ].qos = MQTTQoS0;
    xMQTTSubscription[ 0 ].pTopicFilter = mqttexampleTOPIC;
    xMQTTSubscription[ 0 ].topicFilterLength = ( uint16_t ) strlen( mqttexampleTOPIC );

    /* Get a unique packet id. */
    usSubscribePacketIdentifier = MQTT_GetPacketId( pxMQTTContext );

    /* Send SUBSCRIBE packet. */
    xResult = MQTT_Subscribe( pxMQTTContext,
                              xMQTTSubscription,
                              sizeof( xMQTTSubscription ) / sizeof( MQTTSubscribeInfo_t ),
                              usSubscribePacketIdentifier );
    configASSERT( xResult == MQTTSuccess );

    /* When a SUBSCRIBE packet has been sent, the keep-alive timer can be reset. */
    xTimerStatus = prvCheckTimeoutThenResetTimer( xKeepAliveTimer );
    configASSERT( xTimerStatus == pdPASS );
}
/*-----------------------------------------------------------*/

static void prvMQTTPublishToTopic( MQTTContext_t * pxMQTTContext )
{
    MQTTStatus_t xResult;
    MQTTPublishInfo_t xMQTTPublishInfo;
    BaseType_t xTimerStatus;

    /***
     * For readability, error handling in this function is restricted to the use of
     * asserts().
     ***/

    /* Some fields not used by this demo so start with everything at 0. */
    ( void ) memset( ( void * ) &xMQTTPublishInfo, 0x00, sizeof( xMQTTPublishInfo ) );

    /* This demo uses QOS0 */
    xMQTTPublishInfo.qos = MQTTQoS0;
    xMQTTPublishInfo.retain = false;
    xMQTTPublishInfo.pTopicName = mqttexampleTOPIC;
    xMQTTPublishInfo.topicNameLength = ( uint16_t ) strlen( mqttexampleTOPIC );
    xMQTTPublishInfo.pPayload = mqttexampleMESSAGE;
    xMQTTPublishInfo.payloadLength = strlen( mqttexampleMESSAGE );

    /* Send PUBLISH packet. Packet ID is not used for a QoS0 publish. */
    xResult = MQTT_Publish( pxMQTTContext, &xMQTTPublishInfo, 0U );
    configASSERT( xResult == MQTTSuccess );

    /* When a PUBLISH packet has been sent, the keep-alive timer can be reset. */
    xTimerStatus = prvCheckTimeoutThenResetTimer( xKeepAliveTimer );
    configASSERT( xTimerStatus == pdPASS );
}
/*-----------------------------------------------------------*/

static void prvMQTTUnsubscribeFromTopic( MQTTContext_t * pxMQTTContext )
{
    MQTTStatus_t xResult;
    MQTTSubscribeInfo_t xMQTTSubscription[ 1 ];
    BaseType_t xTimerStatus;

    /* Some fields not used by this demo so start with everything at 0. */
    memset( ( void * ) &xMQTTSubscription, 0x00, sizeof( xMQTTSubscription ) );

    /* Unsubscribe to the mqttexampleTOPIC topic filter. */
    xMQTTSubscription[ 0 ].qos = MQTTQoS0;
    xMQTTSubscription[ 0 ].pTopicFilter = mqttexampleTOPIC;
    xMQTTSubscription[ 0 ].topicFilterLength = ( uint16_t ) strlen( mqttexampleTOPIC );

    /* Get next unique packet identifier */
    usUnsubscribePacketIdentifier = MQTT_GetPacketId( pxMQTTContext );
    /* Make sure the packet id obtained is valid. */
    configASSERT( usUnsubscribePacketIdentifier != 0 );

    /* Send UNSUBSCRIBE packet. */
    xResult = MQTT_Unsubscribe( pxMQTTContext,
                                xMQTTSubscription,
                                sizeof( xMQTTSubscription ) / sizeof( MQTTSubscribeInfo_t ),
                                usUnsubscribePacketIdentifier );
    configASSERT( xResult == MQTTSuccess );

    /* When an UNSUBSCRIBE packet has been sent, the keep-alive timer can be reset. */
    xTimerStatus = prvCheckTimeoutThenResetTimer( xKeepAliveTimer );
    configASSERT( xTimerStatus == pdPASS );
}
/*-----------------------------------------------------------*/

static void prvMQTTProcessResponse( MQTTPacketInfo_t * pxIncomingPacket,
                                    uint16_t usPacketId )
{
    switch( pxIncomingPacket->type )
    {
        case MQTT_PACKET_TYPE_SUBACK:
            LogInfo( ( "Subscribed to the topic %s.\r\n", mqttexampleTOPIC ) );
            /* Make sure ACK packet identifier matches with Request packet identifier. */
            configASSERT( usSubscribePacketIdentifier == usPacketId );
            break;

        case MQTT_PACKET_TYPE_UNSUBACK:
            LogInfo( ( "Unsubscribed from the topic %s.\r\n", mqttexampleTOPIC ) );
            /* Make sure ACK packet identifier matches with Request packet identifier. */
            configASSERT( usUnsubscribePacketIdentifier == usPacketId );
            break;

        case MQTT_PACKET_TYPE_PINGRESP:
            xWaitingForPingResp = false;
            LogInfo( ( "Ping Response successfully received.\r\n" ) );
            break;

        /* Any other packet type is invalid. */
        default:
            LogWarn( ( "prvMQTTProcessResponse() called with unknown packet type:(%02X).\r\n",
                       pxIncomingPacket->type ) );
    }
}

/*-----------------------------------------------------------*/

static void prvMQTTProcessIncomingPublish( MQTTPublishInfo_t * pxPublishInfo )
{
    configASSERT( pxPublishInfo != NULL );

    /* Process incoming Publish. */
    LogInfo( ( "Incoming QoS : %d\n", pxPublishInfo->qos ) );

    /* Verify the received publish is for the we have subscribed to. */
    if( ( pxPublishInfo->topicNameLength == strlen( mqttexampleTOPIC ) ) &&
        ( 0 == strncmp( mqttexampleTOPIC, pxPublishInfo->pTopicName, pxPublishInfo->topicNameLength ) ) )
    {
        LogInfo( ( "\r\nIncoming Publish Topic Name: %.*s matches subscribed topic.\r\n"
                   "Incoming Publish Message : %.*s\r\n",
                   pxPublishInfo->topicNameLength,
                   pxPublishInfo->pTopicName,
                   pxPublishInfo->payloadLength,
                   pxPublishInfo->pPayload ) );
    }
    else
    {
        LogInfo( ( "Incoming Publish Topic Name: %.*s does not match subscribed topic.\r\n",
                   pxPublishInfo->topicNameLength,
                   pxPublishInfo->pTopicName ) );
    }
}

/*-----------------------------------------------------------*/

static BaseType_t prvCheckTimeoutThenResetTimer( TimerHandle_t pxTimer )
{
    uint32_t now = 0U;

    if( xWaitingForPingResp == true )
    {
        now = prvGetTimeMs();
        /* Assert that the PINGRESP timeout has not expired. */
        configASSERT( ( now - ulPingReqSendTimeMs ) <= ulPingRespTimeoutMs );
    }

    return xTimerReset( pxTimer, 0 );
}

/*-----------------------------------------------------------*/

static void prvKeepAliveTimerCallback( TimerHandle_t pxTimer )
{
    TransportInterface_t * pxTransport;
    int32_t xTransportStatus;
    uint32_t now = 0U;

    pxTransport = ( TransportInterface_t * ) pvTimerGetTimerID( pxTimer );

    if( xWaitingForPingResp == true )
    {
        now = prvGetTimeMs();
        /* Assert that the PINGRESP timeout has not expired. */
        configASSERT( ( now - ulPingReqSendTimeMs ) <= ulPingRespTimeoutMs );
    }
    else
    {
        /* Send Ping Request to the broker. */
        LogInfo( ( "Attempt to ping the MQTT broker.\r\n" ) );
        xTransportStatus = pxTransport->send( pxTransport->pNetworkContext,
                                              ( void * ) xPingReqBuffer.pBuffer,
                                              xPingReqBuffer.size );
        configASSERT( ( size_t ) xTransportStatus == xPingReqBuffer.size );

        ulPingReqSendTimeMs = prvGetTimeMs();
        xWaitingForPingResp = true;
    }
}

/*-----------------------------------------------------------*/

static void prvEventCallback( MQTTContext_t * pxMQTTContext,
                              MQTTPacketInfo_t * pxPacketInfo,
                              uint16_t usPacketIdentifier,
                              MQTTPublishInfo_t * pxPublishInfo )
{
    /* The MQTT context is not used for this demo. */
    ( void ) pxMQTTContext;

    if( ( pxPacketInfo->type & 0xF0U ) == MQTT_PACKET_TYPE_PUBLISH )
    {
        prvMQTTProcessIncomingPublish( pxPublishInfo );
    }
    else
    {
        prvMQTTProcessResponse( pxPacketInfo, usPacketIdentifier );
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
    ulTimeMs = ( uint32_t ) xTickCount * _MILLISECONDS_PER_TICK;

    /* Reduce ulGlobalEntryTimeMs from obtained time so as to always return the
     * elapsed time in the application. */
    ulTimeMs = ( uint32_t ) ( ulTimeMs - ulGlobalEntryTimeMs );

    return ulTimeMs;
}

/*-----------------------------------------------------------*/
