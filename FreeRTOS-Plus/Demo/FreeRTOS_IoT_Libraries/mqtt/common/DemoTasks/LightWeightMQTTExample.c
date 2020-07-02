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
 * Demo for showing use of the MQTT light weight serializer API.
 * The Light weight serializer API lets user to serialize and
 * deserialize MQTT messages into a user provided buffer.
 * This API allows use of a statically allocated buffer.
 *
 * The Example shown below uses this API to create MQTT messages and
 * send them over the connection established using FreeRTOS sockets.
 * The example is single threaded and uses statically allocated memory;
 * it uses QOS0 and therefore does not implement any retransmission
 * mechanism for Publish messages.
 *
 * !!! NOTE !!!
 * This is work in progress to show how the light weight serializer
 * API can be used. This is not a complete demo, and should not
 * be treated as production ready code.
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

/* IoT SDK includes. */
#include "iot_mqtt_protocol.h"
#include "iot_mqtt_lightweight.h"
#include "platform/iot_network_freertos.h"

/* Demo Specific configs. */
#include "mqtt_demo_profile.h"


/**
 * @brief Time to wait between each cycle of the demo implemented by prvMQTTDemoTask().
 */
#define mqttexampleDELAY_BETWEEN_DEMO_ITERATIONS    ( pdMS_TO_TICKS( 5000 ) )

/**
 * @brief Time to wait before sending ping request to keep MQTT connection alive.
 */
#define mqttexampleKEEP_ALIVE_DELAY                 ( pdMS_TO_TICKS( 1000 ) )


/**
 * @brief The MQTT client identifier used in this example.  Each client identifier
 * must be unique so edit as required to ensure no two clients connecting to the
 * same broker use the same client identifier.
 */
#define mqttexampleCLIENT_IDENTIFIER       mqttdemoprofileCLIENT_IDENTIFIER

/**
 * @brief Details of the MQTT broker to connect to.
 */
#define mqttexampleMQTT_BROKER_ENDPOINT    mqttdemoprofileBROKER_ENDPOINT

/**
 * @brief The port to use for the demo.
 */
#define mqttexampleMQTT_BROKER_PORT        mqttdemoprofileBROKER_PORT

/**
 * @brief The topic to subscribe and publish to in the example.
 *
 * The topic name starts with the client identifier to ensure that each demo
 * interacts with a unique topic name.
 */
#define mqttexampleTOPIC                   mqttexampleCLIENT_IDENTIFIER "/example/topic"

/**
 * @brief The MQTT message published in this example.
 */
#define mqttexampleMESSAGE                 "Hello Light Weight MQTT World!"

/**
 * @brief Dimensions a file scope buffer currently used to send and receive MQTT data
 * from a socket.
 */
#define mqttexampleSHARED_BUFFER_SIZE      500

/*-----------------------------------------------------------*/

/**
 * @brief The task used to demonstrate the light weight MQTT API.
 *
 * @param[in] pvParameters Parameters as passed at the time of task creation. Not
 * used in this example.
 */
static void prvMQTTDemoTask( void * pvParameters );

/**
 * @brief Creates a TCP connection to the MQTT broker as specified by
 * mqttexampleMQTT_BROKER_ENDPOINT and mqttexampleMQTT_BROKER_PORT defined at the
 * top of this file.
 *
 * @return On success the socket connected to the MQTT broker is returned.
 *
 */
static Socket_t prvCreateTCPConnectionToBroker( void );

/**
 * @brief Sends an MQTT Connect packet over the already connected TCP socket.
 *
 * @param xMQTTSocket is a TCP socket that is connected to an MQTT broker.
 *
 */
static void prvCreateMQTTConnectionWithBroker( Socket_t xMQTTSocket );

/**
 * @brief Performs a graceful shutdown and close of the socket passed in as its
 * parameter.
 *
 * @param xMQTTSocket is a TCP socket that is connected to an MQTT broker to which
 * an MQTT connection has been established.
 */
static void prvGracefulShutDown( Socket_t xSocket );

/**
 * @brief Subscribes to the topic as specified in mqttexampleTOPIC at the top oc
 * this file.
 *
 * @param xMQTTSocket is a TCP socket that is connected to an MQTT broker to which
 * an MQTT connection has been established.
 */
static void prvMQTTSubscribeToTopic( Socket_t xMQTTSocket );

/**
 * @brief  Publishes a message mqttexampleMESSAGE on mqttexampleTOPIC topic.
 *
 * @param xMQTTSocket is a TCP socket that is connected to an MQTT broker to which
 * an MQTT connection has been established.
 */
static void prvMQTTPublishToTopic( Socket_t xMQTTSocket );

/**
 * @brief Unsubscribes from the previously subscribed topic as specified
 * in mqttexampleTOPIC.
 *
 * @param xMQTTSocket is a TCP socket that is connected to an MQTT broker to which
 * an MQTT connection has been established.
 */
static void prvMQTTUnsubscribeFromTopic( Socket_t xMQTTSocket );

/**
 * @brief Send MQTT Ping Request to the broker.
 * Ping request is used to keep connection to the broker alive.
 *
 * @param xMQTTSocket is a TCP socket that is connected to an MQTT broker to which
 * an MQTT connection has been established.
 */
static void prvMQTTKeepAlive( Socket_t xMQTTSocket );

/**
 * @brief Disconnect From the MQTT broker.
 *
 * @param xMQTTSocket is a TCP socket that is connected to an MQTT broker to which
 * an MQTT connection has been established.
 */
static void prvMQTTDisconnect( Socket_t xMQTTSocket );

/**
 * @brief Process a response or ack to an MQTT request (PING, SUBSCRIBE
 * or UNSUBSCRIBE). This function processes PING_RESP, SUB_ACK, UNSUB_ACK
 *
 * @param pxIncomingPacket is a pointer to structure containing deserialized
 * MQTT response.
 */
static void prvMQTTProcessResponse( IotMqttPacketInfo_t * pxIncomingPacket );

/**
 * @brief Process incoming Publish message.
 *
 * @param pxIncomingPacket is a pointer to structure containing deserialized
 * Publish message.
 */
static void prvMQTTProcessIncomingPublish( IotMqttPacketInfo_t * pxIncomingPacket );

/**
 * @brief Receive and validate MQTT packet from the broker, determine the type
 * of the packet and processes the packet based on the type.
 *
 * @param xMQTTSocket is a TCP socket that is connected to an MQTT broker to which
 * an MQTT connection has been established.
 *
 */
static void prvMQTTProcessIncomingPacket( Socket_t xMQTTSocket );

/*-----------------------------------------------------------*/

/**
 * @brief Function to receive next byte from network,
 * The declaration must match IotMqttGetNextByte_t.
 *
 * @param[in] pvContext Network Connection context. Implementation in this
 * file uses FreeRTOS socket.
 * @param[in, out] pNextBye Pointer to buffer where the byte will be stored.
 *
 * @return #IOT_MQTT_SUCCESS or #IOT_MQTT_TIMEOUT
 */

static IotMqttError_t getNextByte( IotNetworkConnection_t pvContext,
                                   uint8_t * pNextByte );

/*-----------------------------------------------------------*/

/* @brief Static buffer used to hold MQTT messages being sent and received. */
static uint8_t ucSharedBuffer[ mqttexampleSHARED_BUFFER_SIZE ];

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
 * @brief Packet Identifier generated when Publish message was sent to the broker;
 * it is use to match incoming Publish acknowledgment message to the transmitted
 * publish.
 */
static uint16_t usPublishPacketIdentifier;

/*-----------------------------------------------------------*/

/*
 * @brief Create the task that demonstrates the Light Weight MQTT API Demo.
 */
void vStartSimpleMQTTDemo( void )
{
    /* This example uses a single application task, which in turn is used to
     * connect, subscribe, publish, unsubscribe and disconnect from the MQTT
     * broker. */
    xTaskCreate( prvMQTTDemoTask,          /* Function that implements the task. */
                 "MQTTLWDemo",             /* Text name for the task - only used for debugging. */
                 democonfigDEMO_STACKSIZE, /* Size of stack (in words, not bytes) to allocate for the task. */
                 NULL,                     /* Task parameter - not used in this case. */
                 tskIDLE_PRIORITY,         /* Task priority, must be between 0 and configMAX_PRIORITIES - 1. */
                 NULL );                   /* Used to pass out a handle to the created task - not used in this case. */
}
/*-----------------------------------------------------------*/

static void prvGracefulShutDown( Socket_t xSocket )
{
    uint8_t          ucDummy[ 20 ];
    const TickType_t xShortDelay = pdMS_TO_MIN_TICKS( 250 );

    if( xSocket != ( Socket_t ) 0 )
    {
        if( xSocket != FREERTOS_INVALID_SOCKET )
        {
            /* Initiate graceful shutdown. */
            FreeRTOS_shutdown( xSocket, FREERTOS_SHUT_RDWR );

            /* Wait for the socket to disconnect gracefully (indicated by FreeRTOS_recv()
             * returning a FREERTOS_EINVAL error) before closing the socket. */
            while( FreeRTOS_recv( xSocket, ucDummy, sizeof( ucDummy ), 0 ) >= 0 )
            {
                /* Wait for shutdown to complete.  If a receive block time is used then
                 * this delay will not be necessary as FreeRTOS_recv() will place the RTOS task
                 * into the Blocked state anyway. */
                vTaskDelay( xShortDelay );

                /* Note a real applications should implement a timeout here, not just
                 * loop forever. */
            }

            /* The socket has shut down and is safe to close. */
            FreeRTOS_closesocket( xSocket );
        }
    }
}
/*-----------------------------------------------------------*/

static IotMqttError_t getNextByte( IotNetworkConnection_t pvContext,
                                   uint8_t * pNextByte )
{
    Socket_t       xMQTTSocket = ( Socket_t ) pvContext;
    BaseType_t     receivedBytes;
    IotMqttError_t result;

    /* Receive one byte from network.  Note the use of this function may be
     * deprecated before the final light weight API release. */
    receivedBytes = FreeRTOS_recv( xMQTTSocket, ( void * ) pNextByte, sizeof( uint8_t ), 0 );

    if( receivedBytes == sizeof( uint8_t ) )
    {
        result = IOT_MQTT_SUCCESS;
    }
    else
    {
        result = IOT_MQTT_TIMEOUT;
    }

    return result;
}
/*-----------------------------------------------------------*/

static void prvMQTTDemoTask( void * pvParameters )
{
    Socket_t       xMQTTSocket;
    uint32_t       ulPublishCount    = 0;
    const uint32_t ulMaxPublishCount = 5UL;

    /* Remove compiler warnings about unused parameters. */
    ( void ) pvParameters;

    for( ; ; )
    {
        /****************************** Connect. ******************************/

        /* Establish a TCP connection with the MQTT broker. This example connects to
         * the MQTT broker as specified in mqttexampleMQTT_BROKER_ENDPOINT and
         * mqttexampleMQTT_BROKER_PORT at the top of this file. */
        configPRINTF( ( "Create a TCP connection to %s\r\n", mqttexampleMQTT_BROKER_ENDPOINT ) );
        xMQTTSocket = prvCreateTCPConnectionToBroker();

        /* Sends an MQTT Connect packet over the already connected TCP socket
         * xMQTTSocket, and waits for connection acknowledgment (CONNACK) packet. */
        configPRINTF( ( "Creating an MQTT connection to %s\r\n", mqttexampleMQTT_BROKER_ENDPOINT ) );
        prvCreateMQTTConnectionWithBroker( xMQTTSocket );

        /**************************** Subscribe. ******************************/

        /* The client is now connected to the broker. Subscribe to the topic
         * as specified in mqttexampleTOPIC at the top of this file by sending a
         * subscribe packet then waiting for a subscribe acknowledgment (SUBACK).
         * This client will then publish to the same topic it subscribed to, so it
         * will expect all the messages it sends to the broker to be sent back to it
         * from the broker. This demo uses QOS0 in Subscribe, therefore, the Publish
         * messages received from the broker will have QOS0. */
        configPRINTF( ( "Attempt to subscribed to the MQTT topic %s\r\n", mqttexampleTOPIC ) );
        prvMQTTSubscribeToTopic( xMQTTSocket );

        /* Process incoming packet from the broker. After sending the subscribe, the
         * client may receive a publish before it receives a subscribe ack. Therefore,
         * call generic incoming packet processing function. Since this demo is
         * subscribing to the topic to which no one is publishing, probability of
         * receiving Publish message before subscribe ack is zero; but application
         * must be ready to receive any packet.  This demo uses the generic packet
         * processing function everywhere to highlight this fact. */
        prvMQTTProcessIncomingPacket( xMQTTSocket );

        /**************************** Publish and Keep Alive Loop. ******************************/
        /* Publish messages with QOS0, send and process Keep alive messages. */
        for( ulPublishCount = 0; ulPublishCount < ulMaxPublishCount; ulPublishCount++ )
        {
            configPRINTF( ( "Publish to the MQTT topic %s\r\n", mqttexampleTOPIC ) );
            prvMQTTPublishToTopic( xMQTTSocket );

            /* Process incoming publish echo, since application subscribed to the same
             * topic the broker will send publish message back to the application. */
            configPRINTF( ( "Attempt to receive publish message from broker\r\n" ) );
            prvMQTTProcessIncomingPacket( xMQTTSocket );

            /* Leave Connection Idle for some time */
            configPRINTF( ( "Keeping Connection Idle\r\n" ) );
            vTaskDelay( pdMS_TO_TICKS( mqttexampleKEEP_ALIVE_DELAY ) );

            /* Send Ping request to broker and receive ping response */
            configPRINTF( ( "Sending Ping Request to the broker\r\n" ) );
            prvMQTTKeepAlive( xMQTTSocket );

            /* Process Incoming packet from the broker */
            prvMQTTProcessIncomingPacket( xMQTTSocket );
        }

        /************************ Unsubscribe from the topic. **************************/
        configPRINTF( ( "Unsubscribe from the MQTT topic %s.\r\n", mqttexampleTOPIC ) );
        prvMQTTUnsubscribeFromTopic( xMQTTSocket );

        /* Process Incoming packet from the broker. */
        prvMQTTProcessIncomingPacket( xMQTTSocket );

        /**************************** Disconnect. ******************************/

        /* Send an MQTT Disconnect packet over the already connected TCP socket.
         * There is no corresponding response for the disconnect packet. After sending
         * disconnect, client must close the network connection. */
        configPRINTF( ( "Disconnecting the MQTT connection with %s.\r\n", mqttexampleMQTT_BROKER_ENDPOINT ) );
        prvMQTTDisconnect( xMQTTSocket );

        /* Close the network connection.  */
        prvGracefulShutDown( xMQTTSocket );

        /* Wait for some time between two iterations to ensure that we do not
         * bombard the public test mosquitto broker. */
        configPRINTF( ( "prvMQTTDemoTask() completed an iteration successfully. Total free heap is %u\r\n", xPortGetFreeHeapSize() ) );
        configPRINTF( ( "Demo completed successfully.\r\n" ) );
        configPRINTF( ( "Short delay before starting the next iteration.... \r\n\r\n" ) );
        vTaskDelay( pdMS_TO_TICKS( mqttexampleDELAY_BETWEEN_DEMO_ITERATIONS ) );
    }
}
/*-----------------------------------------------------------*/

static Socket_t prvCreateTCPConnectionToBroker( void )
{
    Socket_t                 xMQTTSocket = FREERTOS_INVALID_SOCKET;
    struct freertos_sockaddr xBrokerAddress;
    uint32_t                 ulBrokerIPAddress;
    BaseType_t               xStatus     = pdFAIL;

    /* This is the socket used to connect to the MQTT broker. */
    xMQTTSocket = FreeRTOS_socket( FREERTOS_AF_INET,
                                   FREERTOS_SOCK_STREAM,
                                   FREERTOS_IPPROTO_TCP );

    if( xMQTTSocket != FREERTOS_INVALID_SOCKET )
    {
        /* Socket was created.  Locate then connect to the MQTT broker. */
        ulBrokerIPAddress = FreeRTOS_gethostbyname( mqttexampleMQTT_BROKER_ENDPOINT );

        if( ulBrokerIPAddress != 0 )
        {
            xBrokerAddress.sin_port = FreeRTOS_htons( mqttexampleMQTT_BROKER_PORT );
            xBrokerAddress.sin_addr = ulBrokerIPAddress;

            if( FreeRTOS_connect( xMQTTSocket, &xBrokerAddress, sizeof( xBrokerAddress ) ) == 0 )
            {
                /* Connection was successful. */
                xStatus = pdPASS;
            }
            else
            {
                configPRINTF( ( "Located but could not connect to MQTT broker %s.\r\n\r\n", mqttexampleMQTT_BROKER_ENDPOINT ) );
            }
        }
        else
        {
            configPRINTF( ( "Could not locate MQTT broker %s.\r\n\r\n", mqttexampleMQTT_BROKER_ENDPOINT ) );
        }
    }
    else
    {
        configPRINTF( ( "Could not create TCP socket.\r\n\r\n" ) );
    }

    /* If the socket was created but the connection was not successful then delete
     * the socket again. */
    if( xStatus == pdFAIL )
    {
        if( xMQTTSocket != FREERTOS_INVALID_SOCKET )
        {
            FreeRTOS_closesocket( xMQTTSocket );
            xMQTTSocket = FREERTOS_INVALID_SOCKET;
        }
    }

    return xMQTTSocket;
}
/*-----------------------------------------------------------*/

static void prvCreateMQTTConnectionWithBroker( Socket_t xMQTTSocket )
{
    IotMqttConnectInfo_t xConnectInfo;
    size_t               xRemainingLength;
    size_t               xPacketSize;
    IotMqttError_t       xResult;
    IotMqttPacketInfo_t  xIncomingPacket;
    BaseType_t           xStatus;

    /***
     * For readability, error handling in this function is restricted to the use of
     * asserts().
     ***/

    /* Many fields not used in this demo so start with everything at 0. */
    memset( ( void * ) &xConnectInfo, 0x00, sizeof( xConnectInfo ) );

    /* Start with a clean session i.e. direct the MQTT broker to discard any
     * previous session data. Also, establishing a connection with clean session
     * will ensure that the broker does not store any data when this client
     * gets disconnected. */
    xConnectInfo.cleanSession           = true;

    /* The client identifier is used to uniquely identify this MQTT client to
     * the MQTT broker. In a production device the identifier can be something
     * unique, such as a device serial number. */
    xConnectInfo.pClientIdentifier      = mqttexampleCLIENT_IDENTIFIER;
    xConnectInfo.clientIdentifierLength = ( uint16_t ) strlen( mqttexampleCLIENT_IDENTIFIER );

    /* Get size requirement for the connect packet */
    xResult                             = IotMqtt_GetConnectPacketSize( &xConnectInfo, &xRemainingLength, &xPacketSize );

    /* Make sure the packet size is less than static buffer size. */
    configASSERT( xResult == IOT_MQTT_SUCCESS );
    configASSERT( xPacketSize < mqttexampleSHARED_BUFFER_SIZE );

    /* Serialize MQTT connect packet into the provided buffer. */
    xResult                             = IotMqtt_SerializeConnect( &xConnectInfo, xRemainingLength, ucSharedBuffer, xPacketSize );
    configASSERT( xResult == IOT_MQTT_SUCCESS );

    xStatus                             = FreeRTOS_send( xMQTTSocket, ( void * ) ucSharedBuffer, xPacketSize, 0 );
    configASSERT( xStatus == ( BaseType_t ) xPacketSize );

    /* Reset all fields of the incoming packet structure. */
    memset( ( void * ) &xIncomingPacket, 0x00, sizeof( IotMqttPacketInfo_t ) );

    /* Wait for connection acknowledgment.  We cannot assume received data is the
     * connection acknowledgment. Therefore this function reads type and remaining
     * length of the received packet, before processing entire packet - although in
     * this case to keep the example simple error checks are just performed by
     * asserts.
     */
    xResult                             = IotMqtt_GetIncomingMQTTPacketTypeAndLength( &xIncomingPacket, getNextByte, ( void * ) xMQTTSocket );
    configASSERT( xResult == IOT_MQTT_SUCCESS );
    configASSERT( xIncomingPacket.type == MQTT_PACKET_TYPE_CONNACK );
    configASSERT( xIncomingPacket.remainingLength <= mqttexampleSHARED_BUFFER_SIZE );

    /* Now receive the reset of the packet into the statically allocated buffer. */
    xStatus                             = FreeRTOS_recv( xMQTTSocket, ( void * ) ucSharedBuffer, xIncomingPacket.remainingLength, 0 );
    configASSERT( xStatus == ( BaseType_t ) xIncomingPacket.remainingLength );

    xIncomingPacket.pRemainingData      = ucSharedBuffer;
    xResult                             = IotMqtt_DeserializeResponse( &xIncomingPacket );

    configASSERT( xResult == IOT_MQTT_SUCCESS );

    if( xResult != IOT_MQTT_SUCCESS )
    {
        configPRINTF( ( "Connection with MQTT broker failed.\r\n" ) );
    }
}
/*-----------------------------------------------------------*/

static void prvMQTTSubscribeToTopic( Socket_t xMQTTSocket )
{
    IotMqttError_t        xResult;
    IotMqttSubscription_t xMQTTSubscription[ 1 ];
    size_t                xRemainingLength;
    size_t                xPacketSize;
    BaseType_t            xStatus;

    /***
     * For readability, error handling in this function is restricted to the use of
     * asserts().
     ***/

    /* Some fields not used by this demo so start with everything at 0. */
    memset( ( void * ) &xMQTTSubscription, 0x00, sizeof( xMQTTSubscription ) );

    /* Subscribe to the mqttexampleTOPIC topic filter. This example subscribes to
     * only one topic and uses QOS0. */
    xMQTTSubscription[ 0 ].qos               = IOT_MQTT_QOS_0;
    xMQTTSubscription[ 0 ].pTopicFilter      = mqttexampleTOPIC;
    xMQTTSubscription[ 0 ].topicFilterLength = ( uint16_t ) strlen( mqttexampleTOPIC );

    xResult                                  = IotMqtt_GetSubscriptionPacketSize( IOT_MQTT_SUBSCRIBE,
                                                                                  xMQTTSubscription,
                                                                                  sizeof( xMQTTSubscription ) / sizeof( IotMqttSubscription_t ),
                                                                                  &xRemainingLength, &xPacketSize );

    /* Make sure the packet size is less than static buffer size. */
    configASSERT( xResult == IOT_MQTT_SUCCESS );
    configASSERT( xPacketSize < mqttexampleSHARED_BUFFER_SIZE );

    /* Serialize subscribe into statically allocated ucSharedBuffer. */
    xResult                                  = IotMqtt_SerializeSubscribe( xMQTTSubscription,
                                                                           sizeof( xMQTTSubscription ) / sizeof( IotMqttSubscription_t ),
                                                                           xRemainingLength,
                                                                           &usSubscribePacketIdentifier,
                                                                           ucSharedBuffer,
                                                                           xPacketSize );

    configASSERT( xResult == IOT_MQTT_SUCCESS );

    /* Send Subscribe request to the broker. */
    xStatus                                  = FreeRTOS_send( xMQTTSocket, ( void * ) ucSharedBuffer, xPacketSize, 0 );
    configASSERT( xStatus == ( BaseType_t ) xPacketSize );
}
/*-----------------------------------------------------------*/

static void prvMQTTPublishToTopic( Socket_t xMQTTSocket )
{
    IotMqttError_t       xResult;
    IotMqttPublishInfo_t xMQTTPublishInfo;
    size_t               xRemainingLength;
    size_t               xPacketSize = 0;
    uint8_t *            pusPacketIdentifierHigh;
    BaseType_t           xStatus;


    /***
     * For readability, error handling in this function is restricted to the use of
     * asserts().
     ***/

    /* Some fields not used by this demo so start with everything at 0. */
    memset( ( void * ) &xMQTTPublishInfo, 0x00, sizeof( xMQTTPublishInfo ) );

    /* This demo uses QOS0 */
    xMQTTPublishInfo.qos             = IOT_MQTT_QOS_0;
    xMQTTPublishInfo.retain          = false;
    xMQTTPublishInfo.pTopicName      = mqttexampleTOPIC;
    xMQTTPublishInfo.topicNameLength = ( uint16_t ) strlen( mqttexampleTOPIC );
    xMQTTPublishInfo.pPayload        = mqttexampleMESSAGE;
    xMQTTPublishInfo.payloadLength   = strlen( mqttexampleMESSAGE );

    /* Find out length of Publish packet size. */
    xResult                          = IotMqtt_GetPublishPacketSize( &xMQTTPublishInfo, &xRemainingLength, &xPacketSize );
    configASSERT( xResult == IOT_MQTT_SUCCESS );

    /* Make sure the packet size is less than static buffer size. */
    configASSERT( xPacketSize < mqttexampleSHARED_BUFFER_SIZE );

    xResult                          = IotMqtt_SerializePublish( &xMQTTPublishInfo,
                                                                 xRemainingLength,
                                                                 &usPublishPacketIdentifier,
                                                                 &pusPacketIdentifierHigh,
                                                                 ucSharedBuffer,
                                                                 xPacketSize );
    configASSERT( xResult == IOT_MQTT_SUCCESS );

    /* Send Publish message to the broker. */
    xStatus                          = FreeRTOS_send( xMQTTSocket, ( void * ) ucSharedBuffer, xPacketSize, 0 );
    configASSERT( xStatus == ( BaseType_t ) xPacketSize );
}
/*-----------------------------------------------------------*/

static void prvMQTTUnsubscribeFromTopic( Socket_t xMQTTSocket )
{
    IotMqttError_t        xResult;
    IotMqttSubscription_t xMQTTSubscription[ 1 ];
    size_t                xRemainingLength;
    size_t                xPacketSize;
    BaseType_t            xStatus;

    /* Some fields not used by this demo so start with everything at 0. */
    memset( ( void * ) &xMQTTSubscription, 0x00, sizeof( xMQTTSubscription ) );

    /* Unsubscribe to the mqttexampleTOPIC topic filter. The task handle is passed
     * as the callback context which is used by the callback to send a task
     * notification to this task.*/
    xMQTTSubscription[ 0 ].qos               = IOT_MQTT_QOS_0;
    xMQTTSubscription[ 0 ].pTopicFilter      = mqttexampleTOPIC;
    xMQTTSubscription[ 0 ].topicFilterLength = ( uint16_t ) strlen( mqttexampleTOPIC );

    xResult                                  = IotMqtt_GetSubscriptionPacketSize( IOT_MQTT_UNSUBSCRIBE,
                                                                                  xMQTTSubscription,
                                                                                  sizeof( xMQTTSubscription ) / sizeof( IotMqttSubscription_t ),
                                                                                  &xRemainingLength,
                                                                                  &xPacketSize );
    configASSERT( xResult == IOT_MQTT_SUCCESS );
    /* Make sure the packet size is less than static buffer size */
    configASSERT( xPacketSize < mqttexampleSHARED_BUFFER_SIZE );

    xResult                                  = IotMqtt_SerializeUnsubscribe( xMQTTSubscription,
                                                                             sizeof( xMQTTSubscription ) / sizeof( IotMqttSubscription_t ),
                                                                             xRemainingLength,
                                                                             &usUnsubscribePacketIdentifier,
                                                                             ucSharedBuffer,
                                                                             xPacketSize );
    configASSERT( xResult == IOT_MQTT_SUCCESS );

    /* Send Unsubscribe request to the broker. */
    xStatus                                  = FreeRTOS_send( xMQTTSocket, ( void * ) ucSharedBuffer, xPacketSize, 0 );
    configASSERT( xStatus == ( BaseType_t ) xPacketSize );
}
/*-----------------------------------------------------------*/

static void prvMQTTKeepAlive( Socket_t xMQTTSocket )
{
    IotMqttError_t xResult;
    BaseType_t     xStatus;

    /* PingReq is fixed length packet, therefore there is no need to calculate the size,
     * just makes sure static buffer can accommodate ping request. */
    configASSERT( MQTT_PACKET_PINGREQ_SIZE <= mqttexampleSHARED_BUFFER_SIZE );

    xResult = IotMqtt_SerializePingreq( ucSharedBuffer, MQTT_PACKET_PINGREQ_SIZE );
    configASSERT( xResult == IOT_MQTT_SUCCESS );

    /* Send Ping Request to the broker. */
    xStatus = FreeRTOS_send( xMQTTSocket, ( void * ) ucSharedBuffer, MQTT_PACKET_PINGREQ_SIZE, 0 );
    configASSERT( xStatus == ( BaseType_t ) MQTT_PACKET_PINGREQ_SIZE );
}

/*-----------------------------------------------------------*/

static void prvMQTTDisconnect( Socket_t xMQTTSocket )
{
    IotMqttError_t xResult;
    BaseType_t     xStatus;

    /* Disconnect is fixed length packet, therefore there is no need to calculate the size,
     * just makes sure static buffer can accommodate disconnect request. */
    configASSERT( MQTT_PACKET_DISCONNECT_SIZE <= mqttexampleSHARED_BUFFER_SIZE );

    xResult = IotMqtt_SerializeDisconnect( ucSharedBuffer, MQTT_PACKET_DISCONNECT_SIZE );
    configASSERT( xResult == IOT_MQTT_SUCCESS );

    xStatus = FreeRTOS_send( xMQTTSocket, ( void * ) ucSharedBuffer, MQTT_PACKET_DISCONNECT_SIZE, 0 );
    configASSERT( xStatus == ( BaseType_t ) MQTT_PACKET_DISCONNECT_SIZE );
}

/*-----------------------------------------------------------*/

static void prvMQTTProcessResponse( IotMqttPacketInfo_t * pxIncomingPacket )
{
    switch( pxIncomingPacket->type & 0xf0 )
    {
        case MQTT_PACKET_TYPE_SUBACK:
            configPRINTF( ( "Subscribed to the topic %s.\r\n", mqttexampleTOPIC ) );
            /* Make sure ACK packet identifier matches with Request packet identifier. */
            configASSERT( usSubscribePacketIdentifier == pxIncomingPacket->packetIdentifier );
            break;

        case MQTT_PACKET_TYPE_UNSUBACK:
            configPRINTF( ( "Unsubscribed from the topic %s.\r\n", mqttexampleTOPIC ) );
            /* Make sure ACK packet identifier matches with Request packet identifier. */
            configASSERT( usUnsubscribePacketIdentifier == pxIncomingPacket->packetIdentifier );
            break;

        case MQTT_PACKET_TYPE_PINGRESP:
            configPRINTF( ( "Ping Response successfully received.\r\n" ) );
            break;

        /* Any other packet type is invalid. */
        default:
            configPRINTF( ( "prvMQTTProcessResponse() called with unknown packet type:(%lu).", pxIncomingPacket->type ) );
    }
}

/*-----------------------------------------------------------*/

static void prvMQTTProcessIncomingPublish( IotMqttPacketInfo_t * pxIncomingPacket )
{
    configASSERT( pxIncomingPacket != NULL );

    /* Process incoming Publish. */
    configPRINTF( ( "Incoming QOS : %d\n", pxIncomingPacket->pubInfo.qos ) );

    /* Verify the received publish is for the we have subscribed to. */
    if( ( pxIncomingPacket->pubInfo.topicNameLength == strlen( mqttexampleTOPIC ) ) &&
        ( 0 == strncmp( mqttexampleTOPIC, pxIncomingPacket->pubInfo.pTopicName, pxIncomingPacket->pubInfo.topicNameLength ) ) )
    {
        configPRINTF( ( "Incoming Publish Topic Name: %.*s matches subscribed topic.\n",
                        pxIncomingPacket->pubInfo.topicNameLength,
                        pxIncomingPacket->pubInfo.pTopicName ) );
        configPRINTF( ( "Incoming Publish Message : %.*s\n",
                        pxIncomingPacket->pubInfo.payloadLength,
                        pxIncomingPacket->pubInfo.pPayload ) );

        /* Check if the incoming Publish message is echo of the last Publish message
         * we sent out. */
        if( pxIncomingPacket->packetIdentifier != usPublishPacketIdentifier )
        {
            configPRINTF( ( "Incoming Publish has different packet identifier than outgoing Publish.\n" ) );
        }
        else
        {
            configPRINTF( ( "Incoming Publish packet identifier matches with outgoing Publish. \n" ) );
        }
    }
    else
    {
        configPRINTF( ( "Incoming Publish Topic Name: %.*s does not match subscribed topic. \n",
                        pxIncomingPacket->pubInfo.topicNameLength,
                        pxIncomingPacket->pubInfo.pTopicName ) );
    }
}

/*-----------------------------------------------------------*/

static void prvMQTTProcessIncomingPacket( Socket_t xMQTTSocket )
{
    IotMqttError_t      xResult;
    IotMqttPacketInfo_t xIncomingPacket;
    BaseType_t          xStatus;

    /***
     * For readability, error handling in this function is restricted to the use of
     * asserts().
     ***/

    memset( ( void * ) &xIncomingPacket, 0x00, sizeof( IotMqttPacketInfo_t ) );

    /* Determine incoming packet type and remaining length. */
    xResult                        = IotMqtt_GetIncomingMQTTPacketTypeAndLength( &xIncomingPacket, getNextByte, ( void * ) xMQTTSocket );
    configASSERT( xResult == IOT_MQTT_SUCCESS );
    configASSERT( xIncomingPacket.remainingLength <= mqttexampleSHARED_BUFFER_SIZE );

    /* Current implementation expects an incoming Publish and three different
     * responses ( SUBACK, PINGRESP and UNSUBACK ). */

    /* Receive the remaining bytes. */
    xStatus                        = FreeRTOS_recv( xMQTTSocket, ( void * ) ucSharedBuffer, xIncomingPacket.remainingLength, 0 );
    configASSERT( xStatus == ( BaseType_t ) xIncomingPacket.remainingLength );

    xIncomingPacket.pRemainingData = ucSharedBuffer;

    if( ( xIncomingPacket.type & 0xf0 ) == MQTT_PACKET_TYPE_PUBLISH )
    {
        xResult = IotMqtt_DeserializePublish( &xIncomingPacket );
        configASSERT( xResult == IOT_MQTT_SUCCESS );

        /* Process incoming Publish message. */
        prvMQTTProcessIncomingPublish( &xIncomingPacket );
    }
    else
    {
        /* If the received packet is not a Publish message, then it is an ACK for one
         * of the messages we sent out, verify that the ACK packet is a valid MQTT
         * packet. */
        xResult = IotMqtt_DeserializeResponse( &xIncomingPacket );
        configASSERT( xResult == IOT_MQTT_SUCCESS );

        /* Process the response. */
        prvMQTTProcessResponse( &xIncomingPacket );
    }
}

/*-----------------------------------------------------------*/
