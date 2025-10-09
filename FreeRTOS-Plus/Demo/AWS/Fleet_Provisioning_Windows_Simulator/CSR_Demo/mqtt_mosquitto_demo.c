/*
 * FreeRTOS MQTT Mosquitto Demo for Windows Simulator
 * Connects to test.mosquitto.org:1883
 */

/* Standard includes. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* TCP stack includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"

/* MQTT library includes. */
#include "core_mqtt.h"

/* Demo config. */
#include "demo_config.h"

/* Logging includes. */
#include "logging.h"

/**
 * @brief Timeout for MQTT operations in milliseconds.
 */
#define mqttexampleMQTT_TIMEOUT_MS    ( 5000U )

/**
 * @brief The number of topic filters to subscribe to.
 */
#define mqttexampleTOPIC_COUNT        ( 1 )

/**
 * @brief The MQTT context structure.
 */
static MQTTContext_t xMqttContext;

/**
 * @brief The network context structure.
 */
static NetworkContext_t xNetworkContext;

/**
 * @brief The buffer used to hold MQTT messages.
 */
static uint8_t ucSharedBuffer[ democonfigNETWORK_BUFFER_SIZE ];

/**
 * @brief Global variable to indicate connection status.
 */
static volatile BaseType_t xConnected = pdFALSE;

/**
 * @brief Connect to Mosquitto broker over plain TCP.
 */
static BaseType_t xConnectToBroker( void )
{
    BaseType_t xReturn = pdFAIL;
    Socket_t xSocket = NULL;
    struct freertos_sockaddr xBrokerAddress;
    TickType_t xTimeout = pdMS_TO_TICKS( mqttexampleMQTT_TIMEOUT_MS );

    LogInfo( ( "Creating TCP socket for Mosquitto broker." ) );

    /* Create a TCP socket. */
    xSocket = FreeRTOS_socket( FREERTOS_AF_INET, 
                              FREERTOS_SOCK_STREAM, 
                              FREERTOS_IPPROTO_TCP );

    if( xSocket != NULL )
    {
        /* Set the IP address and port of the Mosquitto broker. */
        xBrokerAddress.sin_addr = FreeRTOS_inet_addr_quick( 188, 165, 217, 43 ); /* test.mosquitto.org */
        xBrokerAddress.sin_port = FreeRTOS_htons( democonfigMQTT_BROKER_PORT );
        xBrokerAddress.sin_family = FREERTOS_AF_INET;

        LogInfo( ( "Attempting to connect to Mosquitto broker: %s:%d", 
                  democonfigMQTT_BROKER_ENDPOINT, 
                  democonfigMQTT_BROKER_PORT ) );

        /* Connect to the broker. */
        if( FreeRTOS_connect( xSocket, 
                             &xBrokerAddress, 
                             sizeof( xBrokerAddress ) ) == 0 )
        {
            xNetworkContext.socket = xSocket;
            xReturn = pdPASS;
            LogInfo( ( "Successfully connected to Mosquitto broker." ) );
        }
        else
        {
            LogError( ( "Failed to connect to Mosquitto broker." ) );
            FreeRTOS_closesocket( xSocket );
        }
    }
    else
    {
        LogError( ( "Failed to create TCP socket." ) );
    }

    return xReturn;
}

/**
 * @brief MQTT event callback function.
 */
static void prvEventCallback( MQTTContext_t * pxMqttContext,
                              MQTTPacketInfo_t * pxPacketInfo,
                              MQTTDeserializedInfo_t * pxDeserializedInfo )
{
    if( ( pxPacketInfo->type & 0xF0U ) == MQTT_PACKET_TYPE_PUBLISH )
    {
        LogInfo( ( "Received message on topic: %.*s", 
                  pxDeserializedInfo->pPublishInfo->topicNameLength,
                  pxDeserializedInfo->pPublishInfo->pTopicName ) );
        LogInfo( ( "Message: %.*s", 
                  pxDeserializedInfo->pPublishInfo->payloadLength,
                  pxDeserializedInfo->pPublishInfo->pPayload ) );
    }
    else
    {
        switch( pxPacketInfo->type )
        {
            case MQTT_PACKET_TYPE_CONNACK:
                LogInfo( ( "MQTT connection accepted." ) );
                xConnected = pdTRUE;
                break;

            case MQTT_PACKET_TYPE_PINGRESP:
                LogInfo( ( "Ping response received." ) );
                break;

            case MQTT_PACKET_TYPE_PUBACK:
                LogInfo( ( "Publish acknowledged." ) );
                break;

            case MQTT_PACKET_TYPE_SUBACK:
                LogInfo( ( "Subscribe acknowledged." ) );
                break;

            case MQTT_PACKET_TYPE_UNSUBACK:
                LogInfo( ( "Unsubscribe acknowledged." ) );
                break;

            default:
                LogWarn( ( "Unknown packet type: 0x%02x", pxPacketInfo->type ) );
                break;
        }
    }
}

/**
 * @brief Establish MQTT connection with Mosquitto broker.
 */
static BaseType_t xEstablishMqttSession( void )
{
    BaseType_t xReturn = pdFAIL;
    MQTTConnectInfo_t xConnectInfo;
    MQTTFixedBuffer_t xFixedBuffer = { .pBuffer = ucSharedBuffer, .size = democonfigNETWORK_BUFFER_SIZE };
    TransportInterface_t xTransport;
    MQTTPublishInfo_t xWillInfo;
    bool sessionPresent = false;

    /* Initialize the MQTT context. */
    xTransport.pNetworkContext = &xNetworkContext;
    xTransport.send = FreeRTOS_send;
    xTransport.recv = FreeRTOS_recv;

    if( MQTT_Init( &xMqttContext, 
                   &xTransport, 
                   FreeRTOS_gettimems, 
                   prvEventCallback, 
                   &xFixedBuffer ) == MQTTSuccess )
    {
        LogInfo( ( "MQTT context initialized successfully." ) );

        /* Set up the connection info. */
        memset( &xConnectInfo, 0, sizeof( xConnectInfo ) );
        xConnectInfo.cleanSession = true;
        xConnectInfo.pClientIdentifier = democonfigCLIENT_IDENTIFIER;
        xConnectInfo.clientIdentifierLength = ( uint16_t ) strlen( democonfigCLIENT_IDENTIFIER );
        xConnectInfo.keepAliveSeconds = 60;

        /* No username/password for public Mosquitto */
        xConnectInfo.pUserName = NULL;
        xConnectInfo.userNameLength = 0U;
        xConnectInfo.pPassword = NULL;
        xConnectInfo.passwordLength = 0U;

        LogInfo( ( "Sending MQTT CONNECT packet to Mosquitto..." ) );

        /* Send MQTT CONNECT packet. */
        if( MQTT_Connect( &xMqttContext, 
                         &xConnectInfo, 
                         NULL, 
                         mqttexampleMQTT_TIMEOUT_MS, 
                         &sessionPresent ) == MQTTSuccess )
        {
            LogInfo( ( "MQTT connection established successfully." ) );
            xReturn = pdTRUE;
        }
        else
        {
            LogError( ( "Failed to establish MQTT connection." ) );
        }
    }
    else
    {
        LogError( ( "Failed to initialize MQTT context." ) );
    }

    return xReturn;
}

/**
 * @brief Subscribe to MQTT topic.
 */
static BaseType_t xSubscribeToTopic( void )
{
    BaseType_t xReturn = pdFAIL;
    MQTTSubscribeInfo_t xSubscription[ mqttexampleTOPIC_COUNT ];

    /* Configure subscription. */
    xSubscription[ 0 ].qos = MQTTQoS0;
    xSubscription[ 0 ].pTopicFilter = democonfigMQTT_TOPIC;
    xSubscription[ 0 ].topicFilterLength = ( uint16_t ) strlen( democonfigMQTT_TOPIC );

    LogInfo( ( "Subscribing to topic: %s", democonfigMQTT_TOPIC ) );

    if( MQTT_Subscribe( &xMqttContext, 
                       xSubscription, 
                       sizeof( xSubscription ) / sizeof( MQTTSubscribeInfo_t ), 
                       mqttexampleMQTT_TIMEOUT_MS ) == MQTTSuccess )
    {
        LogInfo( ( "Successfully subscribed to topic." ) );
        xReturn = pdTRUE;
    }
    else
    {
        LogError( ( "Failed to subscribe to topic." ) );
    }

    return xReturn;
}

/**
 * @brief Publish MQTT message.
 */
static BaseType_t xPublishMessage( void )
{
    BaseType_t xReturn = pdFAIL;
    MQTTPublishInfo_t xPublishInfo;
    static uint32_t ulMessageCount = 0;
    char cMessageBuffer[ 100 ];

    /* Create message. */
    snprintf( cMessageBuffer, sizeof( cMessageBuffer ), 
              "Hello from FreeRTOS! Message #%lu", ulMessageCount++ );

    /* Configure publish info. */
    xPublishInfo.qos = MQTTQoS0;
    xPublishInfo.pTopicName = democonfigMQTT_TOPIC;
    xPublishInfo.topicNameLength = ( uint16_t ) strlen( democonfigMQTT_TOPIC );
    xPublishInfo.pPayload = cMessageBuffer;
    xPublishInfo.payloadLength = ( size_t ) strlen( cMessageBuffer );
    xPublishInfo.retain = false;
    xPublishInfo.dup = false;

    LogInfo( ( "Publishing message: %s", cMessageBuffer ) );

    if( MQTT_Publish( &xMqttContext, 
                     &xPublishInfo, 
                     mqttexampleMQTT_TIMEOUT_MS ) == MQTTSuccess )
    {
        LogInfo( ( "Message published successfully." ) );
        xReturn = pdTRUE;
    }
    else
    {
        LogError( ( "Failed to publish message." ) );
    }

    return xReturn;
}

/**
 * @brief Main MQTT demo task.
 */
static void prvMqttDemoTask( void * pvParameters )
{
    BaseType_t xNetworkConnected = pdFALSE;

    LogInfo( ( "MQTT Mosquitto Demo started." ) );

    /* Wait for network connectivity. */
    while( xNetworkConnected == pdFALSE )
    {
        if( FreeRTOS_IsNetworkUp() == pdTRUE )
        {
            xNetworkConnected = pdTRUE;
            LogInfo( ( "Network is up." ) );
        }
        else
        {
            LogInfo( ( "Waiting for network..." ) );
            vTaskDelay( pdMS_TO_TICKS( 1000 ) );
        }
    }

    /* Connect to Mosquitto broker. */
    if( xConnectToBroker() == pdPASS )
    {
        /* Establish MQTT session. */
        if( xEstablishMqttSession() == pdPASS )
        {
            /* Subscribe to topic. */
            if( xSubscribeToTopic() == pdPASS )
            {
                /* Main demo loop - publish messages periodically. */
                while( 1 )
                {
                    if( xPublishMessage() == pdPASS )
                    {
                        /* Process incoming MQTT packets. */
                        MQTT_ProcessLoop( &xMqttContext, mqttexampleMQTT_TIMEOUT_MS );
                        
                        /* Wait before sending next message. */
                        vTaskDelay( pdMS_TO_TICKS( 5000 ) );
                    }
                    else
                    {
                        LogError( ( "Publish failed, retrying..." ) );
                        vTaskDelay( pdMS_TO_TICKS( 2000 ) );
                    }
                }
            }
        }

        /* Cleanup */
        FreeRTOS_closesocket( xNetworkContext.socket );
    }

    LogError( ( "MQTT demo task exiting." ) );
    vTaskDelete( NULL );
}

/**
 * @brief Create and run the MQTT demo.
 */
void vStartMQTTDemo( void )
{
    BaseType_t xResult;

    LogInfo( ( "Creating MQTT Mosquitto demo task..." ) );

    xResult = xTaskCreate( prvMqttDemoTask,        /* Task function */
                           "MQTTDemo",             /* Task name */
                           democonfigDEMO_STACKSIZE, /* Stack size */
                           NULL,                   /* Parameters */
                           tskIDLE_PRIORITY + 2,   /* Priority */
                           NULL );                 /* Task handle */

    if( xResult != pdPASS )
    {
        LogError( ( "Failed to create MQTT demo task." ) );
    }
    else
    {
        LogInfo( ( "MQTT demo task created successfully." ) );
    }
}