/*
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
 */

/*
 * Demo for showing the use of MQTT APIs to establish an MQTT session,
 * subscribe to a topic, publish to a topic, receive incoming publishes,
 * unsubscribe from a topic and disconnect the MQTT session.
 *
 * The example shown below uses MQTT APIs to send and receive MQTT packets
 * over the TCP connection established using POSIX sockets.
 * The example is single threaded and uses statically allocated memory;
 * it uses QOS0 and therefore does not implement any retransmission
 * mechanism for Publish messages.
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


#define BROKER_ENDPOINT      "10.0.0.127"

#define BROKER_PORT          ( 1883 )

#define CLIENT_IDENTIFIER    "testclient"

/**
 * These configuration settings are required to run the plaintext demo.
 * Throw compilation error if the below configs are not defined.
 */
#ifndef CLIENT_IDENTIFIER
    #error "Please define a unique CLIENT_IDENTIFIER."
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
 * @brief The topic to subscribe and publish to in the example.
 *
 * The topic name starts with the client identifier to ensure that each demo
 * interacts with a unique topic name.
 */
#define MQTT_EXAMPLE_TOPIC                  CLIENT_IDENTIFIER "/example/topic"

/**
 * @brief Length of client MQTT topic.
 */
#define MQTT_EXAMPLE_TOPIC_LENGTH           ( ( uint16_t ) ( sizeof( MQTT_EXAMPLE_TOPIC ) - 1 ) )

/**
 * @brief The MQTT message published in this example.
 */
#define MQTT_EXAMPLE_MESSAGE                "Hello World!"

/**
 * @brief The length of the MQTT message published in this example.
 */
#define MQTT_EXAMPLE_MESSAGE_LENGTH         ( ( uint16_t ) ( sizeof( MQTT_EXAMPLE_MESSAGE ) - 1 ) )

/**
 * @brief Timeout for MQTT_ProcessLoop function in milliseconds.
 */
#define MQTT_PROCESS_LOOP_TIMEOUT_MS        ( 500U )

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
 * @brief Delay between MQTT publishes in milliseconds.
 */
#define DELAY_BETWEEN_PUBLISHES_MS     ( 50U )

/**
 * @brief Transport timeout in milliseconds for transport send and receive.
 */
#define TRANSPORT_SEND_RECV_TIMEOUT_MS      ( 20 )

#define _MILLISECONDS_PER_SECOND                    ( 1000U )                                         /**< @brief Milliseconds per second. */
#define _MILLISECONDS_PER_TICK                      ( _MILLISECONDS_PER_SECOND / configTICK_RATE_HZ ) /**< Milliseconds per FreeRTOS tick. */
#define TICKS_TO_WAIT                       pdMS_TO_TICKS( 1000 )

#ifndef EXIT_SUCCESS
    #define EXIT_SUCCESS 0
#endif
#ifndef EXIT_FAILURE
    #define EXIT_FAILURE 1
#endif

/*-----------------------------------------------------------*/

/**
 * @brief The network buffer must remain valid for the lifetime of the MQTT context.
 */
static uint8_t buffer[ NETWORK_BUFFER_SIZE ];

/*-----------------------------------------------------------*/

/**
 * @brief Sends an MQTT CONNECT packet over the already connected TCP socket.
 *
 * @param[in] pMqttContext MQTT context pointer.
 * @param[in] pNetworkContext Pointer to the network context created using Plaintext_Connect.
 *
 * @return EXIT_SUCCESS if an MQTT session is established;
 * EXIT_FAILURE otherwise.
 */
static int establishMqttSession( MQTTContext_t * pMqttContext,
                                 NetworkContext_t * pNetworkContext );

static void subscriptionManager( MQTTContext_t * pMqttContext,
                                 MQTTPacketInfo_t * pPacketInfo,
                                 uint16_t packetIdentifier,
                                 MQTTPublishInfo_t * pPublishInfo );

static uint32_t prvGetTimeMs( void );

/*-----------------------------------------------------------*/

/**
 * @brief Global entry time into the application to use as a reference timestamp
 * in the #prvGetTimeMs function. #prvGetTimeMs will always return the difference
 * between the current time and the global entry time. This will reduce the chances
 * of overflow for the 32 bit unsigned integer used for holding the timestamp.
 */
static uint32_t ulGlobalEntryTimeMs;

/*-----------------------------------------------------------*/

static int establishMqttSession( MQTTContext_t * pMqttContext,
                                 NetworkContext_t * pNetworkContext )
{
    int returnStatus = EXIT_SUCCESS;
    MQTTStatus_t mqttStatus;
    MQTTConnectInfo_t connectInfo;
    bool sessionPresent;
    MQTTFixedBuffer_t networkBuffer;
    TransportInterface_t transport;

    assert( pMqttContext != NULL );
    assert( pNetworkContext != NULL );

    /* Fill in TransportInterface send and receive function pointers.
     * For this demo, TCP sockets are used to send and receive data
     * from network. Network context is socket file descriptor.*/
    transport.pNetworkContext = pNetworkContext;
    transport.send = Plaintext_FreeRTOS_send;
    transport.recv = Plaintext_FreeRTOS_recv;

    /* Fill the values for network buffer. */
    networkBuffer.pBuffer = buffer;
    networkBuffer.size = NETWORK_BUFFER_SIZE;

    /* Initialize MQTT library. */
    mqttStatus = MQTT_Init( pMqttContext, &transport, prvGetTimeMs, subscriptionManager, &networkBuffer );

    if( mqttStatus != MQTTSuccess )
    {
        returnStatus = EXIT_FAILURE;
        LogError( ( "MQTT init failed with status %u.", mqttStatus ) );
    }
    else
    {
        /* Establish MQTT session by sending a CONNECT packet. */

        /* Start with a clean session i.e. direct the MQTT broker to discard any
         * previous session data. Also, establishing a connection with clean session
         * will ensure that the broker does not store any data when this client
         * gets disconnected. */
        connectInfo.cleanSession = true;

        /* The client identifier is used to uniquely identify this MQTT client to
         * the MQTT broker. In a production device the identifier can be something
         * unique, such as a device serial number. */
        connectInfo.pClientIdentifier = CLIENT_IDENTIFIER;
        connectInfo.clientIdentifierLength = CLIENT_IDENTIFIER_LENGTH;

        /* The maximum time interval in seconds which is allowed to elapse
         * between two Control Packets.
         * It is the responsibility of the Client to ensure that the interval between
         * Control Packets being sent does not exceed the this Keep Alive value. In the
         * absence of sending any other Control Packets, the Client MUST send a
         * PINGREQ Packet. */
        connectInfo.keepAliveSeconds = MQTT_KEEP_ALIVE_INTERVAL_SECONDS;

        /* Username and password for authentication. Not used in this demo. */
        connectInfo.pUserName = NULL;
        connectInfo.userNameLength = 0U;
        connectInfo.pPassword = NULL;
        connectInfo.passwordLength = 0U;

        /* Send MQTT CONNECT packet to broker. */
        mqttStatus = MQTT_Connect( pMqttContext, &connectInfo, NULL, CONNACK_RECV_TIMEOUT_MS, &sessionPresent );

        if( mqttStatus != MQTTSuccess )
        {
            returnStatus = EXIT_FAILURE;
            LogError( ( "Connection with MQTT broker failed with status %u.", mqttStatus ) );
        }
        else
        {
            LogInfo( ( "MQTT connection successfully established with broker.\n\n" ) );
        }
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

typedef enum operationType {
    PROCESSLOOP,
    PUBLISH,
    SUBSCRIBE,
    UNSUBSCRIBE,
    PING,
    DISCONNECT,
    CONNECT
} CommandType_t;

typedef struct CommandContext {
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

typedef void (* CommandCallback_t )( CommandContext_t * );

typedef struct Command {
    CommandType_t commandType;
    CommandContext_t * pContext;
    CommandCallback_t callback;
} Command_t;

typedef struct ackInfo {
    uint16_t packetId;
    CommandContext_t * pCommandContext;
    CommandCallback_t callback;
} AckInfo_t;

typedef struct subscriptionElement {
    char pTopicFilter[ 100 ];
    uint16_t topicFilterLength;
    QueueHandle_t responseQueue;
} SubscriptionElement_t;

typedef struct publishElement {
    MQTTPublishInfo_t publishInfo;
    uint8_t pPayload[ 100 ];
    uint8_t pTopicName[ 100 ];
} PublishElement_t;

#define PENDING_ACKS_MAX_SIZE       20
#define SUBSCRIPTIONS_MAX_COUNT     10
#define PUBLISH_COUNT               12
#define DEMO_BUFFER_SIZE            100
#define COMMAND_QUEUE_SIZE          25
#define PUBLISH_QUEUE_SIZE          20
#define TASK1_COMPLETE_BIT          ( 1 << 1 )
#define TASK2_COMPLETE_BIT          ( 1 << 2 )

static MQTTContext_t globalMqttContext;
static AckInfo_t pendingAcks[ PENDING_ACKS_MAX_SIZE ];
static SubscriptionElement_t subscriptions[ SUBSCRIPTIONS_MAX_COUNT ];

static QueueHandle_t pCommandQueue;
static QueueHandle_t pResponseQueue1;
static QueueHandle_t pResponseQueue2;

static TaskHandle_t mainTask;
static TaskHandle_t task1;
static TaskHandle_t task2;

static void initializeCommandContext( CommandContext_t * pContext )
{
    pContext->complete = false;
    pContext->pResponseQueue = NULL;
    pContext->returnStatus = MQTTSuccess;
    pContext->pPublishInfo = NULL;
    pContext->pSubscribeInfo = NULL;
}

static void destroyCommandContext( CommandContext_t * pContext )
{
    ( void ) pContext;
}

static void addPendingAck( uint16_t packetId,
                           CommandContext_t * pContext,
                           CommandCallback_t callback )
{
    int32_t i = 0;
    for( i = 0; i < PENDING_ACKS_MAX_SIZE; i++ )
    {
        if( pendingAcks[ i ].packetId == MQTT_PACKET_ID_INVALID )
        {
            pendingAcks[ i ].packetId = packetId;
            pendingAcks[ i ].pCommandContext = pContext;
            pendingAcks[ i ].callback = callback;
            break;
        }
    }
}

static AckInfo_t popAck( uint16_t packetId )
{
    int32_t i = 0;
    AckInfo_t ret = { 0 };
    for( i = 0; i < PENDING_ACKS_MAX_SIZE; i++ )
    {
        if( pendingAcks[ i ].packetId == packetId )
        {
            ret = pendingAcks[ i ];
            pendingAcks[ i ].packetId = MQTT_PACKET_ID_INVALID;
            pendingAcks[ i ].pCommandContext = NULL;
            pendingAcks[ i ].callback = NULL;
            break;
        }
    }
    return ret;
}

static void addSubscription( const char * pTopicFilter, uint16_t topicFilterLength, QueueHandle_t pQueue )
{
    int32_t i = 0;
    for( i = 0; i < SUBSCRIPTIONS_MAX_COUNT; i++ )
    {
        if( subscriptions[ i ].topicFilterLength == 0 )
        {
            subscriptions[ i ].topicFilterLength = topicFilterLength;
            subscriptions[ i ].responseQueue = pQueue;
            memcpy( subscriptions[ i ].pTopicFilter, pTopicFilter, topicFilterLength );
            break;
        }
    }
}

static void removeSubscription( const char * pTopicFilter, size_t topicFilterLength, QueueHandle_t pQueue )
{
    /* TODO: Unused for now, but can be used to remove a single subscription
     * when multiple apps are subscribed to the same topic. */
    ( void ) pQueue;
    int32_t i = 0;
    for( i = 0; i< SUBSCRIPTIONS_MAX_COUNT; i++ )
    {
        if( subscriptions[ i ].topicFilterLength == topicFilterLength )
        {
            if( ( strncmp( subscriptions[ i ].pTopicFilter, pTopicFilter, topicFilterLength ) == 0 ) && true )
            {
                subscriptions[ i ].topicFilterLength = 0;
                subscriptions[ i ].responseQueue = NULL;
                memset( ( void * ) subscriptions[ i ].pTopicFilter, 0x00, sizeof( subscriptions[ i ].pTopicFilter ) );
                break;
            }
        }
    }
}

static bool createCommand( CommandType_t commandType,
                                  CommandContext_t * context,
                                  CommandCallback_t callback,
                                  Command_t * pCommand )
{
    bool isValid = true;
    memset( ( void * ) pCommand, 0x00, sizeof( Command_t ) );
    pCommand->commandType = commandType;
    pCommand->pContext = context;
    pCommand->callback = callback;

    /* Determine if all required parameters are present. */
    switch( commandType )
    {
        case PUBLISH:
            isValid = ( context != NULL ) ? ( context->pPublishInfo != NULL ) : false;
            break;

        case SUBSCRIBE:
        case UNSUBSCRIBE:
            isValid = ( context != NULL ) ? ( context->pSubscribeInfo != NULL ) : false;
            break;

        default:
            /* Other operations don't need a context. */
            break;
    }

    return isValid;
}

static void addCommandToQueue( Command_t * pCommand )
{
    xQueueSend( pCommandQueue, pCommand, TICKS_TO_WAIT );
}

static void copyPublishToQueue( MQTTPublishInfo_t * pPublishInfo, QueueHandle_t pResponseQueue )
{
    PublishElement_t copiedPublish;
    MQTTPublishInfo_t * pCopiedPublish = NULL;
    memset( ( void * ) &copiedPublish, 0x00, sizeof( copiedPublish ) );
    pCopiedPublish = &( copiedPublish.publishInfo );
    memcpy( &( copiedPublish.publishInfo ), pPublishInfo, sizeof( MQTTPublishInfo_t ) );
    /* Since adding an MQTTPublishInfo_t to a queue will not copy its string buffers,
     * we need to add buffers to a struct and copy the entire structure. */
    memcpy( copiedPublish.pTopicName, pPublishInfo->pTopicName, pPublishInfo->topicNameLength );
    memcpy( copiedPublish.pPayload, pPublishInfo->pPayload, pPublishInfo->payloadLength );
    pCopiedPublish->pTopicName = ( const char * ) copiedPublish.pTopicName;
    pCopiedPublish->pPayload = copiedPublish.pPayload;
    xQueueSendToBack( pResponseQueue, pCopiedPublish, TICKS_TO_WAIT );
}

static MQTTStatus_t processCommand( Command_t * pCommand )
{
    MQTTStatus_t status = MQTTSuccess;
    uint16_t packetId = MQTT_PACKET_ID_INVALID;
    bool addAckToList = false;
    MQTTPublishInfo_t * pPublishInfo;
    MQTTSubscribeInfo_t * pSubscribeInfo;

    switch( pCommand->commandType )
    {
        case PROCESSLOOP:
            LogInfo( ( "Running Process Loop." ) );
            status = MQTT_ProcessLoop( &globalMqttContext, MQTT_PROCESS_LOOP_TIMEOUT_MS );
            break;
        case PUBLISH:
            assert( pCommand->pContext != NULL );
            pPublishInfo = pCommand->pContext->pPublishInfo;
            assert( pPublishInfo != NULL );
            if( pPublishInfo->qos != MQTTQoS0 )
            {
                packetId = MQTT_GetPacketId( &globalMqttContext );
            }
            LogInfo( ( "Publishing message to %.*s.", ( int ) pPublishInfo->topicNameLength, pPublishInfo->pTopicName ) );
            status = MQTT_Publish( &globalMqttContext, pPublishInfo, packetId );
            pCommand->pContext->returnStatus = status;

            /* Add to pending ack list, or call callback if QoS 0. */
            addAckToList = ( pPublishInfo->qos != MQTTQoS0 ) && ( status == MQTTSuccess );
            break;
        /* TODO: Option to subscribe/unsubscribe without sending a packet,
         * e.g. for Shadow topics. */   
        case SUBSCRIBE:
        case UNSUBSCRIBE:
            assert( pCommand->pContext != NULL );
            pSubscribeInfo = pCommand->pContext->pSubscribeInfo;
            assert( pSubscribeInfo != NULL );
            assert( pSubscribeInfo->pTopicFilter != NULL );
            packetId = MQTT_GetPacketId( &globalMqttContext );
            if( pCommand->commandType == SUBSCRIBE )
            {
                LogInfo( ( "Subscribing to %.*s", pSubscribeInfo->topicFilterLength, pSubscribeInfo->pTopicFilter ) );
                status = MQTT_Subscribe( &globalMqttContext, pSubscribeInfo, pCommand->pContext->subscriptionCount, packetId );
            }
            else
            {
                LogInfo( ( "Unsubscribing from %.*s", pSubscribeInfo->topicFilterLength, pSubscribeInfo->pTopicFilter ) );
                status = MQTT_Unsubscribe( &globalMqttContext, pSubscribeInfo, pCommand->pContext->subscriptionCount, packetId );
            }
            pCommand->pContext->returnStatus = status;
            addAckToList = ( status == MQTTSuccess );
            break;
            
        case PING:
            status = MQTT_Ping( &globalMqttContext );
            if( pCommand->pContext != NULL )
            {
                pCommand->pContext->returnStatus = status;
            }
            break;

        case DISCONNECT:
            status = MQTT_Disconnect( &globalMqttContext );
            if( pCommand->pContext != NULL )
            {
                pCommand->pContext->returnStatus = status;
            }
            break;
        case CONNECT:
            /* TODO: Reconnect. */
            LogInfo( (" Processed Connect Command") );
        default:
            break;
    }

    if( addAckToList )
    {
        addPendingAck( packetId, pCommand->pContext, pCommand->callback );
    }
    else
    {
        if( pCommand->callback != NULL )
        {
            pCommand->callback( pCommand->pContext );
        }
    }
    
    return status;
}

static bool matchEndWildcards( const char * pTopicFilter,
                                uint16_t topicNameLength,
                                uint16_t topicFilterLength,
                                uint16_t nameIndex,
                                uint16_t filterIndex,
                                bool * pMatch )
{
    bool status = false, endChar = false;

    /* Determine if the last character is reached for both topic name and topic
     * filter for the '#' wildcard. */
    endChar = ( nameIndex == ( topicNameLength - 1U ) ) && ( filterIndex == ( topicFilterLength - 3U ) );

    if( endChar == true )
    {
        /* Determine if the topic filter ends with the '#' wildcard. */
        status = ( pTopicFilter[ filterIndex + 2U ] == '#' );
    }

    if( status == false )
    {
        /* Determine if the last character is reached for both topic name and topic
         * filter for the '+' wildcard. */
        endChar = ( nameIndex == ( topicNameLength - 1U ) ) && ( filterIndex == ( topicFilterLength - 2U ) );

        if( endChar == true )
        {
            /* Filter "sport/+" also matches the "sport/" but not "sport". */
            status = ( pTopicFilter[ filterIndex + 1U ] == '+' );
        }
    }

    *pMatch = status;

    return status;
}

/*-----------------------------------------------------------*/

static bool matchWildcards( const char * pTopicFilter,
                             const char * pTopicName,
                             uint16_t topicNameLength,
                             uint16_t filterIndex,
                             uint16_t * pNameIndex,
                             bool * pMatch )
{
    bool status = false;

    /* Check for wildcards. */
    if( pTopicFilter[ filterIndex ] == '+' )
    {
        /* Move topic name index to the end of the current level.
         * This is identified by '/'. */
        while( ( *pNameIndex < topicNameLength ) && ( pTopicName[ *pNameIndex ] != '/' ) )
        {
            ( *pNameIndex )++;
        }

        ( *pNameIndex )--;
    }
    else if( pTopicFilter[ filterIndex ] == '#' )
    {
        /* Subsequent characters don't need to be checked for the
         * multi-level wildcard. */
        *pMatch = true;
        status = true;
    }
    else
    {
        /* Any character mismatch other than '+' or '#' means the topic
         * name does not match the topic filter. */
        *pMatch = false;
        status = true;
    }

    return status;
}

/*-----------------------------------------------------------*/

static bool topicFilterMatch( const char * pTopicName,
                               uint16_t topicNameLength,
                               const char * pTopicFilter,
                               uint16_t topicFilterLength )
{
    bool status = false, matchFound = false;
    uint16_t nameIndex = 0, filterIndex = 0;

    while( ( nameIndex < topicNameLength ) && ( filterIndex < topicFilterLength ) )
    {
        /* Check if the character in the topic name matches the corresponding
         * character in the topic filter string. */
        if( pTopicName[ nameIndex ] == pTopicFilter[ filterIndex ] )
        {
            /* Handle special corner cases regarding wildcards at the end of
             * topic filters, as documented by the MQTT protocol spec. */
            matchFound = matchEndWildcards( pTopicFilter,
                                             topicNameLength,
                                             topicFilterLength,
                                             nameIndex,
                                             filterIndex,
                                             &status );
        }
        else
        {
            /* Check for matching wildcards. */
            matchFound = matchWildcards( pTopicFilter,
                                          pTopicName,
                                          topicNameLength,
                                          filterIndex,
                                          &nameIndex,
                                          &status );
        }

        if( matchFound == true )
        {
            break;
        }

        /* Increment indexes. */
        nameIndex++;
        filterIndex++;
    }

    if( status == false )
    {
        /* If the end of both strings has been reached, they match. */
        status = ( ( nameIndex == topicNameLength ) && ( filterIndex == topicFilterLength ) );
    }

    return status;
}

static void subscriptionManager( MQTTContext_t * pMqttContext,
                                 MQTTPacketInfo_t * pPacketInfo,
                                 uint16_t packetIdentifier,
                                 MQTTPublishInfo_t * pPublishInfo )
{
    assert( pMqttContext != NULL );
    assert( pPacketInfo != NULL );
    AckInfo_t ackInfo;
    MQTTStatus_t status = MQTTSuccess;
    bool isMatched = false;
    size_t i;
    MQTTSubscribeInfo_t * pSubscribeInfo = NULL;

    /* Handle incoming publish. The lower 4 bits of the publish packet
     * type is used for the dup, QoS, and retain flags. Hence masking
     * out the lower bits to check if the packet is publish. */
    if( ( pPacketInfo->type & 0xF0U ) == MQTT_PACKET_TYPE_PUBLISH )
    {
        assert( pPublishInfo != NULL );
        for( i = 0; i < SUBSCRIPTIONS_MAX_COUNT; i++ )
        {
            if( subscriptions[ i ].topicFilterLength > 0 )
            {
                isMatched = topicFilterMatch( pPublishInfo->pTopicName,
                                              pPublishInfo->topicNameLength,
                                              subscriptions[ i ].pTopicFilter,
                                              subscriptions[ i ].topicFilterLength );
                if( isMatched )
                {
                    LogInfo( ( "Adding publish to response queue for %.*s", subscriptions[ i ].topicFilterLength, subscriptions[ i ].pTopicFilter ) );
                    copyPublishToQueue( pPublishInfo, subscriptions[ i ].responseQueue );
                }
            }
        }
    }
    else
    {
        /* Handle other packets. */
        switch( pPacketInfo->type )
        {
            case MQTT_PACKET_TYPE_PUBACK:
            case MQTT_PACKET_TYPE_PUBCOMP:
                ackInfo = popAck( packetIdentifier );
                if( ackInfo.packetId == packetIdentifier )
                {
                    ackInfo.pCommandContext->returnStatus = status;
                    if( ackInfo.callback != NULL )
                    {
                        ackInfo.callback( ackInfo.pCommandContext );
                    }
                }
                break;

            case MQTT_PACKET_TYPE_SUBACK:
                ackInfo = popAck( packetIdentifier );
                if( ackInfo.packetId == packetIdentifier )
                {
                    pSubscribeInfo = ackInfo.pCommandContext->pSubscribeInfo;
                    for( i = 0; i < ackInfo.pCommandContext->subscriptionCount; i++ )
                    {
                        LogInfo( ( "Adding subscription to %.*s",
                                   pSubscribeInfo[ i ].topicFilterLength,
                                   pSubscribeInfo[ i ].pTopicFilter ) );
                        LogInfo( ( "Filter length: %u", pSubscribeInfo[ i ].topicFilterLength ) );
                        addSubscription( pSubscribeInfo[ i ].pTopicFilter,
                                         pSubscribeInfo[ i ].topicFilterLength,
                                         ackInfo.pCommandContext->pResponseQueue );
                    }
                }
                else
                {
                    status = MQTTBadResponse;
                }
                ackInfo.pCommandContext->returnStatus = status;
                if( ackInfo.callback != NULL )
                {
                    ackInfo.callback( ackInfo.pCommandContext );
                }
                break;

            case MQTT_PACKET_TYPE_UNSUBACK:
                ackInfo = popAck( packetIdentifier );
                if( ackInfo.packetId == packetIdentifier )
                {
                    pSubscribeInfo = ackInfo.pCommandContext->pSubscribeInfo;
                    for( i = 0; i < ackInfo.pCommandContext->subscriptionCount; i++ )
                    {
                        LogInfo( ( "Removing subscription to %.*s",
                                   pSubscribeInfo[ i ].topicFilterLength,
                                   pSubscribeInfo[ i ].pTopicFilter ) );
                        removeSubscription( pSubscribeInfo[ i ].pTopicFilter,
                                            pSubscribeInfo[ i ].topicFilterLength,
                                            ackInfo.pCommandContext->pResponseQueue );
                    }
                }
                else
                {
                    status = MQTTBadResponse;
                }
                ackInfo.pCommandContext->returnStatus = status;
                if( ackInfo.callback != NULL )
                {
                    ackInfo.callback( ackInfo.pCommandContext );
                }
                
                break;

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

static void commandLoop()
{
    Command_t command;
    Command_t newCommand;
    Command_t * pCommand;
    static int numProcessed = 0;
    bool breakOnNextProcessLoop = false;
    bool subscribeProcessed = false;
    while( 1 )
    {
        while( xQueueReceive( pCommandQueue, &command, TICKS_TO_WAIT ) )
        {
            pCommand = &command;
            /* This demo requires the subscription to be present before the first publish. */
            if( pCommand->commandType == PUBLISH )
            {
                if( !subscribeProcessed )
                {
                    LogInfo( ( "Publish in queue before subscribe. Sending to back of queue." ) );
                    addCommandToQueue( pCommand );
                    continue;
                }
            }

            processCommand( pCommand );
            numProcessed++;

            if( pCommand->commandType == PROCESSLOOP )
            {
                /* Add process loop back to end of queue. */
                createCommand( PROCESSLOOP, NULL, NULL, &newCommand );
                addCommandToQueue( &newCommand );
                numProcessed--;
                if( breakOnNextProcessLoop )
                {
                    break;
                }
            }

            /* Mark subscribed as being processed. */
            if( pCommand->commandType == SUBSCRIBE )
            {
                subscribeProcessed = true;
            }

            /* In this demo, exit after unsubscribing. */
            if( pCommand->commandType == UNSUBSCRIBE )
            {
                breakOnNextProcessLoop = true;
            }
        }
        vTaskDelay( pdMS_TO_TICKS( 200 ) );

        /* We have PUBLISH_COUNT publishes + 1 subscription */
        if( numProcessed >= PUBLISH_COUNT + 1)
        {
            break;
        }
    }
    LogInfo( ( "Creating Disconnect operation" ) );
    createCommand( DISCONNECT, NULL, NULL, &newCommand );
    processCommand( &newCommand );
    LogInfo( ( "Disconnected from broker" ) );
    return;
}

static void comCallback( CommandContext_t * pContext )
{
    pContext->complete = true;
    xTaskNotify( pContext->taskToNotify, pContext->notificationBit, eSetBits );
    return;
}

void thread1( void * args )
{
    ( void ) args;
    Command_t command;
    MQTTPublishInfo_t publishInfo = { 0 };
    MQTTPublishInfo_t publishes[ PUBLISH_COUNT ];
    char payloadBuf[ DEMO_BUFFER_SIZE ];
    char topicBuf[ DEMO_BUFFER_SIZE ];
    char * payloadBuffers[ PUBLISH_COUNT ];
    char * topicBuffers[ PUBLISH_COUNT ];

    publishInfo.qos = MQTTQoS2;
    publishInfo.pTopicName = topicBuf;
    publishInfo.pPayload = payloadBuf;

    CommandContext_t context;
    CommandContext_t * contexts[PUBLISH_COUNT] = { 0 };
    uint32_t notification;

    for( int i = 0; i < PUBLISH_COUNT / 2; i++ )
    {
        snprintf( payloadBuf, DEMO_BUFFER_SIZE, "Hello World! %d", i+1 );
        publishInfo.payloadLength = ( uint16_t ) strlen( payloadBuf );
        snprintf( topicBuf, DEMO_BUFFER_SIZE, "thread/1/%i/filter", i+1 );
        publishInfo.topicNameLength = ( uint16_t ) strlen( topicBuf );
        initializeCommandContext( &context );
        context.pResponseQueue = pResponseQueue1;
        context.taskToNotify = xTaskGetCurrentTaskHandle();
        context.notificationBit = 1 << i;
        context.pPublishInfo = &publishInfo;
        LogInfo( (  "Adding publish operation for message %s \non topic %.*s\n", payloadBuf, publishInfo.topicNameLength, publishInfo.pTopicName ) );
        createCommand( PUBLISH, &context, comCallback, &command );
        addCommandToQueue( &command );

        LogInfo( ( "Waiting for publish %d to complete.\n", i+1 ) );
        xTaskNotifyWait( 0, 1 << i, &notification, TICKS_TO_WAIT );
        configASSERT( ( notification & ( 1U << i ) ) == ( 1U << i ) );
        destroyCommandContext( &context );
        LogInfo( ( "Publish operation complete.\n" ) );
        LogInfo( ( "\tPublish operation complete. Sleeping for %d ms.\n", 500 ) );
        vTaskDelay( pdMS_TO_TICKS( 500 ) );
    }

    for( int i = PUBLISH_COUNT >> 1; i < PUBLISH_COUNT; i++ )
    {
        contexts[ i ] = ( CommandContext_t * ) pvPortMalloc( sizeof( CommandContext_t ) );
        initializeCommandContext( contexts[ i ] );
        contexts[ i ]->pResponseQueue = pResponseQueue1;
        contexts[ i ]->taskToNotify = xTaskGetCurrentTaskHandle();
        contexts[ i ]->notificationBit = 1 << i;
        payloadBuffers[ i ] = ( char * ) pvPortMalloc( 25 );
        topicBuffers[ i ] = ( char * ) pvPortMalloc( 25 );
        snprintf( payloadBuffers[ i ], 25, "Hello World! %d", i+1 );
        snprintf( topicBuffers[ i ], 25, "thread/1/%i/filter", i+1 );
        /* Set publish info. */
        memset( ( void * ) &( publishes[ i ] ), 0x00, sizeof( MQTTPublishInfo_t ) );
        publishes[ i ].pPayload = payloadBuffers[ i ];
        publishes[ i ].payloadLength = strlen( payloadBuffers[ i ] );
        publishes[ i ].pTopicName = topicBuffers[i ];
        publishes[ i ].topicNameLength = ( uint16_t ) strlen( topicBuffers[ i ] );
        publishes[ i ].qos = MQTTQoS2;
        contexts[ i ]->pPublishInfo = &( publishes[ i ] );
        LogInfo( (  "Adding publish operation for message %s \non topic %.*s\n", payloadBuffers[ i ], publishes[ i ].topicNameLength, publishes[ i ].pTopicName ) );
        createCommand( PUBLISH, contexts[ i ], comCallback, &command );
        addCommandToQueue( &command );
        LogInfo( ( "\tPublish operation complete. Sleeping for %d ms.\n", 50 ) );
        vTaskDelay( pdMS_TO_TICKS( 50 ) );
    }

    LogInfo( ( "Finished publishing\n" ) );
    for( int i = 0; i < PUBLISH_COUNT; i++)
    {
        if( contexts[i] == NULL )
        {
            continue;
        }
        LogInfo( ( "Waiting to free publish context %d.", i ) );
        xTaskNotifyWait( 0, 1 << i, &notification, TICKS_TO_WAIT );
        configASSERT( ( notification & ( 1U << i ) ) == ( 1U << i ) );
        destroyCommandContext( contexts[ i ] );
        vPortFree( contexts[ i ] );
        vPortFree( topicBuffers[ i ] );
        vPortFree( payloadBuffers[ i ] );
        LogInfo( ( "Publish context %d freed.", i ) );
        contexts[ i ] = NULL;
    }
    /* Notify main task this task can be deleted. */
    xTaskNotify( mainTask, TASK1_COMPLETE_BIT, eSetBits );

    return;
}

void thread2( void * args )
{
    ( void ) args;
    MQTTSubscribeInfo_t subscribeInfo;
    Command_t command;
    MQTTPublishInfo_t * pReceivedPublish = NULL;
    static int subCounter = 0;
    subscribeInfo.qos = MQTTQoS0;
    subscribeInfo.pTopicFilter = "thread/1/+/filter";
    subscribeInfo.topicFilterLength = ( uint16_t ) strlen( subscribeInfo.pTopicFilter );
    LogInfo( ( "Topic filter: %.*s", subscribeInfo.topicFilterLength, subscribeInfo.pTopicFilter ) );
    LogInfo( ( "Filter length: %d", subscribeInfo.topicFilterLength ) );

    CommandContext_t context;
    initializeCommandContext( &context );
    context.pResponseQueue = pResponseQueue2;
    context.taskToNotify = xTaskGetCurrentTaskHandle();
    context.notificationBit = 1;
    context.subscriptionCount = 1;
    context.pSubscribeInfo = &subscribeInfo;
    LogInfo( ( "Adding subscribe operation" ) );
    createCommand( SUBSCRIBE, &context, comCallback, &command );
    addCommandToQueue( &command );
    uint32_t notification;

    LogInfo( ("Starting wait on operation.\n" ) );
    xTaskNotifyWait( 0, 1, &notification, TICKS_TO_WAIT );
    configASSERT( ( notification & 1 ) == 1 );
    destroyCommandContext( &context );
    LogInfo( ("Operation wait complete.\n" ) );

    PublishElement_t receivedPublish;

    while( 1 )
    {
        while( xQueueReceive( pResponseQueue2, &receivedPublish, TICKS_TO_WAIT ) )
        {
            pReceivedPublish = &( receivedPublish.publishInfo );
            pReceivedPublish->pTopicName = ( const char * ) receivedPublish.pTopicName;
            pReceivedPublish->pPayload = receivedPublish.pPayload;
            LogInfo( ( "Received publish on topic %.*s\n", pReceivedPublish->topicNameLength, pReceivedPublish->pTopicName ) );
            LogInfo( ( "Message payload: %.*s\n", ( int ) pReceivedPublish->payloadLength, ( const char * ) pReceivedPublish->pPayload ) );
            subCounter++;
            /* Break if all publishes have been received. */
            if( subCounter >= PUBLISH_COUNT )
            {
                break;
            }
        }
        if( subCounter >= PUBLISH_COUNT )
        {
            break;
        }

        LogInfo( ("    No messages queued, received %d publishes, sleeping for %d ms\n", subCounter, 400 ) );
        vTaskDelay( pdMS_TO_TICKS( 400 ) );
    }

    LogInfo( ("Finished receiving\n" ) );
    createCommand( UNSUBSCRIBE, &context, comCallback, &command );
    initializeCommandContext( &context );
    context.pResponseQueue = pResponseQueue2;
    context.taskToNotify = xTaskGetCurrentTaskHandle();
    context.notificationBit = 2;
    context.pSubscribeInfo = &subscribeInfo;
    LogInfo( ("Adding unsubscribe operation\n" ) );
    addCommandToQueue( &command );
    LogInfo( ("Starting wait on operation\n" ) );
    xTaskNotifyWait( 0, 2, &notification, 2 * TICKS_TO_WAIT );
    configASSERT( ( notification & 2 ) == 2 );
    destroyCommandContext( &context );
    LogInfo( ("Operation wait complete.\n" ) );

    /* Notify main task this task can be deleted. */
    xTaskNotify( mainTask, TASK2_COMPLETE_BIT, eSetBits );

    return;
}

/*-----------------------------------------------------------*/

static void prvMQTTDemoTask( void * pvParameters )
{
    NetworkContext_t xNetworkContext = { 0 };
    BaseType_t xNetworkStatus;
    uint32_t ulNotification = 0;

    ( void ) pvParameters;

    ulGlobalEntryTimeMs = prvGetTimeMs();

    pCommandQueue = xQueueCreate( COMMAND_QUEUE_SIZE, sizeof( Command_t ) );
    pResponseQueue2 = xQueueCreate( PUBLISH_QUEUE_SIZE, sizeof( PublishElement_t ) );
    /* Task 1 doesn't receive anything in this demo, so it doesn't need a large queue. */
    pResponseQueue1 = xQueueCreate( 1, sizeof( PublishElement_t ) );

    // for( ; ; )
    // {

        /* Create inital process loop command. */
        Command_t command;
        createCommand( PROCESSLOOP, NULL, NULL, &command );
        addCommandToQueue( &command );

        LogInfo( ( "Create a TCP connection to %s.\r\n", BROKER_ENDPOINT ) );
        xNetworkStatus = Plaintext_FreeRTOS_Connect( &xNetworkContext,
                                                     BROKER_ENDPOINT,
                                                     BROKER_PORT,
                                                     TRANSPORT_SEND_RECV_TIMEOUT_MS,
                                                     TRANSPORT_SEND_RECV_TIMEOUT_MS );
        configASSERT( xNetworkStatus == 0 );
        establishMqttSession( &globalMqttContext, &xNetworkContext );

        xTaskCreate( thread2, "Thread2", democonfigDEMO_STACKSIZE, NULL, tskIDLE_PRIORITY, &task2 );
        vTaskDelay( pdMS_TO_TICKS( 100 ) );
        xTaskCreate( thread1, "Thread1", democonfigDEMO_STACKSIZE, NULL, tskIDLE_PRIORITY, &task1 );

        LogInfo( ( "Running command loop" ) );
        commandLoop();
    // }

    /* Delete created tasks and queues. */
    while( ( ulNotification & TASK2_COMPLETE_BIT ) != TASK2_COMPLETE_BIT )
    {
        LogInfo( ( "Waiting for task 2 to exit." ) );
        xTaskNotifyWait( 0, TASK2_COMPLETE_BIT, &ulNotification, TICKS_TO_WAIT );
    }
    configASSERT( ( ulNotification & TASK2_COMPLETE_BIT ) == TASK2_COMPLETE_BIT );
    vTaskDelete( task2 );
    LogInfo( ( "Task 2 Deleted." ) );
    while( ( ulNotification & TASK1_COMPLETE_BIT ) != TASK1_COMPLETE_BIT )
    {
        LogInfo( ( "Waiting for task 1 to exit." ) );
        xTaskNotifyWait( 0, TASK1_COMPLETE_BIT, &ulNotification, TICKS_TO_WAIT );
    }
    configASSERT( ( ulNotification & TASK1_COMPLETE_BIT ) == TASK1_COMPLETE_BIT );
    vTaskDelete( task1 );
    LogInfo( ( "Task 1 Deleted." ) );
    vQueueDelete( pCommandQueue );
    vQueueDelete( pResponseQueue1 );
    vQueueDelete( pResponseQueue2 );
}

/*
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
                 &mainTask );              /* Used to pass out a handle to the created task. */
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
