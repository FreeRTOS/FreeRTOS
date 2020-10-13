/*
 * FreeRTOS V202010.00
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

/**
 * @file shadow_demo_helpers.c
 *
 * @brief This file provides helper functions used by the Shadow demo application to
 * do MQTT operations over a mutually authenticated TLS connection.
 *
 * A mutually authenticated TLS connection is used to connect to the AWS IoT
 * MQTT message broker in this example. Define ROOT_CA_CERT_PATH,
 * CLIENT_CERT_PATH, and CLIENT_PRIVATE_KEY_PATH in demo_config.h to achieve
 * mutual authentication.
 */

/* Standard includes. */
#include <assert.h>
#include <stdlib.h>
#include <string.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Shadow includes */
#include "shadow_demo_helpers.h"

/* Demo Specific configs. */
#include "demo_config.h"

/* MQTT library includes. */
#include "core_mqtt.h"

/* Retry utilities include. */
#include "retry_utils.h"

/* Transport interface implementation include header for TLS. */
#include "tls_freertos.h"

/*------------- Demo configurations -------------------------*/

/** Note: The device client certificate and private key credentials are
 * obtained by the transport interface implementation (with Secure Sockets)
 * from the demos/include/aws_clientcredential_keys.h file.
 *
 * The following macros SHOULD be defined for this demo which uses both server
 * and client authentications for TLS session:
 *   - keyCLIENT_CERTIFICATE_PEM for client certificate.
 *   - keyCLIENT_PRIVATE_KEY_PEM for client private key.
 */

#ifndef democonfigMQTT_BROKER_ENDPOINT
    #define democonfigMQTT_BROKER_ENDPOINT    clientcredentialMQTT_BROKER_ENDPOINT
#endif

#ifndef democonfigCLIENT_IDENTIFIER

/**
 * @brief The MQTT client identifier used in this example.  Each client identifier
 * must be unique so edit as required to ensure no two clients connecting to the
 * same broker use the same client identifier.
 */
    #define democonfigCLIENT_IDENTIFIER    clientcredentialIOT_THING_NAME
#endif

#ifndef democonfigMQTT_BROKER_PORT

/**
 * @brief The port to use for the demo.
 */
    #define democonfigMQTT_BROKER_PORT    clientcredentialMQTT_BROKER_PORT
#endif

/*-----------------------------------------------------------*/

/**
 * @brief Timeout for receiving CONNACK packet in milliseconds.
 */
#define mqttexampleCONNACK_RECV_TIMEOUT_MS           ( 1000U )

/**
 * @brief The number of topic filters to subscribe.
 */
#define mqttexampleTOPIC_COUNT                       ( 1 )

/**
 * @brief Time to wait between each cycle of the demo implemented by prvMQTTDemoTask().
 */
#define mqttexampleDELAY_BETWEEN_DEMO_ITERATIONS     ( pdMS_TO_TICKS( 5000U ) )

/**
 * @brief Timeout for MQTT_ProcessLoop in milliseconds.
 */
#define mqttexamplePROCESS_LOOP_TIMEOUT_MS           ( 500U )

/**
 * @brief Keep alive time reported to the broker while establishing an MQTT connection.
 *
 * It is the responsibility of the Client to ensure that the interval between
 * Control Packets being sent does not exceed the this Keep Alive value. In the
 * absence of sending any other Control Packets, the Client MUST send a
 * PINGREQ Packet.
 */
#define mqttexampleKEEP_ALIVE_TIMEOUT_SECONDS        ( 60U )

/**
 * @brief Delay between MQTT publishes. Note that the process loop also has a
 * timeout, so the total time between publishes is the sum of the two delays.
 */
#define mqttexampleDELAY_BETWEEN_PUBLISHES           ( pdMS_TO_TICKS( 500U ) )

/**
 * @brief Transport timeout in milliseconds for transport send and receive.
 */
#define mqttexampleTRANSPORT_SEND_RECV_TIMEOUT_MS    ( 200U )

/**
 * @brief Maximum number of outgoing publishes maintained in the application
 * until an ack is received from the broker.
 */
#define MAX_OUTGOING_PUBLISHES                       ( 1U )

/**
 * @brief Milliseconds per second.
 */
#define MILLISECONDS_PER_SECOND                      ( 1000U )

/**
 * @brief Milliseconds per FreeRTOS tick.
 */
#define MILLISECONDS_PER_TICK                        ( MILLISECONDS_PER_SECOND / configTICK_RATE_HZ )

/*-----------------------------------------------------------*/

/**
 * @brief Structure to keep the MQTT publish packets until an ack is received
 * for QoS1 publishes.
 */
typedef struct PublishPackets
{
    /**
     * @brief Packet identifier of the publish packet.
     */
    uint16_t packetId;

    /**
     * @brief Publish info of the publish packet.
     */
    MQTTPublishInfo_t pubInfo;
} PublishPackets_t;

/**
 * @brief Global entry time into the application to use as a reference timestamp
 * in the #prvGetTimeMs function. #prvGetTimeMs will always return the difference
 * between the current time and the global entry time. This will reduce the chances
 * of overflow for the 32 bit unsigned integer used for holding the timestamp.
 */
static uint32_t ulGlobalEntryTimeMs;

/*-----------------------------------------------------------*/

/**
 * @brief Packet Identifier generated when Subscribe request was sent to the broker;
 * it is used to match received Subscribe ACK to the transmitted subscribe.
 */
static uint16_t globalSubscribePacketIdentifier = 0U;

/**
 * @brief Packet Identifier generated when Unsubscribe request was sent to the broker;
 * it is used to match received Unsubscribe ACK to the transmitted unsubscribe
 * request.
 */
static uint16_t globalUnsubscribePacketIdentifier = 0U;

/**
 * @brief Array to keep the outgoing publish messages.
 * These stored outgoing publish messages are kept until a successful ack
 * is received.
 */
static PublishPackets_t outgoingPublishPackets[ MAX_OUTGOING_PUBLISHES ] = { 0 };

/**
 * @brief Static buffer used to hold MQTT messages being sent and received.
 */
static uint8_t ucSharedBuffer[ democonfigNETWORK_BUFFER_SIZE ];

/**
 * @brief The MQTT context used for MQTT operation.
 */
static MQTTContext_t mqttContext = { 0 };

/**
 * @brief The network context used for Openssl operation.
 */
static NetworkContext_t networkContext = { 0 };

/**
 * @brief The flag to indicate the mqtt session changed.
 */
static bool mqttSessionEstablished = false;

/**
 * @brief Static buffer used to hold MQTT messages being sent and received.
 */
static MQTTFixedBuffer_t xBuffer =
{
    .pBuffer = ucSharedBuffer,
    .size    = democonfigNETWORK_BUFFER_SIZE
};

/*-----------------------------------------------------------*/

/**
 * @brief Connect to MQTT broker with reconnection retries.
 *
 * If connection fails, retry is attempted after a timeout.
 * Timeout value will exponentially increase until maximum
 * timeout value is reached or the number of attempts are exhausted.
 *
 * @param[out] pxNetworkContext The output parameter to return the created network context.
 *
 * @return The status of the final connection attempt.
 */
static TlsTransportStatus_t prvConnectToServerWithBackoffRetries( NetworkContext_t * pxNetworkContext );

/**
 * @brief Function to get the free index at which an outgoing publish
 * can be stored.
 *
 * @param[out] pucIndex The output parameter to return the index at which an
 * outgoing publish message can be stored.
 *
 * @return EXIT_FAILURE if no more publishes can be stored;
 * EXIT_SUCCESS if an index to store the next outgoing publish is obtained.
 */
static int prvGetNextFreeIndexForOutgoingPublishes( uint8_t * pucIndex );

/**
 * @brief Function to clean up an outgoing publish at given index from the
 * #outgoingPublishPackets array.
 *
 * @param[in] ucIndex The index at which a publish message has to be cleaned up.
 */
static void vCleanupOutgoingPublishAt( uint8_t ucIndex );

/**
 * @brief Function to clean up all the outgoing publishes maintained in the
 * array.
 */
static void vCleanupOutgoingPublishes( void );

/**
 * @brief Function to clean up the publish packet with the given packet id.
 *
 * @param[in] usPacketId Packet identifier of the packet to be cleaned up from
 * the array.
 */
static void vCleanupOutgoingPublishWithPacketID( uint16_t usPacketId );

/**
 * @brief Function to resend the publishes if a session is re-established with
 * the broker. This function handles the resending of the QoS1 publish packets,
 * which are maintained locally.
 *
 * @param[in] pxMqttContext MQTT context pointer.
 */
static int handlePublishResend( MQTTContext_t * pxMqttContext );

/**
 * @brief The timer query function provided to the MQTT context.
 *
 * @return Time in milliseconds.
 */
static uint32_t prvGetTimeMs( void );

/*-----------------------------------------------------------*/

static TlsTransportStatus_t prvConnectToServerWithBackoffRetries( NetworkContext_t * pxNetworkContext )
{
    TlsTransportStatus_t xNetworkStatus = TLS_TRANSPORT_SUCCESS;
    RetryUtilsStatus_t xRetryUtilsStatus = RetryUtilsSuccess;
    RetryUtilsParams_t xReconnectParams = { 0 };
    NetworkCredentials_t xNetworkCredentials = { 0 };
    
    /* Set the credentials for establishing a TLS connection. */
    xNetworkCredentials.pRootCa = ( const unsigned char * ) democonfigROOT_CA_PEM;
    xNetworkCredentials.rootCaSize = sizeof( democonfigROOT_CA_PEM );
    #ifdef democonfigCLIENT_CERTIFICATE_PEM
        xNetworkCredentials.pClientCert = ( const unsigned char * ) democonfigCLIENT_CERTIFICATE_PEM;
        xNetworkCredentials.clientCertSize = sizeof( democonfigCLIENT_CERTIFICATE_PEM );
        xNetworkCredentials.pPrivateKey = ( const unsigned char * ) democonfigCLIENT_PRIVATE_KEY_PEM;
        xNetworkCredentials.privateKeySize = sizeof( democonfigCLIENT_PRIVATE_KEY_PEM );
    #endif
    #ifdef democonfigUSE_AWS_IOT_CORE_BROKER
        xNetworkCredentials.disableSni = pdFALSE;
        /* The ALPN string changes depending on whether username/password authentication is used. */
        #ifdef democonfigCLIENT_USERNAME
            xNetworkCredentials.pAlpnProtos = AWS_IOT_CUSTOM_AUTH_ALPN;
        #else
            xNetworkCredentials.pAlpnProtos = AWS_IOT_MQTT_ALPN;
        #endif
    #else

        /* When using a local Mosquitto server setup, SNI needs to be disabled for
         * an MQTT broker that only has an IP address but no hostname. However,
         * SNI should be enabled whenever possible. */
        xNetworkCredentials.disableSni = pdTRUE;
    #endif /* ifdef democonfigUSE_AWS_IOT_CORE_BROKER */

    /* Initialize reconnect attempts and interval. */
    RetryUtils_ParamsReset( &xReconnectParams );
    xReconnectParams.maxRetryAttempts = MAX_RETRY_ATTEMPTS;

    /* Attempt to connect to MQTT broker. If connection fails, retry after
     * a timeout. Timeout value will exponentially increase until maximum
     * attempts are reached.
     */
    do
    {
        /* Establish a TCP connection with the MQTT broker. This example connects to
         * the MQTT broker as specified in democonfigMQTT_BROKER_ENDPOINT and
         * democonfigMQTT_BROKER_PORT at the top of this file. */
        LogInfo( ( "Create a TCP connection to %s:%d.",
                   democonfigMQTT_BROKER_ENDPOINT,
                   democonfigMQTT_BROKER_PORT ) );
        xNetworkStatus = TLS_FreeRTOS_Connect( pxNetworkContext,
                                               democonfigMQTT_BROKER_ENDPOINT,
                                               democonfigMQTT_BROKER_PORT,
                                               &xNetworkCredentials,
                                               mqttexampleTRANSPORT_SEND_RECV_TIMEOUT_MS,
                                               mqttexampleTRANSPORT_SEND_RECV_TIMEOUT_MS );

        if( xNetworkStatus != TLS_TRANSPORT_SUCCESS )
        {
            LogWarn( ( "Connection to the broker failed. Retrying connection with backoff and jitter." ) );
            xRetryUtilsStatus = RetryUtils_BackoffAndSleep( &xReconnectParams );
        }

        if( xRetryUtilsStatus == RetryUtilsRetriesExhausted )
        {
            LogError( ( "Connection to the broker failed, all attempts exhausted." ) );
            xNetworkStatus = TLS_TRANSPORT_CONNECT_FAILURE;
        }
    } while( ( xNetworkStatus != TLS_TRANSPORT_SUCCESS ) && ( xRetryUtilsStatus == RetryUtilsSuccess ) );

    return xNetworkStatus;
}

/*-----------------------------------------------------------*/

static int prvGetNextFreeIndexForOutgoingPublishes( uint8_t * pucIndex )
{
    int returnStatus = EXIT_FAILURE;
    uint8_t ucIndex = 0;

    assert( outgoingPublishPackets != NULL );
    assert( pucIndex != NULL );

    for( ucIndex = 0; ucIndex < MAX_OUTGOING_PUBLISHES; ucIndex++ )
    {
        /* A free ucIndex is marked by invalid packet id.
         * Check if the the ucIndex has a free slot. */
        if( outgoingPublishPackets[ ucIndex ].packetId == MQTT_PACKET_ID_INVALID )
        {
            returnStatus = EXIT_SUCCESS;
            break;
        }
    }

    /* Copy the available ucIndex into the output param. */
    *pucIndex = ucIndex;

    return returnStatus;
}
/*-----------------------------------------------------------*/

static void vCleanupOutgoingPublishAt( uint8_t ucIndex )
{
    assert( outgoingPublishPackets != NULL );
    assert( ucIndex < MAX_OUTGOING_PUBLISHES );

    /* Clear the outgoing publish packet. */
    ( void ) memset( &( outgoingPublishPackets[ ucIndex ] ),
                     0x00,
                     sizeof( outgoingPublishPackets[ ucIndex ] ) );
}

/*-----------------------------------------------------------*/

static void vCleanupOutgoingPublishes( void )
{
    assert( outgoingPublishPackets != NULL );

    /* Clean up all the outgoing publish packets. */
    ( void ) memset( outgoingPublishPackets, 0x00, sizeof( outgoingPublishPackets ) );
}

/*-----------------------------------------------------------*/

static void vCleanupOutgoingPublishWithPacketID( uint16_t usPacketId )
{
    uint8_t ucIndex = 0;

    assert( outgoingPublishPackets != NULL );
    assert( usPacketId != MQTT_PACKET_ID_INVALID );

    /* Clean up all the saved outgoing publishes. */
    for( ; ucIndex < MAX_OUTGOING_PUBLISHES; ucIndex++ )
    {
        if( outgoingPublishPackets[ ucIndex ].packetId == usPacketId )
        {
            vCleanupOutgoingPublishAt( ucIndex );
            LogInfo( ( "Cleaned up outgoing publish packet with packet id %u.\n\n",
                       usPacketId ) );
            break;
        }
    }
}

/*-----------------------------------------------------------*/

void vHandleOtherIncomingPacket( MQTTPacketInfo_t * pxPacketInfo,
                                 uint16_t usPacketIdentifier )
{
    /* Handle other packets. */
    switch( pxPacketInfo->type )
    {
        case MQTT_PACKET_TYPE_SUBACK:
            LogInfo( ( "MQTT_PACKET_TYPE_SUBACK.\n\n" ) );
            /* Make sure ACK packet identifier matches with Request packet identifier. */
            assert( globalSubscribePacketIdentifier == usPacketIdentifier );
            break;

        case MQTT_PACKET_TYPE_UNSUBACK:
            LogInfo( ( "MQTT_PACKET_TYPE_UNSUBACK.\n\n" ) );
            /* Make sure ACK packet identifier matches with Request packet identifier. */
            assert( globalUnsubscribePacketIdentifier == usPacketIdentifier );
            break;

        case MQTT_PACKET_TYPE_PINGRESP:

            /* Nothing to be done from application as library handles
             * PINGRESP. */
            LogWarn( ( "PINGRESP should not be handled by the application "
                       "callback when using MQTT_ProcessLoop.\n\n" ) );
            break;

        case MQTT_PACKET_TYPE_PUBACK:
            LogInfo( ( "PUBACK received for packet id %u.\n\n",
                       usPacketIdentifier ) );
            /* Cleanup publish packet when a PUBACK is received. */
            vCleanupOutgoingPublishWithPacketID( usPacketIdentifier );
            break;

        /* Any other packet type is invalid. */
        default:
            LogError( ( "Unknown packet type received:(%02x).\n\n",
                        pxPacketInfo->type ) );
    }
}

/*-----------------------------------------------------------*/

static int handlePublishResend( MQTTContext_t * pxMqttContext )
{
    int returnStatus = EXIT_SUCCESS;
    MQTTStatus_t eMqttStatus = MQTTSuccess;
    uint8_t ucIndex = 0U;

    assert( outgoingPublishPackets != NULL );

    /* Resend all the QoS1 publishes still in the array. These are the
     * publishes that hasn't received a PUBACK. When a PUBACK is
     * received, the publish is removed from the array. */
    for( ucIndex = 0U; ucIndex < MAX_OUTGOING_PUBLISHES; ucIndex++ )
    {
        if( outgoingPublishPackets[ ucIndex ].packetId != MQTT_PACKET_ID_INVALID )
        {
            outgoingPublishPackets[ ucIndex ].pubInfo.dup = true;

            LogInfo( ( "Sending duplicate PUBLISH with packet id %u.",
                       outgoingPublishPackets[ ucIndex ].packetId ) );
            eMqttStatus = MQTT_Publish( pxMqttContext,
                                        &outgoingPublishPackets[ ucIndex ].pubInfo,
                                        outgoingPublishPackets[ ucIndex ].packetId );

            if( eMqttStatus != MQTTSuccess )
            {
                LogError( ( "Sending duplicate PUBLISH for packet id %u "
                            " failed with status %u.",
                            outgoingPublishPackets[ ucIndex ].packetId,
                            eMqttStatus ) );
                returnStatus = EXIT_FAILURE;
                break;
            }
            else
            {
                LogInfo( ( "Sent duplicate PUBLISH successfully for packet id %u.\n\n",
                           outgoingPublishPackets[ ucIndex ].packetId ) );
            }
        }
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

TlsTransportStatus_t xEstablishMqttSession( MQTTEventCallback_t eventCallback )
{
    TlsTransportStatus_t returnStatus = EXIT_SUCCESS;
    MQTTStatus_t eMqttStatus;
    MQTTConnectInfo_t xConnectInfo;
    TransportInterface_t xTransport;
    MQTTContext_t * pxMqttContext = &mqttContext;
    NetworkContext_t * pxNetworkContext = &networkContext;
    bool sessionPresent = false;

    assert( pxMqttContext != NULL );
    assert( pxNetworkContext != NULL );

    /* Initialize the mqtt context and network context. */
    ( void ) memset( pxMqttContext, 0U, sizeof( MQTTContext_t ) );
    ( void ) memset( pxNetworkContext, 0U, sizeof( NetworkContext_t ) );

    returnStatus = prvConnectToServerWithBackoffRetries( pxNetworkContext );

    if( returnStatus != EXIT_SUCCESS )
    {
        /* Log error to indicate connection failure after all
         * reconnect attempts are over. */
        LogError( ( "Failed to connect to MQTT broker %.*s.",
                    strlen( democonfigMQTT_BROKER_ENDPOINT ),
                    democonfigMQTT_BROKER_ENDPOINT ) );
    }
    else
    {
        /* Fill in Transport Interface send and receive function pointers. */
        xTransport.pNetworkContext = pxNetworkContext;
        xTransport.send = TLS_FreeRTOS_send;
        xTransport.recv = TLS_FreeRTOS_recv;

        /* Initialize MQTT library. */
        eMqttStatus = MQTT_Init( pxMqttContext,
                                 &xTransport,
                                 prvGetTimeMs,
                                 eventCallback,
                                 &xBuffer );

        if( eMqttStatus != MQTTSuccess )
        {
            returnStatus = EXIT_FAILURE;
            LogError( ( "MQTT init failed with status %u.", eMqttStatus ) );
        }
        else
        {
            /* Establish MQTT session by sending a CONNECT packet. */

            /* Many fields not used in this demo so start with everything at 0. */
            ( void ) memset( ( void * ) &xConnectInfo, 0x00, sizeof( xConnectInfo ) );

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

            /* The maximum time interval in seconds which is allowed to elapse
             * between two Control Packets.
             * It is the responsibility of the Client to ensure that the interval between
             * Control Packets being sent does not exceed the this Keep Alive value. In the
             * absence of sending any other Control Packets, the Client MUST send a
             * PINGREQ Packet. */
            xConnectInfo.keepAliveSeconds = mqttexampleKEEP_ALIVE_TIMEOUT_SECONDS;

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
                #endif /* ifdef democonfigCLIENT_USERNAME */
            #else /* ifdef democonfigUSE_AWS_IOT_CORE_BROKER */
                #ifdef democonfigCLIENT_USERNAME
                    xConnectInfo.pUserName = democonfigCLIENT_USERNAME;
                    xConnectInfo.userNameLength = ( uint16_t ) strlen( democonfigCLIENT_USERNAME );
                    xConnectInfo.pPassword = democonfigCLIENT_PASSWORD;
                    xConnectInfo.passwordLength = ( uint16_t ) strlen( democonfigCLIENT_PASSWORD );
                #endif /* ifdef democonfigCLIENT_USERNAME */
            #endif /* ifdef democonfigUSE_AWS_IOT_CORE_BROKER */

            /* Send MQTT CONNECT packet to broker. */
            eMqttStatus = MQTT_Connect( pxMqttContext,
                                        &xConnectInfo,
                                        NULL,
                                        mqttexampleCONNACK_RECV_TIMEOUT_MS,
                                        &sessionPresent );

            if( eMqttStatus != MQTTSuccess )
            {
                returnStatus = EXIT_FAILURE;
                LogError( ( "Connection with MQTT broker failed with status %u.", eMqttStatus ) );
            }
            else
            {
                LogInfo( ( "MQTT connection successfully established with broker.\n\n" ) );
            }
        }

        if( returnStatus == EXIT_SUCCESS )
        {
            /* Keep a flag for indicating if MQTT session is established. This
             * flag will mark that an MQTT DISCONNECT has to be sent at the end
             * of the demo even if there are intermediate failures. */
            mqttSessionEstablished = true;
        }

        if( returnStatus == EXIT_SUCCESS )
        {
            /* Check if session is present and if there are any outgoing publishes
             * that need to resend. This is only valid if the broker is
             * re-establishing a session which was already present. */
            if( sessionPresent == true )
            {
                LogInfo( ( "An MQTT session with broker is re-established. "
                           "Resending unacked publishes." ) );

                /* Handle all the resend of publish messages. */
                returnStatus = handlePublishResend( &mqttContext );
            }
            else
            {
                LogInfo( ( "A clean MQTT connection is established."
                           " Cleaning up all the stored outgoing publishes.\n\n" ) );

                /* Clean up the outgoing publishes waiting for ack as this new
                 * connection doesn't re-establish an existing session. */
                vCleanupOutgoingPublishes();
            }
        }
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

int32_t lDisconnectMqttSession( void )
{
    MQTTStatus_t eMqttStatus = MQTTSuccess;
    int returnStatus = EXIT_SUCCESS;
    TlsTransportStatus_t xNetworkStatus;
    MQTTContext_t * pxMqttContext = &mqttContext;
    NetworkContext_t * pxNetworkContext = &networkContext;

    assert( pxMqttContext != NULL );
    assert( pxNetworkContext != NULL );

    if( mqttSessionEstablished == true )
    {
        /* Send DISCONNECT. */
        eMqttStatus = MQTT_Disconnect( pxMqttContext );

        if( eMqttStatus != MQTTSuccess )
        {
            LogError( ( "Sending MQTT DISCONNECT failed with status=%u.",
                        eMqttStatus ) );
            returnStatus = EXIT_FAILURE;
        }
    }

    /* Close the network connection.  */
    TLS_FreeRTOS_Disconnect( pxNetworkContext );

    return returnStatus;
}

/*-----------------------------------------------------------*/

int32_t lSubscribeToTopic( const char * pcTopicFilter,
                          uint16_t usTopicFilterLength )
{
    int returnStatus = EXIT_SUCCESS;
    MQTTStatus_t eMqttStatus;
    MQTTContext_t * pxMqttContext = &mqttContext;
    MQTTSubscribeInfo_t pSubscriptionList[ mqttexampleTOPIC_COUNT ];

    assert( pxMqttContext != NULL );
    assert( pcTopicFilter != NULL );
    assert( usTopicFilterLength > 0 );

    /* Start with everything at 0. */
    ( void ) memset( ( void * ) pSubscriptionList, 0x00, sizeof( pSubscriptionList ) );

    /* This example subscribes to only one topic and uses QOS1. */
    pSubscriptionList[ 0 ].qos = MQTTQoS1;
    pSubscriptionList[ 0 ].pTopicFilter = pcTopicFilter;
    pSubscriptionList[ 0 ].topicFilterLength = usTopicFilterLength;

    /* Generate packet identifier for the SUBSCRIBE packet. */
    globalSubscribePacketIdentifier = MQTT_GetPacketId( pxMqttContext );

    /* Send SUBSCRIBE packet. */
    eMqttStatus = MQTT_Subscribe( pxMqttContext,
                                  pSubscriptionList,
                                  sizeof( pSubscriptionList ) / sizeof( MQTTSubscribeInfo_t ),
                                  globalSubscribePacketIdentifier );

    if( eMqttStatus != MQTTSuccess )
    {
        LogError( ( "Failed to send SUBSCRIBE packet to broker with error = %u.",
                    eMqttStatus ) );
        returnStatus = EXIT_FAILURE;
    }
    else
    {
        LogInfo( ( "SUBSCRIBE topic %.*s to broker.\n\n",
                   usTopicFilterLength,
                   pcTopicFilter ) );

        /* Process incoming packet from the broker. Acknowledgment for subscription
         * ( SUBACK ) will be received here. However after sending the subscribe, the
         * client may receive a publish before it receives a subscribe ack. Since this
         * demo is subscribing to the topic to which no one is publishing, probability
         * of receiving publish message before subscribe ack is zero; but application
         * must be ready to receive any packet. This demo uses MQTT_ProcessLoop to
         * receive packet from network. */
        eMqttStatus = MQTT_ProcessLoop( pxMqttContext, mqttexamplePROCESS_LOOP_TIMEOUT_MS );

        if( eMqttStatus != MQTTSuccess )
        {
            returnStatus = EXIT_FAILURE;
            LogError( ( "MQTT_ProcessLoop returned with status = %u.",
                        eMqttStatus ) );
        }
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

int32_t lUnsubscribeFromTopic( const char * pcTopicFilter,
                              uint16_t usTopicFilterLength )
{
    int returnStatus = EXIT_SUCCESS;
    MQTTStatus_t eMqttStatus;
    MQTTContext_t * pxMqttContext = &mqttContext;
    MQTTSubscribeInfo_t pSubscriptionList[ 1 ];

    assert( pxMqttContext != NULL );
    assert( pcTopicFilter != NULL );
    assert( usTopicFilterLength > 0 );

    /* Start with everything at 0. */
    ( void ) memset( ( void * ) pSubscriptionList, 0x00, sizeof( pSubscriptionList ) );

    /* This example subscribes to only one topic and uses QOS1. */
    pSubscriptionList[ 0 ].qos = MQTTQoS1;
    pSubscriptionList[ 0 ].pTopicFilter = pcTopicFilter;
    pSubscriptionList[ 0 ].topicFilterLength = usTopicFilterLength;

    /* Generate packet identifier for the UNSUBSCRIBE packet. */
    globalUnsubscribePacketIdentifier = MQTT_GetPacketId( pxMqttContext );

    /* Send UNSUBSCRIBE packet. */
    eMqttStatus = MQTT_Unsubscribe( pxMqttContext,
                                    pSubscriptionList,
                                    sizeof( pSubscriptionList ) / sizeof( MQTTSubscribeInfo_t ),
                                    globalUnsubscribePacketIdentifier );

    if( eMqttStatus != MQTTSuccess )
    {
        LogError( ( "Failed to send UNSUBSCRIBE packet to broker with error = %u.",
                    eMqttStatus ) );
        returnStatus = EXIT_FAILURE;
    }
    else
    {
        LogInfo( ( "UNSUBSCRIBE sent topic %.*s to broker.\n\n",
                   usTopicFilterLength,
                   pcTopicFilter ) );

        /* Process incoming packet from the broker. Acknowledgment for subscription
         * ( SUBACK ) will be received here. However after sending the subscribe, the
         * client may receive a publish before it receives a subscribe ack. Since this
         * demo is subscribing to the topic to which no one is publishing, probability
         * of receiving publish message before subscribe ack is zero; but application
         * must be ready to receive any packet. This demo uses MQTT_ProcessLoop to
         * receive packet from network. */
        eMqttStatus = MQTT_ProcessLoop( pxMqttContext, mqttexamplePROCESS_LOOP_TIMEOUT_MS );

        if( eMqttStatus != MQTTSuccess )
        {
            returnStatus = EXIT_FAILURE;
            LogError( ( "MQTT_ProcessLoop returned with status = %u.",
                        eMqttStatus ) );
        }
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

int32_t lPublishToTopic( const char * pcTopicFilter,
                        int32_t topicFilterLength,
                        const char * pcPayload,
                        size_t payloadLength )
{
    int returnStatus = EXIT_SUCCESS;
    MQTTStatus_t eMqttStatus = MQTTSuccess;
    uint8_t ucPublishIndex = MAX_OUTGOING_PUBLISHES;
    MQTTContext_t * pxMqttContext = &mqttContext;

    assert( pxMqttContext != NULL );
    assert( pcTopicFilter != NULL );
    assert( topicFilterLength > 0 );

    /* Get the next free index for the outgoing publish. All QoS1 outgoing
     * publishes are stored until a PUBACK is received. These messages are
     * stored for supporting a resend if a network connection is broken before
     * receiving a PUBACK. */
    returnStatus = prvGetNextFreeIndexForOutgoingPublishes( &ucPublishIndex );

    if( returnStatus == EXIT_FAILURE )
    {
        LogError( ( "Unable to find a free spot for outgoing PUBLISH message.\n\n" ) );
    }
    else
    {
        LogInfo( ( "the published payload:%s \r\n ", pcPayload ) );
        /* This example publishes to only one topic and uses QOS1. */
        outgoingPublishPackets[ ucPublishIndex ].pubInfo.qos = MQTTQoS1;
        outgoingPublishPackets[ ucPublishIndex ].pubInfo.pTopicName = pcTopicFilter;
        outgoingPublishPackets[ ucPublishIndex ].pubInfo.topicNameLength = topicFilterLength;
        outgoingPublishPackets[ ucPublishIndex ].pubInfo.pPayload = pcPayload;
        outgoingPublishPackets[ ucPublishIndex ].pubInfo.payloadLength = payloadLength;

        /* Get a new packet id. */
        outgoingPublishPackets[ ucPublishIndex ].packetId = MQTT_GetPacketId( pxMqttContext );

        /* Send PUBLISH packet. */
        eMqttStatus = MQTT_Publish( pxMqttContext,
                                    &outgoingPublishPackets[ ucPublishIndex ].pubInfo,
                                    outgoingPublishPackets[ ucPublishIndex ].packetId );

        if( eMqttStatus != MQTTSuccess )
        {
            LogError( ( "Failed to send PUBLISH packet to broker with error = %u.",
                        eMqttStatus ) );
            vCleanupOutgoingPublishAt( ucPublishIndex );
            returnStatus = EXIT_FAILURE;
        }
        else
        {
            LogInfo( ( "PUBLISH sent for topic %.*s to broker with packet ID %u.\n\n",
                       topicFilterLength,
                       pcTopicFilter,
                       outgoingPublishPackets[ ucPublishIndex ].packetId ) );

            /* Calling MQTT_ProcessLoop to process incoming publish echo, since
             * application subscribed to the same topic the broker will send
             * publish message back to the application. This function also
             * sends ping request to broker if MQTT_KEEP_ALIVE_INTERVAL_SECONDS
             * has expired since the last MQTT packet sent and receive
             * ping responses. */
            eMqttStatus = MQTT_ProcessLoop( &mqttContext, mqttexamplePROCESS_LOOP_TIMEOUT_MS );

            if( eMqttStatus != MQTTSuccess )
            {
                LogWarn( ( "MQTT_ProcessLoop returned with status = %u.",
                           eMqttStatus ) );
            }
        }
    }

    return returnStatus;
}
/*-----------------------------------------------------------*/

static uint32_t prvGetTimeMs( void )
{
    TickType_t xTickCount = 0;
    uint32_t ulTimeMs = 0UL;

    /* Get the current tick count. */
    xTickCount = xTaskGetTickCount();

    /* Convert the ticks to milliseconds. */
    ulTimeMs = ( uint32_t ) xTickCount * MILLISECONDS_PER_TICK;

    /* Reduce ulGlobalEntryTimeMs from obtained time so as to always return the
     * elapsed time in the application. */
    ulTimeMs = ( uint32_t ) ( ulTimeMs - ulGlobalEntryTimeMs );

    return ulTimeMs;
}

/*-----------------------------------------------------------*/
