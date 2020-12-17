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

/**
 * @file mqtt_demo_helpers.c
 *
 * @brief This file provides helper functions used by the AWS demo applications to
 * do MQTT operations over a mutually authenticated TLS connection.
 *
 * A mutually authenticated TLS connection is used to connect to the AWS IoT
 * MQTT message broker in this example. Define democonfigCLIENT_PRIVATE_KEY_PEM,
 * democonfigCLIENT_CERTIFICATE_PEM, and democonfigMQTT_BROKER_ENDPOINT in
 * demo_config.h to achieve mutual authentication.
 */

/* Standard includes. */
#include <stdlib.h>
#include <string.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Shadow includes */
#include "mqtt_demo_helpers.h"

/* MQTT library includes. */
#include "core_mqtt.h"

/* Exponential backoff retry include. */
#include "backoff_algorithm.h"

/* Transport interface implementation include header for TLS. */
#include "using_mbedtls.h"

/* Demo specific config. */
#include "demo_config.h"

/*------------- Demo configurations -------------------------*/

/**
 * Note: The TLS connection credentials for the server root CA certificate,
 * and device client certificate and private key should be defined in the
 * demo_config.h file.
 */

#ifndef democonfigROOT_CA_PEM
    #error "Please define the AWS Root CA certificate (democonfigROOT_CA_PEM) in demo_config.h."
#endif
#ifndef democonfigCLIENT_PRIVATE_KEY_PEM
    #error "Please define client private key (democonfigCLIENT_PRIVATE_KEY_PEM) in demo_config.h."
#endif

#ifndef democonfigCLIENT_CERTIFICATE_PEM
    #error "Please define client certificate (democonfigCLIENT_CERTIFICATE_PEM) in demo_config.h."
#endif

#ifndef democonfigMQTT_BROKER_ENDPOINT
    #error "Please define the AWS IoT broker endpoint (democonfigMQTT_BROKER_ENDPOINT) in demo_config.h."
#endif

/*-----------------------------------------------------------*/

/**
 * @brief The maximum number of retries for network operation with server.
 */
#define RETRY_MAX_ATTEMPTS                           ( 5U )

/**
 * @brief The maximum back-off delay (in milliseconds) for retrying failed operation
 *  with server.
 */
#define RETRY_MAX_BACKOFF_DELAY_MS                   ( 5000U )

/**
 * @brief The base back-off delay (in milliseconds) to use for network operation retry
 * attempts.
 */
#define RETRY_BACKOFF_BASE_MS                        ( 500U )

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
 * Control Packets being sent does not exceed this Keep Alive value. In the
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

/**
 * @brief The MQTT metrics string expected by AWS IoT.
 */
#define AWS_IOT_METRICS_STRING                                 \
    "?SDK=" democonfigOS_NAME "&Version=" democonfigOS_VERSION \
    "&Platform=" democonfigHARDWARE_PLATFORM_NAME "&MQTTLib=" democonfigMQTT_LIB

/**
 * @brief The length of the MQTT metrics string expected by AWS IoT.
 */
#define AWS_IOT_METRICS_STRING_LENGTH    ( ( uint16_t ) ( sizeof( AWS_IOT_METRICS_STRING ) - 1 ) )

/**
 * @brief ALPN (Application-Layer Protocol Negotiation) protocol name for AWS IoT MQTT.
 *
 * This will be used if democonfigMQTT_BROKER_PORT is configured as 443 for the AWS IoT MQTT broker.
 * Please see more details about the ALPN protocol for AWS IoT MQTT endpoint
 * in the link below.
 * https://aws.amazon.com/blogs/iot/mqtt-with-tls-client-authentication-on-port-443-why-it-is-useful-and-how-it-works/
 */
#define AWS_IOT_MQTT_ALPN                "\x0ex-amzn-mqtt-ca"


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
    TlsTransportParams_t * pParams;
};

/*-----------------------------------------------------------*/

/**
 * @brief Global entry time into the application to use as a reference timestamp
 * in the #prvGetTimeMs function. #prvGetTimeMs will always return the difference
 * between the current time and the global entry time. This will reduce the chances
 * of overflow for the 32 bit unsigned integer used for holding the timestamp.
 */
static uint32_t ulGlobalEntryTimeMs;

/**
 * @brief The flag to indicate the MQTT session changed.
 */
static BaseType_t xMqttSessionEstablished = pdFALSE;

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

/*-----------------------------------------------------------*/

/**
 * @brief A wrapper to the "uxRand()" random number generator so that it
 * can be passed to the backoffAlgorithm library for retry logic.
 *
 * This function implements the #BackoffAlgorithm_RNG_T type interface
 * in the backoffAlgorithm library API.
 *
 * @note The "uxRand" function represents a pseudo random number generator.
 * However, it is recommended to use a True Randon Number Generator (TRNG)
 * for generating unique device-specific random values to avoid possibility
 * of network collisions from multiple devices retrying network operations.
 *
 * @return The generated randon number. This function ALWAYS succeeds.
 */
static int32_t prvGenerateRandomNumber();

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
 * @return pdFAIL if no more publishes can be stored;
 * pdTRUE if an index to store the next outgoing publish is obtained.
 */
static BaseType_t prvGetNextFreeIndexForOutgoingPublishes( uint8_t * pucIndex );

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
static BaseType_t xHandlePublishResend( MQTTContext_t * pxMqttContext );

/**
 * @brief The timer query function provided to the MQTT context.
 *
 * @return Time in milliseconds.
 */
static uint32_t prvGetTimeMs( void );

/*-----------------------------------------------------------*/

static int32_t prvGenerateRandomNumber()
{
    return( uxRand() & INT32_MAX );
}

/*-----------------------------------------------------------*/

static TlsTransportStatus_t prvConnectToServerWithBackoffRetries( NetworkContext_t * pxNetworkContext )
{
    TlsTransportStatus_t xNetworkStatus = TLS_TRANSPORT_SUCCESS;
    BackoffAlgorithmStatus_t xBackoffAlgStatus = BackoffAlgorithmSuccess;
    BackoffAlgorithmContext_t xReconnectParams = { 0 };
    NetworkCredentials_t xNetworkCredentials = { 0 };
    uint16_t usNextRetryBackOff = 0U;

    /* ALPN protocols must be a NULL-terminated list of strings. Therefore,
     * the first entry will contain the actual ALPN protocol string while the
     * second entry must remain NULL. */
    char * pcAlpnProtocols[] = { NULL, NULL };

    configASSERT( pxNetworkContext != NULL );

    /* Set the credentials for establishing a TLS connection. */
    xNetworkCredentials.pRootCa = ( const unsigned char * ) democonfigROOT_CA_PEM;
    xNetworkCredentials.rootCaSize = sizeof( democonfigROOT_CA_PEM );
    #ifdef democonfigCLIENT_CERTIFICATE_PEM
        xNetworkCredentials.pClientCert = ( const unsigned char * ) democonfigCLIENT_CERTIFICATE_PEM;
        xNetworkCredentials.clientCertSize = sizeof( democonfigCLIENT_CERTIFICATE_PEM );
        xNetworkCredentials.pPrivateKey = ( const unsigned char * ) democonfigCLIENT_PRIVATE_KEY_PEM;
        xNetworkCredentials.privateKeySize = sizeof( democonfigCLIENT_PRIVATE_KEY_PEM );
    #endif

    xNetworkCredentials.disableSni = pdFALSE;
/* The ALPN string changes depending on whether username/password authentication is used. */
    #ifdef democonfigCLIENT_USERNAME
        pcAlpnProtocols[ 0 ] = AWS_IOT_CUSTOM_AUTH_ALPN;
    #else
        pcAlpnProtocols[ 0 ] = AWS_IOT_MQTT_ALPN;
    #endif
    xNetworkCredentials.pAlpnProtos = pcAlpnProtocols;

    /* Initialize reconnect attempts and interval.*/
    BackoffAlgorithm_InitializeParams( &xReconnectParams,
                                       RETRY_BACKOFF_BASE_MS,
                                       RETRY_MAX_BACKOFF_DELAY_MS,
                                       RETRY_MAX_ATTEMPTS );

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
    } while( ( xNetworkStatus != TLS_TRANSPORT_SUCCESS ) && ( xBackoffAlgStatus == BackoffAlgorithmSuccess ) );

    return xNetworkStatus;
}

/*-----------------------------------------------------------*/

static BaseType_t prvGetNextFreeIndexForOutgoingPublishes( uint8_t * pucIndex )
{
    BaseType_t xReturnStatus = pdFAIL;
    uint8_t ucIndex = 0;

    configASSERT( outgoingPublishPackets != NULL );
    configASSERT( pucIndex != NULL );

    for( ucIndex = 0; ucIndex < MAX_OUTGOING_PUBLISHES; ucIndex++ )
    {
        /* A free ucIndex is marked by invalid packet id.
         * Check if the ucIndex has a free slot. */
        if( outgoingPublishPackets[ ucIndex ].packetId == MQTT_PACKET_ID_INVALID )
        {
            xReturnStatus = pdPASS;
            break;
        }
    }

    /* Copy the available ucIndex into the output param. */
    *pucIndex = ucIndex;

    return xReturnStatus;
}
/*-----------------------------------------------------------*/

static void vCleanupOutgoingPublishAt( uint8_t ucIndex )
{
    configASSERT( outgoingPublishPackets != NULL );
    configASSERT( ucIndex < MAX_OUTGOING_PUBLISHES );

    /* Clear the outgoing publish packet. */
    ( void ) memset( &( outgoingPublishPackets[ ucIndex ] ),
                     0x00,
                     sizeof( outgoingPublishPackets[ ucIndex ] ) );
}

/*-----------------------------------------------------------*/

static void vCleanupOutgoingPublishes( void )
{
    configASSERT( outgoingPublishPackets != NULL );

    /* Clean up all the outgoing publish packets. */
    ( void ) memset( outgoingPublishPackets, 0x00, sizeof( outgoingPublishPackets ) );
}

/*-----------------------------------------------------------*/

static void vCleanupOutgoingPublishWithPacketID( uint16_t usPacketId )
{
    uint8_t ucIndex = 0;

    configASSERT( outgoingPublishPackets != NULL );
    configASSERT( usPacketId != MQTT_PACKET_ID_INVALID );

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
            configASSERT( globalSubscribePacketIdentifier == usPacketIdentifier );
            break;

        case MQTT_PACKET_TYPE_UNSUBACK:
            LogInfo( ( "MQTT_PACKET_TYPE_UNSUBACK.\n\n" ) );
            /* Make sure ACK packet identifier matches with Request packet identifier. */
            configASSERT( globalUnsubscribePacketIdentifier == usPacketIdentifier );
            break;

        case MQTT_PACKET_TYPE_PINGRESP:

            /* Nothing to be done from application as library handles
             * PINGRESP with the use of MQTT_ProcessLoop API function. */
            LogWarn( ( "PINGRESP should not be handled by the application "
                       "callback when using MQTT_ProcessLoop.\n" ) );
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

static BaseType_t xHandlePublishResend( MQTTContext_t * pxMqttContext )
{
    BaseType_t xReturnStatus = pdTRUE;
    MQTTStatus_t xMQTTStatus = MQTTSuccess;
    uint8_t ucIndex = 0U;

    configASSERT( outgoingPublishPackets != NULL );

    /* Resend all the QoS1 publishes still in the array. These are the
     * publishes that haven't received a PUBACK. When a PUBACK is
     * received, the publish is removed from the array. */
    for( ucIndex = 0U; ucIndex < MAX_OUTGOING_PUBLISHES; ucIndex++ )
    {
        if( outgoingPublishPackets[ ucIndex ].packetId != MQTT_PACKET_ID_INVALID )
        {
            outgoingPublishPackets[ ucIndex ].pubInfo.dup = true;

            LogInfo( ( "Sending duplicate PUBLISH with packet id %u.",
                       outgoingPublishPackets[ ucIndex ].packetId ) );
            xMQTTStatus = MQTT_Publish( pxMqttContext,
                                        &outgoingPublishPackets[ ucIndex ].pubInfo,
                                        outgoingPublishPackets[ ucIndex ].packetId );

            if( xMQTTStatus != MQTTSuccess )
            {
                LogError( ( "Sending duplicate PUBLISH for packet id %u "
                            " failed with status %s.",
                            outgoingPublishPackets[ ucIndex ].packetId,
                            MQTT_Status_strerror( xMQTTStatus ) ) );
                xReturnStatus = pdFAIL;
                break;
            }
            else
            {
                LogInfo( ( "Sent duplicate PUBLISH successfully for packet id %u.\n\n",
                           outgoingPublishPackets[ ucIndex ].packetId ) );
            }
        }
    }

    return xReturnStatus;
}

/*-----------------------------------------------------------*/

BaseType_t xEstablishMqttSession( MQTTContext_t * pxMqttContext,
                                  NetworkContext_t * pxNetworkContext,
                                  MQTTFixedBuffer_t * pxNetworkBuffer,
                                  MQTTEventCallback_t eventCallback )
{
    BaseType_t xReturnStatus = pdTRUE;
    MQTTStatus_t xMQTTStatus;
    MQTTConnectInfo_t xConnectInfo;
    TransportInterface_t xTransport;
    bool sessionPresent = false;

    configASSERT( pxMqttContext != NULL );
    configASSERT( pxNetworkContext != NULL );

    /* Initialize the mqtt context. */
    ( void ) memset( pxMqttContext, 0U, sizeof( MQTTContext_t ) );

    if( prvConnectToServerWithBackoffRetries( pxNetworkContext ) != TLS_TRANSPORT_SUCCESS )
    {
        /* Log error to indicate connection failure after all
         * reconnect attempts are over. */
        LogError( ( "Failed to connect to MQTT broker %.*s.",
                    strlen( democonfigMQTT_BROKER_ENDPOINT ),
                    democonfigMQTT_BROKER_ENDPOINT ) );
        xReturnStatus = pdFAIL;
    }
    else
    {
        /* Fill in Transport Interface send and receive function pointers. */
        xTransport.pNetworkContext = pxNetworkContext;
        xTransport.send = TLS_FreeRTOS_send;
        xTransport.recv = TLS_FreeRTOS_recv;

        /* Initialize MQTT library. */
        xMQTTStatus = MQTT_Init( pxMqttContext,
                                 &xTransport,
                                 prvGetTimeMs,
                                 eventCallback,
                                 pxNetworkBuffer );

        if( xMQTTStatus != MQTTSuccess )
        {
            xReturnStatus = pdFAIL;
            LogError( ( "MQTT init failed with status %s.",
                        MQTT_Status_strerror( xMQTTStatus ) ) );
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
             * Control Packets being sent does not exceed this Keep Alive value. In the
             * absence of sending any other Control Packets, the Client MUST send a
             * PINGREQ Packet. */
            xConnectInfo.keepAliveSeconds = mqttexampleKEEP_ALIVE_TIMEOUT_SECONDS;

/* Append metrics when connecting to the AWS IoT Core broker. */
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

            /* Send MQTT CONNECT packet to broker. */
            xMQTTStatus = MQTT_Connect( pxMqttContext,
                                        &xConnectInfo,
                                        NULL,
                                        mqttexampleCONNACK_RECV_TIMEOUT_MS,
                                        &sessionPresent );

            if( xMQTTStatus != MQTTSuccess )
            {
                xReturnStatus = pdFAIL;
                LogError( ( "Connection with MQTT broker failed with status %s.",
                            MQTT_Status_strerror( xMQTTStatus ) ) );
            }
            else
            {
                LogInfo( ( "MQTT connection successfully established with broker.\n\n" ) );
            }
        }

        if( xReturnStatus == pdFAIL )
        {
            /* Keep a flag for indicating if MQTT session is established. This
             * flag will mark that an MQTT DISCONNECT has to be sent at the end
             * of the demo even if there are intermediate failures. */
            xMqttSessionEstablished = true;
        }

        if( xReturnStatus == pdFAIL )
        {
            /* Check if session is present and if there are any outgoing publishes
             * that need to resend. This is only valid if the broker is
             * re-establishing a session which was already present. */
            if( sessionPresent == true )
            {
                LogInfo( ( "An MQTT session with broker is re-established. "
                           "Resending unacked publishes." ) );

                /* Handle all the resend of publish messages. */
                xReturnStatus = xHandlePublishResend( pxMqttContext );
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

    return xReturnStatus;
}

/*-----------------------------------------------------------*/

BaseType_t xDisconnectMqttSession( MQTTContext_t * pxMqttContext,
                                   NetworkContext_t * pxNetworkContext )
{
    MQTTStatus_t xMQTTStatus = MQTTSuccess;
    BaseType_t xReturnStatus = pdTRUE;

    configASSERT( pxMqttContext != NULL );
    configASSERT( pxNetworkContext != NULL );

    if( xMqttSessionEstablished == true )
    {
        /* Send DISCONNECT. */
        xMQTTStatus = MQTT_Disconnect( pxMqttContext );

        if( xMQTTStatus != MQTTSuccess )
        {
            LogError( ( "Sending MQTT DISCONNECT failed with status=%s.",
                        MQTT_Status_strerror( xMQTTStatus ) ) );
            xReturnStatus = pdFAIL;
        }
    }

    /* Close the network connection.  */
    TLS_FreeRTOS_Disconnect( pxNetworkContext );

    return xReturnStatus;
}

/*-----------------------------------------------------------*/

BaseType_t xSubscribeToTopic( MQTTContext_t * pxMqttContext,
                              const char * pcTopicFilter,
                              uint16_t usTopicFilterLength )
{
    BaseType_t xReturnStatus = pdTRUE;
    MQTTStatus_t xMQTTStatus;
    MQTTSubscribeInfo_t pSubscriptionList[ mqttexampleTOPIC_COUNT ];

    configASSERT( pxMqttContext != NULL );
    configASSERT( pcTopicFilter != NULL );
    configASSERT( usTopicFilterLength > 0 );

    /* Start with everything at 0. */
    ( void ) memset( ( void * ) pSubscriptionList, 0x00, sizeof( pSubscriptionList ) );

    /* This example subscribes to only one topic and uses QOS1. */
    pSubscriptionList[ 0 ].qos = MQTTQoS1;
    pSubscriptionList[ 0 ].pTopicFilter = pcTopicFilter;
    pSubscriptionList[ 0 ].topicFilterLength = usTopicFilterLength;

    /* Generate packet identifier for the SUBSCRIBE packet. */
    globalSubscribePacketIdentifier = MQTT_GetPacketId( pxMqttContext );

    /* Send SUBSCRIBE packet. */
    xMQTTStatus = MQTT_Subscribe( pxMqttContext,
                                  pSubscriptionList,
                                  sizeof( pSubscriptionList ) / sizeof( MQTTSubscribeInfo_t ),
                                  globalSubscribePacketIdentifier );

    if( xMQTTStatus != MQTTSuccess )
    {
        LogError( ( "Failed to send SUBSCRIBE packet to broker with error = %s.",
                    MQTT_Status_strerror( xMQTTStatus ) ) );
        xReturnStatus = pdFAIL;
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
        xMQTTStatus = MQTT_ProcessLoop( pxMqttContext, mqttexamplePROCESS_LOOP_TIMEOUT_MS );

        if( xMQTTStatus != MQTTSuccess )
        {
            xReturnStatus = pdFAIL;
            LogError( ( "MQTT_ProcessLoop returned with status = %s.",
                        MQTT_Status_strerror( xMQTTStatus ) ) );
        }
    }

    return xReturnStatus;
}

/*-----------------------------------------------------------*/

BaseType_t xUnsubscribeFromTopic( MQTTContext_t * pxMqttContext,
                                  const char * pcTopicFilter,
                                  uint16_t usTopicFilterLength )
{
    BaseType_t xReturnStatus = pdTRUE;
    MQTTStatus_t xMQTTStatus;
    MQTTSubscribeInfo_t pSubscriptionList[ 1 ];

    configASSERT( pxMqttContext != NULL );
    configASSERT( pcTopicFilter != NULL );
    configASSERT( usTopicFilterLength > 0 );

    /* Start with everything at 0. */
    ( void ) memset( ( void * ) pSubscriptionList, 0x00, sizeof( pSubscriptionList ) );

    /* This example subscribes to only one topic and uses QOS1. */
    pSubscriptionList[ 0 ].qos = MQTTQoS1;
    pSubscriptionList[ 0 ].pTopicFilter = pcTopicFilter;
    pSubscriptionList[ 0 ].topicFilterLength = usTopicFilterLength;

    /* Generate packet identifier for the UNSUBSCRIBE packet. */
    globalUnsubscribePacketIdentifier = MQTT_GetPacketId( pxMqttContext );

    /* Send UNSUBSCRIBE packet. */
    xMQTTStatus = MQTT_Unsubscribe( pxMqttContext,
                                    pSubscriptionList,
                                    sizeof( pSubscriptionList ) / sizeof( MQTTSubscribeInfo_t ),
                                    globalUnsubscribePacketIdentifier );

    if( xMQTTStatus != MQTTSuccess )
    {
        LogError( ( "Failed to send UNSUBSCRIBE packet to broker with error = %s.",
                    MQTT_Status_strerror( xMQTTStatus ) ) );
        xReturnStatus = pdFAIL;
    }
    else
    {
        LogInfo( ( "UNSUBSCRIBE sent topic %.*s to broker.\n\n",
                   usTopicFilterLength,
                   pcTopicFilter ) );

        /* Process the incoming packet from the broker. */
        xMQTTStatus = MQTT_ProcessLoop( pxMqttContext, mqttexamplePROCESS_LOOP_TIMEOUT_MS );

        if( xMQTTStatus != MQTTSuccess )
        {
            xReturnStatus = pdFAIL;
            LogError( ( "MQTT_ProcessLoop returned with status = %s.",
                        MQTT_Status_strerror( xMQTTStatus ) ) );
        }
    }

    return xReturnStatus;
}

/*-----------------------------------------------------------*/

BaseType_t xPublishToTopic( MQTTContext_t * pxMqttContext,
                            const char * pcTopicFilter,
                            int32_t topicFilterLength,
                            const char * pcPayload,
                            size_t payloadLength )
{
    BaseType_t xReturnStatus = pdPASS;
    MQTTStatus_t xMQTTStatus = MQTTSuccess;
    uint8_t ucPublishIndex = MAX_OUTGOING_PUBLISHES;

    configASSERT( pxMqttContext != NULL );
    configASSERT( pcTopicFilter != NULL );
    configASSERT( topicFilterLength > 0 );

    /* Get the next free index for the outgoing publish. All QoS1 outgoing
     * publishes are stored until a PUBACK is received. These messages are
     * stored for supporting a resend if a network connection is broken before
     * receiving a PUBACK. */
    xReturnStatus = prvGetNextFreeIndexForOutgoingPublishes( &ucPublishIndex );

    if( xReturnStatus == pdFAIL )
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
        xMQTTStatus = MQTT_Publish( pxMqttContext,
                                    &outgoingPublishPackets[ ucPublishIndex ].pubInfo,
                                    outgoingPublishPackets[ ucPublishIndex ].packetId );

        if( xMQTTStatus != MQTTSuccess )
        {
            LogError( ( "Failed to send PUBLISH packet to broker with error = %s.",
                        MQTT_Status_strerror( xMQTTStatus ) ) );
            vCleanupOutgoingPublishAt( ucPublishIndex );
            xReturnStatus = pdFAIL;
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
            xMQTTStatus = MQTT_ProcessLoop( pxMqttContext, mqttexamplePROCESS_LOOP_TIMEOUT_MS );

            if( xMQTTStatus != MQTTSuccess )
            {
                LogError( ( "MQTT_ProcessLoop returned with status = %s.",
                            MQTT_Status_strerror( xMQTTStatus ) ) );
                xReturnStatus = pdFAIL;
            }
        }
    }

    return xReturnStatus;
}

/*-----------------------------------------------------------*/

BaseType_t xProcessLoop( MQTTContext_t * pxMqttContext,
                         uint32_t ulTimeoutMs )
{
    BaseType_t xReturnStatus = pdFAIL;
    MQTTStatus_t xMQTTStatus = MQTTSuccess;

    xMQTTStatus = MQTT_ProcessLoop( pxMqttContext, ulTimeoutMs );

    if( xMQTTStatus != MQTTSuccess )
    {
        LogError( ( "MQTT_ProcessLoop returned with status = %s.",
                    MQTT_Status_strerror( xMQTTStatus ) ) );
    }
    else
    {
        LogDebug( ( "MQTT_ProcessLoop successful." ) );
        xReturnStatus = pdPASS;
    }

    return xReturnStatus;
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
