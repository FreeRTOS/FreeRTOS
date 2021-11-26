/*
 * AWS IoT Device SDK for Embedded C 202108.00
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
  * @file mqtt_operations.c
  *
  * @brief This file provides wrapper functions for MQTT operations on a mutually
  * authenticated TLS connection.
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
#include <time.h>

/* Config include. */
#include "demo_config.h"

/* Interface include. */
#include "mqtt_operations.h"

/* MbedTLS transport include. */
#include "using_mbedtls_pkcs11.h"

/*Include backoff algorithm header for retry logic.*/
#include "backoff_algorithm.h"

/**
 * These configurations are required. Throw compilation error if the below
 * configs are not defined.
 */
#ifndef democonfigMQTT_BROKER_ENDPOINT
    #error "Please define AWS IoT MQTT broker endpoint(democonfigMQTT_BROKER_ENDPOINT) in demo_config.h."
#endif
#ifndef democonfigROOT_CA_PEM
    #error "Please define the PEM-encoded Root CA certificate of the MQTT broker(democonfigROOT_CA_PEM) in demo_config.h."
#endif
#ifndef democonfigCLIENT_IDENTIFIER
    #error "Please define a unique democonfigCLIENT_IDENTIFIER."
#endif

 /**
  * Provide default values for undefined configuration settings.
  */
#ifndef AWS_MQTT_PORT
#define AWS_MQTT_PORT    ( 8883 )
#endif

#ifndef democonfigNETWORK_BUFFER_SIZE
#define democonfigNETWORK_BUFFER_SIZE    ( 1024U )
#endif

/**
 * @brief Length of the AWS IoT endpoint.
 */
#define democonfigMQTT_BROKER_ENDPOINT_LENGTH                  ( ( uint16_t ) ( sizeof( democonfigMQTT_BROKER_ENDPOINT ) - 1 ) )

/**
 * @brief Length of the client identifier.
 */
#define CLIENT_IDENTIFIER_LENGTH                 ( ( uint16_t ) ( sizeof( democonfigCLIENT_IDENTIFIER ) - 1 ) )

/**
 * @brief ALPN protocol name for AWS IoT MQTT.
 *
 * This will be used if the AWS_MQTT_PORT is configured as 443 for AWS IoT MQTT
 * broker. Please see more details about the ALPN protocol for AWS IoT MQTT
 * endpoint in the link below.
 * https://aws.amazon.com/blogs/iot/mqtt-with-tls-client-authentication-on-port-443-why-it-is-useful-and-how-it-works/
 *
 * @note OpenSSL requires that the protocol string passed to it for configuration be encoded
 * with the prefix of 8-bit length information of the string. Thus, the 14 byte (0x0e) length
 * information is prefixed to the string.
 */
#define ALPN_PROTOCOL_NAME                       "\x0ex-amzn-mqtt-ca"

/**
 * @brief Length of ALPN protocol name.
 */
#define ALPN_PROTOCOL_NAME_LENGTH                ( ( uint16_t ) ( sizeof( ALPN_PROTOCOL_NAME ) - 1 ) )

/**
 * @brief The maximum number of retries for connecting to server.
 */
#define CONNECTION_RETRY_MAX_ATTEMPTS            ( 5U )

/**
 * @brief The maximum back-off delay (in milliseconds) for retrying connection to server.
 */
#define CONNECTION_RETRY_MAX_BACKOFF_DELAY_MS    ( 5000U )

/**
 * @brief The base back-off delay (in milliseconds) to use for connection retry attempts.
 */
#define CONNECTION_RETRY_BACKOFF_BASE_MS         ( 500U )

/**
 * @brief Timeout for receiving CONNACK packet in milliseconds.
 */
#define CONNACK_RECV_TIMEOUT_MS                  ( 1000U )

/**
 * @brief Maximum number of outgoing publishes maintained in the application
 * until an ack is received from the broker.
 */
#define MAX_OUTGOING_PUBLISHES                   ( 5U )

/**
 * @brief Invalid packet identifier for the MQTT packets. Zero is always an
 * invalid packet identifier as per MQTT 3.1.1 spec.
 */
#define MQTT_PACKET_ID_INVALID                   ( ( uint16_t ) 0U )

/**
 * @brief Timeout for MQTT_ProcessLoop function in milliseconds.
 */
#define MQTT_PROCESS_LOOP_TIMEOUT_MS             ( 1000U )

/**
 * @brief The maximum time interval in seconds which is allowed to elapse
 *  between two Control Packets.
 *
 *  It is the responsibility of the client to ensure that the interval between
 *  control packets being sent does not exceed the this keep-alive value. In the
 *  absence of sending any other control packets, the client MUST send a
 *  PINGREQ packet.
 */
#define MQTT_KEEP_ALIVE_INTERVAL_SECONDS         ( 60U )

/**
 * @brief Timeout in milliseconds for transport send and receive.
 */
#define TRANSPORT_SEND_RECV_TIMEOUT_MS           ( 100U )

/**
 * @brief Milliseconds per second.
 */
#define MILLISECONDS_PER_SECOND                      ( 1000U )

/**
 * @brief Milliseconds per FreeRTOS tick.
 */
#define MILLISECONDS_PER_TICK                        ( MILLISECONDS_PER_SECOND / configTICK_RATE_HZ )

/**
 * @brief The MQTT metrics string expected by AWS IoT MQTT Broker.
 */
#define METRICS_STRING                           "?SDK=" democonfigOS_NAME "&Version=" democonfigOS_VERSION "&Platform=" democonfigHARDWARE_PLATFORM_NAME "&MQTTLib=" democonfigMQTT_LIB

/**
 * @brief The length of the MQTT metrics string.
 */
#define METRICS_STRING_LENGTH                    ( ( uint16_t ) ( sizeof( METRICS_STRING ) - 1 ) )
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

/* Each compilation unit must define the NetworkContext struct. */
struct NetworkContext
{
    SSLContext_t * pParams;
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
 * @brief Packet Identifier generated when Subscribe request was sent to the broker.
 *
 * It is used to match received Subscribe ACK to the transmitted subscribe
 * request.
 */
static uint16_t globalSubscribePacketIdentifier = 0U;

/**
 * @brief Packet Identifier generated when Unsubscribe request was sent to the broker.
 *
 * It is used to match received Unsubscribe ACK to the transmitted unsubscribe
 * request.
 */
static uint16_t globalUnsubscribePacketIdentifier = 0U;

/**
 * @brief Array to keep the outgoing publish messages.
 *
 * These stored outgoing publish messages are kept until a successful ack
 * is received.
 */
static PublishPackets_t outgoingPublishPackets[ MAX_OUTGOING_PUBLISHES ] = { 0 };

/**
 * @brief The network buffer must remain valid for the lifetime of the MQTT context.
 */
static uint8_t buffer[ democonfigNETWORK_BUFFER_SIZE ];

/**
 * @brief The MQTT context used for MQTT operation.
 */
static MQTTContext_t mqttContext = { 0 };

/**
 * @brief The network context used for MbedTLS operation.
 */
static NetworkContext_t networkContext = { 0 };

/**
 * @brief The parameters for MbedTLS operation.
 */
static SSLContext_t tlsContext = { 0 };

/**
 * @brief The flag to indicate that the mqtt session is established.
 */
static bool mqttSessionEstablished = false;

/**
 * @brief Callback registered when calling EstablishMqttSession to get incoming
 * publish messages.
 */
static MQTTPublishCallback_t appPublishCallback = NULL;
/*-----------------------------------------------------------*/

/**
 * @brief The random number generator to use for exponential backoff with
 * jitter retry logic.
 *
 * @return The generated random number.
 */
static uint32_t generateRandomNumber( void );

/**
 * @brief Connect to the MQTT broker with reconnection retries.
 *
 * If connection fails, retry is attempted after a timeout. Timeout value
 * exponentially increases until maximum timeout value is reached or the number
 * of attempts are exhausted.
 *
 * @param[out] pNetworkContext The created network context.
 * @param[in] pClientCertLabel The client certificate PKCS #11 label to use.
 * @param[in] pPrivateKeyLabel The private key PKCS #11 label for the client certificate.
 *
 * @return false on failure; true on successful connection.
 */
static bool connectToBrokerWithBackoffRetries( NetworkContext_t * pNetworkContext,
                                               char * pClientCertLabel,
                                               char * pPrivateKeyLabel );

/**
 * @brief Get the free index in the #outgoingPublishPackets array at which an
 * outgoing publish can be stored.
 *
 * @param[out] pIndex The index at which an outgoing publish can be stored.
 *
 * @return false if no more publishes can be stored;
 * true if an index to store the next outgoing publish is obtained.
 */
static bool getNextFreeIndexForOutgoingPublishes( uint8_t * pIndex );

/**
 * @brief Clean up the outgoing publish at given index from the
 * #outgoingPublishPackets array.
 *
 * @param[in] index The index at which a publish message has to be cleaned up.
 */
static void cleanupOutgoingPublishAt( uint8_t index );

/**
 * @brief Clean up all the outgoing publishes in the #outgoingPublishPackets array.
 */
static void cleanupOutgoingPublishes( void );

/**
 * @brief Clean up the publish packet with the given packet id in the
 * #outgoingPublishPackets array.
 *
 * @param[in] packetId Packet id of the packet to be clean.
 */
static void cleanupOutgoingPublishWithPacketID( uint16_t packetId );

/**
 * @brief Callback registered with the MQTT library.
 *
 * @param[in] pMqttContext MQTT context pointer.
 * @param[in] pPacketInfo Packet Info pointer for the incoming packet.
 * @param[in] pDeserializedInfo Deserialized information from the incoming packet.
 */
static void mqttCallback( MQTTContext_t * pMqttContext,
                          MQTTPacketInfo_t * pPacketInfo,
                          MQTTDeserializedInfo_t * pDeserializedInfo );

/**
 * @brief Resend the publishes if a session is re-established with the broker.
 *
 * This function handles the resending of the QoS1 publish packets, which are
 * maintained locally.
 *
 * @param[in] pMqttContext The MQTT context pointer.
 *
 * @return true if all the unacknowledged QoS1 publishes are re-sent successfully;
 * false otherwise.
 */
static bool handlePublishResend( MQTTContext_t * pMqttContext );

/**
 * @brief The timer query function provided to the MQTT context.
 *
 * @return Time in milliseconds.
 */
static uint32_t prvGetTimeMs(void);

/*-----------------------------------------------------------*/

static uint32_t generateRandomNumber()
{
    return( ( uint32_t ) rand() );
}

/*-----------------------------------------------------------*/

static bool connectToBrokerWithBackoffRetries( NetworkContext_t * pNetworkContext,
                                               char * pClientCertLabel,
                                               char * pPrivateKeyLabel )
{
    bool returnStatus = false;
    BackoffAlgorithmStatus_t backoffAlgStatus = BackoffAlgorithmSuccess;
    TlsTransportStatus_t tlsStatus = TLS_TRANSPORT_SUCCESS;
    BackoffAlgorithmContext_t reconnectParams;
    NetworkCredentials_t tlsCredentials = { 0 };
    uint16_t nextRetryBackOff = 0U;
    const char * alpn[] = { ALPN_PROTOCOL_NAME, NULL };

    /* Set the pParams member of the network context with desired transport. */
    pNetworkContext->pParams = &tlsContext;

    /* Initialize credentials for establishing TLS session. */
    tlsCredentials.pRootCa = democonfigROOT_CA_PEM;
    tlsCredentials.rootCaSize = sizeof(democonfigROOT_CA_PEM);
    tlsCredentials.pClientCertLabel = pClientCertLabel;
    tlsCredentials.pPrivateKeyLabel = pPrivateKeyLabel;
    //tlsCredentials.p11Session = p11Session;

    /* AWS IoT requires devices to send the Server Name Indication (SNI)
     * extension to the Transport Layer Security (TLS) protocol and provide
     * the complete endpoint address in the host_name field. Details about
     * SNI for AWS IoT can be found in the link below.
     * https://docs.aws.amazon.com/iot/latest/developerguide/transport-security.html
     */
    tlsCredentials.disableSni = false;

    if( AWS_MQTT_PORT == 443 )
    {
        /* Pass the ALPN protocol name depending on the port being used.
         * Please see more details about the ALPN protocol for AWS IoT MQTT endpoint
         * in the link below.
         * https://aws.amazon.com/blogs/iot/mqtt-with-tls-client-authentication-on-port-443-why-it-is-useful-and-how-it-works/
         */
        tlsCredentials.pAlpnProtos = alpn;
    }

    /* Initialize reconnect attempts and interval */
    BackoffAlgorithm_InitializeParams( &reconnectParams,
                                       CONNECTION_RETRY_BACKOFF_BASE_MS,
                                       CONNECTION_RETRY_MAX_BACKOFF_DELAY_MS,
                                       CONNECTION_RETRY_MAX_ATTEMPTS );

    do
    {
        /* Establish a TLS session with the MQTT broker. This example connects
         * to the MQTT broker as specified in democonfigMQTT_BROKER_ENDPOINT and AWS_MQTT_PORT
         * at the demo config header. */
        LogDebug( ( "Establishing a TLS session to %.*s:%d.",
                    democonfigMQTT_BROKER_ENDPOINT_LENGTH,
                    democonfigMQTT_BROKER_ENDPOINT,
                    AWS_MQTT_PORT ) );

        tlsStatus = TLS_FreeRTOS_Connect( pNetworkContext,
                                            democonfigMQTT_BROKER_ENDPOINT,
                                            AWS_MQTT_PORT,
                                            &tlsCredentials,
                                            TRANSPORT_SEND_RECV_TIMEOUT_MS, TRANSPORT_SEND_RECV_TIMEOUT_MS);

        if( tlsStatus == TLS_TRANSPORT_SUCCESS )
        {
            /* Connection successful. */
            returnStatus = true;
        }
        else
        {
            /* Generate a random number and get back-off value (in milliseconds) for the next connection retry. */
            backoffAlgStatus = BackoffAlgorithm_GetNextBackoff( &reconnectParams, generateRandomNumber(), &nextRetryBackOff );

            if( backoffAlgStatus == BackoffAlgorithmRetriesExhausted )
            {
                LogError( ( "Connection to the broker failed, all attempts exhausted." ) );
            }
            else if( backoffAlgStatus == BackoffAlgorithmSuccess )
            {
                LogWarn( ( "Connection to the broker failed. Retrying connection "
                           "after %hu ms backoff.",
                           ( unsigned short ) nextRetryBackOff ) );
                vTaskDelay( pdMS_TO_TICKS( nextRetryBackOff ) );
            }
        }
    } while( ( tlsStatus != TLS_TRANSPORT_SUCCESS ) && ( backoffAlgStatus == BackoffAlgorithmSuccess ) );

    return returnStatus;
}
/*-----------------------------------------------------------*/

static bool getNextFreeIndexForOutgoingPublishes( uint8_t * pIndex )
{
    bool returnStatus = false;
    uint8_t index = 0;

    assert( outgoingPublishPackets != NULL );
    assert( pIndex != NULL );

    for( index = 0; index < MAX_OUTGOING_PUBLISHES; index++ )
    {
        /* A free index is marked by invalid packet id. Check if the the index
         * has a free slot. */
        if( outgoingPublishPackets[ index ].packetId == MQTT_PACKET_ID_INVALID )
        {
            returnStatus = true;
            break;
        }
    }

    /* Copy the available index into the output param. */
    if( returnStatus == true )
    {
        *pIndex = index;
    }

    return returnStatus;
}
/*-----------------------------------------------------------*/

static void cleanupOutgoingPublishAt( uint8_t index )
{
    assert( outgoingPublishPackets != NULL );
    assert( index < MAX_OUTGOING_PUBLISHES );

    /* Clear the outgoing publish packet. */
    ( void ) memset( &( outgoingPublishPackets[ index ] ),
                     0x00,
                     sizeof( outgoingPublishPackets[ index ] ) );
}
/*-----------------------------------------------------------*/

static void cleanupOutgoingPublishes( void )
{
    assert( outgoingPublishPackets != NULL );

    /* Clean up all the outgoing publish packets. */
    ( void ) memset( outgoingPublishPackets, 0x00, sizeof( outgoingPublishPackets ) );
}
/*-----------------------------------------------------------*/

static void cleanupOutgoingPublishWithPacketID( uint16_t packetId )
{
    uint8_t index = 0;

    assert( outgoingPublishPackets != NULL );
    assert( packetId != MQTT_PACKET_ID_INVALID );

    /* Clean up the saved outgoing publish with packet Id equal to packetId. */
    for( index = 0; index < MAX_OUTGOING_PUBLISHES; index++ )
    {
        if( outgoingPublishPackets[ index ].packetId == packetId )
        {
            cleanupOutgoingPublishAt( index );

            LogDebug( ( "Cleaned up outgoing publish packet with packet id %u.",
                        packetId ) );

            break;
        }
    }
}
/*-----------------------------------------------------------*/

static void mqttCallback( MQTTContext_t * pMqttContext,
                          MQTTPacketInfo_t * pPacketInfo,
                          MQTTDeserializedInfo_t * pDeserializedInfo )
{
    uint16_t packetIdentifier;

    assert( pMqttContext != NULL );
    assert( pPacketInfo != NULL );
    assert( pDeserializedInfo != NULL );

    /* Suppress the unused parameter warning when asserts are disabled in
     * build. */
    ( void ) pMqttContext;

    packetIdentifier = pDeserializedInfo->packetIdentifier;

    /* Handle an incoming publish. The lower 4 bits of the publish packet
     * type is used for the dup, QoS, and retain flags. Hence masking
     * out the lower bits to check if the packet is publish. */
    if( ( pPacketInfo->type & 0xF0U ) == MQTT_PACKET_TYPE_PUBLISH )
    {
        assert( pDeserializedInfo->pPublishInfo != NULL );

        /* Invoke the application callback for incoming publishes. */
        if( appPublishCallback != NULL )
        {
            appPublishCallback( pDeserializedInfo->pPublishInfo, packetIdentifier );
        }
    }
    else
    {
        /* Handle other packets. */
        switch( pPacketInfo->type )
        {
            case MQTT_PACKET_TYPE_SUBACK:
                LogDebug( ( "MQTT Packet type SUBACK received." ) );

                /* Make sure the ACK packet identifier matches with the request
                 * packet identifier. */
                assert( globalSubscribePacketIdentifier == packetIdentifier );
                break;

            case MQTT_PACKET_TYPE_UNSUBACK:
                LogDebug( ( "MQTT Packet type UNSUBACK received." ) );

                /* Make sure the ACK packet identifier matches with the request
                 * packet identifier. */
                assert( globalUnsubscribePacketIdentifier == packetIdentifier );
                break;

            case MQTT_PACKET_TYPE_PINGRESP:

                /* We do not expect to receive PINGRESP as we are using
                 * MQTT_ProcessLoop. */
                LogWarn( ( "PINGRESP should not be received by the application "
                           "callback when using MQTT_ProcessLoop." ) );
                break;

            case MQTT_PACKET_TYPE_PUBACK:
                LogDebug( ( "PUBACK received for packet id %u.",
                            packetIdentifier ) );

                /* Cleanup the publish packet from the #outgoingPublishPackets
                 * array when a PUBACK is received. */
                cleanupOutgoingPublishWithPacketID( packetIdentifier );
                break;

            /* Any other packet type is invalid. */
            default:
                LogError( ( "Unknown packet type received:(%02x).",
                            pPacketInfo->type ) );
        }
    }
}
/*-----------------------------------------------------------*/

static bool handlePublishResend( MQTTContext_t * pMqttContext )
{
    bool returnStatus = false;
    MQTTStatus_t mqttStatus = MQTTSuccess;
    uint8_t index = 0U;

    assert( outgoingPublishPackets != NULL );

    /* Resend all the QoS1 publishes still in the #outgoingPublishPackets array.
     * These are the publishes that haven't received a PUBACK yet. When a PUBACK
     * is received, the corresponding publish is removed from the array. */
    for( index = 0U; index < MAX_OUTGOING_PUBLISHES; index++ )
    {
        if( outgoingPublishPackets[ index ].packetId != MQTT_PACKET_ID_INVALID )
        {
            outgoingPublishPackets[ index ].pubInfo.dup = true;

            LogDebug( ( "Sending duplicate PUBLISH with packet id %u.",
                        outgoingPublishPackets[ index ].packetId ) );
            mqttStatus = MQTT_Publish( pMqttContext,
                                       &outgoingPublishPackets[ index ].pubInfo,
                                       outgoingPublishPackets[ index ].packetId );

            if( mqttStatus != MQTTSuccess )
            {
                LogError( ( "Sending duplicate PUBLISH for packet id %u "
                            " failed with status %s.",
                            outgoingPublishPackets[ index ].packetId,
                            MQTT_Status_strerror( mqttStatus ) ) );
                break;
            }
            else
            {
                LogDebug( ( "Sent duplicate PUBLISH successfully for packet id %u.",
                            outgoingPublishPackets[ index ].packetId ) );
            }
        }
    }

    /* Were all the unacknowledged QoS1 publishes successfully re-sent? */
    if( index == MAX_OUTGOING_PUBLISHES )
    {
        returnStatus = true;
    }

    return returnStatus;
}
/*-----------------------------------------------------------*/

bool EstablishMqttSession( MQTTPublishCallback_t publishCallback,
                           char * pClientCertLabel,
                           char * pPrivateKeyLabel )
{
    bool returnStatus = false;
    MQTTStatus_t mqttStatus;
    MQTTConnectInfo_t connectInfo;
    MQTTFixedBuffer_t networkBuffer;
    TransportInterface_t transport;
    bool createCleanSession = false;
    MQTTContext_t * pMqttContext = &mqttContext;
    NetworkContext_t * pNetworkContext = &networkContext;
    bool sessionPresent = false;

    assert( pMqttContext != NULL );
    assert( pNetworkContext != NULL );

    /* Initialize the mqtt context and network context. */
    ( void ) memset( pMqttContext, 0U, sizeof( MQTTContext_t ) );
    ( void ) memset( pNetworkContext, 0U, sizeof( NetworkContext_t ) );

    returnStatus = connectToBrokerWithBackoffRetries( pNetworkContext,
                                                      pClientCertLabel,
                                                      pPrivateKeyLabel );

    if( returnStatus != true )
    {
        /* Log an error to indicate connection failure after all
         * reconnect attempts are over. */
        LogError( ( "Failed to connect to MQTT broker %.*s.",
                    democonfigMQTT_BROKER_ENDPOINT_LENGTH,
                    democonfigMQTT_BROKER_ENDPOINT ) );
    }
    else
    {
        /* Fill in TransportInterface send and receive function pointers.
         * For this demo, TCP sockets are used to send and receive data
         * from the network. pNetworkContext is an SSL context for OpenSSL.*/
        transport.pNetworkContext = pNetworkContext;
        transport.send = TLS_FreeRTOS_send;
        transport.recv = TLS_FreeRTOS_recv;

        /* Fill the values for network buffer. */
        networkBuffer.pBuffer = buffer;
        networkBuffer.size = democonfigNETWORK_BUFFER_SIZE;

        /* Remember the publish callback supplied. */
        appPublishCallback = publishCallback;

        /* Initialize the MQTT library. */
        mqttStatus = MQTT_Init( pMqttContext,
                                &transport,
                                prvGetTimeMs,
                                mqttCallback,
                                &networkBuffer );

        if( mqttStatus != MQTTSuccess )
        {
            returnStatus = false;
            LogError( ( "MQTT init failed with status %s.",
                        MQTT_Status_strerror( mqttStatus ) ) );
        }
        else
        {
            /* Establish an MQTT session by sending a CONNECT packet. */

            /* If #createCleanSession is true, start with a clean session
             * i.e. direct the MQTT broker to discard any previous session data.
             * If #createCleanSession is false, direct the broker to attempt to
             * reestablish a session which was already present. */
            connectInfo.cleanSession = createCleanSession;

            /* The client identifier is used to uniquely identify this MQTT client to
             * the MQTT broker. In a production device the identifier can be something
             * unique, such as a device serial number. */
            connectInfo.pClientIdentifier = democonfigCLIENT_IDENTIFIER;
            connectInfo.clientIdentifierLength = CLIENT_IDENTIFIER_LENGTH;

            /* The maximum time interval in seconds which is allowed to elapse
             * between two Control Packets.
             * It is the responsibility of the client to ensure that the interval between
             * control packets being sent does not exceed the this keep-alive value. In the
             * absence of sending any other control packets, the client MUST send a
             * PINGREQ packet. */
            connectInfo.keepAliveSeconds = MQTT_KEEP_ALIVE_INTERVAL_SECONDS;

            /* Username and password for authentication. Not used in this demo. */
            connectInfo.pUserName = METRICS_STRING;
            connectInfo.userNameLength = METRICS_STRING_LENGTH;
            connectInfo.pPassword = NULL;
            connectInfo.passwordLength = 0U;

            /* Send an MQTT CONNECT packet to the broker. */
            mqttStatus = MQTT_Connect( pMqttContext,
                                       &connectInfo,
                                       NULL,
                                       CONNACK_RECV_TIMEOUT_MS,
                                       &sessionPresent );

            if( mqttStatus != MQTTSuccess )
            {
                returnStatus = false;
                LogError( ( "Connection with MQTT broker failed with status %s.",
                            MQTT_Status_strerror( mqttStatus ) ) );
            }
            else
            {
                LogDebug( ( "MQTT connection successfully established with broker." ) );
            }
        }

        if( returnStatus == true )
        {
            /* Keep a flag for indicating if MQTT session is established. This
             * flag will mark that an MQTT DISCONNECT has to be sent at the end
             * of the demo even if there are intermediate failures. */
            mqttSessionEstablished = true;
        }

        if( returnStatus == true )
        {
            /* Check if a session is present and if there are any outgoing
             * publishes that need to be resent. Resending unacknowledged
             * publishes is needed only if the broker is re-establishing a
             * session that was already present. */
            if( sessionPresent == true )
            {
                LogDebug( ( "An MQTT session with broker is re-established. "
                            "Resending unacked publishes." ) );

                /* Handle all the resend of publish messages. */
                returnStatus = handlePublishResend( &mqttContext );
            }
            else
            {
                LogDebug( ( "A clean MQTT connection is established."
                            " Cleaning up all the stored outgoing publishes." ) );

                /* Clean up the outgoing publishes waiting for ack as this new
                 * connection doesn't re-establish an existing session. */
                cleanupOutgoingPublishes();
            }
        }
    }

    return returnStatus;
}
/*-----------------------------------------------------------*/

bool DisconnectMqttSession( void )
{
    MQTTStatus_t mqttStatus = MQTTSuccess;
    bool returnStatus = false;
    MQTTContext_t * pMqttContext = &mqttContext;
    NetworkContext_t * pNetworkContext = &networkContext;

    assert( pMqttContext != NULL );
    assert( pNetworkContext != NULL );

    if( mqttSessionEstablished == true )
    {
        /* Send DISCONNECT. */
        mqttStatus = MQTT_Disconnect( pMqttContext );

        if( mqttStatus != MQTTSuccess )
        {
            LogError( ( "Sending MQTT DISCONNECT failed with status=%u.",
                        mqttStatus ) );
        }
        else
        {
            /* MQTT DISCONNECT sent successfully. */
            returnStatus = true;
        }
    }

    /* End TLS session, then close TCP connection. */
    ( void ) TLS_FreeRTOS_Disconnect( pNetworkContext );

    return returnStatus;
}
/*-----------------------------------------------------------*/

bool SubscribeToTopic( const char * pTopicFilter,
                       uint16_t topicFilterLength )
{
    bool returnStatus = false;
    MQTTStatus_t mqttStatus;
    MQTTContext_t * pMqttContext = &mqttContext;
    MQTTSubscribeInfo_t pSubscriptionList[ 1 ];

    assert( pMqttContext != NULL );
    assert( pTopicFilter != NULL );
    assert( topicFilterLength > 0 );

    /* Start with everything at 0. */
    ( void ) memset( ( void * ) pSubscriptionList, 0x00, sizeof( pSubscriptionList ) );

    /* This example subscribes to only one topic and uses QOS1. */
    pSubscriptionList[ 0 ].qos = MQTTQoS1;
    pSubscriptionList[ 0 ].pTopicFilter = pTopicFilter;
    pSubscriptionList[ 0 ].topicFilterLength = topicFilterLength;

    /* Generate packet identifier for the SUBSCRIBE packet. */
    globalSubscribePacketIdentifier = MQTT_GetPacketId( pMqttContext );

    /* Send SUBSCRIBE packet. */
    mqttStatus = MQTT_Subscribe( pMqttContext,
                                 pSubscriptionList,
                                 sizeof( pSubscriptionList ) / sizeof( MQTTSubscribeInfo_t ),
                                 globalSubscribePacketIdentifier );

    if( mqttStatus != MQTTSuccess )
    {
        LogError( ( "Failed to send SUBSCRIBE packet to broker with error = %s.",
                    MQTT_Status_strerror( mqttStatus ) ) );
    }
    else
    {
        LogDebug( ( "SUBSCRIBE topic %.*s to broker.",
                    topicFilterLength,
                    pTopicFilter ) );

        /* Process incoming packet from the broker. Acknowledgment for subscription
         * ( SUBACK ) will be received here. However after sending the subscribe, the
         * client may receive a publish before it receives a subscribe ack. Since this
         * demo is subscribing to the topic to which no one is publishing, probability
         * of receiving publish message before subscribe ack is zero; but application
         * must be ready to receive any packet. This demo uses MQTT_ProcessLoop to
         * receive packet from network. */
        mqttStatus = MQTT_ProcessLoop( pMqttContext, MQTT_PROCESS_LOOP_TIMEOUT_MS );

        if( mqttStatus != MQTTSuccess )
        {
            LogError( ( "MQTT_ProcessLoop returned with status = %s.",
                        MQTT_Status_strerror( mqttStatus ) ) );
        }
        else
        {
            returnStatus = true;
        }
    }

    return returnStatus;
}
/*-----------------------------------------------------------*/

bool UnsubscribeFromTopic( const char * pTopicFilter,
                           uint16_t topicFilterLength )
{
    bool returnStatus = false;
    MQTTStatus_t mqttStatus;
    MQTTContext_t * pMqttContext = &mqttContext;
    MQTTSubscribeInfo_t pSubscriptionList[ 1 ];

    assert( pMqttContext != NULL );
    assert( pTopicFilter != NULL );
    assert( topicFilterLength > 0 );

    /* Start with everything at 0. */
    ( void ) memset( ( void * ) pSubscriptionList, 0x00, sizeof( pSubscriptionList ) );

    /* This example subscribes to only one topic and uses QOS1. */
    pSubscriptionList[ 0 ].qos = MQTTQoS1;
    pSubscriptionList[ 0 ].pTopicFilter = pTopicFilter;
    pSubscriptionList[ 0 ].topicFilterLength = topicFilterLength;

    /* Generate packet identifier for the UNSUBSCRIBE packet. */
    globalUnsubscribePacketIdentifier = MQTT_GetPacketId( pMqttContext );

    /* Send UNSUBSCRIBE packet. */
    mqttStatus = MQTT_Unsubscribe( pMqttContext,
                                   pSubscriptionList,
                                   sizeof( pSubscriptionList ) / sizeof( MQTTSubscribeInfo_t ),
                                   globalUnsubscribePacketIdentifier );

    if( mqttStatus != MQTTSuccess )
    {
        LogError( ( "Failed to send UNSUBSCRIBE packet to broker with error = %s.",
                    MQTT_Status_strerror( mqttStatus ) ) );
    }
    else
    {
        LogDebug( ( "UNSUBSCRIBE sent topic %.*s to broker.",
                    topicFilterLength,
                    pTopicFilter ) );

        /* Process incoming packet from the broker. Acknowledgment for unsubscribe
         * operation ( UNSUBACK ) will be received here. This demo uses
         * MQTT_ProcessLoop to receive packet from network. */
        mqttStatus = MQTT_ProcessLoop( pMqttContext, MQTT_PROCESS_LOOP_TIMEOUT_MS );

        if( mqttStatus != MQTTSuccess )
        {
            LogError( ( "MQTT_ProcessLoop returned with status = %s.",
                        MQTT_Status_strerror( mqttStatus ) ) );
        }
        else
        {
            returnStatus = true;
        }
    }

    return returnStatus;
}
/*-----------------------------------------------------------*/

bool PublishToTopic( const char * pTopicFilter,
                     uint16_t topicFilterLength,
                     const char * pPayload,
                     size_t payloadLength )
{
    bool returnStatus = false;
    MQTTStatus_t mqttStatus = MQTTSuccess;
    uint8_t publishIndex = MAX_OUTGOING_PUBLISHES;
    MQTTContext_t * pMqttContext = &mqttContext;

    assert( pMqttContext != NULL );
    assert( pTopicFilter != NULL );
    assert( topicFilterLength > 0 );

    /* Get the next free index for the outgoing publish. All QoS1 outgoing
     * publishes are stored until a PUBACK is received. These messages are
     * stored for supporting a resend if a network connection is broken before
     * receiving a PUBACK. */
    returnStatus = getNextFreeIndexForOutgoingPublishes( &publishIndex );

    if( returnStatus == false )
    {
        LogError( ( "Unable to find a free spot for outgoing PUBLISH message." ) );
    }
    else
    {
        LogDebug( ( "Published payload: %.*s",
                    ( int ) payloadLength,
                    ( const char * ) pPayload ) );

        /* This example publishes to only one topic and uses QOS1. */
        outgoingPublishPackets[ publishIndex ].pubInfo.qos = MQTTQoS1;
        outgoingPublishPackets[ publishIndex ].pubInfo.pTopicName = pTopicFilter;
        outgoingPublishPackets[ publishIndex ].pubInfo.topicNameLength = topicFilterLength;
        outgoingPublishPackets[ publishIndex ].pubInfo.pPayload = pPayload;
        outgoingPublishPackets[ publishIndex ].pubInfo.payloadLength = payloadLength;

        /* Get a new packet id. */
        outgoingPublishPackets[ publishIndex ].packetId = MQTT_GetPacketId( pMqttContext );

        /* Send PUBLISH packet. */
        mqttStatus = MQTT_Publish( pMqttContext,
                                   &outgoingPublishPackets[ publishIndex ].pubInfo,
                                   outgoingPublishPackets[ publishIndex ].packetId );

        if( mqttStatus != MQTTSuccess )
        {
            LogError( ( "Failed to send PUBLISH packet to broker with error = %s.",
                        MQTT_Status_strerror( mqttStatus ) ) );
            cleanupOutgoingPublishAt( publishIndex );
            returnStatus = false;
        }
        else
        {
            LogDebug( ( "PUBLISH sent for topic %.*s to broker with packet ID %u.",
                        topicFilterLength,
                        pTopicFilter,
                        outgoingPublishPackets[ publishIndex ].packetId ) );
        }
    }

    return returnStatus;
}
/*-----------------------------------------------------------*/

bool ProcessLoop( void )
{
    bool returnStatus = false;
    MQTTStatus_t mqttStatus = MQTTSuccess;

    mqttStatus = MQTT_ProcessLoop( &mqttContext, MQTT_PROCESS_LOOP_TIMEOUT_MS );

    if( mqttStatus != MQTTSuccess )
    {
        LogError( ( "MQTT_ProcessLoop returned with status = %s.",
                    MQTT_Status_strerror( mqttStatus ) ) );
    }
    else
    {
        LogDebug( ( "MQTT_ProcessLoop successful." ) );
        returnStatus = true;
    }

    return returnStatus;
}
/*-----------------------------------------------------------*/

static uint32_t prvGetTimeMs(void)
{
    TickType_t xTickCount = 0;
    uint32_t ulTimeMs = 0UL;

    /* Get the current tick count. */
    xTickCount = xTaskGetTickCount();

    /* Convert the ticks to milliseconds. */
    ulTimeMs = (uint32_t)xTickCount * MILLISECONDS_PER_TICK;

    /* Reduce ulGlobalEntryTimeMs from obtained time so as to always return the
     * elapsed time in the application. */
    ulTimeMs = (uint32_t)(ulTimeMs - ulGlobalEntryTimeMs);

    return ulTimeMs;
}

/*-----------------------------------------------------------*/
