/*
 * FreeRTOS V202112.00
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
 * @file mqtt_operations.c
 *
 * @brief This file provides wrapper functions for MQTT operations on a mutually
 * authenticated TLS connection.
 *
 * A mutually authenticated TLS connection is used to connect to the AWS IoT
 * MQTT message broker in this example. Run the setup script
 * (fleet_provisioning_demo_setup.py) and define democonfigROOT_CA_PEM
 * in demo_config.h to achieve mutual authentication.
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
#ifndef democonfigMQTT_BROKER_PORT
    #define democonfigMQTT_BROKER_PORT    ( 8883 )
#endif

#ifndef democonfigNETWORK_BUFFER_SIZE
    #define democonfigNETWORK_BUFFER_SIZE    ( 1024U )
#endif

/**
 * @brief Length of the AWS IoT endpoint.
 */
#define democonfigMQTT_BROKER_ENDPOINT_LENGTH          ( ( uint16_t ) ( sizeof( democonfigMQTT_BROKER_ENDPOINT ) - 1 ) )

/**
 * @brief Length of the client identifier.
 */
#define mqttopCLIENT_IDENTIFIER_LENGTH                 ( ( uint16_t ) ( sizeof( democonfigCLIENT_IDENTIFIER ) - 1 ) )

/**
 * @brief ALPN protocol name for AWS IoT MQTT.
 *
 * This will be used if the democonfigMQTT_BROKER_PORT is configured as 443 for AWS IoT MQTT
 * broker. Please see more details about the ALPN protocol for AWS IoT MQTT
 * endpoint in the link below.
 * https://aws.amazon.com/blogs/iot/mqtt-with-tls-client-authentication-on-port-443-why-it-is-useful-and-how-it-works/
 *
 * @note OpenSSL requires that the protocol string passed to it for configuration be encoded
 * with the prefix of 8-bit length information of the string. Thus, the 14 byte (0x0e) length
 * information is prefixed to the string.
 */
#define mqttopALPN_PROTOCOL_NAME                       "\x0ex-amzn-mqtt-ca"

/**
 * @brief Length of ALPN protocol name.
 */
#define mqttopALPN_PROTOCOL_NAME_LENGTH                ( ( uint16_t ) ( sizeof( mqttopALPN_PROTOCOL_NAME ) - 1 ) )

/**
 * @brief The maximum number of retries for connecting to server.
 */
#define mqttopCONNECTION_RETRY_MAX_ATTEMPTS            ( 5U )

/**
 * @brief The maximum back-off delay (in milliseconds) for retrying connection to server.
 */
#define mqttopCONNECTION_RETRY_MAX_BACKOFF_DELAY_MS    ( 5000U )

/**
 * @brief The base back-off delay (in milliseconds) to use for connection retry attempts.
 */
#define mqttopCONNECTION_RETRY_BACKOFF_BASE_MS         ( 500U )

/**
 * @brief Timeout for receiving CONNACK packet in milliseconds.
 */
#define mqttopCONNACK_RECV_TIMEOUT_MS                  ( 1000U )

/**
 * @brief Maximum number of outgoing publishes maintained in the application
 * until an ack is received from the broker.
 */
#define mqttopMAX_OUTGOING_PUBLISHES                   ( 5U )

/**
 * @brief Invalid packet identifier for the MQTT packets. Zero is always an
 * invalid packet identifier as per MQTT 3.1.1 spec.
 */
#define mqttopMQTT_PACKET_ID_INVALID                   ( ( uint16_t ) 0U )

/**
 * @brief Timeout for MQTT_ProcessLoop function in milliseconds.
 */
#define mqttopMQTT_PROCESS_LOOP_TIMEOUT_MS             ( 1000U )

/**
 * @brief The maximum time interval in seconds which is allowed to elapse
 *  between two Control Packets.
 *
 *  It is the responsibility of the client to ensure that the interval between
 *  control packets being sent does not exceed the this keep-alive value. In the
 *  absence of sending any other control packets, the client MUST send a
 *  PINGREQ packet.
 */
#define mqttopMQTT_KEEP_ALIVE_INTERVAL_SECONDS         ( 60U )

/**
 * @brief Timeout in milliseconds for transport send and receive.
 */
#define mqttopTRANSPORT_SEND_RECV_TIMEOUT_MS           ( 100U )

/**
 * @brief Milliseconds per second.
 */
#define mqttopMILLISECONDS_PER_SECOND                  ( 1000U )

/**
 * @brief Milliseconds per FreeRTOS tick.
 */
#define mqttopMILLISECONDS_PER_TICK                    ( mqttopMILLISECONDS_PER_SECOND / configTICK_RATE_HZ )

/**
 * @brief The MQTT metrics string expected by AWS IoT MQTT Broker.
 */
#define mqttopMETRICS_STRING                           "?SDK=" democonfigOS_NAME "&Version=" democonfigOS_VERSION "&Platform=" democonfigHARDWARE_PLATFORM_NAME "&MQTTLib=" democonfigMQTT_LIB

/**
 * @brief The length of the MQTT metrics string.
 */
#define mqttopMETRICS_STRING_LENGTH                    ( ( uint16_t ) ( sizeof( mqttopMETRICS_STRING ) - 1 ) )
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
    uint16_t usPacketId;

    /**
     * @brief Publish info of the publish packet.
     */
    MQTTPublishInfo_t xPubInfo;
} PublishPackets_t;

/* Each compilation unit must define the NetworkContext struct. */
struct NetworkContext
{
    SSLContext_t * pxParams;
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
static uint16_t usGlobalSubscribePacketIdentifier = 0U;

/**
 * @brief Packet Identifier generated when Unsubscribe request was sent to the broker.
 *
 * It is used to match received Unsubscribe ACK to the transmitted unsubscribe
 * request.
 */
static uint16_t usGlobalUnsubscribePacketIdentifier = 0U;

/**
 * @brief Array to keep the outgoing publish messages.
 *
 * These stored outgoing publish messages are kept until a successful ack
 * is received.
 */
static PublishPackets_t pxOutgoingPublishPackets[ mqttopMAX_OUTGOING_PUBLISHES ] = { 0 };

/**
 * @brief The network buffer must remain valid for the lifetime of the MQTT context.
 */
static uint8_t pucBuffer[ democonfigNETWORK_BUFFER_SIZE ];

/**
 * @brief The MQTT context used for MQTT operation.
 */
static MQTTContext_t xMqttContext = { 0 };

/**
 * @brief The network context used for MbedTLS operation.
 */
static NetworkContext_t xNetworkContext = { 0 };

/**
 * @brief The parameters for MbedTLS operation.
 */
static SSLContext_t xTlsContext = { 0 };

/**
 * @brief The flag to indicate that the mqtt session is established.
 */
static bool xMqttSessionEstablished = false;

/**
 * @brief Callback registered when calling xEstablishMqttSession to get incoming
 * publish messages.
 */
static MQTTPublishCallback_t xAppPublishCallback = NULL;
/*-----------------------------------------------------------*/

/**
 * @brief The random number generator to use for exponential backoff with
 * jitter retry logic.
 *
 * @return The generated random number.
 */
static uint32_t prvGenerateRandomNumber( void );

/**
 * @brief Connect to the MQTT broker with reconnection retries.
 *
 * If connection fails, retry is attempted after a timeout. Timeout value
 * exponentially increases until maximum timeout value is reached or the number
 * of attempts are exhausted.
 *
 * @param[out] pxNetworkContext The created network context.
 * @param[in] pcClientCertLabel The client certificate PKCS #11 label to use.
 * @param[in] pcPrivateKeyLabel The private key PKCS #11 label for the client certificate.
 *
 * @return false on failure; true on successful connection.
 */
static bool prvConnectToBrokerWithBackoffRetries( NetworkContext_t * pxNetworkContext,
                                                  char * pcClientCertLabel,
                                                  char * pcPrivateKeyLabel );

/**
 * @brief Get the free index in the #pxOutgoingPublishPackets array at which an
 * outgoing publish can be stored.
 *
 * @param[out] pucIndex The index at which an outgoing publish can be stored.
 *
 * @return false if no more publishes can be stored;
 * true if an index to store the next outgoing publish is obtained.
 */
static bool prvGetNextFreeIndexForOutgoingPublishes( uint8_t * pucIndex );

/**
 * @brief Clean up the outgoing publish at given index from the
 * #pxOutgoingPublishPackets array.
 *
 * @param[in] ucIndex The ucIndex at which a publish message has to be cleaned up.
 */
static void prvCleanupOutgoingPublishAt( uint8_t ucIndex );

/**
 * @brief Clean up all the outgoing publishes in the #pxOutgoingPublishPackets array.
 */
static void prvCleanupOutgoingPublishes( void );

/**
 * @brief Clean up the publish packet with the given packet id in the
 * #pxOutgoingPublishPackets array.
 *
 * @param[in] usPacketId Packet id of the packet to be clean.
 */
static void prvCleanupOutgoingPublishWithPacketID( uint16_t usPacketId );

/**
 * @brief Callback registered with the MQTT library.
 *
 * @param[in] pxMqttContext MQTT context pointer.
 * @param[in] pxPacketInfo Packet Info pointer for the incoming packet.
 * @param[in] pxDeserializedInfo Deserialized information from the incoming packet.
 */
static void prvMqttCallback( MQTTContext_t * pxMqttContext,
                             MQTTPacketInfo_t * pxPacketInfo,
                             MQTTDeserializedInfo_t * pxDeserializedInfo );

/**
 * @brief Resend the publishes if a session is re-established with the broker.
 *
 * This function handles the resending of the QoS1 publish packets, which are
 * maintained locally.
 *
 * @param[in] pxMqttContext The MQTT context pointer.
 *
 * @return true if all the unacknowledged QoS1 publishes are re-sent successfully;
 * false otherwise.
 */
static bool prvHandlePublishResend( MQTTContext_t * pxMqttContext );

/**
 * @brief The timer query function provided to the MQTT context.
 *
 * @return Time in milliseconds.
 */
static uint32_t prvGetTimeMs( void );

/*-----------------------------------------------------------*/

static uint32_t prvGenerateRandomNumber()
{
    return( ( uint32_t ) rand() );
}

/*-----------------------------------------------------------*/

static bool prvConnectToBrokerWithBackoffRetries( NetworkContext_t * pxNetworkContext,
                                                  char * pcClientCertLabel,
                                                  char * pcPrivateKeyLabel )
{
    bool xReturnStatus = false;
    BackoffAlgorithmStatus_t xBackoffAlgStatus = BackoffAlgorithmSuccess;
    TlsTransportStatus_t xTlsStatus = TLS_TRANSPORT_SUCCESS;
    BackoffAlgorithmContext_t xReconnectParams;
    NetworkCredentials_t xTlsCredentials = { 0 };
    uint16_t usNextRetryBackOff = 0U;
    const char * pcAlpn[] = { mqttopALPN_PROTOCOL_NAME, NULL };

    /* Set the pParams member of the network context with desired transport. */
    pxNetworkContext->pxParams = &xTlsContext;

    /* Initialize credentials for establishing TLS session. */
    xTlsCredentials.pRootCa = democonfigROOT_CA_PEM;
    xTlsCredentials.rootCaSize = sizeof( democonfigROOT_CA_PEM );
    xTlsCredentials.pClientCertLabel = pcClientCertLabel;
    xTlsCredentials.pPrivateKeyLabel = pcPrivateKeyLabel;

    /* AWS IoT requires devices to send the Server Name Indication (SNI)
     * extension to the Transport Layer Security (TLS) protocol and provide
     * the complete endpoint address in the host_name field. Details about
     * SNI for AWS IoT can be found in the link below.
     * https://docs.aws.amazon.com/iot/latest/developerguide/transport-security.html
     */
    xTlsCredentials.disableSni = false;

    if( democonfigMQTT_BROKER_PORT == 443 )
    {
        /* Pass the ALPN protocol name depending on the port being used.
         * Please see more details about the ALPN protocol for AWS IoT MQTT endpoint
         * in the link below.
         * https://aws.amazon.com/blogs/iot/mqtt-with-tls-client-authentication-on-port-443-why-it-is-useful-and-how-it-works/
         */
        xTlsCredentials.pAlpnProtos = pcAlpn;
    }

    /* Initialize reconnect attempts and interval */
    BackoffAlgorithm_InitializeParams( &xReconnectParams,
                                       mqttopCONNECTION_RETRY_BACKOFF_BASE_MS,
                                       mqttopCONNECTION_RETRY_MAX_BACKOFF_DELAY_MS,
                                       mqttopCONNECTION_RETRY_MAX_ATTEMPTS );

    do
    {
        /* Establish a TLS session with the MQTT broker. This example connects
         * to the MQTT broker as specified in democonfigMQTT_BROKER_ENDPOINT and democonfigMQTT_BROKER_PORT
         * at the demo config header. */
        LogDebug( ( "Establishing a TLS session to %.*s:%d.",
                    democonfigMQTT_BROKER_ENDPOINT_LENGTH,
                    democonfigMQTT_BROKER_ENDPOINT,
                    democonfigMQTT_BROKER_PORT ) );

        xTlsStatus = TLS_FreeRTOS_Connect( pxNetworkContext,
                                           democonfigMQTT_BROKER_ENDPOINT,
                                           democonfigMQTT_BROKER_PORT,
                                           &xTlsCredentials,
                                           mqttopTRANSPORT_SEND_RECV_TIMEOUT_MS, mqttopTRANSPORT_SEND_RECV_TIMEOUT_MS );

        if( xTlsStatus == TLS_TRANSPORT_SUCCESS )
        {
            /* Connection successful. */
            xReturnStatus = true;
        }
        else
        {
            /* Generate a random number and get back-off value (in milliseconds) for the next connection retry. */
            xBackoffAlgStatus = BackoffAlgorithm_GetNextBackoff( &xReconnectParams, prvGenerateRandomNumber(), &usNextRetryBackOff );

            if( xBackoffAlgStatus == BackoffAlgorithmRetriesExhausted )
            {
                LogError( ( "Connection to the broker failed, all attempts exhausted." ) );
            }
            else if( xBackoffAlgStatus == BackoffAlgorithmSuccess )
            {
                LogWarn( ( "Connection to the broker failed. Retrying connection "
                           "after %hu ms backoff.",
                           ( unsigned short ) usNextRetryBackOff ) );
                vTaskDelay( pdMS_TO_TICKS( usNextRetryBackOff ) );
            }
        }
    } while( ( xTlsStatus != TLS_TRANSPORT_SUCCESS ) && ( xBackoffAlgStatus == BackoffAlgorithmSuccess ) );

    return xReturnStatus;
}
/*-----------------------------------------------------------*/

static bool prvGetNextFreeIndexForOutgoingPublishes( uint8_t * pucIndex )
{
    bool xReturnStatus = false;
    uint8_t ucIndex = 0;

    configASSERT( pxOutgoingPublishPackets != NULL );
    configASSERT( pucIndex != NULL );

    for( ucIndex = 0; ucIndex < mqttopMAX_OUTGOING_PUBLISHES; ucIndex++ )
    {
        /* A free index is marked by invalid packet id. Check if the the index
         * has a free slot. */
        if( pxOutgoingPublishPackets[ ucIndex ].usPacketId == mqttopMQTT_PACKET_ID_INVALID )
        {
            xReturnStatus = true;
            break;
        }
    }

    /* Copy the available index into the output param. */
    if( xReturnStatus == true )
    {
        *pucIndex = ucIndex;
    }

    return xReturnStatus;
}
/*-----------------------------------------------------------*/

static void prvCleanupOutgoingPublishAt( uint8_t ucIndex )
{
    configASSERT( pxOutgoingPublishPackets != NULL );
    configASSERT( ucIndex < mqttopMAX_OUTGOING_PUBLISHES );

    /* Clear the outgoing publish packet. */
    ( void ) memset( &( pxOutgoingPublishPackets[ ucIndex ] ),
                     0x00,
                     sizeof( pxOutgoingPublishPackets[ ucIndex ] ) );
}
/*-----------------------------------------------------------*/

static void prvCleanupOutgoingPublishes( void )
{
    configASSERT( pxOutgoingPublishPackets != NULL );

    /* Clean up all the outgoing publish packets. */
    ( void ) memset( pxOutgoingPublishPackets, 0x00, sizeof( pxOutgoingPublishPackets ) );
}
/*-----------------------------------------------------------*/

static void prvCleanupOutgoingPublishWithPacketID( uint16_t usPacketId )
{
    uint8_t ucIndex = 0;

    configASSERT( pxOutgoingPublishPackets != NULL );
    configASSERT( usPacketId != mqttopMQTT_PACKET_ID_INVALID );

    /* Clean up the saved outgoing publish with packet Id equal to usPacketId. */
    for( ucIndex = 0; ucIndex < mqttopMAX_OUTGOING_PUBLISHES; ucIndex++ )
    {
        if( pxOutgoingPublishPackets[ ucIndex ].usPacketId == usPacketId )
        {
            prvCleanupOutgoingPublishAt( ucIndex );

            LogDebug( ( "Cleaned up outgoing publish packet with packet id %u.",
                        usPacketId ) );

            break;
        }
    }
}
/*-----------------------------------------------------------*/

static void prvMqttCallback( MQTTContext_t * pxMqttContext,
                             MQTTPacketInfo_t * pxPacketInfo,
                             MQTTDeserializedInfo_t * pxDeserializedInfo )
{
    uint16_t usPacketIdentifier;

    configASSERT( pxMqttContext != NULL );
    configASSERT( pxPacketInfo != NULL );
    configASSERT( pxDeserializedInfo != NULL );

    /* Suppress the unused parameter warning when asserts are disabled in
     * build. */
    ( void ) pxMqttContext;

    usPacketIdentifier = pxDeserializedInfo->packetIdentifier;

    /* Handle an incoming publish. The lower 4 bits of the publish packet
     * type is used for the dup, QoS, and retain flags. Hence masking
     * out the lower bits to check if the packet is publish. */
    if( ( pxPacketInfo->type & 0xF0U ) == MQTT_PACKET_TYPE_PUBLISH )
    {
        configASSERT( pxDeserializedInfo->pPublishInfo != NULL );

        /* Invoke the application callback for incoming publishes. */
        if( xAppPublishCallback != NULL )
        {
            xAppPublishCallback( pxDeserializedInfo->pPublishInfo, usPacketIdentifier );
        }
    }
    else
    {
        /* Handle other packets. */
        switch( pxPacketInfo->type )
        {
            case MQTT_PACKET_TYPE_SUBACK:
                LogDebug( ( "MQTT Packet type SUBACK received." ) );

                /* Make sure the ACK packet identifier matches with the request
                 * packet identifier. */
                configASSERT( usGlobalSubscribePacketIdentifier == usPacketIdentifier );
                break;

            case MQTT_PACKET_TYPE_UNSUBACK:
                LogDebug( ( "MQTT Packet type UNSUBACK received." ) );

                /* Make sure the ACK packet identifier matches with the request
                 * packet identifier. */
                configASSERT( usGlobalUnsubscribePacketIdentifier == usPacketIdentifier );
                break;

            case MQTT_PACKET_TYPE_PINGRESP:

                /* We do not expect to receive PINGRESP as we are using
                 * MQTT_ProcessLoop. */
                LogWarn( ( "PINGRESP should not be received by the application "
                           "callback when using MQTT_ProcessLoop." ) );
                break;

            case MQTT_PACKET_TYPE_PUBACK:
                LogDebug( ( "PUBACK received for packet id %u.",
                            usPacketIdentifier ) );

                /* Cleanup the publish packet from the #pxOutgoingPublishPackets
                 * array when a PUBACK is received. */
                prvCleanupOutgoingPublishWithPacketID( usPacketIdentifier );
                break;

            /* Any other packet type is invalid. */
            default:
                LogError( ( "Unknown packet type received:(%02x).",
                            pxPacketInfo->type ) );
        }
    }
}
/*-----------------------------------------------------------*/

static bool prvHandlePublishResend( MQTTContext_t * pxMqttContext )
{
    bool xReturnStatus = false;
    MQTTStatus_t xMqttStatus = MQTTSuccess;
    uint8_t ucIndex = 0U;

    configASSERT( pxOutgoingPublishPackets != NULL );

    /* Resend all the QoS1 publishes still in the #pxOutgoingPublishPackets array.
     * These are the publishes that haven't received a PUBACK yet. When a PUBACK
     * is received, the corresponding publish is removed from the array. */
    for( ucIndex = 0U; ucIndex < mqttopMAX_OUTGOING_PUBLISHES; ucIndex++ )
    {
        if( pxOutgoingPublishPackets[ ucIndex ].usPacketId != mqttopMQTT_PACKET_ID_INVALID )
        {
            pxOutgoingPublishPackets[ ucIndex ].xPubInfo.dup = true;

            LogDebug( ( "Sending duplicate PUBLISH with packet id %u.",
                        pxOutgoingPublishPackets[ ucIndex ].usPacketId ) );
            xMqttStatus = MQTT_Publish( pxMqttContext,
                                        &pxOutgoingPublishPackets[ ucIndex ].xPubInfo,
                                        pxOutgoingPublishPackets[ ucIndex ].usPacketId );

            if( xMqttStatus != MQTTSuccess )
            {
                LogError( ( "Sending duplicate PUBLISH for packet id %u "
                            " failed with status %s.",
                            pxOutgoingPublishPackets[ ucIndex ].usPacketId,
                            MQTT_Status_strerror( xMqttStatus ) ) );
                break;
            }
            else
            {
                LogDebug( ( "Sent duplicate PUBLISH successfully for packet id %u.",
                            pxOutgoingPublishPackets[ ucIndex ].usPacketId ) );
            }
        }
    }

    /* Were all the unacknowledged QoS1 publishes successfully re-sent? */
    if( ucIndex == mqttopMAX_OUTGOING_PUBLISHES )
    {
        xReturnStatus = true;
    }

    return xReturnStatus;
}
/*-----------------------------------------------------------*/

bool xEstablishMqttSession( MQTTPublishCallback_t xPublishCallback,
                            char * pcClientCertLabel,
                            char * pcPrivateKeyLabel )
{
    bool xReturnStatus = false;
    MQTTStatus_t xMqttStatus;
    MQTTConnectInfo_t xConnectInfo;
    MQTTFixedBuffer_t xNetworkBuffer;
    TransportInterface_t xTransport;
    bool xCreateCleanSession = false;
    MQTTContext_t * pxMqttContext = &xMqttContext;
    NetworkContext_t * pxNetworkContext = &xNetworkContext;
    bool xSessionPresent = false;

    configASSERT( pxMqttContext != NULL );
    configASSERT( pxNetworkContext != NULL );

    /* Initialize the mqtt context and network context. */
    ( void ) memset( pxMqttContext, 0U, sizeof( MQTTContext_t ) );
    ( void ) memset( pxNetworkContext, 0U, sizeof( NetworkContext_t ) );

    xReturnStatus = prvConnectToBrokerWithBackoffRetries( pxNetworkContext,
                                                          pcClientCertLabel,
                                                          pcPrivateKeyLabel );

    if( xReturnStatus != true )
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
         * from the network. pxNetworkContext is an SSL context for OpenSSL.*/
        xTransport.pNetworkContext = pxNetworkContext;
        xTransport.send = TLS_FreeRTOS_send;
        xTransport.recv = TLS_FreeRTOS_recv;

        /* Fill the values for network buffer. */
        xNetworkBuffer.pBuffer = pucBuffer;
        xNetworkBuffer.size = democonfigNETWORK_BUFFER_SIZE;

        /* Remember the publish callback supplied. */
        xAppPublishCallback = xPublishCallback;

        /* Initialize the MQTT library. */
        xMqttStatus = MQTT_Init( pxMqttContext,
                                 &xTransport,
                                 prvGetTimeMs,
                                 prvMqttCallback,
                                 &xNetworkBuffer );

        if( xMqttStatus != MQTTSuccess )
        {
            xReturnStatus = false;
            LogError( ( "MQTT init failed with status %s.",
                        MQTT_Status_strerror( xMqttStatus ) ) );
        }
        else
        {
            /* Establish an MQTT session by sending a CONNECT packet. */

            /* If #xCreateCleanSession is true, start with a clean session
             * i.e. direct the MQTT broker to discard any previous session data.
             * If #xCreateCleanSession is false, direct the broker to attempt to
             * reestablish a session which was already present. */
            xConnectInfo.cleanSession = xCreateCleanSession;

            /* The client identifier is used to uniquely identify this MQTT client to
             * the MQTT broker. In a production device the identifier can be something
             * unique, such as a device serial number. */
            xConnectInfo.pClientIdentifier = democonfigCLIENT_IDENTIFIER;
            xConnectInfo.clientIdentifierLength = mqttopCLIENT_IDENTIFIER_LENGTH;

            /* The maximum time interval in seconds which is allowed to elapse
             * between two Control Packets.
             * It is the responsibility of the client to ensure that the interval between
             * control packets being sent does not exceed the this keep-alive value. In the
             * absence of sending any other control packets, the client MUST send a
             * PINGREQ packet. */
            xConnectInfo.keepAliveSeconds = mqttopMQTT_KEEP_ALIVE_INTERVAL_SECONDS;

            /* Username and password for authentication. Not used in this demo. */
            xConnectInfo.pUserName = mqttopMETRICS_STRING;
            xConnectInfo.userNameLength = mqttopMETRICS_STRING_LENGTH;
            xConnectInfo.pPassword = NULL;
            xConnectInfo.passwordLength = 0U;

            /* Send an MQTT CONNECT packet to the broker. */
            xMqttStatus = MQTT_Connect( pxMqttContext,
                                        &xConnectInfo,
                                        NULL,
                                        mqttopCONNACK_RECV_TIMEOUT_MS,
                                        &xSessionPresent );

            if( xMqttStatus != MQTTSuccess )
            {
                xReturnStatus = false;
                LogError( ( "Connection with MQTT broker failed with status %s.",
                            MQTT_Status_strerror( xMqttStatus ) ) );
            }
            else
            {
                LogDebug( ( "MQTT connection successfully established with broker." ) );
            }
        }

        if( xReturnStatus == true )
        {
            /* Keep a flag for indicating if MQTT session is established. This
             * flag will mark that an MQTT DISCONNECT has to be sent at the end
             * of the demo even if there are intermediate failures. */
            xMqttSessionEstablished = true;
        }

        if( xReturnStatus == true )
        {
            /* Check if a session is present and if there are any outgoing
             * publishes that need to be resent. Resending unacknowledged
             * publishes is needed only if the broker is re-establishing a
             * session that was already present. */
            if( xSessionPresent == true )
            {
                LogDebug( ( "An MQTT session with broker is re-established. "
                            "Resending unacked publishes." ) );

                /* Handle all the resend of publish messages. */
                xReturnStatus = prvHandlePublishResend( &xMqttContext );
            }
            else
            {
                LogDebug( ( "A clean MQTT connection is established."
                            " Cleaning up all the stored outgoing publishes." ) );

                /* Clean up the outgoing publishes waiting for ack as this new
                 * connection doesn't re-establish an existing session. */
                prvCleanupOutgoingPublishes();
            }
        }
    }

    return xReturnStatus;
}
/*-----------------------------------------------------------*/

bool xDisconnectMqttSession( void )
{
    MQTTStatus_t xMqttStatus = MQTTSuccess;
    bool xReturnStatus = false;
    MQTTContext_t * pxMqttContext = &xMqttContext;
    NetworkContext_t * pxNetworkContext = &xNetworkContext;

    configASSERT( pxMqttContext != NULL );
    configASSERT( pxNetworkContext != NULL );

    if( xMqttSessionEstablished == true )
    {
        /* Send DISCONNECT. */
        xMqttStatus = MQTT_Disconnect( pxMqttContext );

        if( xMqttStatus != MQTTSuccess )
        {
            LogError( ( "Sending MQTT DISCONNECT failed with status=%u.",
                        xMqttStatus ) );
        }
        else
        {
            /* MQTT DISCONNECT sent successfully. */
            xReturnStatus = true;
        }
    }

    /* End TLS session, then close TCP connection. */
    ( void ) TLS_FreeRTOS_Disconnect( pxNetworkContext );

    return xReturnStatus;
}
/*-----------------------------------------------------------*/

bool xSubscribeToTopic( const char * pcTopicFilter,
                        uint16_t usTopicFilterLength )
{
    bool xReturnStatus = false;
    MQTTStatus_t xMqttStatus;
    MQTTContext_t * pxMqttContext = &xMqttContext;
    MQTTSubscribeInfo_t pxSubscriptionList[ 1 ];

    configASSERT( pxMqttContext != NULL );
    configASSERT( pcTopicFilter != NULL );
    configASSERT( usTopicFilterLength > 0 );

    /* Start with everything at 0. */
    ( void ) memset( ( void * ) pxSubscriptionList, 0x00, sizeof( pxSubscriptionList ) );

    /* This example subscribes to only one topic and uses QOS1. */
    pxSubscriptionList[ 0 ].qos = MQTTQoS1;
    pxSubscriptionList[ 0 ].pTopicFilter = pcTopicFilter;
    pxSubscriptionList[ 0 ].topicFilterLength = usTopicFilterLength;

    /* Generate packet identifier for the SUBSCRIBE packet. */
    usGlobalSubscribePacketIdentifier = MQTT_GetPacketId( pxMqttContext );

    /* Send SUBSCRIBE packet. */
    xMqttStatus = MQTT_Subscribe( pxMqttContext,
                                  pxSubscriptionList,
                                  sizeof( pxSubscriptionList ) / sizeof( MQTTSubscribeInfo_t ),
                                  usGlobalSubscribePacketIdentifier );

    if( xMqttStatus != MQTTSuccess )
    {
        LogError( ( "Failed to send SUBSCRIBE packet to broker with error = %s.",
                    MQTT_Status_strerror( xMqttStatus ) ) );
    }
    else
    {
        LogDebug( ( "SUBSCRIBE topic %.*s to broker.",
                    usTopicFilterLength,
                    pcTopicFilter ) );

        /* Process incoming packet from the broker. Acknowledgment for subscription
         * ( SUBACK ) will be received here. However after sending the subscribe, the
         * client may receive a publish before it receives a subscribe ack. Since this
         * demo is subscribing to the topic to which no one is publishing, probability
         * of receiving publish message before subscribe ack is zero; but application
         * must be ready to receive any packet. This demo uses MQTT_ProcessLoop to
         * receive packet from network. */
        xMqttStatus = MQTT_ProcessLoop( pxMqttContext, mqttopMQTT_PROCESS_LOOP_TIMEOUT_MS );

        if( xMqttStatus != MQTTSuccess )
        {
            LogError( ( "MQTT_ProcessLoop returned with status = %s.",
                        MQTT_Status_strerror( xMqttStatus ) ) );
        }
        else
        {
            xReturnStatus = true;
        }
    }

    return xReturnStatus;
}
/*-----------------------------------------------------------*/

bool xUnsubscribeFromTopic( const char * pcTopicFilter,
                            uint16_t usTopicFilterLength )
{
    bool xReturnStatus = false;
    MQTTStatus_t xMqttStatus;
    MQTTContext_t * pxMqttContext = &xMqttContext;
    MQTTSubscribeInfo_t pxSubscriptionList[ 1 ];

    configASSERT( pxMqttContext != NULL );
    configASSERT( pcTopicFilter != NULL );
    configASSERT( usTopicFilterLength > 0 );

    /* Start with everything at 0. */
    ( void ) memset( ( void * ) pxSubscriptionList, 0x00, sizeof( pxSubscriptionList ) );

    /* This example subscribes to only one topic and uses QOS1. */
    pxSubscriptionList[ 0 ].qos = MQTTQoS1;
    pxSubscriptionList[ 0 ].pTopicFilter = pcTopicFilter;
    pxSubscriptionList[ 0 ].topicFilterLength = usTopicFilterLength;

    /* Generate packet identifier for the UNSUBSCRIBE packet. */
    usGlobalUnsubscribePacketIdentifier = MQTT_GetPacketId( pxMqttContext );

    /* Send UNSUBSCRIBE packet. */
    xMqttStatus = MQTT_Unsubscribe( pxMqttContext,
                                    pxSubscriptionList,
                                    sizeof( pxSubscriptionList ) / sizeof( MQTTSubscribeInfo_t ),
                                    usGlobalUnsubscribePacketIdentifier );

    if( xMqttStatus != MQTTSuccess )
    {
        LogError( ( "Failed to send UNSUBSCRIBE packet to broker with error = %s.",
                    MQTT_Status_strerror( xMqttStatus ) ) );
    }
    else
    {
        LogDebug( ( "UNSUBSCRIBE sent topic %.*s to broker.",
                    usTopicFilterLength,
                    pcTopicFilter ) );

        /* Process incoming packet from the broker. Acknowledgment for unsubscribe
         * operation ( UNSUBACK ) will be received here. This demo uses
         * MQTT_ProcessLoop to receive packet from network. */
        xMqttStatus = MQTT_ProcessLoop( pxMqttContext, mqttopMQTT_PROCESS_LOOP_TIMEOUT_MS );

        if( xMqttStatus != MQTTSuccess )
        {
            LogError( ( "MQTT_ProcessLoop returned with status = %s.",
                        MQTT_Status_strerror( xMqttStatus ) ) );
        }
        else
        {
            xReturnStatus = true;
        }
    }

    return xReturnStatus;
}
/*-----------------------------------------------------------*/

bool xPublishToTopic( const char * pcTopicFilter,
                      uint16_t usTopicFilterLength,
                      const char * pcPayload,
                      size_t xPayloadLength )
{
    bool xReturnStatus = false;
    MQTTStatus_t xMqttStatus = MQTTSuccess;
    uint8_t ucPublishIndex = mqttopMAX_OUTGOING_PUBLISHES;
    MQTTContext_t * pxMqttContext = &xMqttContext;

    configASSERT( pxMqttContext != NULL );
    configASSERT( pcTopicFilter != NULL );
    configASSERT( usTopicFilterLength > 0 );

    /* Get the next free index for the outgoing publish. All QoS1 outgoing
     * publishes are stored until a PUBACK is received. These messages are
     * stored for supporting a resend if a network connection is broken before
     * receiving a PUBACK. */
    xReturnStatus = prvGetNextFreeIndexForOutgoingPublishes( &ucPublishIndex );

    if( xReturnStatus == false )
    {
        LogError( ( "Unable to find a free spot for outgoing PUBLISH message." ) );
    }
    else
    {
        LogDebug( ( "Published payload: %.*s",
                    ( int ) xPayloadLength,
                    ( const char * ) pcPayload ) );

        /* This example publishes to only one topic and uses QOS1. */
        pxOutgoingPublishPackets[ ucPublishIndex ].xPubInfo.qos = MQTTQoS1;
        pxOutgoingPublishPackets[ ucPublishIndex ].xPubInfo.pTopicName = pcTopicFilter;
        pxOutgoingPublishPackets[ ucPublishIndex ].xPubInfo.topicNameLength = usTopicFilterLength;
        pxOutgoingPublishPackets[ ucPublishIndex ].xPubInfo.pPayload = pcPayload;
        pxOutgoingPublishPackets[ ucPublishIndex ].xPubInfo.payloadLength = xPayloadLength;

        /* Get a new packet id. */
        pxOutgoingPublishPackets[ ucPublishIndex ].usPacketId = MQTT_GetPacketId( pxMqttContext );

        /* Send PUBLISH packet. */
        xMqttStatus = MQTT_Publish( pxMqttContext,
                                    &pxOutgoingPublishPackets[ ucPublishIndex ].xPubInfo,
                                    pxOutgoingPublishPackets[ ucPublishIndex ].usPacketId );

        if( xMqttStatus != MQTTSuccess )
        {
            LogError( ( "Failed to send PUBLISH packet to broker with error = %s.",
                        MQTT_Status_strerror( xMqttStatus ) ) );
            prvCleanupOutgoingPublishAt( ucPublishIndex );
            xReturnStatus = false;
        }
        else
        {
            LogDebug( ( "PUBLISH sent for topic %.*s to broker with packet ID %u.",
                        usTopicFilterLength,
                        pcTopicFilter,
                        pxOutgoingPublishPackets[ ucPublishIndex ].usPacketId ) );
        }
    }

    return xReturnStatus;
}
/*-----------------------------------------------------------*/

bool xProcessLoop( void )
{
    bool xReturnStatus = false;
    MQTTStatus_t xMqttStatus = MQTTSuccess;

    xMqttStatus = MQTT_ProcessLoop( &xMqttContext, mqttopMQTT_PROCESS_LOOP_TIMEOUT_MS );

    if( xMqttStatus != MQTTSuccess )
    {
        LogError( ( "MQTT_ProcessLoop returned with status = %s.",
                    MQTT_Status_strerror( xMqttStatus ) ) );
    }
    else
    {
        LogDebug( ( "MQTT_ProcessLoop successful." ) );
        xReturnStatus = true;
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
    ulTimeMs = ( uint32_t ) xTickCount * mqttopMILLISECONDS_PER_TICK;

    /* Reduce ulGlobalEntryTimeMs from obtained time so as to always return the
     * elapsed time in the application. */
    ulTimeMs = ( uint32_t ) ( ulTimeMs - ulGlobalEntryTimeMs );

    return ulTimeMs;
}

/*-----------------------------------------------------------*/
