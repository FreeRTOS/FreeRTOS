/*
 * IoT MQTT V2.1.1
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
 * @file iot_mqtt_lightweight_api.c
 * @brief Implements most user-facing functions of the MQTT library.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <string.h>
#include <limits.h>

/* MQTT include. */
/* MQTT types include. */
#include "types/iot_mqtt_types.h"
#include "private/iot_mqtt_helper.h"
#include "iot_mqtt_lightweight.h"

/*-----------------------------------------------------------*/

/* Configure logs for MQTT functions. */
#ifdef IOT_LOG_LEVEL_MQTT
    #define LIBRARY_LOG_LEVEL        IOT_LOG_LEVEL_MQTT
#else
    #ifdef IOT_LOG_LEVEL_GLOBAL
        #define LIBRARY_LOG_LEVEL    IOT_LOG_LEVEL_GLOBAL
    #else
        #define LIBRARY_LOG_LEVEL    IOT_LOG_NONE
    #endif
#endif

#define LIBRARY_LOG_NAME    ( "MQTT" )
#include "iot_logging_setup.h"


/*-----------------------------------------------------------*/

/**
 * @def IotMqtt_Assert( expression )
 * @brief Assertion macro for the MQTT library.
 *
 * Set @ref IOT_MQTT_ENABLE_ASSERTS to `1` to enable assertions in the MQTT
 * library.
 *
 * @param[in] expression Expression to be evaluated.
 */
#if IOT_MQTT_ENABLE_ASSERTS == 1
    #ifndef IotMqtt_Assert
        #ifdef Iot_DefaultAssert
            #define IotMqtt_Assert( expression )    Iot_DefaultAssert( expression )
        #else
            #error "Asserts are enabled for MQTT, but IotMqtt_Assert is not defined"
        #endif
    #endif
#else
    #define IotMqtt_Assert( expression )
#endif

/*-----------------------------------------------------------*/

/**
 * @brief Get the remaining length from a stream of bytes off the network.
 *
 * @param[in] pNetworkConnection Reference to the network connection.
 * @param[in] getNextByte Function pointer used to interact with the
 * network to get next byte.
 *
 * @return The remaining length; #MQTT_REMAINING_LENGTH_INVALID on error.
 *
 * @note This function is similar to _IotMqtt_GetRemainingLength() but it uses
 * user provided getNextByte function to parse the stream instead of using
 * _IotMqtt_GetNextByte(). pNetworkConnection is implementation dependent and
 * user provided function makes use of it.
 *
 */
static size_t _getRemainingLength( IotNetworkConnection_t pNetworkConnection,
                                   IotMqttGetNextByte_t getNextByte );

/**
 * @brief Deserialize a CONNACK packet.
 *
 * Converts the packet from a stream of bytes to an #IotMqttError_t. Also
 * prints out debug log messages about the packet.
 *
 * @param[in,out] pConnack Pointer to an MQTT packet struct representing a CONNACK.
 *
 * @return #IOT_MQTT_SUCCESS if CONNACK specifies that CONNECT was accepted;
 * #IOT_MQTT_SERVER_REFUSED if CONNACK specifies that CONNECT was rejected;
 * #IOT_MQTT_BAD_RESPONSE if the CONNACK packet doesn't follow MQTT spec.
 */
static IotMqttError_t _deserializeConnack( IotMqttPacketInfo_t * pConnack );

/**
 * @brief Deserialize a SUBACK packet.
 *
 * Converts the packet from a stream of bytes to an #IotMqttError_t and extracts
 * the packet identifier. Also prints out debug log messages about the packet.
 *
 * @param[in,out] pSuback Pointer to an MQTT packet struct representing a SUBACK.
 *
 * @return #IOT_MQTT_SUCCESS if SUBACK is valid; #IOT_MQTT_BAD_RESPONSE
 * if the SUBACK packet doesn't follow MQTT spec.
 */
static IotMqttError_t _deserializeSuback( IotMqttPacketInfo_t * pSuback );

/**
 * @brief Deserialize a PUBACK packet.
 *
 * Converts the packet from a stream of bytes to an #IotMqttError_t and extracts
 * the packet identifier. Also prints out debug log messages about the packet.
 *
 * @param[in,out] pPuback Pointer to an MQTT packet struct representing a PUBACK.
 *
 * @return #IOT_MQTT_SUCCESS if PUBACK is valid; #IOT_MQTT_BAD_RESPONSE
 * if the PUBACK packet doesn't follow MQTT spec.
 */
static IotMqttError_t _deserializePuback( IotMqttPacketInfo_t * pPuback );

/**
 * @brief Deserialize a PINGRESP packet.
 *
 * Converts the packet from a stream of bytes to an #IotMqttError_t. Also
 * prints out debug log messages about the packet.
 *
 * @param[in,out] pPingresp Pointer to an MQTT packet struct representing a PINGRESP.
 *
 * @return #IOT_MQTT_SUCCESS if PINGRESP is valid; #IOT_MQTT_BAD_RESPONSE
 * if the PINGRESP packet doesn't follow MQTT spec.
 */
static IotMqttError_t _deserializePingresp( IotMqttPacketInfo_t * pPingresp );

/**
 * @brief Deserialize a UNSUBACK packet.
 *
 * Converts the packet from a stream of bytes to an #IotMqttError_t and extracts
 * the packet identifier. Also prints out debug log messages about the packet.
 *
 * @param[in,out] pUnsuback Pointer to an MQTT packet struct representing an UNSUBACK.
 *
 * @return #IOT_MQTT_SUCCESS if UNSUBACK is valid; #IOT_MQTT_BAD_RESPONSE
 * if the UNSUBACK packet doesn't follow MQTT spec.
 */
static IotMqttError_t _deserializeUnsuback( IotMqttPacketInfo_t * pUnsuback );

/**
 * @brief Deserialize a PUBLISH packet received from the server.
 *
 * Converts the packet from a stream of bytes to an #IotMqttPublishInfo_t and
 * extracts the packet identifier. Also prints out debug log messages about the
 * packet.
 *
 * @param[in,out] pPublish Pointer to an MQTT packet struct representing a PUBLISH.
 *
 * @return #IOT_MQTT_SUCCESS if PUBLISH is valid; #IOT_MQTT_BAD_RESPONSE
 * if the PUBLISH packet doesn't follow MQTT spec.
 */
static IotMqttError_t _deserializePublish( IotMqttPacketInfo_t * pPublish );

/**
 * @brief Decode the status bytes of a SUBACK packet.
 *
 * @param[in] statusCount Number of status bytes in the SUBACK.
 * @param[in] pStatusStart The first status byte in the SUBACK.
 *
 * @return #IOT_MQTT_SUCCESS, #IOT_MQTT_SERVER_REFUSED, or #IOT_MQTT_BAD_RESPONSE.
 */
static IotMqttError_t _readSubackStatus( size_t statusCount,
                                         const uint8_t * pStatusStart );

/**
 * @brief Check the remaining length of incoming Publish against some value for
 * QoS 0 or QoS 1/2.
 *
 * The remaining length for a QoS 1/2 will always be two greater than for a QoS 0.
 *
 * @param[in] pPublish Pointer to an MQTT packet struct representing a PUBLISH.
 * @param[in] qos The QoS of the PUBLISH.
 * @param[in] qos0Minimum Minimum possible remaining length for a QoS 0 PUBLISH.
 *
 * @return #IOT_MQTT_SUCCESS or #IOT_MQTT_BAD_RESPONSE.
 */
static IotMqttError_t _checkPublishRemainingLength( const IotMqttPacketInfo_t * pPublish,
                                                    IotMqttQos_t qos,
                                                    size_t qos0Minimum );

/*-----------------------------------------------------------*/

static IotMqttError_t _readSubackStatus( size_t statusCount,
                                         const uint8_t * pStatusStart )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;
    uint8_t subscriptionStatus = 0;
    size_t i = 0;

    /* Iterate through each status byte in the SUBACK packet. */
    for( i = 0; i < statusCount; i++ )
    {
        /* Read a single status byte in SUBACK. */
        subscriptionStatus = *( pStatusStart + i );

        /* MQTT 3.1.1 defines the following values as status codes. */
        switch( subscriptionStatus )
        {
            case 0x00:
            case 0x01:
            case 0x02:

                /* In some implementations IotLogDebug() maps to C standard printing API
                 * that need specific primitive types for format specifiers. Also
                 * inttypes.h may not be available on some C99 compilers, despite
                 * stdint.h being available. */
                /* coverity[misra_c_2012_directive_4_6_violation] */
                IotLogDebug( "Topic filter %lu accepted, max QoS %hhu.",
                             ( unsigned long ) i, subscriptionStatus );
                break;

            case 0x80:

                /* In some implementations IotLogDebug() maps to C standard printing API
                 * that need specific primitive types for format specifiers. Also
                 * inttypes.h may not be available on some C99 compilers, despite
                 * stdint.h being available. */
                /* coverity[misra_c_2012_directive_4_6_violation] */
                IotLogDebug( "Topic filter %lu refused.", ( unsigned long ) i );

                /* Application should remove subscription from the list */
                status = IOT_MQTT_SERVER_REFUSED;

                break;

            default:
                IotLogDebug( "Bad SUBSCRIBE status %hhu.", subscriptionStatus );

                status = IOT_MQTT_BAD_RESPONSE;

                break;
        }

        /* Stop parsing the subscription statuses if a bad response was received. */
        if( status == IOT_MQTT_BAD_RESPONSE )
        {
            break;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static size_t _getRemainingLength( IotNetworkConnection_t pNetworkConnection,
                                   IotMqttGetNextByte_t getNextByte )
{
    uint8_t encodedByte = 0;
    size_t remainingLength = 0, multiplier = 1, bytesDecoded = 0, expectedSize = 0;

    /* This algorithm is copied from the MQTT v3.1.1 spec. */
    do
    {
        if( multiplier > 2097152U ) /* 128 ^ 3 */
        {
            remainingLength = MQTT_REMAINING_LENGTH_INVALID;
        }
        else
        {
            if( getNextByte( pNetworkConnection, &encodedByte ) == IOT_MQTT_SUCCESS )
            {
                remainingLength += ( ( size_t ) encodedByte & 0x7FU ) * multiplier;
                multiplier *= 128U;
                bytesDecoded++;
            }
            else
            {
                remainingLength = MQTT_REMAINING_LENGTH_INVALID;
            }
        }

        if( remainingLength == MQTT_REMAINING_LENGTH_INVALID )
        {
            break;
        }
    } while( ( encodedByte & 0x80U ) != 0U );

    /* Check that the decoded remaining length conforms to the MQTT specification. */
    if( remainingLength != MQTT_REMAINING_LENGTH_INVALID )
    {
        expectedSize = _IotMqtt_RemainingLengthEncodedSize( remainingLength );

        if( bytesDecoded != expectedSize )
        {
            remainingLength = MQTT_REMAINING_LENGTH_INVALID;
        }
        else
        {
            /* Valid remaining length should be at most 4 bytes. */
            IotMqtt_Assert( bytesDecoded <= 4U );
        }
    }

    return remainingLength;
}

/*-----------------------------------------------------------*/

static IotMqttError_t _deserializeConnack( IotMqttPacketInfo_t * pConnack )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;
    const uint8_t * pRemainingData = pConnack->pRemainingData;

    /* If logging is enabled, declare the CONNACK response code strings. The
     * fourth byte of CONNACK indexes into this array for the corresponding response. */
    #if LIBRARY_LOG_LEVEL > IOT_LOG_NONE
        static const char * const pConnackResponses[ 6 ] =
        {
            "Connection accepted.",                               /* 0 */
            "Connection refused: unacceptable protocol version.", /* 1 */
            "Connection refused: identifier rejected.",           /* 2 */
            "Connection refused: server unavailable",             /* 3 */
            "Connection refused: bad user name or password.",     /* 4 */
            "Connection refused: not authorized."                 /* 5 */
        };
    #endif

    /* According to MQTT 3.1.1, the second byte of CONNACK must specify a
     * "Remaining length" of 2. */
    if( pConnack->remainingLength != MQTT_PACKET_CONNACK_REMAINING_LENGTH )
    {
        IotLogError( "CONNACK does not have remaining length of %d.",
                     MQTT_PACKET_CONNACK_REMAINING_LENGTH );

        status = IOT_MQTT_BAD_RESPONSE;
    }

    /* Check the reserved bits in CONNACK. The high 7 bits of the second byte
     * in CONNACK must be 0. */
    else if( ( pRemainingData[ 0 ] | 0x01U ) != 0x01U )
    {
        IotLogError( "Reserved bits in CONNACK incorrect." );

        status = IOT_MQTT_BAD_RESPONSE;
    }
    else
    {
        /* Determine if the "Session Present" bit is set. This is the lowest bit of
         * the second byte in CONNACK. */
        if( ( pRemainingData[ 0 ] & MQTT_PACKET_CONNACK_SESSION_PRESENT_MASK )
            == MQTT_PACKET_CONNACK_SESSION_PRESENT_MASK )
        {
            IotLogDebug( "CONNACK session present bit set." );

            /* MQTT 3.1.1 specifies that the fourth byte in CONNACK must be 0 if the
             * "Session Present" bit is set. */
            if( pRemainingData[ 1 ] != 0U )
            {
                status = IOT_MQTT_BAD_RESPONSE;
            }
        }
        else
        {
            IotLogDebug( "CONNACK session present bit not set." );
        }
    }

    if( status == IOT_MQTT_SUCCESS )
    {
        /* In MQTT 3.1.1, only values 0 through 5 are valid CONNACK response codes. */
        if( pRemainingData[ 1 ] > 5U )
        {
            IotLogError( "CONNACK response %hhu is not valid.",
                         pRemainingData[ 1 ] );

            status = IOT_MQTT_BAD_RESPONSE;
        }
        else
        {
            /* Print the appropriate message for the CONNACK response code if logs are
             * enabled. */
            #if LIBRARY_LOG_LEVEL > IOT_LOG_NONE
                IotLogDebug( "%s", pConnackResponses[ pRemainingData[ 1 ] ] );
            #endif

            /* A nonzero CONNACK response code means the connection was refused. */
            if( pRemainingData[ 1 ] > 0U )
            {
                status = IOT_MQTT_SERVER_REFUSED;
            }
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static IotMqttError_t _deserializeSuback( IotMqttPacketInfo_t * pSuback )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;
    size_t remainingLength = pSuback->remainingLength;
    const uint8_t * pVariableHeader = pSuback->pRemainingData;

    /* A SUBACK must have a remaining length of at least 3 to accommodate the
     * packet identifier and at least 1 return code. */
    if( remainingLength < 3U )
    {
        IotLogDebug( "SUBACK cannot have a remaining length less than 3." );
        status = IOT_MQTT_BAD_RESPONSE;
    }
    else
    {
        /* Extract the packet identifier (first 2 bytes of variable header) from SUBACK. */
        pSuback->packetIdentifier = UINT16_DECODE( pVariableHeader );

        IotLogDebug( "Packet identifier %hu.", pSuback->packetIdentifier );

        status = _readSubackStatus( remainingLength - sizeof( uint16_t ),
                                    pVariableHeader + sizeof( uint16_t ) );
    }

    return status;
}

/*-----------------------------------------------------------*/

static IotMqttError_t _deserializeUnsuback( IotMqttPacketInfo_t * pUnsuback )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;

    /* Check the "Remaining length" (second byte) of the received UNSUBACK. */
    if( pUnsuback->remainingLength != MQTT_PACKET_UNSUBACK_REMAINING_LENGTH )
    {
        IotLogError( "UNSUBACK does not have remaining length of %d.",
                     MQTT_PACKET_UNSUBACK_REMAINING_LENGTH );

        status = IOT_MQTT_BAD_RESPONSE;
    }
    else
    {
        /* Extract the packet identifier (third and fourth bytes) from UNSUBACK. */
        pUnsuback->packetIdentifier = UINT16_DECODE( pUnsuback->pRemainingData );

        /* Packet identifier cannot be 0. */
        if( pUnsuback->packetIdentifier == 0U )
        {
            status = IOT_MQTT_BAD_RESPONSE;
        }
    }

    if( status == IOT_MQTT_SUCCESS )
    {
        IotLogDebug( "Packet identifier %hu.", pUnsuback->packetIdentifier );
    }

    return status;
}

/*-----------------------------------------------------------*/

static IotMqttError_t _deserializePingresp( IotMqttPacketInfo_t * pPingresp )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;

    /* Check the "Remaining length" (second byte) of the received PINGRESP. */
    if( pPingresp->remainingLength != MQTT_PACKET_PINGRESP_REMAINING_LENGTH )
    {
        IotLogError( "PINGRESP does not have remaining length of %d.",
                     MQTT_PACKET_PINGRESP_REMAINING_LENGTH );

        status = IOT_MQTT_BAD_RESPONSE;
    }

    return status;
}

/*-----------------------------------------------------------*/

static IotMqttError_t _deserializePuback( IotMqttPacketInfo_t * pPuback )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;

    /* Check the "Remaining length" of the received PUBACK. */
    if( pPuback->remainingLength != MQTT_PACKET_PUBACK_REMAINING_LENGTH )
    {
        IotLogError( "PUBACK does not have remaining length of %d.",
                     MQTT_PACKET_PUBACK_REMAINING_LENGTH );

        status = IOT_MQTT_BAD_RESPONSE;
    }
    else
    {
        /* Extract the packet identifier (third and fourth bytes) from PUBACK. */
        pPuback->packetIdentifier = UINT16_DECODE( pPuback->pRemainingData );

        IotLogDebug( "Packet identifier %hu.", pPuback->packetIdentifier );

        /* Packet identifier cannot be 0. */
        if( pPuback->packetIdentifier == 0U )
        {
            status = IOT_MQTT_BAD_RESPONSE;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static IotMqttError_t _deserializePublish( IotMqttPacketInfo_t * pPublish )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;
    IotMqttPublishInfo_t * pOutput = &( pPublish->pubInfo );
    uint8_t publishFlags = 0;
    const uint8_t * pVariableHeader = pPublish->pRemainingData, * pPacketIdentifierHigh = NULL;

    /* The flags are the lower 4 bits of the first byte in PUBLISH. */
    publishFlags = pPublish->type;

    status = _IotMqtt_ProcessPublishFlags( publishFlags, pOutput );

    if( status == IOT_MQTT_SUCCESS )
    {
        /* Sanity checks for "Remaining length". A QoS 0 PUBLISH  must have a remaining
         * length of at least 3 to accommodate topic name length (2 bytes) and topic
         * name (at least 1 byte). A QoS 1 or 2 PUBLISH must have a remaining length of
         * at least 5 for the packet identifier in addition to the topic name length and
         * topic name. */
        status = _checkPublishRemainingLength( pPublish, pOutput->qos, MQTT_MIN_PUBLISH_REMAINING_LENGTH_QOS0 );
    }

    if( status == IOT_MQTT_SUCCESS )
    {
        /* Extract the topic name starting from the first byte of the variable header.
         * The topic name string starts at byte 3 in the variable header. */
        pOutput->topicNameLength = UINT16_DECODE( pVariableHeader );

        /* Sanity checks for topic name length and "Remaining length". The remaining
         * length must be at least as large as the variable length header. */
        status = _checkPublishRemainingLength( pPublish,
                                               pOutput->qos,
                                               pOutput->topicNameLength + sizeof( uint16_t ) );
    }

    if( status == IOT_MQTT_SUCCESS )
    {
        /* Parse the topic. */
        pOutput->pTopicName = ( const char * ) ( pVariableHeader + sizeof( uint16_t ) );

        IotLogDebug( "Topic name length %hu: %.*s",
                     pOutput->topicNameLength,
                     pOutput->topicNameLength,
                     pOutput->pTopicName );

        /* Extract the packet identifier for QoS 1 or 2 PUBLISH packets. Packet
         * identifier starts immediately after the topic name. */
        pPacketIdentifierHigh = ( const uint8_t * ) ( pOutput->pTopicName + pOutput->topicNameLength );

        if( pOutput->qos > IOT_MQTT_QOS_0 )
        {
            pPublish->packetIdentifier = UINT16_DECODE( pPacketIdentifierHigh );

            IotLogDebug( "Packet identifier %hu.", pPublish->packetIdentifier );

            /* Packet identifier cannot be 0. */
            if( pPublish->packetIdentifier == 0U )
            {
                status = IOT_MQTT_BAD_RESPONSE;
            }
        }
    }

    if( status == IOT_MQTT_SUCCESS )
    {
        /* Calculate the length of the payload. QoS 1 or 2 PUBLISH packets contain
         * a packet identifier, but QoS 0 PUBLISH packets do not. */
        if( pOutput->qos == IOT_MQTT_QOS_0 )
        {
            pOutput->payloadLength = ( pPublish->remainingLength - pOutput->topicNameLength - sizeof( uint16_t ) );
            pOutput->pPayload = pPacketIdentifierHigh;
        }
        else
        {
            pOutput->payloadLength = ( pPublish->remainingLength - pOutput->topicNameLength - 2U * sizeof( uint16_t ) );
            pOutput->pPayload = pPacketIdentifierHigh + sizeof( uint16_t );
        }

        IotLogDebug( "Payload length %hu.", pOutput->payloadLength );
    }

    return status;
}

/*-----------------------------------------------------------*/

static IotMqttError_t _checkPublishRemainingLength( const IotMqttPacketInfo_t * pPublish,
                                                    IotMqttQos_t qos,
                                                    size_t qos0Minimum )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;

    /* Sanity checks for "Remaining length". */
    if( qos == IOT_MQTT_QOS_0 )
    {
        /* Check that the "Remaining length" is greater than the minimum. */
        if( pPublish->remainingLength < qos0Minimum )
        {
            IotLogDebug( "QoS 0 PUBLISH cannot have a remaining length less than %lu.",
                         qos0Minimum );

            status = IOT_MQTT_BAD_RESPONSE;
        }
    }
    else
    {
        /* Check that the "Remaining length" is greater than the minimum. For
         * QoS 1 or 2, this will be two bytes greater than for QoS 0 due to the
         * packet identifier. */
        if( pPublish->remainingLength < ( qos0Minimum + 2U ) )
        {
            IotLogDebug( "QoS 1 or 2 PUBLISH cannot have a remaining length less than %lu.",
                         qos0Minimum + 2U );

            status = IOT_MQTT_BAD_RESPONSE;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

/* Lightweight Public API Functions */

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_GetConnectPacketSize( const IotMqttConnectInfo_t * pConnectInfo,
                                             size_t * pRemainingLength,
                                             size_t * pPacketSize )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;

    if( ( pConnectInfo == NULL ) || ( pRemainingLength == NULL ) || ( pPacketSize == NULL ) )
    {
        IotLogError( "IotMqtt_GetConnectPacketSize() called with required parameter(s) set to NULL." );
        status = IOT_MQTT_BAD_PARAMETER;
    }
    else if( ( pConnectInfo->clientIdentifierLength == 0U ) || ( pConnectInfo->pClientIdentifier == NULL ) )
    {
        IotLogError( "IotMqtt_GetConnectPacketSize() client identifier must be set." );
        status = IOT_MQTT_BAD_PARAMETER;
    }
    else
    {
        /* Calculate the "Remaining length" field and total packet size. If it exceeds
         * what is allowed in the MQTT standard, return an error. */
        if( _IotMqtt_ConnectPacketSize( pConnectInfo, pRemainingLength, pPacketSize ) == false )
        {
            IotLogError( "Connect packet length exceeds %lu, which is the maximum"
                         " size allowed by MQTT 3.1.1.",
                         MQTT_PACKET_CONNECT_MAX_SIZE );

            status = IOT_MQTT_BAD_PARAMETER;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_SerializeConnect( const IotMqttConnectInfo_t * pConnectInfo,
                                         size_t remainingLength,
                                         uint8_t * pBuffer,
                                         size_t bufferSize )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;

    if( ( pBuffer == NULL ) || ( pConnectInfo == NULL ) )
    {
        IotLogError( "IotMqtt_SerializeConnect() called with required parameter(s) set to NULL." );
        status = IOT_MQTT_BAD_PARAMETER;
    }
    else if( pConnectInfo->pClientIdentifier == NULL )
    {
        IotLogError( "Client identifier must be set." );
        status = IOT_MQTT_BAD_PARAMETER;
    }
    else if( pConnectInfo->clientIdentifierLength == 0U )
    {
        IotLogError( "Client identifier length must be set." );
        status = IOT_MQTT_BAD_PARAMETER;
    }
    else if( remainingLength > bufferSize )
    {
        IotLogError( " Serialize Connect packet remaining length (%lu) exceeds buffer size (%lu)",
                     remainingLength, bufferSize );
        status = IOT_MQTT_BAD_PARAMETER;
    }
    else
    {
        _IotMqtt_SerializeConnectCommon( pConnectInfo,
                                         remainingLength,
                                         pBuffer,
                                         bufferSize );
    }

    return status;
}

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_GetSubscriptionPacketSize( IotMqttOperationType_t type,
                                                  const IotMqttSubscription_t * pSubscriptionList,
                                                  size_t subscriptionCount,
                                                  size_t * pRemainingLength,
                                                  size_t * pPacketSize )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;

    if( ( pSubscriptionList == NULL ) || ( pRemainingLength == NULL ) || ( pPacketSize == NULL ) )
    {
        IotLogError( "IotMqtt_GetSubscriptionPacketSize() called with required parameter(s) set to NULL." );
        status = IOT_MQTT_BAD_PARAMETER;
    }
    else if( ( type != IOT_MQTT_SUBSCRIBE ) && ( type != IOT_MQTT_UNSUBSCRIBE ) )
    {
        IotLogError( "IotMqtt_GetSubscriptionPacketSize() called with unknown type." );
        status = IOT_MQTT_BAD_PARAMETER;
    }
    else if( subscriptionCount == 0U )
    {
        IotLogError( "IotMqtt_GetSubscriptionPacketSize() called with zero subscription count." );
        status = IOT_MQTT_BAD_PARAMETER;
    }
    else
    {
        if( _IotMqtt_SubscriptionPacketSize( type,
                                             pSubscriptionList,
                                             subscriptionCount,
                                             pRemainingLength,
                                             pPacketSize ) == false )
        {
            IotLogError( "Subscription packet remaining length exceeds %lu, which is the "
                         "maximum size allowed by MQTT 3.1.1.",
                         MQTT_MAX_REMAINING_LENGTH );
            status = IOT_MQTT_BAD_PARAMETER;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_SerializeSubscribe( const IotMqttSubscription_t * pSubscriptionList,
                                           size_t subscriptionCount,
                                           size_t remainingLength,
                                           uint16_t * pPacketIdentifier,
                                           uint8_t * pBuffer,
                                           size_t bufferSize )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;

    if( ( pBuffer == NULL ) || ( pSubscriptionList == NULL ) || ( pPacketIdentifier == NULL ) )
    {
        IotLogError( "IotMqtt_SerializeSubscribe() called with required parameter(s) set to NULL." );
        status = IOT_MQTT_BAD_PARAMETER;
    }
    else if( subscriptionCount == 0U )
    {
        IotLogError( "IotMqtt_SerializeSubscribe() called with zero subscription count." );
        status = IOT_MQTT_BAD_PARAMETER;
    }
    else if( remainingLength > bufferSize )
    {
        IotLogError( " Subscribe packet remaining length (%lu) exceeds buffer size (%lu).",
                     remainingLength, bufferSize );
        status = IOT_MQTT_BAD_PARAMETER;
    }
    else
    {
        _IotMqtt_SerializeSubscribeCommon( pSubscriptionList,
                                           subscriptionCount,
                                           remainingLength,
                                           pPacketIdentifier,
                                           pBuffer,
                                           bufferSize );
    }

    return status;
}

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_GetIncomingMQTTPacketTypeAndLength( IotMqttPacketInfo_t * pIncomingPacket,
                                                           IotMqttGetNextByte_t getNextByte,
                                                           IotNetworkConnection_t pNetworkConnection )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;

    /* Read the packet type, which is the first byte available. */
    if( getNextByte( pNetworkConnection, &( pIncomingPacket->type ) ) == IOT_MQTT_SUCCESS )
    {
        /* Check that the incoming packet type is valid. */
        if( _IotMqtt_IncomingPacketValid( pIncomingPacket->type ) == false )
        {
            IotLogError( "(MQTT connection) Unknown packet type %02x received.",
                         pIncomingPacket->type );

            status = IOT_MQTT_BAD_RESPONSE;
        }
        else
        {
            /* Read the remaining length. */
            pIncomingPacket->remainingLength = _getRemainingLength( pNetworkConnection,
                                                                    getNextByte );

            if( pIncomingPacket->remainingLength == MQTT_REMAINING_LENGTH_INVALID )
            {
                status = IOT_MQTT_BAD_RESPONSE;
            }
        }
    }
    else
    {
        status = IOT_MQTT_NETWORK_ERROR;
    }

    return status;
}

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_GetPublishPacketSize( const IotMqttPublishInfo_t * pPublishInfo,
                                             size_t * pRemainingLength,
                                             size_t * pPacketSize )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;

    if( ( pPublishInfo == NULL ) || ( pRemainingLength == NULL ) || ( pPacketSize == NULL ) )
    {
        IotLogError( "IotMqtt_GetPublishPacketSize() called with required parameter(s) set to NULL." );
        status = IOT_MQTT_BAD_PARAMETER;
    }
    else if( ( pPublishInfo->pTopicName == NULL ) || ( pPublishInfo->topicNameLength == 0U ) )
    {
        IotLogError( "IotMqtt_GetPublishPacketSize() called with no topic." );
        status = IOT_MQTT_BAD_PARAMETER;
    }
    else
    {
        /* Calculate the "Remaining length" field and total packet size. If it exceeds
         * what is allowed in the MQTT standard, return an error. */
        if( _IotMqtt_PublishPacketSize( pPublishInfo, pRemainingLength, pPacketSize ) == false )
        {
            IotLogError( "Publish packet remaining length exceeds %lu, which is the "
                         "maximum size allowed by MQTT 3.1.1.",
                         MQTT_MAX_REMAINING_LENGTH );

            status = IOT_MQTT_BAD_PARAMETER;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_SerializePublish( const IotMqttPublishInfo_t * pPublishInfo,
                                         size_t remainingLength,
                                         uint16_t * pPacketIdentifier,
                                         uint8_t ** pPacketIdentifierHigh,
                                         uint8_t * pBuffer,
                                         size_t bufferSize )

{
    IotMqttError_t status = IOT_MQTT_SUCCESS;

    if( ( pBuffer == NULL ) || ( pPublishInfo == NULL ) || ( pPacketIdentifier == NULL ) )
    {
        IotLogError( "IotMqtt_SerializePublish() called with required parameter(s) set to NULL." );
        status = IOT_MQTT_BAD_PARAMETER;
    }
    else if( ( pPublishInfo->pTopicName == NULL ) || ( pPublishInfo->topicNameLength == 0U ) )
    {
        IotLogError( "IotMqtt_SerializePublish() called with no topic." );
        status = IOT_MQTT_BAD_PARAMETER;
    }
    else if( remainingLength > bufferSize )
    {
        IotLogError( "Publish packet remaining length (%lu) exceeds buffer size (%lu).",
                     remainingLength, bufferSize );
        status = IOT_MQTT_BAD_PARAMETER;
    }
    else
    {
        _IotMqtt_SerializePublishCommon( pPublishInfo,
                                         remainingLength,
                                         pPacketIdentifier,
                                         pPacketIdentifierHigh,
                                         pBuffer,
                                         bufferSize );
    }

    return status;
}

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_SerializeUnsubscribe( const IotMqttSubscription_t * pSubscriptionList,
                                             size_t subscriptionCount,
                                             size_t remainingLength,
                                             uint16_t * pPacketIdentifier,
                                             uint8_t * pBuffer,
                                             size_t bufferSize )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;

    if( ( pBuffer == NULL ) || ( pPacketIdentifier == NULL ) || ( pSubscriptionList == NULL ) )
    {
        IotLogError( "IotMqtt_SerializeUnsubscribe() called with required parameter(s) set to NULL." );
        status = IOT_MQTT_BAD_PARAMETER;
    }
    else if( subscriptionCount == 0U )
    {
        IotLogError( "IotMqtt_SerializeUnsubscribe() called with zero subscription count." );
        status = IOT_MQTT_BAD_PARAMETER;
    }
    else if( remainingLength > bufferSize )
    {
        IotLogError( "Unsubscribe packet remaining length (%lu) exceeds buffer size (%lu).",
                     remainingLength, bufferSize );
        status = IOT_MQTT_BAD_PARAMETER;
    }
    else
    {
        _IotMqtt_SerializeUnsubscribeCommon( pSubscriptionList,
                                             subscriptionCount,
                                             remainingLength,
                                             pPacketIdentifier,
                                             pBuffer,
                                             bufferSize );
    }

    return status;
}

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_SerializeDisconnect( uint8_t * pBuffer,
                                            size_t bufferSize )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;

    if( pBuffer == NULL )
    {
        IotLogError( "IotMqtt_SerializeDisconnect() called with NULL buffer pointer." );
        status = IOT_MQTT_BAD_PARAMETER;
    }

    else if( bufferSize < MQTT_PACKET_DISCONNECT_SIZE )
    {
        IotLogError( "Disconnect packet length (%lu) exceeds buffer size (%lu).",
                     MQTT_PACKET_DISCONNECT_SIZE, bufferSize );
        status = IOT_MQTT_BAD_PARAMETER;
    }
    else
    {
        /* Disconnect packets are always the same. */
        pBuffer[ 0 ] = MQTT_PACKET_TYPE_DISCONNECT;
        pBuffer[ 1 ] = 0x00;
    }

    return status;
}

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_SerializePingreq( uint8_t * pBuffer,
                                         size_t bufferSize )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;

    if( pBuffer == NULL )
    {
        IotLogError( "IotMqtt_SerializePingreq() called with NULL buffer pointer." );
        status = IOT_MQTT_BAD_PARAMETER;
    }
    else if( bufferSize < MQTT_PACKET_PINGREQ_SIZE )
    {
        IotLogError( "Pingreq length (%lu) exceeds buffer size (%lu).",
                     MQTT_PACKET_DISCONNECT_SIZE, bufferSize );
        status = IOT_MQTT_BAD_PARAMETER;
    }
    else
    {
        /* Ping request packets are always the same. */
        pBuffer[ 0 ] = MQTT_PACKET_TYPE_PINGREQ;
        pBuffer[ 1 ] = 0x00;
    }

    return status;
}

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_DeserializePublish( IotMqttPacketInfo_t * pMqttPacket )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;
    /* Internal MQTT packet structure */
    IotMqttPacketInfo_t mqttPacket = { 0 };

    if( pMqttPacket == NULL )
    {
        IotLogError( "IotMqtt_DeserializePublish()called with NULL pMqttPacket pointer." );
        status = IOT_MQTT_BAD_PARAMETER;
    }
    else if( ( pMqttPacket->type & 0xf0U ) != MQTT_PACKET_TYPE_PUBLISH )
    {
        IotLogError( "IotMqtt_DeserializePublish() called with incorrect packet type:(%lu).", pMqttPacket->type );
        status = IOT_MQTT_BAD_PARAMETER;
    }
    else
    {
        /* Set internal mqtt packet parameters. */
        mqttPacket.pRemainingData = pMqttPacket->pRemainingData;
        mqttPacket.remainingLength = pMqttPacket->remainingLength;
        mqttPacket.type = pMqttPacket->type;
        status = _deserializePublish( &mqttPacket );
    }

    if( status == IOT_MQTT_SUCCESS )
    {
        pMqttPacket->pubInfo = mqttPacket.pubInfo;
        pMqttPacket->packetIdentifier = mqttPacket.packetIdentifier;
    }

    return status;
}

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_DeserializeResponse( IotMqttPacketInfo_t * pMqttPacket )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;
    /* Internal MQTT packet structure */
    IotMqttPacketInfo_t mqttPacket = { 0 };

    if( pMqttPacket == NULL )
    {
        IotLogError( "IotMqtt_DeserializeResponse() called with NULL pMqttPacket pointer." );
        status = IOT_MQTT_BAD_PARAMETER;
    }
    else if( pMqttPacket->pRemainingData == NULL )
    {
        IotLogError( "IotMqtt_DeserializeResponse() called with NULL pRemainingLength." );
        status = IOT_MQTT_BAD_PARAMETER;
    }
    else
    {
        /* Set internal mqtt packet parameters. */
        mqttPacket.pRemainingData = pMqttPacket->pRemainingData;
        mqttPacket.remainingLength = pMqttPacket->remainingLength;
        mqttPacket.type = pMqttPacket->type;

        /* Make sure response packet is a valid packet */
        switch( pMqttPacket->type & 0xf0U )
        {
            case MQTT_PACKET_TYPE_CONNACK:
                status = _deserializeConnack( &mqttPacket );
                break;

            case MQTT_PACKET_TYPE_SUBACK:
                status = _deserializeSuback( &mqttPacket );
                break;

            case MQTT_PACKET_TYPE_UNSUBACK:
                status = _deserializeUnsuback( &mqttPacket );
                break;

            case MQTT_PACKET_TYPE_PINGRESP:
                status = _deserializePingresp( &mqttPacket );
                break;

            case MQTT_PACKET_TYPE_PUBACK:
                status = _deserializePuback( &mqttPacket );
                break;

            /* Any other packet type is invalid. */
            default:
                IotLogError( "IotMqtt_DeserializeResponse() called with unknown packet type:(%lu).", pMqttPacket->type );
                status = IOT_MQTT_BAD_RESPONSE;
                break;
        }
    }

    if( status == IOT_MQTT_SUCCESS )
    {
        /* Set packetIdentifier only if success is returned. */
        pMqttPacket->packetIdentifier = mqttPacket.packetIdentifier;
    }

    return status;
}

/*-----------------------------------------------------------*/
