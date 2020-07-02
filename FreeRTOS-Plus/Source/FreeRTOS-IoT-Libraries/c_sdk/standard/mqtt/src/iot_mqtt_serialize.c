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
 * @file iot_mqtt_serialize.c
 * @brief Implements functions that generate and decode MQTT network packets.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <string.h>
#include <limits.h>

/* MQTT internal includes. */
#include "private/iot_mqtt_internal.h"
#include "private/iot_mqtt_helper.h"

/* Platform layer includes. */
#include "platform/iot_threads.h"

/* Atomic operations. */
#include "iot_atomic.h"

/*-----------------------------------------------------------*/

/**
 * @brief Decode the status bytes of a SUBACK packet.
 *
 * @param[in] statusCount Number of status bytes in the SUBACK.
 * @param[in] pStatusStart The first status byte in the SUBACK.
 * @param[in] pSuback The SUBACK packet received from the network.
 *
 * @return #IOT_MQTT_SUCCESS, #IOT_MQTT_SERVER_REFUSED, or #IOT_MQTT_BAD_RESPONSE.
 */
static IotMqttError_t _decodeSubackStatus( size_t statusCount,
                                           const uint8_t * pStatusStart,
                                           const _mqttPacket_t * pSuback );

/**
 * @brief Check the remaining length against some value for QoS 0 or QoS 1/2.
 *
 * The remaining length for a QoS 1/2 will always be two greater than for a QoS 0.
 *
 * @param[in] pPublish Pointer to an MQTT packet struct representing a PUBLISH.
 * @param[in] qos The QoS of the PUBLISH.
 * @param[in] qos0Minimum Minimum possible remaining length for a QoS 0 PUBLISH.
 *
 * @return #IOT_MQTT_SUCCESS or #IOT_MQTT_BAD_RESPONSE.
 */
static IotMqttError_t _checkRemainingLength( const _mqttPacket_t * pPublish,
                                             IotMqttQos_t qos,
                                             size_t qos0Minimum );

/*-----------------------------------------------------------*/

#if LIBRARY_LOG_LEVEL > IOT_LOG_NONE

/**
 * @brief If logging is enabled, define a log configuration that only prints the log
 * string. This is used when printing out details of deserialized MQTT packets.
 */
    static const IotLogConfig_t _logHideAll =
    {
        .hideLibraryName = ( bool ) ( true ),
        .hideLogLevel    = ( bool ) ( true ),
        .hideTimestring  = ( bool ) ( true )
    };
#endif


/*-----------------------------------------------------------*/

static IotMqttError_t _decodeSubackStatus( size_t statusCount,
                                           const uint8_t * pStatusStart,
                                           const _mqttPacket_t * pSuback )
{
    IotMqttError_t status             = IOT_MQTT_SUCCESS;
    uint8_t        subscriptionStatus = 0;
    size_t         i                  = 0;

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

                /* In some implementations IotLog() maps to C standard printing API
                 * that need specific primitive types for format specifiers. Also
                 * inttypes.h may not be available on some C99 compilers, despite
                 * stdint.h being available. */
                /* coverity[misra_c_2012_directive_4_6_violation] */
                IotLog( IOT_LOG_DEBUG,
                        &_logHideAll,
                        "Topic filter %lu accepted, max QoS %hhu.",
                        ( unsigned long ) i, subscriptionStatus );
                break;

            case 0x80:

                /* In some implementations IotLog() maps to C standard printing API
                 * that need specific primitive types for format specifiers. Also
                 * inttypes.h may not be available on some C99 compilers, despite
                 * stdint.h being available. */
                /* coverity[misra_c_2012_directive_4_6_violation] */
                IotLog( IOT_LOG_DEBUG,
                        &_logHideAll,
                        "Topic filter %lu refused.", ( unsigned long ) i );

                /* Remove a rejected subscription from the subscription manager. */
                _IotMqtt_RemoveSubscriptionByPacket( pSuback->u.pMqttConnection,
                                                     pSuback->packetIdentifier,
                                                     ( int32_t ) i );

                status = IOT_MQTT_SERVER_REFUSED;

                break;

            default:
                IotLog( IOT_LOG_DEBUG,
                        &_logHideAll,
                        "Bad SUBSCRIBE status %hhu.", subscriptionStatus );

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

static IotMqttError_t _checkRemainingLength( const _mqttPacket_t * pPublish,
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
            IotLog( IOT_LOG_DEBUG,
                    &_logHideAll,
                    "QoS 0 PUBLISH cannot have a remaining length less than %lu.",
                    qos0Minimum );

            status = IOT_MQTT_BAD_RESPONSE;
        }
    }
    else
    {
        /* Check that the "Remaining length" is greater than the minimum. For
         * QoS 1 or 2, this will be two bytes greater than for QoS due to the
         * packet identifier. */
        if( pPublish->remainingLength < ( qos0Minimum + 2U ) )
        {
            IotLog( IOT_LOG_DEBUG,
                    &_logHideAll,
                    "QoS 1 or 2 PUBLISH cannot have a remaining length less than %lu.",
                    qos0Minimum + 2U );

            status = IOT_MQTT_BAD_RESPONSE;
        }
    }

    return status;
}


/*-----------------------------------------------------------*/

uint8_t _IotMqtt_GetPacketType( IotNetworkConnection_t pNetworkConnection,
                                const IotNetworkInterface_t * pNetworkInterface )
{
    uint8_t packetType = 0xff;

    /* The MQTT packet type is in the first byte of the packet. */
    ( void ) _IotMqtt_GetNextByte( pNetworkConnection,
                                   pNetworkInterface,
                                   &packetType );

    return packetType;
}

/*-----------------------------------------------------------*/

size_t _IotMqtt_GetRemainingLength( IotNetworkConnection_t pNetworkConnection,
                                    const IotNetworkInterface_t * pNetworkInterface )
{
    uint8_t encodedByte = 0;
    size_t  remainingLength = 0, multiplier = 1, bytesDecoded = 0, expectedSize = 0;

    /* This algorithm is copied from the MQTT v3.1.1 spec. */
    do
    {
        if( multiplier > 2097152U ) /* 128 ^ 3 */
        {
            remainingLength = MQTT_REMAINING_LENGTH_INVALID;
        }
        else
        {
            if( _IotMqtt_GetNextByte( pNetworkConnection,
                                      pNetworkInterface,
                                      &encodedByte ) == true )
            {
                remainingLength += ( ( size_t ) encodedByte & 0x7FU ) * multiplier;
                multiplier      *= 128U;
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

IotMqttError_t _IotMqtt_SerializeConnect( const IotMqttConnectInfo_t * pConnectInfo,
                                          uint8_t ** pConnectPacket,
                                          size_t * pPacketSize )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;
    size_t         remainingLength = 0, connectPacketSize = 0;
    uint8_t *      pBuffer = NULL;

    /* Calculate the "Remaining length" field and total packet size. If it exceeds
     * what is allowed in the MQTT standard, return an error. */
    if( _IotMqtt_ConnectPacketSize( pConnectInfo, &remainingLength, &connectPacketSize ) == false )
    {
        IotLogError( "Connect packet length exceeds %lu, which is the maximum"
                     " size allowed by MQTT 3.1.1.",
                     MQTT_PACKET_CONNECT_MAX_SIZE );

        status = IOT_MQTT_BAD_PARAMETER;
    }

    if( status == IOT_MQTT_SUCCESS )
    {
        /* Total size of the connect packet should be larger than the "Remaining length"
         * field. */
        IotMqtt_Assert( connectPacketSize > remainingLength );

        /* Allocate memory to hold the CONNECT packet. */
        pBuffer = IotMqtt_MallocMessage( connectPacketSize );

        /* Check that sufficient memory was allocated. */
        if( pBuffer == NULL )
        {
            IotLogError( "Failed to allocate memory for CONNECT packet." );

            status = IOT_MQTT_NO_MEMORY;
        }
        else
        {
            /* Set the output parameters. The remainder of this function always succeeds. */
            *pConnectPacket = pBuffer;
            *pPacketSize    = connectPacketSize;

            _IotMqtt_SerializeConnectCommon( pConnectInfo, remainingLength, pBuffer, connectPacketSize );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

IotMqttError_t _IotMqtt_DeserializeConnack( _mqttPacket_t * pConnack )
{
    IotMqttError_t  status                               = IOT_MQTT_SUCCESS;
    const uint8_t * pRemainingData                       = pConnack->pRemainingData;

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

    /* Check that the control packet type is 0x20. */
    if( pConnack->type != MQTT_PACKET_TYPE_CONNACK )
    {
        IotLog( IOT_LOG_ERROR,
                &_logHideAll,
                "Bad control packet type 0x%02x.",
                pConnack->type );

        status = IOT_MQTT_BAD_RESPONSE;
    }

    /* According to MQTT 3.1.1, the second byte of CONNACK must specify a
     * "Remaining length" of 2. */
    else if( pConnack->remainingLength != MQTT_PACKET_CONNACK_REMAINING_LENGTH )
    {
        IotLog( IOT_LOG_ERROR,
                &_logHideAll,
                "CONNACK does not have remaining length of %d.",
                MQTT_PACKET_CONNACK_REMAINING_LENGTH );

        status = IOT_MQTT_BAD_RESPONSE;
    }

    /* Check the reserved bits in CONNACK. The high 7 bits of the second byte
     * in CONNACK must be 0. */
    else if( ( pRemainingData[ 0 ] | 0x01U ) != 0x01U )
    {
        IotLog( IOT_LOG_ERROR,
                &_logHideAll,
                "Reserved bits in CONNACK incorrect." );

        status = IOT_MQTT_BAD_RESPONSE;
    }
    else
    {
        /* Determine if the "Session Present" bit is set. This is the lowest bit of
         * the second byte in CONNACK. */
        if( ( pRemainingData[ 0 ] & MQTT_PACKET_CONNACK_SESSION_PRESENT_MASK )
            == MQTT_PACKET_CONNACK_SESSION_PRESENT_MASK )
        {
            IotLog( IOT_LOG_DEBUG,
                    &_logHideAll,
                    "CONNACK session present bit set." );

            /* MQTT 3.1.1 specifies that the fourth byte in CONNACK must be 0 if the
             * "Session Present" bit is set. */
            if( pRemainingData[ 1 ] != 0U )
            {
                status = IOT_MQTT_BAD_RESPONSE;
            }
        }
        else
        {
            IotLog( IOT_LOG_DEBUG,
                    &_logHideAll,
                    "CONNACK session present bit not set." );
        }
    }

    if( status == IOT_MQTT_SUCCESS )
    {
        /* In MQTT 3.1.1, only values 0 through 5 are valid CONNACK response codes. */
        if( pRemainingData[ 1 ] > 5U )
        {
            IotLog( IOT_LOG_DEBUG,
                    &_logHideAll,
                    "CONNACK response %hhu is not valid.",
                    pRemainingData[ 1 ] );

            status = IOT_MQTT_BAD_RESPONSE;
        }
        else
        {
            /* Print the appropriate message for the CONNACK response code if logs are
             * enabled. */
            #if LIBRARY_LOG_LEVEL > IOT_LOG_NONE
                IotLog( IOT_LOG_DEBUG,
                        &_logHideAll,
                        "%s",
                        pConnackResponses[ pRemainingData[ 1 ] ] );
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

IotMqttError_t _IotMqtt_SerializePublish( const IotMqttPublishInfo_t * pPublishInfo,
                                          uint8_t ** pPublishPacket,
                                          size_t * pPacketSize,
                                          uint16_t * pPacketIdentifier,
                                          uint8_t ** pPacketIdentifierHigh )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;
    size_t         remainingLength = 0, publishPacketSize = 0;
    uint8_t *      pBuffer = NULL;

    /* Calculate the "Remaining length" field and total packet size. If it exceeds
     * what is allowed in the MQTT standard, return an error. */
    if( _IotMqtt_PublishPacketSize( pPublishInfo, &remainingLength, &publishPacketSize ) == false )
    {
        IotLogError( "Publish packet remaining length exceeds %lu, which is the "
                     "maximum size allowed by MQTT 3.1.1.",
                     MQTT_MAX_REMAINING_LENGTH );

        status = IOT_MQTT_BAD_PARAMETER;
    }

    if( status == IOT_MQTT_SUCCESS )
    {
        /* Total size of the publish packet should be larger than the "Remaining length"
         * field. */
        IotMqtt_Assert( publishPacketSize > remainingLength );

        /* Allocate memory to hold the PUBLISH packet. */
        pBuffer = IotMqtt_MallocMessage( publishPacketSize );

        /* Check that sufficient memory was allocated. */
        if( pBuffer == NULL )
        {
            IotLogError( "Failed to allocate memory for PUBLISH packet." );

            status = IOT_MQTT_NO_MEMORY;
        }
        else
        {
            /* Set the output parameters. The remainder of this function always succeeds. */
            *pPublishPacket = pBuffer;
            *pPacketSize    = publishPacketSize;

            /* Serialize publish into buffer pointed to by pBuffer */
            _IotMqtt_SerializePublishCommon( pPublishInfo,
                                             remainingLength,
                                             pPacketIdentifier,
                                             pPacketIdentifierHigh,
                                             pBuffer,
                                             publishPacketSize );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

void _IotMqtt_PublishSetDup( uint8_t * pPublishPacket,
                             uint8_t * pPacketIdentifierHigh,
                             uint16_t * pNewPacketIdentifier )
{
    uint16_t newPacketIdentifier = 0;

    /* For an AWS IoT MQTT server, change the packet identifier. */
    if( pPacketIdentifierHigh != NULL )
    {
        /* Output parameter for new packet identifier must be provided. */
        IotMqtt_Assert( pNewPacketIdentifier != NULL );

        /* Generate a new packet identifier. */
        newPacketIdentifier            = _IotMqtt_NextPacketIdentifier();

        IotLogDebug( "Changing PUBLISH packet identifier %hu to %hu.",
                     UINT16_DECODE( pPacketIdentifierHigh ),
                     newPacketIdentifier );

        /* Replace the packet identifier. */
        *pPacketIdentifierHigh         = UINT16_HIGH_BYTE( newPacketIdentifier );
        *( pPacketIdentifierHigh + 1 ) = UINT16_LOW_BYTE( newPacketIdentifier );
        *pNewPacketIdentifier          = newPacketIdentifier;
    }
    else
    {
        /* For a compliant MQTT 3.1.1 server, set the DUP flag. */
        UINT8_SET_BIT( *pPublishPacket, MQTT_PUBLISH_FLAG_DUP );

        IotLogDebug( "PUBLISH DUP flag set." );
    }
}

/*-----------------------------------------------------------*/

IotMqttError_t _IotMqtt_DeserializePublish( _mqttPacket_t * pPublish )
{
    IotMqttError_t         status = IOT_MQTT_SUCCESS;
    IotMqttPublishInfo_t * pOutput = &( pPublish->u.pIncomingPublish->u.publish.publishInfo );
    uint8_t                publishFlags = 0;
    const uint8_t *        pVariableHeader = pPublish->pRemainingData, * pPacketIdentifierHigh = NULL;

    /* The flags are the lower 4 bits of the first byte in PUBLISH. */
    publishFlags = pPublish->type;

    status       = _IotMqtt_ProcessPublishFlags( publishFlags, pOutput );

    if( status == IOT_MQTT_SUCCESS )
    {
        /* Sanity checks for "Remaining length". A QoS 0 PUBLISH  must have a remaining
         * length of at least 3 to accommodate topic name length (2 bytes) and topic
         * name (at least 1 byte). A QoS 1 or 2 PUBLISH must have a remaining length of
         * at least 5 for the packet identifier in addition to the topic name length and
         * topic name. */
        status = _checkRemainingLength( pPublish, pOutput->qos, MQTT_MIN_PUBLISH_REMAINING_LENGTH_QOS0 );
    }

    if( status == IOT_MQTT_SUCCESS )
    {
        /* Extract the topic name starting from the first byte of the variable header.
         * The topic name string starts at byte 3 in the variable header. */
        pOutput->topicNameLength = UINT16_DECODE( pVariableHeader );

        /* Sanity checks for topic name length and "Remaining length". The remaining
         * length must be at least as large as the variable length header. */
        status                   = _checkRemainingLength( pPublish,
                                                          pOutput->qos,
                                                          pOutput->topicNameLength + sizeof( uint16_t ) );
    }

    if( status == IOT_MQTT_SUCCESS )
    {
        /* Parse the topic. */
        pOutput->pTopicName   = ( const char * ) ( pVariableHeader + sizeof( uint16_t ) );

        IotLog( IOT_LOG_DEBUG,
                &_logHideAll,
                "Topic name length %hu: %.*s",
                pOutput->topicNameLength,
                pOutput->topicNameLength,
                pOutput->pTopicName );

        /* Extract the packet identifier for QoS 1 or 2 PUBLISH packets. Packet
         * identifier starts immediately after the topic name. */
        pPacketIdentifierHigh = ( const uint8_t * ) ( pOutput->pTopicName + pOutput->topicNameLength );

        if( pOutput->qos > IOT_MQTT_QOS_0 )
        {
            pPublish->packetIdentifier = UINT16_DECODE( pPacketIdentifierHigh );

            IotLog( IOT_LOG_DEBUG,
                    &_logHideAll,
                    "Packet identifier %hu.", pPublish->packetIdentifier );

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
            pOutput->pPayload      = pPacketIdentifierHigh;
        }
        else
        {
            pOutput->payloadLength = ( pPublish->remainingLength - pOutput->topicNameLength - 2U * sizeof( uint16_t ) );
            pOutput->pPayload      = pPacketIdentifierHigh + sizeof( uint16_t );
        }

        IotLog( IOT_LOG_DEBUG,
                &_logHideAll,
                "Payload length %hu.", pOutput->payloadLength );
    }

    return status;
}

/*-----------------------------------------------------------*/

IotMqttError_t _IotMqtt_SerializePuback( uint16_t packetIdentifier,
                                         uint8_t ** pPubackPacket,
                                         size_t * pPacketSize )
{
    IotMqttError_t status  = IOT_MQTT_SUCCESS;

    /* Allocate memory for PUBACK. */
    uint8_t *      pBuffer = IotMqtt_MallocMessage( MQTT_PACKET_PUBACK_SIZE );

    if( pBuffer == NULL )
    {
        IotLogError( "Failed to allocate memory for PUBACK packet" );

        status = IOT_MQTT_NO_MEMORY;
    }
    else
    {
        /* Set the output parameters. The remainder of this function always succeeds. */
        *pPubackPacket = pBuffer;
        *pPacketSize   = MQTT_PACKET_PUBACK_SIZE;

        /* Set the 4 bytes in PUBACK. */
        pBuffer[ 0 ]   = MQTT_PACKET_TYPE_PUBACK;
        pBuffer[ 1 ]   = MQTT_PACKET_PUBACK_REMAINING_LENGTH;
        pBuffer[ 2 ]   = UINT16_HIGH_BYTE( packetIdentifier );
        pBuffer[ 3 ]   = UINT16_LOW_BYTE( packetIdentifier );

        /* Print out the serialized PUBACK packet for debugging purposes. */
        IotLog_PrintBuffer( "MQTT PUBACK packet:", *pPubackPacket, MQTT_PACKET_PUBACK_SIZE );
    }

    return status;
}

/*-----------------------------------------------------------*/

IotMqttError_t _IotMqtt_DeserializePuback( _mqttPacket_t * pPuback )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;

    /* Check the "Remaining length" of the received PUBACK. */
    if( pPuback->remainingLength != MQTT_PACKET_PUBACK_REMAINING_LENGTH )
    {
        IotLog( IOT_LOG_ERROR,
                &_logHideAll,
                "PUBACK does not have remaining length of %d.",
                MQTT_PACKET_PUBACK_REMAINING_LENGTH );

        status = IOT_MQTT_BAD_RESPONSE;
    }
    else
    {
        /* Extract the packet identifier (third and fourth bytes) from PUBACK. */
        pPuback->packetIdentifier = UINT16_DECODE( pPuback->pRemainingData );

        IotLog( IOT_LOG_DEBUG,
                &_logHideAll,
                "Packet identifier %hu.", pPuback->packetIdentifier );

        /* Packet identifier cannot be 0. */
        if( pPuback->packetIdentifier == 0U )
        {
            status = IOT_MQTT_BAD_RESPONSE;
        }
        else
        {
            /* Check that the control packet type is 0x40 (this must be done after the
             * packet identifier is parsed). */
            if( pPuback->type != MQTT_PACKET_TYPE_PUBACK )
            {
                IotLog( IOT_LOG_ERROR,
                        &_logHideAll,
                        "Bad control packet type 0x%02x.",
                        pPuback->type );

                status = IOT_MQTT_BAD_RESPONSE;
            }
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

IotMqttError_t _IotMqtt_SerializeSubscribe( const IotMqttSubscription_t * pSubscriptionList,
                                            size_t subscriptionCount,
                                            uint8_t ** pSubscribePacket,
                                            size_t * pPacketSize,
                                            uint16_t * pPacketIdentifier )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;
    size_t         subscribePacketSize = 0, remainingLength = 0;
    uint8_t *      pBuffer = NULL;

    /* Calculate the "Remaining length" field and total packet size. If it exceeds
     * what is allowed in the MQTT standard, return an error. */
    if( _IotMqtt_SubscriptionPacketSize( IOT_MQTT_SUBSCRIBE,
                                         pSubscriptionList,
                                         subscriptionCount,
                                         &remainingLength,
                                         &subscribePacketSize ) == false )
    {
        IotLogError( "Subscribe packet remaining length exceeds %lu, which is the "
                     "maximum size allowed by MQTT 3.1.1.",
                     MQTT_MAX_REMAINING_LENGTH );

        status = IOT_MQTT_BAD_PARAMETER;
    }
    else
    {
        /* Total size of the subscribe packet should be larger than the "Remaining length"
         * field. */
        IotMqtt_Assert( subscribePacketSize > remainingLength );

        /* Allocate memory to hold the SUBSCRIBE packet. */
        pBuffer = IotMqtt_MallocMessage( subscribePacketSize );

        /* Check that sufficient memory was allocated. */
        if( pBuffer == NULL )
        {
            IotLogError( "Failed to allocate memory for SUBSCRIBE packet." );

            status = IOT_MQTT_NO_MEMORY;
        }
        else
        {
            /* Set the output parameters. The remainder of this function always succeeds. */
            *pSubscribePacket = pBuffer;
            *pPacketSize      = subscribePacketSize;

            /* Serialize subscribe into buffer pointed to by pBuffer */
            _IotMqtt_SerializeSubscribeCommon( pSubscriptionList,
                                               subscriptionCount,
                                               remainingLength,
                                               pPacketIdentifier,
                                               pBuffer,
                                               subscribePacketSize );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

IotMqttError_t _IotMqtt_DeserializeSuback( _mqttPacket_t * pSuback )
{
    IotMqttError_t  status          = IOT_MQTT_SUCCESS;
    size_t          remainingLength = pSuback->remainingLength;
    const uint8_t * pVariableHeader = pSuback->pRemainingData;

    /* A SUBACK must have a remaining length of at least 3 to accommodate the
     * packet identifier and at least 1 return code. */
    if( remainingLength < 3U )
    {
        IotLog( IOT_LOG_DEBUG,
                &_logHideAll,
                "SUBACK cannot have a remaining length less than 3." );

        status = IOT_MQTT_BAD_RESPONSE;
    }
    else
    {
        /* Extract the packet identifier (first 2 bytes of variable header) from SUBACK. */
        pSuback->packetIdentifier = UINT16_DECODE( pVariableHeader );

        IotLog( IOT_LOG_DEBUG,
                &_logHideAll,
                "Packet identifier %hu.", pSuback->packetIdentifier );

        /* Check that the control packet type is 0x90 (this must be done after the
         * packet identifier is parsed). */
        if( pSuback->type != MQTT_PACKET_TYPE_SUBACK )
        {
            IotLog( IOT_LOG_ERROR,
                    &_logHideAll,
                    "Bad control packet type 0x%02x.",
                    pSuback->type );

            status = IOT_MQTT_BAD_RESPONSE;
        }
        else
        {
            status = _decodeSubackStatus( remainingLength - sizeof( uint16_t ),
                                          pVariableHeader + sizeof( uint16_t ),
                                          pSuback );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

IotMqttError_t _IotMqtt_SerializeUnsubscribe( const IotMqttSubscription_t * pSubscriptionList,
                                              size_t subscriptionCount,
                                              uint8_t ** pUnsubscribePacket,
                                              size_t * pPacketSize,
                                              uint16_t * pPacketIdentifier )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;
    size_t         unsubscribePacketSize = 0, remainingLength = 0;
    uint8_t *      pBuffer = NULL;

    /* Calculate the "Remaining length" field and total packet size. If it exceeds
     * what is allowed in the MQTT standard, return an error. */
    if( _IotMqtt_SubscriptionPacketSize( IOT_MQTT_UNSUBSCRIBE,
                                         pSubscriptionList,
                                         subscriptionCount,
                                         &remainingLength,
                                         &unsubscribePacketSize ) == false )
    {
        IotLogError( "Unsubscribe packet remaining length exceeds %lu, which is the "
                     "maximum size allowed by MQTT 3.1.1.",
                     MQTT_MAX_REMAINING_LENGTH );

        status = IOT_MQTT_BAD_PARAMETER;
    }
    else
    {
        /* Total size of the unsubscribe packet should be larger than the "Remaining length"
         * field. */
        IotMqtt_Assert( unsubscribePacketSize > remainingLength );

        /* Allocate memory to hold the UNSUBSCRIBE packet. */
        pBuffer = IotMqtt_MallocMessage( unsubscribePacketSize );

        /* Check that sufficient memory was allocated. */
        if( pBuffer == NULL )
        {
            IotLogError( "Failed to allocate memory for UNSUBSCRIBE packet." );

            status = IOT_MQTT_NO_MEMORY;
        }
        else
        {
            /* Set the output parameters. The remainder of this function always succeeds. */
            *pUnsubscribePacket = pBuffer;
            *pPacketSize        = unsubscribePacketSize;

            /* Serialize unsubscribe into buffer pointed to by pBuffer */
            _IotMqtt_SerializeUnsubscribeCommon( pSubscriptionList,
                                                 subscriptionCount,
                                                 remainingLength,
                                                 pPacketIdentifier,
                                                 pBuffer,
                                                 unsubscribePacketSize );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

IotMqttError_t _IotMqtt_DeserializeUnsuback( _mqttPacket_t * pUnsuback )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;

    /* Check the "Remaining length" (second byte) of the received UNSUBACK. */
    if( pUnsuback->remainingLength != MQTT_PACKET_UNSUBACK_REMAINING_LENGTH )
    {
        IotLog( IOT_LOG_ERROR,
                &_logHideAll,
                "UNSUBACK does not have remaining length of %d.",
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
        IotLog( IOT_LOG_DEBUG,
                &_logHideAll,
                "Packet identifier %hu.", pUnsuback->packetIdentifier );

        /* Check that the control packet type is 0xb0 (this must be done after the
         * packet identifier is parsed). */
        if( pUnsuback->type != MQTT_PACKET_TYPE_UNSUBACK )
        {
            IotLog( IOT_LOG_ERROR,
                    &_logHideAll,
                    "Bad control packet type 0x%02x.",
                    pUnsuback->type );

            status = IOT_MQTT_BAD_RESPONSE;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

IotMqttError_t _IotMqtt_SerializePingreq( uint8_t ** pPingreqPacket,
                                          size_t * pPacketSize )
{
    /* PINGREQ packets are always the same. */

    /* It is not necessary to make this array const. Since there are other
     * types of MQTT packets that are not constant, this array would be
     * cast to remove the const qualifier anyway. */
    /* coverity[misra_c_2012_rule_8_13_violation] */
    static uint8_t pPingreq[ MQTT_PACKET_PINGREQ_SIZE ] =
    {
        MQTT_PACKET_TYPE_PINGREQ,
        0x00
    };

    /* Set the output parameters. */
    *pPingreqPacket = ( uint8_t * ) pPingreq;
    *pPacketSize    = MQTT_PACKET_PINGREQ_SIZE;

    /* Print out the PINGREQ packet for debugging purposes. */
    IotLog_PrintBuffer( "MQTT PINGREQ packet:", pPingreq, MQTT_PACKET_PINGREQ_SIZE );

    return IOT_MQTT_SUCCESS;
}

/*-----------------------------------------------------------*/

IotMqttError_t _IotMqtt_DeserializePingresp( _mqttPacket_t * pPingresp )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;

    /* Check that the control packet type is 0xd0. */
    if( pPingresp->type != MQTT_PACKET_TYPE_PINGRESP )
    {
        IotLog( IOT_LOG_ERROR,
                &_logHideAll,
                "Bad control packet type 0x%02x.",
                pPingresp->type );

        status = IOT_MQTT_BAD_RESPONSE;
    }
    /* Check the "Remaining length" (second byte) of the received PINGRESP. */
    else if( pPingresp->remainingLength != MQTT_PACKET_PINGRESP_REMAINING_LENGTH )
    {
        IotLog( IOT_LOG_ERROR,
                &_logHideAll,
                "PINGRESP does not have remaining length of %d.",
                MQTT_PACKET_PINGRESP_REMAINING_LENGTH );

        status = IOT_MQTT_BAD_RESPONSE;
    }
    else
    {
        /* Empty else MISRA 15.7 */
    }

    return status;
}

/*-----------------------------------------------------------*/

IotMqttError_t _IotMqtt_SerializeDisconnect( uint8_t ** pDisconnectPacket,
                                             size_t * pPacketSize )
{
    /* DISCONNECT packets are always the same. */

    /* It is not necessary to make this array const. Since there are other
     * types of MQTT packets that are not constant, this array would be
     * cast to remove the const qualifier anyway. */
    /* coverity[misra_c_2012_rule_8_13_violation] */
    static uint8_t pDisconnect[ MQTT_PACKET_DISCONNECT_SIZE ] =
    {
        MQTT_PACKET_TYPE_DISCONNECT,
        0x00
    };

    /* Set the output parameters. */
    *pDisconnectPacket = ( uint8_t * ) pDisconnect;
    *pPacketSize       = MQTT_PACKET_DISCONNECT_SIZE;

    /* Print out the DISCONNECT packet for debugging purposes. */
    IotLog_PrintBuffer( "MQTT DISCONNECT packet:", pDisconnect, MQTT_PACKET_DISCONNECT_SIZE );

    return IOT_MQTT_SUCCESS;
}

/*-----------------------------------------------------------*/

void _IotMqtt_FreePacket( uint8_t * pPacket )
{
    uint8_t packetType = *pPacket;

    /* Don't call free on DISCONNECT and PINGREQ; those are allocated from static
     * memory. */
    if( packetType != MQTT_PACKET_TYPE_DISCONNECT )
    {
        if( packetType != MQTT_PACKET_TYPE_PINGREQ )
        {
            IotMqtt_FreeMessage( pPacket );
        }
    }
}

/*-----------------------------------------------------------*/

/* Public interface functions for serialization */

/*-----------------------------------------------------------*/
