/*
 * IoT MQTT V2.1.0
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/* Error handling include. */
#include "iot_error.h"

/* MQTT internal includes. */
#include "private/iot_mqtt_internal.h"

/* Platform layer includes. */
#include "platform/iot_threads.h"

/* Atomic operations. */
#include "iot_atomic.h"

/*-----------------------------------------------------------*/

/*
 * Macros for reading the high and low byte of a 2-byte unsigned int.
 */
#define UINT16_HIGH_BYTE( x )    ( ( uint8_t ) ( x >> 8 ) )            /**< @brief Get high byte. */
#define UINT16_LOW_BYTE( x )     ( ( uint8_t ) ( x & 0x00ff ) )        /**< @brief Get low byte. */

/**
 * @brief Macro for decoding a 2-byte unsigned int from a sequence of bytes.
 *
 * @param[in] ptr A uint8_t* that points to the high byte.
 */
#define UINT16_DECODE( ptr )                                \
    ( uint16_t ) ( ( ( ( uint16_t ) ( *( ptr ) ) ) << 8 ) | \
                   ( ( uint16_t ) ( *( ptr + 1 ) ) ) )

/**
 * @brief Macro for setting a bit in a 1-byte unsigned int.
 *
 * @param[in] x The unsigned int to set.
 * @param[in] position Which bit to set.
 */
#define UINT8_SET_BIT( x, position )      ( x = ( uint8_t ) ( x | ( 0x01 << position ) ) )

/**
 * @brief Macro for checking if a bit is set in a 1-byte unsigned int.
 *
 * @param[in] x The unsigned int to check.
 * @param[in] position Which bit to check.
 */
#define UINT8_CHECK_BIT( x, position )    ( ( x & ( 0x01 << position ) ) == ( 0x01 << position ) )

/*
 * Positions of each flag in the "Connect Flag" field of an MQTT CONNECT
 * packet.
 */
#define MQTT_CONNECT_FLAG_CLEAN                     ( 1 )  /**< @brief Clean session. */
#define MQTT_CONNECT_FLAG_WILL                      ( 2 )  /**< @brief Will present. */
#define MQTT_CONNECT_FLAG_WILL_QOS1                 ( 3 )  /**< @brief Will QoS1. */
#define MQTT_CONNECT_FLAG_WILL_QOS2                 ( 4 )  /**< @brief Will QoS2. */
#define MQTT_CONNECT_FLAG_WILL_RETAIN               ( 5 )  /**< @brief Will retain. */
#define MQTT_CONNECT_FLAG_PASSWORD                  ( 6 )  /**< @brief Password present. */
#define MQTT_CONNECT_FLAG_USERNAME                  ( 7 )  /**< @brief Username present. */

/*
 * Positions of each flag in the first byte of an MQTT PUBLISH packet's
 * fixed header.
 */
#define MQTT_PUBLISH_FLAG_RETAIN                    ( 0 )  /**< @brief Message retain flag. */
#define MQTT_PUBLISH_FLAG_QOS1                      ( 1 )  /**< @brief Publish QoS 1. */
#define MQTT_PUBLISH_FLAG_QOS2                      ( 2 )  /**< @brief Publish QoS 2. */
#define MQTT_PUBLISH_FLAG_DUP                       ( 3 )  /**< @brief Duplicate message. */

/**
 * @brief The constant specifying MQTT version 3.1.1. Placed in the CONNECT packet.
 */
#define MQTT_VERSION_3_1_1                          ( ( uint8_t ) 4U )

/**
 * @brief Per the MQTT 3.1.1 spec, the largest "Remaining Length" of an MQTT
 * packet is this value.
 */
#define MQTT_MAX_REMAINING_LENGTH                   ( 268435455UL )

/**
 * @brief The maximum possible size of a CONNECT packet.
 *
 * All strings in a CONNECT packet are constrained to 2-byte lengths, giving a
 * maximum length smaller than the max "Remaining Length" constant above.
 */
#define MQTT_PACKET_CONNECT_MAX_SIZE                ( 327700UL )

/*
 * Constants relating to CONNACK packets, defined by MQTT 3.1.1 spec.
 */
#define MQTT_PACKET_CONNACK_REMAINING_LENGTH        ( ( uint8_t ) 2 )    /**< @brief A CONNACK packet always has a "Remaining length" of 2. */
#define MQTT_PACKET_CONNACK_SESSION_PRESENT_MASK    ( ( uint8_t ) 0x01 ) /**< @brief The "Session Present" bit is always the lowest bit. */

/*
 * Constants relating to PUBLISH and PUBACK packets, defined by MQTT
 * 3.1.1 spec.
 */
#define MQTT_PACKET_PUBACK_SIZE                     ( 4 )               /**< @brief A PUBACK packet is always 4 bytes in size. */
#define MQTT_PACKET_PUBACK_REMAINING_LENGTH         ( ( uint8_t ) 2 )   /**< @brief A PUBACK packet always has a "Remaining length" of 2. */

/*
 * Constants relating to SUBACK and UNSUBACK packets, defined by MQTT
 * 3.1.1 spec.
 */
#define MQTT_PACKET_SUBACK_MINIMUM_SIZE             ( 5 )               /**< @brief The size of the smallest valid SUBACK packet. */
#define MQTT_PACKET_UNSUBACK_REMAINING_LENGTH       ( ( uint8_t ) 2 )   /**< @brief An UNSUBACK packet always has a "Remaining length" of 2. */

/*
 * Constants relating to PINGREQ and PINGRESP packets, defined by MQTT 3.1.1 spec.
 */
#define MQTT_PACKET_PINGREQ_SIZE                    ( 2 ) /**< @brief A PINGREQ packet is always 2 bytes in size. */
#define MQTT_PACKET_PINGRESP_REMAINING_LENGTH       ( 0 ) /**< @brief A PINGRESP packet always has a "Remaining length" of 0. */

/*
 * Constants relating to DISCONNECT packets, defined by MQTT 3.1.1 spec.
 */
#define MQTT_PACKET_DISCONNECT_SIZE                 ( 2 ) /**< @brief A DISCONNECT packet is always 2 bytes in size. */

/* Username for metrics with AWS IoT. */
#if AWS_IOT_MQTT_ENABLE_METRICS == 1 || DOXYGEN == 1
    #ifndef AWS_IOT_METRICS_USERNAME

/**
 * @brief Specify C SDK and version.
 */
        #define AWS_IOT_METRICS_USERNAME           "?SDK=C&Version=4.0.0"

/**
 * @brief The length of #AWS_IOT_METRICS_USERNAME.
 */
        #define AWS_IOT_METRICS_USERNAME_LENGTH    ( ( uint16_t ) sizeof( AWS_IOT_METRICS_USERNAME ) - 1 )
    #endif /* ifndef AWS_IOT_METRICS_USERNAME */
#endif /* if AWS_IOT_MQTT_ENABLE_METRICS == 1 || DOXYGEN == 1 */

/*-----------------------------------------------------------*/

/**
 * @brief Generate and return a 2-byte packet identifier.
 *
 * This packet identifier will be nonzero.
 *
 * @return The packet identifier.
 */
static uint16_t _nextPacketIdentifier( void );

/**
 * @brief Calculate the number of bytes required to encode an MQTT
 * "Remaining length" field.
 *
 * @param[in] length The value of the "Remaining length" to encode.
 *
 * @return The size of the encoding of length. This is always `1`, `2`, `3`, or `4`.
 */
static size_t _remainingLengthEncodedSize( size_t length );

/**
 * @brief Encode the "Remaining length" field per MQTT spec.
 *
 * @param[out] pDestination Where to write the encoded "Remaining length".
 * @param[in] length The "Remaining length" to encode.
 *
 * @return Pointer to the end of the encoded "Remaining length", which is 1-4
 * bytes greater than `pDestination`.
 *
 * @warning This function does not check the size of `pDestination`! Ensure that
 * `pDestination` is large enough to hold the encoded "Remaining length" using
 * the function #_remainingLengthEncodedSize to avoid buffer overflows.
 */
static uint8_t * _encodeRemainingLength( uint8_t * pDestination,
                                         size_t length );

/**
 * @brief Encode a C string as a UTF-8 string, per MQTT 3.1.1 spec.
 *
 * @param[out] pDestination Where to write the encoded string.
 * @param[in] source The string to encode.
 * @param[in] sourceLength The length of source.
 *
 * @return Pointer to the end of the encoded string, which is `sourceLength+2`
 * bytes greater than `pDestination`.
 *
 * @warning This function does not check the size of `pDestination`! Ensure that
 * `pDestination` is large enough to hold `sourceLength+2` bytes to avoid a buffer
 * overflow.
 */
static uint8_t * _encodeString( uint8_t * pDestination,
                                const char * source,
                                uint16_t sourceLength );

/**
 * @brief Calculate the size and "Remaining length" of a CONNECT packet generated
 * from the given parameters.
 *
 * @param[in] pConnectInfo User-provided CONNECT information struct.
 * @param[out] pRemainingLength Output for calculated "Remaining length" field.
 * @param[out] pPacketSize Output for calculated total packet size.
 *
 * @return `true` if the packet is within the length allowed by MQTT 3.1.1 spec; `false`
 * otherwise. If this function returns `false`, the output parameters should be ignored.
 */
static bool _connectPacketSize( const IotMqttConnectInfo_t * pConnectInfo,
                                size_t * pRemainingLength,
                                size_t * pPacketSize );

/**
 * @brief Calculate the size and "Remaining length" of a PUBLISH packet generated
 * from the given parameters.
 *
 * @param[in] pPublishInfo User-provided PUBLISH information struct.
 * @param[out] pRemainingLength Output for calculated "Remaining length" field.
 * @param[out] pPacketSize Output for calculated total packet size.
 *
 * @return `true` if the packet is within the length allowed by MQTT 3.1.1 spec; `false`
 * otherwise. If this function returns `false`, the output parameters should be ignored.
 */
static bool _publishPacketSize( const IotMqttPublishInfo_t * pPublishInfo,
                                size_t * pRemainingLength,
                                size_t * pPacketSize );

/**
 * @brief Calculate the size and "Remaining length" of a SUBSCRIBE or UNSUBSCRIBE
 * packet generated from the given parameters.
 *
 * @param[in] type Either IOT_MQTT_SUBSCRIBE or IOT_MQTT_UNSUBSCRIBE.
 * @param[in] pSubscriptionList User-provided array of subscriptions.
 * @param[in] subscriptionCount Size of `pSubscriptionList`.
 * @param[out] pRemainingLength Output for calculated "Remaining length" field.
 * @param[out] pPacketSize Output for calculated total packet size.
 *
 * @return `true` if the packet is within the length allowed by MQTT 3.1.1 spec; `false`
 * otherwise. If this function returns `false`, the output parameters should be ignored.
 */
static bool _subscriptionPacketSize( IotMqttOperationType_t type,
                                     const IotMqttSubscription_t * pSubscriptionList,
                                     size_t subscriptionCount,
                                     size_t * pRemainingLength,
                                     size_t * pPacketSize );

/**
 * @brief Generate a CONNECT packet from the given parameters.
 *
 * @param[in] pConnectInfo User-provided CONNECT information.
 * @param[in] remainingLength User provided remaining length.
 * @param[in, out] pBuffer User provided buffer where the CONNECT packet is written.
 * @param[in] connectPacketSize Size of the buffer pointed to by `pBuffer`.
 *
 */
void _serializeConnect( const IotMqttConnectInfo_t * pConnectInfo,
                        size_t remainingLength,
                        uint8_t * pBuffer,
                        size_t connectPacketSize );

/**
 * @brief Generate a PUBLISH packet from the given parameters.
 *
 * @param[in] pPublishInfo User-provided PUBLISH information.
 * @param[in] remainingLength User provided remaining length.
 * @param[out] pPacketIdentifier The packet identifier generated for this PUBLISH.
 * @param[out] pPacketIdentifierHigh Where the high byte of the packet identifier
 * is written.
 * @param[in, out] pBuffer User provided buffer where the PUBLISH packet is written.
 * @param[in] publishPacketSize Size of buffer pointed to by `pBuffer`.
 *
 */
void _serializePublish( const IotMqttPublishInfo_t * pPublishInfo,
                        size_t remainingLength,
                        uint16_t * pPacketIdentifier,
                        uint8_t ** pPacketIdentifierHigh,
                        uint8_t * pBuffer,
                        size_t publishPacketSize );

/**
 * @brief Generate a SUBSCRIBE packet from the given parameters.
 *
 * @param[in] pSubscriptionList User-provided array of subscriptions.
 * @param[in] subscriptionCount Size of `pSubscriptionList`.
 * @param[in] remainingLength User provided remaining length.
 * @param[out] pPacketIdentifier The packet identifier generated for this SUBSCRIBE.
 * @param[in, out] pBuffer User provided buffer where the SUBSCRIBE packet is written.
 * @param[in] subscribePacketSize Size of the buffer pointed to by  `pBuffer`.
 *
 */
void _serializeSubscribe( const IotMqttSubscription_t * pSubscriptionList,
                          size_t subscriptionCount,
                          size_t remainingLength,
                          uint16_t * pPacketIdentifier,
                          uint8_t * pBuffer,
                          size_t subscribePacketSize );

/**
 * @brief Generate an UNSUBSCRIBE packet from the given parameters.
 *
 * @param[in] pSubscriptionList User-provided array of subscriptions to remove.
 * @param[in] subscriptionCount Size of `pSubscriptionList`.
 * @param[in] remainingLength User provided remaining length.
 * @param[out] pPacketIdentifier The packet identifier generated for this UNSUBSCRIBE.
 * @param[in, out] pBuffer User provided buffer where the UNSUBSCRIBE packet is written.
 * @param[in] unsubscribePacketSize size of the buffer pointed to by  `pBuffer`.
 *
 */
void _serializeUnsubscribe( const IotMqttSubscription_t * pSubscriptionList,
                            size_t subscriptionCount,
                            size_t remainingLength,
                            uint16_t * pPacketIdentifier,
                            uint8_t * pBuffer,
                            size_t unsubscribePacketSize );

/*-----------------------------------------------------------*/

#if LIBRARY_LOG_LEVEL > IOT_LOG_NONE

/**
 * @brief If logging is enabled, define a log configuration that only prints the log
 * string. This is used when printing out details of deserialized MQTT packets.
 */
    static const IotLogConfig_t _logHideAll =
    {
        .hideLibraryName = true,
        .hideLogLevel    = true,
        .hideTimestring  = true
    };
#endif

/*-----------------------------------------------------------*/

static uint16_t _nextPacketIdentifier( void )
{
    /* MQTT specifies 2 bytes for the packet identifier; however, operating on
     * 32-bit integers is generally faster. */
    static uint32_t nextPacketIdentifier = 1;

    /* The next packet identifier will be greater by 2. This prevents packet
     * identifiers from ever being 0, which is not allowed by MQTT 3.1.1. Packet
     * identifiers will follow the sequence 1,3,5...65535,1,3,5... */
    return ( uint16_t ) Atomic_Add_u32( &nextPacketIdentifier, 2 );
}

/*-----------------------------------------------------------*/

static size_t _remainingLengthEncodedSize( size_t length )
{
    size_t encodedSize = 0;

    /* length should have already been checked before calling this function. */
    IotMqtt_Assert( length <= MQTT_MAX_REMAINING_LENGTH );

    /* Determine how many bytes are needed to encode length.
     * The values below are taken from the MQTT 3.1.1 spec. */

    /* 1 byte is needed to encode lengths between 0 and 127. */
    if( length < 128 )
    {
        encodedSize = 1;
    }
    /* 2 bytes are needed to encode lengths between 128 and 16,383. */
    else if( length < 16384 )
    {
        encodedSize = 2;
    }
    /* 3 bytes are needed to encode lengths between 16,384 and 2,097,151. */
    else if( length < 2097152 )
    {
        encodedSize = 3;
    }
    /* 4 bytes are needed to encode lengths between 2,097,152 and 268,435,455. */
    else
    {
        encodedSize = 4;
    }

    return encodedSize;
}

/*-----------------------------------------------------------*/

static uint8_t * _encodeRemainingLength( uint8_t * pDestination,
                                         size_t length )
{
    uint8_t lengthByte = 0, * pLengthEnd = pDestination;

    /* This algorithm is copied from the MQTT v3.1.1 spec. */
    do
    {
        lengthByte = length % 128;
        length = length / 128;

        /* Set the high bit of this byte, indicating that there's more data. */
        if( length > 0 )
        {
            UINT8_SET_BIT( lengthByte, 7 );
        }
        else
        {
            EMPTY_ELSE_MARKER;
        }

        /* Output a single encoded byte. */
        *pLengthEnd = lengthByte;
        pLengthEnd++;
    } while( length > 0 );

    return pLengthEnd;
}

/*-----------------------------------------------------------*/

static uint8_t * _encodeString( uint8_t * pDestination,
                                const char * source,
                                uint16_t sourceLength )
{
    /* The first byte of a UTF-8 string is the high byte of the string length. */
    *pDestination = UINT16_HIGH_BYTE( sourceLength );
    pDestination++;

    /* The second byte of a UTF-8 string is the low byte of the string length. */
    *pDestination = UINT16_LOW_BYTE( sourceLength );
    pDestination++;

    /* Copy the string into pDestination. */
    ( void ) memcpy( pDestination, source, sourceLength );

    /* Return the pointer to the end of the encoded string. */
    pDestination += sourceLength;

    return pDestination;
}

/*-----------------------------------------------------------*/

static bool _connectPacketSize( const IotMqttConnectInfo_t * pConnectInfo,
                                size_t * pRemainingLength,
                                size_t * pPacketSize )
{
    bool status = true;
    size_t connectPacketSize = 0, remainingLength = 0;

    /* The CONNECT packet will always include a 10-byte variable header. */
    connectPacketSize += 10U;

    /* Add the length of the client identifier if provided. */
    connectPacketSize += pConnectInfo->clientIdentifierLength + sizeof( uint16_t );

    /* Add the lengths of the will message and topic name if provided. */
    if( pConnectInfo->pWillInfo != NULL )
    {
        connectPacketSize += pConnectInfo->pWillInfo->topicNameLength + sizeof( uint16_t ) +
                             pConnectInfo->pWillInfo->payloadLength + sizeof( uint16_t );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    /* Depending on the status of metrics, add the length of the metrics username
     * or the user-provided username. */
    if( pConnectInfo->awsIotMqttMode == true )
    {
        #if AWS_IOT_MQTT_ENABLE_METRICS == 1
            connectPacketSize += AWS_IOT_METRICS_USERNAME_LENGTH + sizeof( uint16_t );
        #endif
    }
    else
    {
        /* Add the lengths of the username and password if provided and not
         * connecting to an AWS IoT MQTT server. */
        if( pConnectInfo->pUserName != NULL )
        {
            connectPacketSize += pConnectInfo->userNameLength + sizeof( uint16_t );
        }
        else
        {
            EMPTY_ELSE_MARKER;
        }

        if( pConnectInfo->pPassword != NULL )
        {
            connectPacketSize += pConnectInfo->passwordLength + sizeof( uint16_t );
        }
        else
        {
            EMPTY_ELSE_MARKER;
        }
    }

    /* At this point, the "Remaining Length" field of the MQTT CONNECT packet has
     * been calculated. */
    remainingLength = connectPacketSize;

    /* Calculate the full size of the MQTT CONNECT packet by adding the size of
     * the "Remaining Length" field plus 1 byte for the "Packet Type" field. */
    connectPacketSize += 1 + _remainingLengthEncodedSize( connectPacketSize );

    /* Check that the CONNECT packet is within the bounds of the MQTT spec. */
    if( connectPacketSize > MQTT_PACKET_CONNECT_MAX_SIZE )
    {
        status = false;
    }
    else
    {
        *pRemainingLength = remainingLength;
        *pPacketSize = connectPacketSize;
    }

    return status;
}

/*-----------------------------------------------------------*/

static bool _publishPacketSize( const IotMqttPublishInfo_t * pPublishInfo,
                                size_t * pRemainingLength,
                                size_t * pPacketSize )
{
    bool status = true;
    size_t publishPacketSize = 0, payloadLimit = 0;

    /* The variable header of a PUBLISH packet always contains the topic name. */
    publishPacketSize += pPublishInfo->topicNameLength + sizeof( uint16_t );

    /* The variable header of a QoS 1 or 2 PUBLISH packet contains a 2-byte
     * packet identifier. */
    if( pPublishInfo->qos > IOT_MQTT_QOS_0 )
    {
        publishPacketSize += sizeof( uint16_t );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    /* Calculate the maximum allowed size of the payload for the given parameters.
     * This calculation excludes the "Remaining length" encoding, whose size is not
     * yet known. */
    payloadLimit = MQTT_MAX_REMAINING_LENGTH - publishPacketSize - 1;

    /* Ensure that the given payload fits within the calculated limit. */
    if( pPublishInfo->payloadLength > payloadLimit )
    {
        status = false;
    }
    else
    {
        /* Add the length of the PUBLISH payload. At this point, the "Remaining length"
         * has been calculated. */
        publishPacketSize += pPublishInfo->payloadLength;

        /* Now that the "Remaining length" is known, recalculate the payload limit
         * based on the size of its encoding. */
        payloadLimit -= _remainingLengthEncodedSize( publishPacketSize );

        /* Check that the given payload fits within the size allowed by MQTT spec. */
        if( pPublishInfo->payloadLength > payloadLimit )
        {
            status = false;
        }
        else
        {
            /* Set the "Remaining length" output parameter and calculate the full
             * size of the PUBLISH packet. */
            *pRemainingLength = publishPacketSize;

            publishPacketSize += 1 + _remainingLengthEncodedSize( publishPacketSize );
            *pPacketSize = publishPacketSize;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static bool _subscriptionPacketSize( IotMqttOperationType_t type,
                                     const IotMqttSubscription_t * pSubscriptionList,
                                     size_t subscriptionCount,
                                     size_t * pRemainingLength,
                                     size_t * pPacketSize )
{
    bool status = true;
    size_t i = 0, subscriptionPacketSize = 0;

    /* Only SUBSCRIBE and UNSUBSCRIBE operations should call this function. */
    IotMqtt_Assert( ( type == IOT_MQTT_SUBSCRIBE ) || ( type == IOT_MQTT_UNSUBSCRIBE ) );

    /* The variable header of a subscription packet consists of a 2-byte packet
     * identifier. */
    subscriptionPacketSize += sizeof( uint16_t );

    /* Sum the lengths of all subscription topic filters; add 1 byte for each
     * subscription's QoS if type is IOT_MQTT_SUBSCRIBE. */
    for( i = 0; i < subscriptionCount; i++ )
    {
        /* Add the length of the topic filter. */
        subscriptionPacketSize += pSubscriptionList[ i ].topicFilterLength + sizeof( uint16_t );

        /* Only SUBSCRIBE packets include the QoS. */
        if( type == IOT_MQTT_SUBSCRIBE )
        {
            subscriptionPacketSize += 1;
        }
        else
        {
            EMPTY_ELSE_MARKER;
        }
    }

    /* At this point, the "Remaining length" has been calculated. Return error
     * if the "Remaining length" exceeds what is allowed by MQTT 3.1.1. Otherwise,
     * set the output parameter.*/
    if( subscriptionPacketSize > MQTT_MAX_REMAINING_LENGTH )
    {
        status = false;
    }
    else
    {
        *pRemainingLength = subscriptionPacketSize;

        /* Calculate the full size of the subscription packet by adding the size of the
         * "Remaining length" field plus 1 byte for the "Packet type" field. Set the
         * pPacketSize output parameter. */
        subscriptionPacketSize += 1 + _remainingLengthEncodedSize( subscriptionPacketSize );
        *pPacketSize = subscriptionPacketSize;
    }

    return status;
}

/*-----------------------------------------------------------*/

void _serializeConnect( const IotMqttConnectInfo_t * pConnectInfo,
                        size_t remainingLength,
                        uint8_t * pBuffer,
                        size_t connectPacketSize )
{
    uint8_t connectFlags = 0;
    uint8_t * pConnectPacket = pBuffer;

    /* The first byte in the CONNECT packet is the control packet type. */
    *pBuffer = MQTT_PACKET_TYPE_CONNECT;
    pBuffer++;

    /* The remaining length of the CONNECT packet is encoded starting from the
     * second byte. The remaining length does not include the length of the fixed
     * header or the encoding of the remaining length. */
    pBuffer = _encodeRemainingLength( pBuffer, remainingLength );

    /* The string "MQTT" is placed at the beginning of the CONNECT packet's variable
     * header. This string is 4 bytes long. */
    pBuffer = _encodeString( pBuffer, "MQTT", 4 );

    /* The MQTT protocol version is the second byte of the variable header. */
    *pBuffer = MQTT_VERSION_3_1_1;
    pBuffer++;

    /* Set the CONNECT flags based on the given parameters. */
    if( pConnectInfo->cleanSession == true )
    {
        UINT8_SET_BIT( connectFlags, MQTT_CONNECT_FLAG_CLEAN );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    /* Username and password depend on MQTT mode. */
    if( pConnectInfo->awsIotMqttMode == true )
    {
        /* Set the username flag for AWS IoT metrics. The AWS IoT MQTT server
         * never uses a password. */
        #if AWS_IOT_MQTT_ENABLE_METRICS == 1
            UINT8_SET_BIT( connectFlags, MQTT_CONNECT_FLAG_USERNAME );
        #endif
    }
    else
    {
        /* Set the flags for username and password if provided. */
        if( pConnectInfo->pUserName != NULL )
        {
            UINT8_SET_BIT( connectFlags, MQTT_CONNECT_FLAG_USERNAME );
        }
        else
        {
            EMPTY_ELSE_MARKER;
        }

        if( pConnectInfo->pPassword != NULL )
        {
            UINT8_SET_BIT( connectFlags, MQTT_CONNECT_FLAG_PASSWORD );
        }
        else
        {
            EMPTY_ELSE_MARKER;
        }
    }

    /* Set will flag if an LWT is provided. */
    if( pConnectInfo->pWillInfo != NULL )
    {
        UINT8_SET_BIT( connectFlags, MQTT_CONNECT_FLAG_WILL );

        /* Flags only need to be changed for will QoS 1 and 2. */
        switch( pConnectInfo->pWillInfo->qos )
        {
            case IOT_MQTT_QOS_1:
                UINT8_SET_BIT( connectFlags, MQTT_CONNECT_FLAG_WILL_QOS1 );
                break;

            case IOT_MQTT_QOS_2:
                UINT8_SET_BIT( connectFlags, MQTT_CONNECT_FLAG_WILL_QOS2 );
                break;

            default:
                break;
        }

        if( pConnectInfo->pWillInfo->retain == true )
        {
            UINT8_SET_BIT( connectFlags, MQTT_CONNECT_FLAG_WILL_RETAIN );
        }
        else
        {
            EMPTY_ELSE_MARKER;
        }
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    *pBuffer = connectFlags;
    pBuffer++;

    /* Write the 2 bytes of the keep alive interval into the CONNECT packet. */
    *pBuffer = UINT16_HIGH_BYTE( pConnectInfo->keepAliveSeconds );
    *( pBuffer + 1 ) = UINT16_LOW_BYTE( pConnectInfo->keepAliveSeconds );
    pBuffer += 2;

    /* Write the client identifier into the CONNECT packet. */
    pBuffer = _encodeString( pBuffer,
                             pConnectInfo->pClientIdentifier,
                             pConnectInfo->clientIdentifierLength );

    /* Write the will topic name and message into the CONNECT packet if provided. */
    if( pConnectInfo->pWillInfo != NULL )
    {
        pBuffer = _encodeString( pBuffer,
                                 pConnectInfo->pWillInfo->pTopicName,
                                 pConnectInfo->pWillInfo->topicNameLength );

        pBuffer = _encodeString( pBuffer,
                                 pConnectInfo->pWillInfo->pPayload,
                                 ( uint16_t ) pConnectInfo->pWillInfo->payloadLength );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    /* If metrics are enabled, write the metrics username into the CONNECT packet.
     * Otherwise, write the username and password only when not connecting to an
     * AWS IoT MQTT server. */
    if( pConnectInfo->awsIotMqttMode == true )
    {
        #if AWS_IOT_MQTT_ENABLE_METRICS == 1
            IotLogInfo( "Anonymous metrics (SDK language, SDK version) will be provided to AWS IoT. "
                        "Recompile with AWS_IOT_MQTT_ENABLE_METRICS set to 0 to disable." );

            pBuffer = _encodeString( pBuffer,
                                     AWS_IOT_METRICS_USERNAME,
                                     AWS_IOT_METRICS_USERNAME_LENGTH );
        #endif
    }
    else
    {
        if( pConnectInfo->pUserName != NULL )
        {
            pBuffer = _encodeString( pBuffer,
                                     pConnectInfo->pUserName,
                                     pConnectInfo->userNameLength );
        }
        else
        {
            EMPTY_ELSE_MARKER;
        }

        if( pConnectInfo->pPassword != NULL )
        {
            pBuffer = _encodeString( pBuffer,
                                     pConnectInfo->pPassword,
                                     pConnectInfo->passwordLength );
        }
        else
        {
            EMPTY_ELSE_MARKER;
        }
    }

    /* Ensure that the difference between the end and beginning of the buffer
     * is equal to connectPacketSize, i.e. pBuffer did not overflow. */
    IotMqtt_Assert( ( size_t ) ( pBuffer - pConnectPacket ) == connectPacketSize );

    /* Print out the serialized CONNECT packet for debugging purposes. */
    IotLog_PrintBuffer( "MQTT CONNECT packet:", pConnectPacket, connectPacketSize );
}

/*-----------------------------------------------------------*/

void _serializePublish( const IotMqttPublishInfo_t * pPublishInfo,
                        size_t remainingLength,
                        uint16_t * pPacketIdentifier,
                        uint8_t ** pPacketIdentifierHigh,
                        uint8_t * pBuffer,
                        size_t publishPacketSize )
{
    uint8_t publishFlags = 0;
    uint16_t packetIdentifier = 0;
    uint8_t * pPublishPacket = pBuffer;

    /* The first byte of a PUBLISH packet contains the packet type and flags. */
    publishFlags = MQTT_PACKET_TYPE_PUBLISH;

    if( pPublishInfo->qos == IOT_MQTT_QOS_1 )
    {
        UINT8_SET_BIT( publishFlags, MQTT_PUBLISH_FLAG_QOS1 );
    }
    else if( pPublishInfo->qos == IOT_MQTT_QOS_2 )
    {
        UINT8_SET_BIT( publishFlags, MQTT_PUBLISH_FLAG_QOS2 );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    if( pPublishInfo->retain == true )
    {
        UINT8_SET_BIT( publishFlags, MQTT_PUBLISH_FLAG_RETAIN );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    *pBuffer = publishFlags;
    pBuffer++;

    /* The "Remaining length" is encoded from the second byte. */
    pBuffer = _encodeRemainingLength( pBuffer, remainingLength );

    /* The topic name is placed after the "Remaining length". */
    pBuffer = _encodeString( pBuffer,
                             pPublishInfo->pTopicName,
                             pPublishInfo->topicNameLength );

    /* A packet identifier is required for QoS 1 and 2 messages. */
    if( pPublishInfo->qos > IOT_MQTT_QOS_0 )
    {
        /* Get the next packet identifier. It should always be nonzero. */
        packetIdentifier = _nextPacketIdentifier();
        IotMqtt_Assert( packetIdentifier != 0 );

        /* Set the packet identifier output parameters. */
        *pPacketIdentifier = packetIdentifier;

        if( pPacketIdentifierHigh != NULL )
        {
            *pPacketIdentifierHigh = pBuffer;
        }
        else
        {
            EMPTY_ELSE_MARKER;
        }

        /* Place the packet identifier into the PUBLISH packet. */
        *pBuffer = UINT16_HIGH_BYTE( packetIdentifier );
        *( pBuffer + 1 ) = UINT16_LOW_BYTE( packetIdentifier );
        pBuffer += 2;
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    /* The payload is placed after the packet identifier. */
    if( pPublishInfo->payloadLength > 0 )
    {
        ( void ) memcpy( pBuffer, pPublishInfo->pPayload, pPublishInfo->payloadLength );
        pBuffer += pPublishInfo->payloadLength;
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    /* Ensure that the difference between the end and beginning of the buffer
     * is equal to publishPacketSize, i.e. pBuffer did not overflow. */
    IotMqtt_Assert( ( size_t ) ( pBuffer - pPublishPacket ) == publishPacketSize );

    /* Print out the serialized PUBLISH packet for debugging purposes. */
    IotLog_PrintBuffer( "MQTT PUBLISH packet:", pPublishPacket, publishPacketSize );
}

/*-----------------------------------------------------------*/

void _serializeSubscribe( const IotMqttSubscription_t * pSubscriptionList,
                          size_t subscriptionCount,
                          size_t remainingLength,
                          uint16_t * pPacketIdentifier,
                          uint8_t * pBuffer,
                          size_t subscribePacketSize )
{
    uint16_t packetIdentifier = 0;
    size_t i = 0;
    uint8_t * pSubscribePacket = pBuffer;

    /* The first byte in SUBSCRIBE is the packet type. */
    *pBuffer = MQTT_PACKET_TYPE_SUBSCRIBE;
    pBuffer++;

    /* Encode the "Remaining length" starting from the second byte. */
    pBuffer = _encodeRemainingLength( pBuffer, remainingLength );

    /* Get the next packet identifier. It should always be nonzero. */
    packetIdentifier = _nextPacketIdentifier();
    *pPacketIdentifier = packetIdentifier;
    IotMqtt_Assert( packetIdentifier != 0 );

    /* Place the packet identifier into the SUBSCRIBE packet. */
    *pBuffer = UINT16_HIGH_BYTE( packetIdentifier );
    *( pBuffer + 1 ) = UINT16_LOW_BYTE( packetIdentifier );
    pBuffer += 2;

    /* Serialize each subscription topic filter and QoS. */
    for( i = 0; i < subscriptionCount; i++ )
    {
        pBuffer = _encodeString( pBuffer,
                                 pSubscriptionList[ i ].pTopicFilter,
                                 pSubscriptionList[ i ].topicFilterLength );

        /* Place the QoS in the SUBSCRIBE packet. */
        *pBuffer = ( uint8_t ) ( pSubscriptionList[ i ].qos );
        pBuffer++;
    }

    /* Ensure that the difference between the end and beginning of the buffer
     * is equal to subscribePacketSize, i.e. pBuffer did not overflow. */
    IotMqtt_Assert( ( size_t ) ( pBuffer - pSubscribePacket ) == subscribePacketSize );

    /* Print out the serialized SUBSCRIBE packet for debugging purposes. */
    IotLog_PrintBuffer( "MQTT SUBSCRIBE packet:", pSubscribePacket, subscribePacketSize );
}

/*-----------------------------------------------------------*/

void _serializeUnsubscribe( const IotMqttSubscription_t * pSubscriptionList,
                            size_t subscriptionCount,
                            size_t remainingLength,
                            uint16_t * pPacketIdentifier,
                            uint8_t * pBuffer,
                            size_t unsubscribePacketSize )
{
    uint16_t packetIdentifier = 0;
    size_t i = 0;
    uint8_t * pUnsubscribePacket = pBuffer;

    /* The first byte in UNSUBSCRIBE is the packet type. */
    *pBuffer = MQTT_PACKET_TYPE_UNSUBSCRIBE;
    pBuffer++;

    /* Encode the "Remaining length" starting from the second byte. */
    pBuffer = _encodeRemainingLength( pBuffer, remainingLength );

    /* Get the next packet identifier. It should always be nonzero. */
    packetIdentifier = _nextPacketIdentifier();
    *pPacketIdentifier = packetIdentifier;
    IotMqtt_Assert( packetIdentifier != 0 );

    /* Place the packet identifier into the UNSUBSCRIBE packet. */
    *pBuffer = UINT16_HIGH_BYTE( packetIdentifier );
    *( pBuffer + 1 ) = UINT16_LOW_BYTE( packetIdentifier );
    pBuffer += 2;

    /* Serialize each subscription topic filter. */
    for( i = 0; i < subscriptionCount; i++ )
    {
        pBuffer = _encodeString( pBuffer,
                                 pSubscriptionList[ i ].pTopicFilter,
                                 pSubscriptionList[ i ].topicFilterLength );
    }

    /* Ensure that the difference between the end and beginning of the buffer
     * is equal to unsubscribePacketSize, i.e. pBuffer did not overflow. */
    IotMqtt_Assert( ( size_t ) ( pBuffer - pUnsubscribePacket ) == unsubscribePacketSize );

    /* Print out the serialized UNSUBSCRIBE packet for debugging purposes. */
    IotLog_PrintBuffer( "MQTT UNSUBSCRIBE packet:", pUnsubscribePacket, unsubscribePacketSize );
}

/*-----------------------------------------------------------*/

uint8_t _IotMqtt_GetPacketType( void * pNetworkConnection,
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

size_t _IotMqtt_GetRemainingLength( void * pNetworkConnection,
                                    const IotNetworkInterface_t * pNetworkInterface )
{
    uint8_t encodedByte = 0;
    size_t remainingLength = 0, multiplier = 1, bytesDecoded = 0, expectedSize = 0;

    /* This algorithm is copied from the MQTT v3.1.1 spec. */
    do
    {
        if( multiplier > 2097152 ) /* 128 ^ 3 */
        {
            remainingLength = MQTT_REMAINING_LENGTH_INVALID;
            break;
        }
        else
        {
            if( _IotMqtt_GetNextByte( pNetworkConnection,
                                      pNetworkInterface,
                                      &encodedByte ) == true )
            {
                remainingLength += ( encodedByte & 0x7F ) * multiplier;
                multiplier *= 128;
                bytesDecoded++;
            }
            else
            {
                remainingLength = MQTT_REMAINING_LENGTH_INVALID;
                break;
            }
        }
    } while( ( encodedByte & 0x80 ) != 0 );

    /* Check that the decoded remaining length conforms to the MQTT specification. */
    if( remainingLength != MQTT_REMAINING_LENGTH_INVALID )
    {
        expectedSize = _remainingLengthEncodedSize( remainingLength );

        if( bytesDecoded != expectedSize )
        {
            remainingLength = MQTT_REMAINING_LENGTH_INVALID;
        }
        else
        {
            /* Valid remaining length should be at most 4 bytes. */
            IotMqtt_Assert( bytesDecoded <= 4 );
        }
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    return remainingLength;
}

/*-----------------------------------------------------------*/

size_t _IotMqtt_GetRemainingLength_Generic( void * pNetworkConnection,
                                            IotMqttGetNextByte_t getNextByte )
{
    uint8_t encodedByte = 0;
    size_t remainingLength = 0, multiplier = 1, bytesDecoded = 0, expectedSize = 0;

    /* This algorithm is copied from the MQTT v3.1.1 spec. */
    do
    {
        if( multiplier > 2097152 ) /* 128 ^ 3 */
        {
            remainingLength = MQTT_REMAINING_LENGTH_INVALID;
            break;
        }
        else
        {
            if( getNextByte( pNetworkConnection, &encodedByte ) == IOT_MQTT_SUCCESS )
            {
                remainingLength += ( encodedByte & 0x7F ) * multiplier;
                multiplier *= 128;
                bytesDecoded++;
            }
            else
            {
                remainingLength = MQTT_REMAINING_LENGTH_INVALID;
                break;
            }
        }
    } while( ( encodedByte & 0x80 ) != 0 );

    /* Check that the decoded remaining length conforms to the MQTT specification. */
    if( remainingLength != MQTT_REMAINING_LENGTH_INVALID )
    {
        expectedSize = _remainingLengthEncodedSize( remainingLength );

        if( bytesDecoded != expectedSize )
        {
            remainingLength = MQTT_REMAINING_LENGTH_INVALID;
        }
        else
        {
            /* Valid remaining length should be at most 4 bytes. */
            IotMqtt_Assert( bytesDecoded <= 4 );
        }
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    return remainingLength;
}

/*-----------------------------------------------------------*/

IotMqttError_t _IotMqtt_SerializeConnect( const IotMqttConnectInfo_t * pConnectInfo,
                                          uint8_t ** pConnectPacket,
                                          size_t * pPacketSize )
{
    IOT_FUNCTION_ENTRY( IotMqttError_t, IOT_MQTT_SUCCESS );
    size_t remainingLength = 0, connectPacketSize = 0;
    uint8_t * pBuffer = NULL;

    /* Calculate the "Remaining length" field and total packet size. If it exceeds
     * what is allowed in the MQTT standard, return an error. */
    if( _connectPacketSize( pConnectInfo, &remainingLength, &connectPacketSize ) == false )
    {
        IotLogError( "Connect packet length exceeds %lu, which is the maximum"
                     " size allowed by MQTT 3.1.1.",
                     MQTT_PACKET_CONNECT_MAX_SIZE );

        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_PARAMETER );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    /* Total size of the connect packet should be larger than the "Remaining length"
     * field. */
    IotMqtt_Assert( connectPacketSize > remainingLength );

    /* Allocate memory to hold the CONNECT packet. */
    pBuffer = IotMqtt_MallocMessage( connectPacketSize );

    /* Check that sufficient memory was allocated. */
    if( pBuffer == NULL )
    {
        IotLogError( "Failed to allocate memory for CONNECT packet." );

        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_NO_MEMORY );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    /* Set the output parameters. The remainder of this function always succeeds. */
    *pConnectPacket = pBuffer;
    *pPacketSize = connectPacketSize;

    _serializeConnect( pConnectInfo, remainingLength, pBuffer, connectPacketSize );

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

IotMqttError_t _IotMqtt_DeserializeConnack( _mqttPacket_t * pConnack )
{
    IOT_FUNCTION_ENTRY( IotMqttError_t, IOT_MQTT_SUCCESS );
    const uint8_t * pRemainingData = pConnack->pRemainingData;

    /* If logging is enabled, declare the CONNACK response code strings. The
     * fourth byte of CONNACK indexes into this array for the corresponding response. */
    #if LIBRARY_LOG_LEVEL > IOT_LOG_NONE
        static const char * pConnackResponses[ 6 ] =
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

        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_RESPONSE );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    /* According to MQTT 3.1.1, the second byte of CONNACK must specify a
     * "Remaining length" of 2. */
    if( pConnack->remainingLength != MQTT_PACKET_CONNACK_REMAINING_LENGTH )
    {
        IotLog( IOT_LOG_ERROR,
                &_logHideAll,
                "CONNACK does not have remaining length of %d.",
                MQTT_PACKET_CONNACK_REMAINING_LENGTH );

        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_RESPONSE );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    /* Check the reserved bits in CONNACK. The high 7 bits of the second byte
     * in CONNACK must be 0. */
    if( ( pRemainingData[ 0 ] | 0x01 ) != 0x01 )
    {
        IotLog( IOT_LOG_ERROR,
                &_logHideAll,
                "Reserved bits in CONNACK incorrect." );

        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_RESPONSE );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    /* Determine if the "Session Present" bit it set. This is the lowest bit of
     * the second byte in CONNACK. */
    if( ( pRemainingData[ 0 ] & MQTT_PACKET_CONNACK_SESSION_PRESENT_MASK )
        == MQTT_PACKET_CONNACK_SESSION_PRESENT_MASK )
    {
        IotLog( IOT_LOG_DEBUG,
                &_logHideAll,
                "CONNACK session present bit set." );

        /* MQTT 3.1.1 specifies that the fourth byte in CONNACK must be 0 if the
         * "Session Present" bit is set. */
        if( pRemainingData[ 1 ] != 0 )
        {
            IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_RESPONSE );
        }
        else
        {
            EMPTY_ELSE_MARKER;
        }
    }
    else
    {
        IotLog( IOT_LOG_DEBUG,
                &_logHideAll,
                "CONNACK session present bit not set." );
    }

    /* In MQTT 3.1.1, only values 0 through 5 are valid CONNACK response codes. */
    if( pRemainingData[ 1 ] > 5 )
    {
        IotLog( IOT_LOG_DEBUG,
                &_logHideAll,
                "CONNACK response %hhu is not valid.",
                pRemainingData[ 1 ] );

        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_RESPONSE );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    /* Print the appropriate message for the CONNACK response code if logs are
     * enabled. */
    #if LIBRARY_LOG_LEVEL > IOT_LOG_NONE
        IotLog( IOT_LOG_DEBUG,
                &_logHideAll,
                "%s",
                pConnackResponses[ pRemainingData[ 1 ] ] );
    #endif

    /* A nonzero CONNACK response code means the connection was refused. */
    if( pRemainingData[ 1 ] > 0 )
    {
        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_SERVER_REFUSED );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

IotMqttError_t _IotMqtt_SerializePublish( const IotMqttPublishInfo_t * pPublishInfo,
                                          uint8_t ** pPublishPacket,
                                          size_t * pPacketSize,
                                          uint16_t * pPacketIdentifier,
                                          uint8_t ** pPacketIdentifierHigh )
{
    IOT_FUNCTION_ENTRY( IotMqttError_t, IOT_MQTT_SUCCESS );
    size_t remainingLength = 0, publishPacketSize = 0;
    uint8_t * pBuffer = NULL;

    /* Calculate the "Remaining length" field and total packet size. If it exceeds
     * what is allowed in the MQTT standard, return an error. */
    if( _publishPacketSize( pPublishInfo, &remainingLength, &publishPacketSize ) == false )
    {
        IotLogError( "Publish packet remaining length exceeds %lu, which is the "
                     "maximum size allowed by MQTT 3.1.1.",
                     MQTT_MAX_REMAINING_LENGTH );

        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_PARAMETER );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    /* Total size of the publish packet should be larger than the "Remaining length"
     * field. */
    IotMqtt_Assert( publishPacketSize > remainingLength );

    /* Allocate memory to hold the PUBLISH packet. */
    pBuffer = IotMqtt_MallocMessage( publishPacketSize );

    /* Check that sufficient memory was allocated. */
    if( pBuffer == NULL )
    {
        IotLogError( "Failed to allocate memory for PUBLISH packet." );

        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_NO_MEMORY );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    /* Set the output parameters. The remainder of this function always succeeds. */
    *pPublishPacket = pBuffer;
    *pPacketSize = publishPacketSize;

    /* Serialize publish into buffer pointed to by pBuffer */
    _serializePublish( pPublishInfo,
                       remainingLength,
                       pPacketIdentifier,
                       pPacketIdentifierHigh,
                       pBuffer,
                       publishPacketSize );

    IOT_FUNCTION_EXIT_NO_CLEANUP();
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
        newPacketIdentifier = _nextPacketIdentifier();

        IotLogDebug( "Changing PUBLISH packet identifier %hu to %hu.",
                     UINT16_DECODE( pPacketIdentifierHigh ),
                     newPacketIdentifier );

        /* Replace the packet identifier. */
        *pPacketIdentifierHigh = UINT16_HIGH_BYTE( newPacketIdentifier );
        *( pPacketIdentifierHigh + 1 ) = UINT16_LOW_BYTE( newPacketIdentifier );
        *pNewPacketIdentifier = newPacketIdentifier;
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
    IOT_FUNCTION_ENTRY( IotMqttError_t, IOT_MQTT_SUCCESS );
    IotMqttPublishInfo_t * pOutput = &( pPublish->u.pIncomingPublish->u.publish.publishInfo );
    uint8_t publishFlags = 0;
    const uint8_t * pVariableHeader = pPublish->pRemainingData, * pPacketIdentifierHigh = NULL;

    /* The flags are the lower 4 bits of the first byte in PUBLISH. */
    publishFlags = pPublish->type;

    /* Parse the Retain bit. */
    pOutput->retain = UINT8_CHECK_BIT( publishFlags, MQTT_PUBLISH_FLAG_RETAIN );

    IotLog( IOT_LOG_DEBUG,
            &_logHideAll,
            "Retain bit is %d.", pOutput->retain );

    /* Check for QoS 2. */
    if( UINT8_CHECK_BIT( publishFlags, MQTT_PUBLISH_FLAG_QOS2 ) == true )
    {
        /* PUBLISH packet is invalid if both QoS 1 and QoS 2 bits are set. */
        if( UINT8_CHECK_BIT( publishFlags, MQTT_PUBLISH_FLAG_QOS1 ) == true )
        {
            IotLog( IOT_LOG_DEBUG,
                    &_logHideAll,
                    "Bad QoS: 3." );

            IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_RESPONSE );
        }
        else
        {
            EMPTY_ELSE_MARKER;
        }

        pOutput->qos = IOT_MQTT_QOS_2;
    }
    /* Check for QoS 1. */
    else if( UINT8_CHECK_BIT( publishFlags, MQTT_PUBLISH_FLAG_QOS1 ) == true )
    {
        pOutput->qos = IOT_MQTT_QOS_1;
    }
    /* If the PUBLISH isn't QoS 1 or 2, then it's QoS 0. */
    else
    {
        pOutput->qos = IOT_MQTT_QOS_0;
    }

    IotLog( IOT_LOG_DEBUG,
            &_logHideAll,
            "QoS is %d.", pOutput->qos );

    /* Parse the DUP bit. */
    if( UINT8_CHECK_BIT( publishFlags, MQTT_PUBLISH_FLAG_DUP ) == true )
    {
        IotLog( IOT_LOG_DEBUG,
                &_logHideAll,
                "DUP is 1." );
    }
    else
    {
        IotLog( IOT_LOG_DEBUG,
                &_logHideAll,
                "DUP is 0." );
    }

    /* Sanity checks for "Remaining length". */
    if( pOutput->qos == IOT_MQTT_QOS_0 )
    {
        /* A QoS 0 PUBLISH must have a remaining length of at least 3 to accommodate
         * topic name length (2 bytes) and topic name (at least 1 byte). */
        if( pPublish->remainingLength < 3 )
        {
            IotLog( IOT_LOG_DEBUG,
                    &_logHideAll,
                    "QoS 0 PUBLISH cannot have a remaining length less than 3." );

            IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_RESPONSE );
        }
        else
        {
            EMPTY_ELSE_MARKER;
        }
    }
    else
    {
        /* A QoS 1 or 2 PUBLISH must have a remaining length of at least 5 to
         * accommodate a packet identifier as well as the topic name length and
         * topic name. */
        if( pPublish->remainingLength < 5 )
        {
            IotLog( IOT_LOG_DEBUG,
                    &_logHideAll,
                    "QoS 1 or 2 PUBLISH cannot have a remaining length less than 5." );

            IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_RESPONSE );
        }
        else
        {
            EMPTY_ELSE_MARKER;
        }
    }

    /* Extract the topic name starting from the first byte of the variable header.
     * The topic name string starts at byte 3 in the variable header. */
    pOutput->topicNameLength = UINT16_DECODE( pVariableHeader );

    /* Sanity checks for topic name length and "Remaining length". */
    if( pOutput->qos == IOT_MQTT_QOS_0 )
    {
        /* Check that the "Remaining length" is at least as large as the variable
         * header. */
        if( pPublish->remainingLength < pOutput->topicNameLength + sizeof( uint16_t ) )
        {
            IotLog( IOT_LOG_DEBUG,
                    &_logHideAll,
                    "Remaining length cannot be less than variable header length." );

            IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_RESPONSE );
        }
        else
        {
            EMPTY_ELSE_MARKER;
        }
    }
    else
    {
        /* Check that the "Remaining length" is at least as large as the variable
         * header. */
        if( pPublish->remainingLength < pOutput->topicNameLength + 2 * sizeof( uint16_t ) )
        {
            IotLog( IOT_LOG_DEBUG,
                    &_logHideAll,
                    "Remaining length cannot be less than variable header length." );

            IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_RESPONSE );
        }
        else
        {
            EMPTY_ELSE_MARKER;
        }
    }

    /* Parse the topic. */
    pOutput->pTopicName = ( const char * ) ( pVariableHeader + sizeof( uint16_t ) );

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
        if( pPublish->packetIdentifier == 0 )
        {
            IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_RESPONSE );
        }
        else
        {
            EMPTY_ELSE_MARKER;
        }
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    /* Calculate the length of the payload. QoS 1 or 2 PUBLISH packets contain
     * a packet identifier, but QoS 0 PUBLISH packets do not. */
    if( pOutput->qos == IOT_MQTT_QOS_0 )
    {
        pOutput->payloadLength = ( pPublish->remainingLength - pOutput->topicNameLength - sizeof( uint16_t ) );
        pOutput->pPayload = pPacketIdentifierHigh;
    }
    else
    {
        pOutput->payloadLength = ( pPublish->remainingLength - pOutput->topicNameLength - 2 * sizeof( uint16_t ) );
        pOutput->pPayload = pPacketIdentifierHigh + sizeof( uint16_t );
    }

    IotLog( IOT_LOG_DEBUG,
            &_logHideAll,
            "Payload length %hu.", pOutput->payloadLength );

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

IotMqttError_t _IotMqtt_SerializePuback( uint16_t packetIdentifier,
                                         uint8_t ** pPubackPacket,
                                         size_t * pPacketSize )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;

    /* Allocate memory for PUBACK. */
    uint8_t * pBuffer = IotMqtt_MallocMessage( MQTT_PACKET_PUBACK_SIZE );

    if( pBuffer == NULL )
    {
        IotLogError( "Failed to allocate memory for PUBACK packet" );

        status = IOT_MQTT_NO_MEMORY;
    }
    else
    {
        /* Set the output parameters. The remainder of this function always succeeds. */
        *pPubackPacket = pBuffer;
        *pPacketSize = MQTT_PACKET_PUBACK_SIZE;

        /* Set the 4 bytes in PUBACK. */
        pBuffer[ 0 ] = MQTT_PACKET_TYPE_PUBACK;
        pBuffer[ 1 ] = MQTT_PACKET_PUBACK_REMAINING_LENGTH;
        pBuffer[ 2 ] = UINT16_HIGH_BYTE( packetIdentifier );
        pBuffer[ 3 ] = UINT16_LOW_BYTE( packetIdentifier );

        /* Print out the serialized PUBACK packet for debugging purposes. */
        IotLog_PrintBuffer( "MQTT PUBACK packet:", *pPubackPacket, MQTT_PACKET_PUBACK_SIZE );
    }

    return status;
}

/*-----------------------------------------------------------*/

IotMqttError_t _IotMqtt_DeserializePuback( _mqttPacket_t * pPuback )
{
    IOT_FUNCTION_ENTRY( IotMqttError_t, IOT_MQTT_SUCCESS );

    /* Check the "Remaining length" of the received PUBACK. */
    if( pPuback->remainingLength != MQTT_PACKET_PUBACK_REMAINING_LENGTH )
    {
        IotLog( IOT_LOG_ERROR,
                &_logHideAll,
                "PUBACK does not have remaining length of %d.",
                MQTT_PACKET_PUBACK_REMAINING_LENGTH );

        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_RESPONSE );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    /* Extract the packet identifier (third and fourth bytes) from PUBACK. */
    pPuback->packetIdentifier = UINT16_DECODE( pPuback->pRemainingData );

    IotLog( IOT_LOG_DEBUG,
            &_logHideAll,
            "Packet identifier %hu.", pPuback->packetIdentifier );

    /* Packet identifier cannot be 0. */
    if( pPuback->packetIdentifier == 0 )
    {
        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_RESPONSE );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    /* Check that the control packet type is 0x40 (this must be done after the
     * packet identifier is parsed). */
    if( pPuback->type != MQTT_PACKET_TYPE_PUBACK )
    {
        IotLog( IOT_LOG_ERROR,
                &_logHideAll,
                "Bad control packet type 0x%02x.",
                pPuback->type );

        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_RESPONSE );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

IotMqttError_t _IotMqtt_SerializeSubscribe( const IotMqttSubscription_t * pSubscriptionList,
                                            size_t subscriptionCount,
                                            uint8_t ** pSubscribePacket,
                                            size_t * pPacketSize,
                                            uint16_t * pPacketIdentifier )
{
    IOT_FUNCTION_ENTRY( IotMqttError_t, IOT_MQTT_SUCCESS );
    size_t subscribePacketSize = 0, remainingLength = 0;
    uint8_t * pBuffer = NULL;

    /* Calculate the "Remaining length" field and total packet size. If it exceeds
     * what is allowed in the MQTT standard, return an error. */
    if( _subscriptionPacketSize( IOT_MQTT_SUBSCRIBE,
                                 pSubscriptionList,
                                 subscriptionCount,
                                 &remainingLength,
                                 &subscribePacketSize ) == false )
    {
        IotLogError( "Subscribe packet remaining length exceeds %lu, which is the "
                     "maximum size allowed by MQTT 3.1.1.",
                     MQTT_MAX_REMAINING_LENGTH );

        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_PARAMETER );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    /* Total size of the subscribe packet should be larger than the "Remaining length"
     * field. */
    IotMqtt_Assert( subscribePacketSize > remainingLength );

    /* Allocate memory to hold the SUBSCRIBE packet. */
    pBuffer = IotMqtt_MallocMessage( subscribePacketSize );

    /* Check that sufficient memory was allocated. */
    if( pBuffer == NULL )
    {
        IotLogError( "Failed to allocate memory for SUBSCRIBE packet." );

        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_NO_MEMORY );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    /* Set the output parameters. The remainder of this function always succeeds. */
    *pSubscribePacket = pBuffer;
    *pPacketSize = subscribePacketSize;

    /* Serialize subscribe into buffer pointed to by pBuffer */
    _serializeSubscribe( pSubscriptionList,
                         subscriptionCount,
                         remainingLength,
                         pPacketIdentifier,
                         pBuffer,
                         subscribePacketSize );


    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

IotMqttError_t _IotMqtt_DeserializeSuback( _mqttPacket_t * pSuback )
{
    IOT_FUNCTION_ENTRY( IotMqttError_t, IOT_MQTT_SUCCESS );
    size_t i = 0, remainingLength = pSuback->remainingLength;
    uint8_t subscriptionStatus = 0;
    const uint8_t * pVariableHeader = pSuback->pRemainingData;

    /* A SUBACK must have a remaining length of at least 3 to accommodate the
     * packet identifier and at least one return code. */
    if( remainingLength < 3 )
    {
        IotLog( IOT_LOG_DEBUG,
                &_logHideAll,
                "SUBACK cannot have a remaining length less than 3." );

        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_RESPONSE );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

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

        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_RESPONSE );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    /* Iterate through each status byte in the SUBACK packet. */
    for( i = 0; i < remainingLength - sizeof( uint16_t ); i++ )
    {
        /* Read a single status byte in SUBACK. */
        subscriptionStatus = *( pVariableHeader + sizeof( uint16_t ) + i );

        /* MQTT 3.1.1 defines the following values as status codes. */
        switch( subscriptionStatus )
        {
            case 0x00:
            case 0x01:
            case 0x02:
                IotLog( IOT_LOG_DEBUG,
                        &_logHideAll,
                        "Topic filter %lu accepted, max QoS %hhu.",
                        ( unsigned long ) i, subscriptionStatus );
                break;

            case 0x80:
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
        else
        {
            EMPTY_ELSE_MARKER;
        }
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

IotMqttError_t _IotMqtt_SerializeUnsubscribe( const IotMqttSubscription_t * pSubscriptionList,
                                              size_t subscriptionCount,
                                              uint8_t ** pUnsubscribePacket,
                                              size_t * pPacketSize,
                                              uint16_t * pPacketIdentifier )
{
    IOT_FUNCTION_ENTRY( IotMqttError_t, IOT_MQTT_SUCCESS );
    size_t unsubscribePacketSize = 0, remainingLength = 0;
    uint8_t * pBuffer = NULL;

    /* Calculate the "Remaining length" field and total packet size. If it exceeds
     * what is allowed in the MQTT standard, return an error. */
    if( _subscriptionPacketSize( IOT_MQTT_UNSUBSCRIBE,
                                 pSubscriptionList,
                                 subscriptionCount,
                                 &remainingLength,
                                 &unsubscribePacketSize ) == false )
    {
        IotLogError( "Unsubscribe packet remaining length exceeds %lu, which is the "
                     "maximum size allowed by MQTT 3.1.1.",
                     MQTT_MAX_REMAINING_LENGTH );

        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_PARAMETER );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    /* Total size of the unsubscribe packet should be larger than the "Remaining length"
     * field. */
    IotMqtt_Assert( unsubscribePacketSize > remainingLength );

    /* Allocate memory to hold the UNSUBSCRIBE packet. */
    pBuffer = IotMqtt_MallocMessage( unsubscribePacketSize );

    /* Check that sufficient memory was allocated. */
    if( pBuffer == NULL )
    {
        IotLogError( "Failed to allocate memory for UNSUBSCRIBE packet." );

        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_NO_MEMORY );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    /* Set the output parameters. The remainder of this function always succeeds. */
    *pUnsubscribePacket = pBuffer;
    *pPacketSize = unsubscribePacketSize;

    /* Serialize unsubscribe into buffer pointed to by pBuffer */
    _serializeUnsubscribe( pSubscriptionList,
                           subscriptionCount,
                           remainingLength,
                           pPacketIdentifier,
                           pBuffer,
                           unsubscribePacketSize );

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

IotMqttError_t _IotMqtt_DeserializeUnsuback( _mqttPacket_t * pUnsuback )
{
    IOT_FUNCTION_ENTRY( IotMqttError_t, IOT_MQTT_SUCCESS );

    /* Check the "Remaining length" (second byte) of the received UNSUBACK. */
    if( pUnsuback->remainingLength != MQTT_PACKET_UNSUBACK_REMAINING_LENGTH )
    {
        IotLog( IOT_LOG_ERROR,
                &_logHideAll,
                "UNSUBACK does not have remaining length of %d.",
                MQTT_PACKET_UNSUBACK_REMAINING_LENGTH );

        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_RESPONSE );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    /* Extract the packet identifier (third and fourth bytes) from UNSUBACK. */
    pUnsuback->packetIdentifier = UINT16_DECODE( pUnsuback->pRemainingData );

    /* Packet identifier cannot be 0. */
    if( pUnsuback->packetIdentifier == 0 )
    {
        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_RESPONSE );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

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

        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_RESPONSE );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

IotMqttError_t _IotMqtt_SerializePingreq( uint8_t ** pPingreqPacket,
                                          size_t * pPacketSize )
{
    /* PINGREQ packets are always the same. */
    static const uint8_t pPingreq[ MQTT_PACKET_PINGREQ_SIZE ] =
    {
        MQTT_PACKET_TYPE_PINGREQ,
        0x00
    };

    /* Set the output parameters. */
    *pPingreqPacket = ( uint8_t * ) pPingreq;
    *pPacketSize = MQTT_PACKET_PINGREQ_SIZE;

    /* Print out the PINGREQ packet for debugging purposes. */
    IotLog_PrintBuffer( "MQTT PINGREQ packet:", pPingreq, MQTT_PACKET_PINGREQ_SIZE );

    return IOT_MQTT_SUCCESS;
}

/*-----------------------------------------------------------*/

IotMqttError_t _IotMqtt_DeserializePingresp( _mqttPacket_t * pPingresp )
{
    IOT_FUNCTION_ENTRY( IotMqttError_t, IOT_MQTT_SUCCESS );

    /* Check that the control packet type is 0xd0. */
    if( pPingresp->type != MQTT_PACKET_TYPE_PINGRESP )
    {
        IotLog( IOT_LOG_ERROR,
                &_logHideAll,
                "Bad control packet type 0x%02x.",
                pPingresp->type );

        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_RESPONSE );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    /* Check the "Remaining length" (second byte) of the received PINGRESP. */
    if( pPingresp->remainingLength != MQTT_PACKET_PINGRESP_REMAINING_LENGTH )
    {
        IotLog( IOT_LOG_ERROR,
                &_logHideAll,
                "PINGRESP does not have remaining length of %d.",
                MQTT_PACKET_PINGRESP_REMAINING_LENGTH );

        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_RESPONSE );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

IotMqttError_t _IotMqtt_SerializeDisconnect( uint8_t ** pDisconnectPacket,
                                             size_t * pPacketSize )
{
    /* DISCONNECT packets are always the same. */
    static const uint8_t pDisconnect[ MQTT_PACKET_DISCONNECT_SIZE ] =
    {
        MQTT_PACKET_TYPE_DISCONNECT,
        0x00
    };

    /* Set the output parameters. */
    *pDisconnectPacket = ( uint8_t * ) pDisconnect;
    *pPacketSize = MQTT_PACKET_DISCONNECT_SIZE;

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
        else
        {
            EMPTY_ELSE_MARKER;
        }
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }
}

/*-----------------------------------------------------------*/

/* Public interface functions for serialization */

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_GetConnectPacketSize( const IotMqttConnectInfo_t * pConnectInfo,
                                             size_t * pRemainingLength,
                                             size_t * pPacketSize )
{
    IOT_FUNCTION_ENTRY( IotMqttError_t, IOT_MQTT_SUCCESS );

    if( ( pConnectInfo == NULL ) || ( pRemainingLength == NULL ) || ( pPacketSize == NULL ) )
    {
        IotLogError( "IotMqtt_GetConnectPacketSize() called with required parameter(s) set to NULL." );
        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_PARAMETER );
    }

    if( ( pConnectInfo->clientIdentifierLength == 0 ) || ( pConnectInfo->pClientIdentifier == NULL ) )
    {
        IotLogError( "IotMqtt_GetConnectPacketSize() client identifier must be set." );
        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_PARAMETER );
    }

    /* Calculate the "Remaining length" field and total packet size. If it exceeds
     * what is allowed in the MQTT standard, return an error. */
    if( _connectPacketSize( pConnectInfo, pRemainingLength, pPacketSize ) == false )
    {
        IotLogError( "Connect packet length exceeds %lu, which is the maximum"
                     " size allowed by MQTT 3.1.1.",
                     MQTT_PACKET_CONNECT_MAX_SIZE );

        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_PARAMETER );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    /* Total size of the subscribe packet should be larger than the "Remaining length"
     * field. */
    if( ( *pPacketSize ) < ( *pRemainingLength ) )
    {
        IotLogError( "Connection packet remaining length (%lu) exceeds packet size (%lu)",
                     ( *pRemainingLength ), ( *pPacketSize ) );
        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_PARAMETER );
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_SerializeConnect( const IotMqttConnectInfo_t * pConnectInfo,
                                         size_t remainingLength,
                                         uint8_t * pBuffer,
                                         size_t bufferSize )
{
    IOT_FUNCTION_ENTRY( IotMqttError_t, IOT_MQTT_SUCCESS );

    if( ( pBuffer == NULL ) || ( pConnectInfo == NULL ) )
    {
        IotLogError( "IotMqtt_SerializeConnect() called with required parameter(s) set to NULL." );
        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_PARAMETER );
    }

    if( ( pConnectInfo->clientIdentifierLength == 0 ) || ( pConnectInfo->pClientIdentifier == NULL ) )
    {
        IotLogError( "IotMqtt_SerializeConnect() client identifier must be set." );
        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_PARAMETER );
    }

    if( remainingLength > bufferSize )
    {
        IotLogError( " Serialize Connect packet remaining length (%lu) exceeds buffer size (%lu)",
                     remainingLength, bufferSize );
        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_PARAMETER );
    }

    _serializeConnect( pConnectInfo,
                       remainingLength,
                       pBuffer,
                       bufferSize );

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_GetSubscriptionPacketSize( IotMqttOperationType_t type,
                                                  const IotMqttSubscription_t * pSubscriptionList,
                                                  size_t subscriptionCount,
                                                  size_t * pRemainingLength,
                                                  size_t * pPacketSize )
{
    IOT_FUNCTION_ENTRY( IotMqttError_t, IOT_MQTT_SUCCESS );

    if( ( pSubscriptionList == NULL ) || ( pRemainingLength == NULL ) || ( pPacketSize == NULL ) )
    {
        IotLogError( "IotMqtt_GetSubscriptionPacketSize() called with required parameter(s) set to NULL." );
        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_PARAMETER );
    }

    if( ( type != IOT_MQTT_SUBSCRIBE ) && ( type != IOT_MQTT_UNSUBSCRIBE ) )
    {
        IotLogError( "IotMqtt_GetSubscriptionPacketSize() called with unknown type." );
        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_PARAMETER );
    }

    if( subscriptionCount == 0 )
    {
        IotLogError( "IotMqtt_GetSubscriptionPacketSize() called with zero subscription count." );
        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_PARAMETER );
    }

    if( _subscriptionPacketSize( type,
                                 pSubscriptionList,
                                 subscriptionCount,
                                 pRemainingLength,
                                 pPacketSize ) == false )
    {
        IotLogError( "Unsubscribe packet remaining length exceeds %lu, which is the "
                     "maximum size allowed by MQTT 3.1.1.",
                     MQTT_MAX_REMAINING_LENGTH );
        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_PARAMETER );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    /* Total size of the subscribe packet should be larger than the "Remaining length"
     * field. */
    if( ( *pPacketSize ) < ( *pRemainingLength ) )
    {
        IotLogError( "Subscription packet remaining length (%lu) exceeds packet size (%lu)",
                     ( *pRemainingLength ), ( *pPacketSize ) );
        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_PARAMETER );
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_SerializeSubscribe( const IotMqttSubscription_t * pSubscriptionList,
                                           size_t subscriptionCount,
                                           size_t remainingLength,
                                           uint16_t * pPacketIdentifier,
                                           uint8_t * pBuffer,
                                           size_t bufferSize )
{
    IOT_FUNCTION_ENTRY( IotMqttError_t, IOT_MQTT_SUCCESS );

    if( ( pBuffer == NULL ) || ( pSubscriptionList == NULL ) || ( pPacketIdentifier == NULL ) )
    {
        IotLogError( "IotMqtt_SerializeSubscribe() called with required parameter(s) set to NULL." );
        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_PARAMETER );
    }

    if( subscriptionCount == 0 )
    {
        IotLogError( "IotMqtt_SerializeSubscribe() called with zero subscription count." );
        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_PARAMETER );
    }

    if( remainingLength > bufferSize )
    {
        IotLogError( " Subscribe packet remaining length (%lu) exceeds buffer size (%lu).",
                     remainingLength, bufferSize );
        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_PARAMETER );
    }

    _serializeSubscribe( pSubscriptionList,
                         subscriptionCount,
                         remainingLength,
                         pPacketIdentifier,
                         pBuffer,
                         bufferSize );

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_GetPublishPacketSize( IotMqttPublishInfo_t * pPublishInfo,
                                             size_t * pRemainingLength,
                                             size_t * pPacketSize )
{
    IOT_FUNCTION_ENTRY( IotMqttError_t, IOT_MQTT_SUCCESS );

    if( ( pPublishInfo == NULL ) || ( pRemainingLength == NULL ) || ( pPacketSize == NULL ) )
    {
        IotLogError( "IotMqtt_GetPublishPacketSize() called with required parameter(s) set to NULL." );
        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_PARAMETER );
    }

    if( ( pPublishInfo->pTopicName == NULL ) || ( pPublishInfo->topicNameLength == 0 ) )
    {
        IotLogError( "IotMqtt_GetPublishPacketSize() called with no topic." );
        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_PARAMETER );
    }

    /* Calculate the "Remaining length" field and total packet size. If it exceeds
     * what is allowed in the MQTT standard, return an error. */
    if( _publishPacketSize( pPublishInfo, pRemainingLength, pPacketSize ) == false )
    {
        IotLogError( "Publish packet remaining length exceeds %lu, which is the "
                     "maximum size allowed by MQTT 3.1.1.",
                     MQTT_MAX_REMAINING_LENGTH );

        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_PARAMETER );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    /* Total size of the publish packet should be larger than the "Remaining length"
     * field. */
    if( ( *pPacketSize ) < ( *pRemainingLength ) )
    {
        IotLogError( "Publish packet remaining length (%lu) exceeds packet size (%lu).",
                     ( *pRemainingLength ), ( *pPacketSize ) );
        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_PARAMETER );
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_SerializePublish( IotMqttPublishInfo_t * pPublishInfo,
                                         size_t remainingLength,
                                         uint16_t * pPacketIdentifier,
                                         uint8_t ** pPacketIdentifierHigh,
                                         uint8_t * pBuffer,
                                         size_t bufferSize )

{
    IOT_FUNCTION_ENTRY( IotMqttError_t, IOT_MQTT_SUCCESS );

    if( ( pBuffer == NULL ) || ( pPublishInfo == NULL ) || ( pPacketIdentifier == NULL ) )
    {
        IotLogError( "IotMqtt_SerializePublish() called with required parameter(s) set to NULL." );
        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_PARAMETER );
    }

    if( ( pPublishInfo->pTopicName == NULL ) || ( pPublishInfo->topicNameLength == 0 ) )
    {
        IotLogError( "IotMqtt_SerializePublish() called with no topic." );
        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_PARAMETER );
    }

    if( remainingLength > bufferSize )
    {
        IotLogError( "Publish packet remaining length (%lu) exceeds buffer size (%lu).",
                     remainingLength, bufferSize );
        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_PARAMETER );
    }

    _serializePublish( pPublishInfo,
                       remainingLength,
                       pPacketIdentifier,
                       pPacketIdentifierHigh,
                       pBuffer,
                       bufferSize );
    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_SerializeUnsubscribe( const IotMqttSubscription_t * pSubscriptionList,
                                             size_t subscriptionCount,
                                             size_t remainingLength,
                                             uint16_t * pPacketIdentifier,
                                             uint8_t * pBuffer,
                                             size_t bufferSize )
{
    IOT_FUNCTION_ENTRY( IotMqttError_t, IOT_MQTT_SUCCESS );

    if( ( pBuffer == NULL ) || ( pPacketIdentifier == NULL ) || ( pSubscriptionList == NULL ) )
    {
        IotLogError( "IotMqtt_SerializeUnsubscribe() called with required parameter(s) set to NULL." );
        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_PARAMETER );
    }

    if( subscriptionCount == 0 )
    {
        IotLogError( "IotMqtt_SerializeUnsubscribe() called with zero subscription count." );
        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_PARAMETER );
    }

    if( remainingLength > bufferSize )
    {
        IotLogError( "Unsubscribe packet remaining length (%lu) exceeds buffer size (%lu).",
                     remainingLength, bufferSize );
        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_PARAMETER );
    }

    _serializeUnsubscribe( pSubscriptionList,
                           subscriptionCount,
                           remainingLength,
                           pPacketIdentifier,
                           pBuffer,
                           bufferSize );
    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_SerializeDisconnect( uint8_t * pBuffer,
                                            size_t bufferSize )
{
    IOT_FUNCTION_ENTRY( IotMqttError_t, IOT_MQTT_SUCCESS );
    uint8_t * pDisconnectPacket = NULL;
    size_t remainingLength = 0;

    if( pBuffer == NULL )
    {
        IotLogError( "IotMqtt_SerializeDisconnect() called with NULL buffer pointer." );
        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_PARAMETER );
    }

    if( bufferSize < MQTT_PACKET_DISCONNECT_SIZE )
    {
        IotLogError( "Disconnect packet length (%lu) exceeds buffer size (%lu).",
                     MQTT_PACKET_DISCONNECT_SIZE, bufferSize );
        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_PARAMETER );
    }

    /* Call internal function with local variables, as disconnect  uses
     * static memory, there is no need to pass the buffer
     * Note: _IotMqtt_SerializeDisconnect always succeeds */
    _IotMqtt_SerializeDisconnect( &pDisconnectPacket, &remainingLength );

    memcpy( pBuffer, pDisconnectPacket, MQTT_PACKET_DISCONNECT_SIZE );
    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_SerializePingreq( uint8_t * pBuffer,
                                         size_t bufferSize )
{
    IOT_FUNCTION_ENTRY( IotMqttError_t, IOT_MQTT_SUCCESS );
    uint8_t * pPingreqPacket = NULL;
    size_t packetSize = 0;

    if( pBuffer == NULL )
    {
        IotLogError( "IotMqtt_SerializePingreq() called with NULL buffer pointer." );
        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_PARAMETER );
    }

    if( bufferSize < MQTT_PACKET_PINGREQ_SIZE )
    {
        IotLogError( "Pingreq length (%lu) exceeds buffer size (%lu).",
                     MQTT_PACKET_DISCONNECT_SIZE, bufferSize );
        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_PARAMETER );
    }

    /* Call internal function with local variables, as ping request uses
     * static memory, there is no need to pass the buffer
     * Note: _IotMqtt_SerializePingReq always succeeds */
    _IotMqtt_SerializePingreq( &pPingreqPacket, &packetSize );
    memcpy( pBuffer, pPingreqPacket, MQTT_PACKET_PINGREQ_SIZE );
    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_DeserializePublish( IotMqttPacketInfo_t * pMqttPacket )
{
    IOT_FUNCTION_ENTRY( IotMqttError_t, IOT_MQTT_SUCCESS );
    /* Internal MQTT packet structure */
    _mqttPacket_t mqttPacket;
    /* Internal MQTT operation structure needed for deserializing publish */
    _mqttOperation_t mqttOperation;

    if( pMqttPacket == NULL )
    {
        IotLogError( "IotMqtt_DeserializePublish()called with NULL pMqttPacket pointer." );
        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_PARAMETER );
    }

    if( ( pMqttPacket->type & 0xf0 ) != MQTT_PACKET_TYPE_PUBLISH )
    {
        IotLogError( "IotMqtt_DeserializePublish() called with incorrect packet type:(%lu).", pMqttPacket->type );
        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_PARAMETER );
    }

    /* Set internal mqtt packet parameters. */
    memset( ( void * ) &mqttPacket, 0x00, sizeof( _mqttPacket_t ) );
    mqttPacket.pRemainingData = pMqttPacket->pRemainingData;
    mqttPacket.remainingLength = pMqttPacket->remainingLength;
    mqttPacket.type = pMqttPacket->type;

    /* Set Publish specific parameters */
    memset( ( void * ) &mqttOperation, 0x00, sizeof( _mqttOperation_t ) );
    mqttOperation.incomingPublish = true;
    mqttPacket.u.pIncomingPublish = &mqttOperation;
    status = _IotMqtt_DeserializePublish( &mqttPacket );

    if( status == IOT_MQTT_SUCCESS )
    {
        pMqttPacket->pubInfo = mqttOperation.u.publish.publishInfo;
        pMqttPacket->packetIdentifier = mqttPacket.packetIdentifier;
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_DeserializeResponse( IotMqttPacketInfo_t * pMqttPacket )
{
    IOT_FUNCTION_ENTRY( IotMqttError_t, IOT_MQTT_SUCCESS );
    /* Internal MQTT packet structure */
    _mqttPacket_t mqttPacket;

    if( ( pMqttPacket == NULL ) || ( pMqttPacket->pRemainingData == NULL ) )
    {
        IotLogError( "IotMqtt_DeserializeResponse() called with NULL pMqttPacket pointer or NULL pRemainingLength." );
        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_PARAMETER );
    }

    /* Set internal mqtt packet parameters. */
    memset( ( void * ) &mqttPacket, 0x00, sizeof( _mqttPacket_t ) );

    mqttPacket.pRemainingData = pMqttPacket->pRemainingData;
    mqttPacket.remainingLength = pMqttPacket->remainingLength;
    mqttPacket.type = pMqttPacket->type;

    /* Call internal deserialize */
    switch( pMqttPacket->type & 0xf0 )
    {
        case MQTT_PACKET_TYPE_CONNACK:
            status = _IotMqtt_DeserializeConnack( &mqttPacket );
            break;

        case MQTT_PACKET_TYPE_PUBACK:
            status = _IotMqtt_DeserializePuback( &mqttPacket );
            break;

        case MQTT_PACKET_TYPE_SUBACK:
            status = _IotMqtt_DeserializeSuback( &mqttPacket );
            break;

        case MQTT_PACKET_TYPE_UNSUBACK:
            status = _IotMqtt_DeserializeUnsuback( &mqttPacket );
            break;

        case MQTT_PACKET_TYPE_PINGRESP:
            status = _IotMqtt_DeserializePingresp( &mqttPacket );
            break;

        /* Any other packet type is invalid. */
        default:
            IotLogError( "IotMqtt_DeserializeResponse() called with unknown packet type:(%lu).", pMqttPacket->type );
            IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_PARAMETER );
    }

    if( status != IOT_MQTT_SUCCESS )
    {
        IOT_SET_AND_GOTO_CLEANUP( status );
    }
    else
    {
        /* Set packetIdentifier only if success is returned. */
        pMqttPacket->packetIdentifier = mqttPacket.packetIdentifier;
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/
