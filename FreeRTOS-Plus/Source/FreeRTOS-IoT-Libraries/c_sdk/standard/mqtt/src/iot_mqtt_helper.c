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
 * @file iot_mqtt_helper.c
 * @brief Implements helper functions for the MQTT library.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <string.h>
#include <limits.h>
/* Default assert and memory allocation functions. */
#include <assert.h>
#include <stdlib.h>

/* For use of atomics library */
#include "iot_atomic.h"

/* MQTT helper header. */
#include "private/iot_mqtt_helper.h"

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

/* Username for metrics with AWS IoT. */
#if ( AWS_IOT_MQTT_ENABLE_METRICS == 1 ) || ( DOXYGEN == 1 )
    #ifndef AWS_IOT_METRICS_USERNAME

/**
 * @brief Specify C SDK and version.
 */
        #define AWS_IOT_METRICS_USERNAME           "?SDK=C&Version=4.0.0"

/**
 * @brief The length of #AWS_IOT_METRICS_USERNAME.
 */
        #define AWS_IOT_METRICS_USERNAME_LENGTH    ( ( uint16_t ) sizeof( AWS_IOT_METRICS_USERNAME ) - 1U )
    #endif /* ifndef AWS_IOT_METRICS_USERNAME */
#endif /* if AWS_IOT_MQTT_ENABLE_METRICS == 1 || DOXYGEN == 1 */

/*-----------------------------------------------------------*/

/**
 * @brief Encode both connection and metrics username into a buffer,
 * if they will fit.
 *
 * @param[in] pDestination Buffer to write username into.
 * @param[in] pConnectInfo User-provided CONNECT information.
 * @param[out] pEncodedUserName Whether the username was written into the buffer.
 *
 * @return Pointer to the end of encoded string, which will be identical to
 * `pDestination` if nothing was encoded.
 *
 * @warning This function does not check the size of `pDestination`! Ensure that
 * `pDestination` is large enough to hold `pConnectInfo->userNameLength` +
 * #AWS_IOT_METRICS_USERNAME_LENGTH bytes to avoid a buffer overflow.
 */

static uint8_t * _encodeUserNameAndMetrics( uint8_t * pDestination,
                                            const IotMqttConnectInfo_t * pConnectInfo,
                                            bool * pEncodedUserName );

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
 * the function #_IotMqtt_RemainingLengthEncodedSize to avoid buffer overflows.
 */
static uint8_t * _encodeRemainingLength( uint8_t * pDestination,
                                         size_t length );

/**
 * @brief Encode a username into a CONNECT packet, if necessary.
 *
 * @param[out] pDestination Buffer for the CONNECT packet.
 * @param[in] pConnectInfo User-provided CONNECT information.
 *
 * @return Pointer to the end of the encoded string, which will be identical to
 * `pDestination` if nothing was encoded.
 *
 * @warning This function does not check the size of `pDestination`! To avoid a
 * buffer overflow, ensure that `pDestination` is large enough to hold
 * `pConnectInfo->userNameLength` bytes if a username is supplied, and/or
 * #AWS_IOT_METRICS_USERNAME_LENGTH bytes if metrics are enabled.
 */
static uint8_t * _encodeUserName( uint8_t * pDestination,
                                  const IotMqttConnectInfo_t * pConnectInfo );

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

/*-----------------------------------------------------------*/

static uint8_t * _encodeUserNameAndMetrics( uint8_t * pDestination,
                                            const IotMqttConnectInfo_t * pConnectInfo,
                                            bool * pEncodedUserName )
{
    uint8_t *        pBuffer          = pDestination;

    #if AWS_IOT_MQTT_ENABLE_METRICS == 1
        const char * pMetricsUserName = AWS_IOT_METRICS_USERNAME;

        /* Only include metrics if it will fit within the encoding
         * standard. */
        if( ( pConnectInfo->userNameLength + AWS_IOT_METRICS_USERNAME_LENGTH ) <= ( ( uint16_t ) ( UINT16_MAX ) ) )
        {
            /* Write the high byte of the combined length. */
            pBuffer[ 0 ]      = UINT16_HIGH_BYTE( ( pConnectInfo->userNameLength +
                                                    AWS_IOT_METRICS_USERNAME_LENGTH ) );

            /* Write the low byte of the combined length. */
            pBuffer[ 1 ]      = UINT16_LOW_BYTE( ( pConnectInfo->userNameLength +
                                                   AWS_IOT_METRICS_USERNAME_LENGTH ) );
            pBuffer          += 2;

            /* Write the identity portion of the username.
             * As the types of char and uint8_t are of the same size, this memcpy
             * is acceptable. */
            /* coverity[misra_c_2012_rule_21_15_violation] */
            ( void ) memcpy( pBuffer, pConnectInfo->pUserName, pConnectInfo->userNameLength );
            pBuffer          += pConnectInfo->userNameLength;

            /* Write the metrics portion of the username.
             * As the types of char and uint8_t are of the same size, this memcpy
             * is acceptable. */
            /* coverity[misra_c_2012_rule_21_15_violation] */
            ( void ) memcpy( pBuffer, pMetricsUserName, AWS_IOT_METRICS_USERNAME_LENGTH );
            pBuffer          += AWS_IOT_METRICS_USERNAME_LENGTH;

            *pEncodedUserName = true;
        }
        else
        {
            IotLogWarn( "Username length of %lu is larger than maximum %lu.",
                        ( pConnectInfo->userNameLength + AWS_IOT_METRICS_USERNAME_LENGTH ),
                        UINT16_MAX );
        }
    #else /* if AWS_IOT_MQTT_ENABLE_METRICS == 1 */
        /* Avoid unused variable warnings when AWS_IOT_MQTT_ENABLE_METRICS is set to 0. */
        ( void ) pBuffer;
        ( void ) pConnectInfo;
        ( void ) pEncodedUserName;
    #endif /* if AWS_IOT_MQTT_ENABLE_METRICS == 1 */

    return pBuffer;
}

static uint8_t * _encodeUserName( uint8_t * pDestination,
                                  const IotMqttConnectInfo_t * pConnectInfo )
{
    bool      encodedUserName = false;
    uint8_t * pBuffer         = pDestination;

    /* If metrics are enabled, write the metrics username into the CONNECT packet.
     * Otherwise, write the username and password only when not connecting to the
     * AWS IoT MQTT server. */
    if( pConnectInfo->awsIotMqttMode == true )
    {
        #if AWS_IOT_MQTT_ENABLE_METRICS == 1
            IotLogInfo( "Anonymous metrics (SDK language, SDK version) will be provided to AWS IoT. "
                        "Recompile with AWS_IOT_MQTT_ENABLE_METRICS set to 0 to disable." );

            /* Determine if the Connect packet should use a combination of the username
             * for authentication plus the SDK version string. */
            if( pConnectInfo->pUserName != NULL )
            {
                /* Encode username and metrics if they will fit. */
                pBuffer = _encodeUserNameAndMetrics( pBuffer, pConnectInfo, &encodedUserName );
            }
            else
            {
                /* The username is not being used for authentication, but
                 * metrics are enabled. */
                pBuffer         = _encodeString( pBuffer,
                                                 AWS_IOT_METRICS_USERNAME,
                                                 AWS_IOT_METRICS_USERNAME_LENGTH );

                encodedUserName = true;
            }
        #endif /* #if AWS_IOT_MQTT_ENABLE_METRICS == 1 */
    }

    /* Encode the username if there is one and it hasn't already been done. */
    if( ( pConnectInfo->pUserName != NULL ) && ( encodedUserName == false ) )
    {
        pBuffer = _encodeString( pBuffer,
                                 pConnectInfo->pUserName,
                                 pConnectInfo->userNameLength );
    }

    return pBuffer;
}
/*-----------------------------------------------------------*/

static uint8_t * _encodeString( uint8_t * pDestination,
                                const char * source,
                                uint16_t sourceLength )
{
    uint8_t * pBuffer = pDestination;

    /* The first byte of a UTF-8 string is the high byte of the string length. */
    *pBuffer = UINT16_HIGH_BYTE( sourceLength );
    pBuffer++;

    /* The second byte of a UTF-8 string is the low byte of the string length. */
    *pBuffer = UINT16_LOW_BYTE( sourceLength );
    pBuffer++;

    /* Copy the string into pBuffer.
     * A precondition of this function is that pBuffer can hold sourceLength+2
     * bytes. */
    /* coverity[misra_c_2012_rule_21_15_violation] */
    ( void ) memcpy( pBuffer, source, sourceLength );

    /* Return the pointer to the end of the encoded string. */
    pBuffer += sourceLength;

    return pBuffer;
}

/*-----------------------------------------------------------*/

static uint8_t * _encodeRemainingLength( uint8_t * pDestination,
                                         size_t length )
{
    uint8_t lengthByte = 0, * pLengthEnd = pDestination;
    size_t  remainingLength = length;

    /* This algorithm is copied from the MQTT v3.1.1 spec. */
    do
    {
        lengthByte      = ( uint8_t ) ( remainingLength % 128U );
        remainingLength = remainingLength / 128U;

        /* Set the high bit of this byte, indicating that there's more data. */
        if( remainingLength > 0U )
        {
            UINT8_SET_BIT( lengthByte, 7 );
        }

        /* Output a single encoded byte. */
        *pLengthEnd     = lengthByte;
        pLengthEnd++;
    } while( remainingLength > 0U );

    return pLengthEnd;
}

/*-----------------------------------------------------------*/

size_t _IotMqtt_RemainingLengthEncodedSize( size_t length )
{
    size_t encodedSize = 0;

    /* length should have already been checked before calling this function. */
    IotMqtt_Assert( length <= MQTT_MAX_REMAINING_LENGTH );

    /* Determine how many bytes are needed to encode length.
     * The values below are taken from the MQTT 3.1.1 spec. */

    /* 1 byte is needed to encode lengths between 0 and 127. */
    if( length < 128U )
    {
        encodedSize = 1;
    }
    /* 2 bytes are needed to encode lengths between 128 and 16,383. */
    else if( length < 16384U )
    {
        encodedSize = 2;
    }
    /* 3 bytes are needed to encode lengths between 16,384 and 2,097,151. */
    else if( length < 2097152U )
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

uint16_t _IotMqtt_NextPacketIdentifier( void )
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

bool _IotMqtt_ConnectPacketSize( const IotMqttConnectInfo_t * pConnectInfo,
                                 size_t * pRemainingLength,
                                 size_t * pPacketSize )
{
    bool   status = true;
    bool   encodedUserName = false;
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

    /* Depending on the status of metrics, add the length of the metrics username
     * or the user-provided username. */
    if( pConnectInfo->awsIotMqttMode == true )
    {
        #if AWS_IOT_MQTT_ENABLE_METRICS == 1
            connectPacketSize += ( AWS_IOT_METRICS_USERNAME_LENGTH +
                                   ( size_t ) ( pConnectInfo->userNameLength ) + sizeof( uint16_t ) );
            encodedUserName    = true;
        #endif
    }

    /* Add the lengths of the username (if it wasn't already handled above) and
     * password, if specified. */
    if( ( pConnectInfo->pUserName != NULL ) && ( encodedUserName == false ) )
    {
        connectPacketSize += pConnectInfo->userNameLength + sizeof( uint16_t );
    }

    if( pConnectInfo->pPassword != NULL )
    {
        connectPacketSize += pConnectInfo->passwordLength + sizeof( uint16_t );
    }

    /* At this point, the "Remaining Length" field of the MQTT CONNECT packet has
     * been calculated. */
    remainingLength    = connectPacketSize;

    /* Calculate the full size of the MQTT CONNECT packet by adding the size of
     * the "Remaining Length" field plus 1 byte for the "Packet Type" field. */
    connectPacketSize += 1U + _IotMqtt_RemainingLengthEncodedSize( connectPacketSize );

    /* Check that the CONNECT packet is within the bounds of the MQTT spec. */
    if( connectPacketSize > MQTT_PACKET_CONNECT_MAX_SIZE )
    {
        status = false;
    }
    else
    {
        *pRemainingLength = remainingLength;
        *pPacketSize      = connectPacketSize;
    }

    return status;
}

/*-----------------------------------------------------------*/

void _IotMqtt_SerializeConnectCommon( const IotMqttConnectInfo_t * pConnectInfo,
                                      size_t remainingLength,
                                      uint8_t * pPacket,
                                      size_t connectPacketSize )
{
    uint8_t   connectFlags = 0;
    uint8_t * pBuffer      = pPacket;

    /* Avoid unused variable warning when logging and asserts are disabled. */
    ( void ) pPacket;
    ( void ) connectPacketSize;

    /* The first byte in the CONNECT packet is the control packet type. */
    *pBuffer         = MQTT_PACKET_TYPE_CONNECT;
    pBuffer++;

    /* The remaining length of the CONNECT packet is encoded starting from the
     * second byte. The remaining length does not include the length of the fixed
     * header or the encoding of the remaining length. */
    pBuffer          = _encodeRemainingLength( pBuffer, remainingLength );

    /* The string "MQTT" is placed at the beginning of the CONNECT packet's variable
     * header. This string is 4 bytes long. */
    pBuffer          = _encodeString( pBuffer, "MQTT", 4 );

    /* The MQTT protocol version is the second byte of the variable header. */
    *pBuffer         = MQTT_VERSION_3_1_1;
    pBuffer++;

    /* Set the CONNECT flags based on the given parameters. */
    if( pConnectInfo->cleanSession == true )
    {
        UINT8_SET_BIT( connectFlags, MQTT_CONNECT_FLAG_CLEAN );
    }

    /* Username and password depend on MQTT mode. */
    if( ( pConnectInfo->pUserName == NULL ) &&
        ( pConnectInfo->awsIotMqttMode == true ) )
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

        if( pConnectInfo->pPassword != NULL )
        {
            UINT8_SET_BIT( connectFlags, MQTT_CONNECT_FLAG_PASSWORD );
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
                /* Empty default MISRA 16.4 */
                break;
        }

        if( pConnectInfo->pWillInfo->retain == true )
        {
            UINT8_SET_BIT( connectFlags, MQTT_CONNECT_FLAG_WILL_RETAIN );
        }
    }

    *pBuffer         = connectFlags;
    pBuffer++;

    /* Write the 2 bytes of the keep alive interval into the CONNECT packet. */
    *pBuffer         = UINT16_HIGH_BYTE( pConnectInfo->keepAliveSeconds );
    *( pBuffer + 1 ) = UINT16_LOW_BYTE( pConnectInfo->keepAliveSeconds );
    pBuffer         += 2;

    /* Write the client identifier into the CONNECT packet. */
    pBuffer          = _encodeString( pBuffer,
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

    /* Encode the username if there is one or metrics are enabled. */
    pBuffer          = _encodeUserName( pBuffer, pConnectInfo );

    /* Encode the password field, if requested by the app. */
    if( pConnectInfo->pPassword != NULL )
    {
        pBuffer = _encodeString( pBuffer,
                                 pConnectInfo->pPassword,
                                 pConnectInfo->passwordLength );
    }

    /* Ensure that the difference between the end and beginning of the buffer
     * is equal to connectPacketSize, i.e. pBuffer did not overflow. */
    IotMqtt_Assert( ( ( size_t ) ( pBuffer - pPacket ) ) == connectPacketSize );

    /* Print out the serialized CONNECT packet for debugging purposes. */
    IotLog_PrintBuffer( "MQTT CONNECT packet:", pPacket, connectPacketSize );
}

/*-----------------------------------------------------------*/

bool _IotMqtt_IncomingPacketValid( uint8_t packetType )
{
    bool status = true;

    /* Check packet type. Mask out lower bits to ignore flags. */
    switch( packetType & 0xf0U )
    {
        /* Valid incoming packet types. */
        case MQTT_PACKET_TYPE_CONNACK:
        case MQTT_PACKET_TYPE_PUBLISH:
        case MQTT_PACKET_TYPE_PUBACK:
        case MQTT_PACKET_TYPE_SUBACK:
        case MQTT_PACKET_TYPE_UNSUBACK:
        case MQTT_PACKET_TYPE_PINGRESP:
            break;

        /* Any other packet type is invalid. */
        default:
            status = false;
            break;
    }

    return status;
}

/*-----------------------------------------------------------*/

void _IotMqtt_SerializeSubscribeCommon( const IotMqttSubscription_t * pSubscriptionList,
                                        size_t subscriptionCount,
                                        size_t remainingLength,
                                        uint16_t * pPacketIdentifier,
                                        uint8_t * pPacket,
                                        size_t subscribePacketSize )
{
    uint16_t  packetIdentifier = 0;
    size_t    i                = 0;
    uint8_t * pBuffer          = pPacket;

    /* Avoid unused variable warning when logging and asserts are disabled. */
    ( void ) pPacket;
    ( void ) subscribePacketSize;

    /* The first byte in SUBSCRIBE is the packet type. */
    *pBuffer           = MQTT_PACKET_TYPE_SUBSCRIBE;
    pBuffer++;

    /* Encode the "Remaining length" starting from the second byte. */
    pBuffer            = _encodeRemainingLength( pBuffer, remainingLength );

    /* Get the next packet identifier. It should always be nonzero. */
    packetIdentifier   = _IotMqtt_NextPacketIdentifier();
    *pPacketIdentifier = packetIdentifier;
    IotMqtt_Assert( packetIdentifier != 0U );

    /* Place the packet identifier into the SUBSCRIBE packet. */
    *pBuffer           = UINT16_HIGH_BYTE( packetIdentifier );
    *( pBuffer + 1 )   = UINT16_LOW_BYTE( packetIdentifier );
    pBuffer           += 2;

    /* Serialize each subscription topic filter and QoS. */
    for( i = 0; i < subscriptionCount; i++ )
    {
        pBuffer  = _encodeString( pBuffer,
                                  pSubscriptionList[ i ].pTopicFilter,
                                  pSubscriptionList[ i ].topicFilterLength );

        /* Place the QoS in the SUBSCRIBE packet. */
        *pBuffer = ( uint8_t ) ( pSubscriptionList[ i ].qos );
        pBuffer++;
    }

    /* Ensure that the difference between the end and beginning of the buffer
     * is equal to subscribePacketSize, i.e. pBuffer did not overflow. */
    IotMqtt_Assert( ( ( size_t ) ( pBuffer - pPacket ) ) == subscribePacketSize );

    /* Print out the serialized SUBSCRIBE packet for debugging purposes. */
    IotLog_PrintBuffer( "MQTT SUBSCRIBE packet:", pPacket, subscribePacketSize );
}

/*-----------------------------------------------------------*/

bool _IotMqtt_SubscriptionPacketSize( IotMqttOperationType_t type,
                                      const IotMqttSubscription_t * pSubscriptionList,
                                      size_t subscriptionCount,
                                      size_t * pRemainingLength,
                                      size_t * pPacketSize )
{
    bool   status = true;
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
            subscriptionPacketSize += 1U;
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
        *pRemainingLength       = subscriptionPacketSize;

        /* Calculate the full size of the subscription packet by adding the size of the
         * "Remaining length" field plus 1 byte for the "Packet type" field. Set the
         * pPacketSize output parameter. */
        subscriptionPacketSize += 1U + _IotMqtt_RemainingLengthEncodedSize( subscriptionPacketSize );
        *pPacketSize            = subscriptionPacketSize;
    }

    return status;
}

/*-----------------------------------------------------------*/

bool _IotMqtt_PublishPacketSize( const IotMqttPublishInfo_t * pPublishInfo,
                                 size_t * pRemainingLength,
                                 size_t * pPacketSize )
{
    bool   status = true;
    size_t publishPacketSize = 0, payloadLimit = 0;

    /* The variable header of a PUBLISH packet always contains the topic name. */
    publishPacketSize += pPublishInfo->topicNameLength + sizeof( uint16_t );

    /* The variable header of a QoS 1 or 2 PUBLISH packet contains a 2-byte
     * packet identifier. */
    if( pPublishInfo->qos > IOT_MQTT_QOS_0 )
    {
        publishPacketSize += sizeof( uint16_t );
    }

    /* Calculate the maximum allowed size of the payload for the given parameters.
     * This calculation excludes the "Remaining length" encoding, whose size is not
     * yet known. */
    payloadLimit       = MQTT_MAX_REMAINING_LENGTH - publishPacketSize - 1U;

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
        payloadLimit      -= _IotMqtt_RemainingLengthEncodedSize( publishPacketSize );

        /* Check that the given payload fits within the size allowed by MQTT spec. */
        if( pPublishInfo->payloadLength > payloadLimit )
        {
            status = false;
        }
        else
        {
            /* Set the "Remaining length" output parameter and calculate the full
             * size of the PUBLISH packet. */
            *pRemainingLength  = publishPacketSize;

            publishPacketSize += 1U + _IotMqtt_RemainingLengthEncodedSize( publishPacketSize );
            *pPacketSize       = publishPacketSize;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

void _IotMqtt_SerializePublishCommon( const IotMqttPublishInfo_t * pPublishInfo,
                                      size_t remainingLength,
                                      uint16_t * pPacketIdentifier,
                                      uint8_t ** pPacketIdentifierHigh,
                                      uint8_t * pPacket,
                                      size_t publishPacketSize )
{
    uint8_t   publishFlags     = 0;
    uint16_t  packetIdentifier = 0;
    uint8_t * pBuffer          = pPacket;

    /* Avoid unused variable warning when logging and asserts are disabled. */
    ( void ) pPacket;
    ( void ) publishPacketSize;

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
        /* Empty else MISRA 15.7 */
    }

    if( pPublishInfo->retain == true )
    {
        UINT8_SET_BIT( publishFlags, MQTT_PUBLISH_FLAG_RETAIN );
    }

    *pBuffer     = publishFlags;
    pBuffer++;

    /* The "Remaining length" is encoded from the second byte. */
    pBuffer      = _encodeRemainingLength( pBuffer, remainingLength );

    /* The topic name is placed after the "Remaining length". */
    pBuffer      = _encodeString( pBuffer,
                                  pPublishInfo->pTopicName,
                                  pPublishInfo->topicNameLength );

    /* A packet identifier is required for QoS 1 and 2 messages. */
    if( pPublishInfo->qos > IOT_MQTT_QOS_0 )
    {
        /* Get the next packet identifier. It should always be nonzero. */
        packetIdentifier   = _IotMqtt_NextPacketIdentifier();
        IotMqtt_Assert( packetIdentifier != 0U );

        /* Set the packet identifier output parameters. */
        *pPacketIdentifier = packetIdentifier;

        if( pPacketIdentifierHigh != NULL )
        {
            *pPacketIdentifierHigh = pBuffer;
        }

        /* Place the packet identifier into the PUBLISH packet. */
        *pBuffer           = UINT16_HIGH_BYTE( packetIdentifier );
        *( pBuffer + 1 )   = UINT16_LOW_BYTE( packetIdentifier );
        pBuffer           += 2;
    }

    /* The payload is placed after the packet identifier. */
    if( pPublishInfo->payloadLength > 0U )
    {
        /* This memcpy intentionally copies bytes from a void * buffer into
         * a uint8_t * buffer. */
        /* coverity[misra_c_2012_rule_21_15_violation] */
        ( void ) memcpy( pBuffer, pPublishInfo->pPayload, pPublishInfo->payloadLength );
        pBuffer += pPublishInfo->payloadLength;
    }

    /* Ensure that the difference between the end and beginning of the buffer
     * is equal to publishPacketSize, i.e. pBuffer did not overflow. */
    IotMqtt_Assert( ( ( size_t ) ( pBuffer - pPacket ) ) == publishPacketSize );

    /* Print out the serialized PUBLISH packet for debugging purposes. */
    IotLog_PrintBuffer( "MQTT PUBLISH packet:", pPacket, publishPacketSize );
}

/*-----------------------------------------------------------*/

void _IotMqtt_SerializeUnsubscribeCommon( const IotMqttSubscription_t * pSubscriptionList,
                                          size_t subscriptionCount,
                                          size_t remainingLength,
                                          uint16_t * pPacketIdentifier,
                                          uint8_t * pPacket,
                                          size_t unsubscribePacketSize )
{
    uint16_t  packetIdentifier = 0;
    size_t    i                = 0;
    uint8_t * pBuffer          = pPacket;

    /* Avoid unused variable warning when logging and asserts are disabled. */
    ( void ) pPacket;
    ( void ) unsubscribePacketSize;

    /* The first byte in UNSUBSCRIBE is the packet type. */
    *pBuffer           = MQTT_PACKET_TYPE_UNSUBSCRIBE;
    pBuffer++;

    /* Encode the "Remaining length" starting from the second byte. */
    pBuffer            = _encodeRemainingLength( pBuffer, remainingLength );

    /* Get the next packet identifier. It should always be nonzero. */
    packetIdentifier   = _IotMqtt_NextPacketIdentifier();
    *pPacketIdentifier = packetIdentifier;
    IotMqtt_Assert( packetIdentifier != 0U );

    /* Place the packet identifier into the UNSUBSCRIBE packet. */
    *pBuffer           = UINT16_HIGH_BYTE( packetIdentifier );
    *( pBuffer + 1 )   = UINT16_LOW_BYTE( packetIdentifier );
    pBuffer           += 2;

    /* Serialize each subscription topic filter. */
    for( i = 0; i < subscriptionCount; i++ )
    {
        pBuffer = _encodeString( pBuffer,
                                 pSubscriptionList[ i ].pTopicFilter,
                                 pSubscriptionList[ i ].topicFilterLength );
    }

    /* Ensure that the difference between the end and beginning of the buffer
     * is equal to unsubscribePacketSize, i.e. pBuffer did not overflow. */
    IotMqtt_Assert( ( ( size_t ) ( pBuffer - pPacket ) ) == unsubscribePacketSize );

    /* Print out the serialized UNSUBSCRIBE packet for debugging purposes. */
    IotLog_PrintBuffer( "MQTT UNSUBSCRIBE packet:", pPacket, unsubscribePacketSize );
}

/*-----------------------------------------------------------*/

IotMqttError_t _IotMqtt_ProcessPublishFlags( uint8_t publishFlags,
                                             IotMqttPublishInfo_t * pOutput )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;

    if( pOutput == NULL )
    {
        status = IOT_MQTT_BAD_RESPONSE;
    }
    /* Check for QoS 2. */
    else if( UINT8_CHECK_BIT( publishFlags, MQTT_PUBLISH_FLAG_QOS2 ) == true )
    {
        /* PUBLISH packet is invalid if both QoS 1 and QoS 2 bits are set. */
        if( UINT8_CHECK_BIT( publishFlags, MQTT_PUBLISH_FLAG_QOS1 ) == true )
        {
            IotLogDebug( "Bad QoS: 3." );

            status = IOT_MQTT_BAD_RESPONSE;
        }
        else
        {
            pOutput->qos = IOT_MQTT_QOS_2;
        }
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

    if( status == IOT_MQTT_SUCCESS )
    {
        IotLogDebug( "QoS is %d.", pOutput->qos );

        /* Parse the Retain bit. */
        pOutput->retain = UINT8_CHECK_BIT( publishFlags, MQTT_PUBLISH_FLAG_RETAIN );

        IotLogDebug( "Retain bit is %d.", pOutput->retain );

        /* Parse the DUP bit. */
        if( UINT8_CHECK_BIT( publishFlags, MQTT_PUBLISH_FLAG_DUP ) == true )
        {
            IotLogDebug( "DUP is 1." );
        }
        else
        {
            IotLogDebug( "DUP is 0." );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/
