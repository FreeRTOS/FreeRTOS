/*
 * Amazon FreeRTOS MQTT V2.0.0
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
 *
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

/**
 * @file aws_mqtt_lib_ble.c
 * @brief MQTT library for BLE.
 */
/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <string.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"

#include "iot_ble_config.h"


/* MQTT internal includes. */
#include "platform/iot_threads.h"
#include "iot_serializer.h"
#include "platform/iot_network_ble.h"
#include "iot_ble_data_transfer.h"
#include "iot_ble_mqtt_serialize.h"
#include "private/iot_mqtt_internal.h"

#define _INVALID_MQTT_PACKET_TYPE        ( 0xF0 )


#define _IS_VALID_SERIALIZER_RET( ret, pSerializerBuf )                                \
    (  ( ret == IOT_SERIALIZER_SUCCESS ) ||                                        \
          (  ( !pSerializerBuf ) && ( ret == IOT_SERIALIZER_BUFFER_TOO_SMALL ) ) )

#define _NUM_CONNECT_PARMAS                   ( 4 )
#define _NUM_DEFAULT_PUBLISH_PARMAS           ( 4 )
#define _NUM_PUBACK_PARMAS                    ( 2 )
#define _NUM_SUBACK_PARAMS                    ( 4 )
#define _NUM_UNSUBACK_PARAMS                  ( 3 )
#define _NUM_DISCONNECT_PARAMS                ( 1 )
#define _NUM_PINGREQUEST_PARAMS               ( 1 )

const IotMqttSerializer_t IotBleMqttSerializer = {
    .serialize.connect       = IotBleMqtt_SerializeConnect,
    .serialize.publish       = IotBleMqtt_SerializePublish,
    .serialize.publishSetDup = IotBleMqtt_PublishSetDup,
    .serialize.puback        = IotBleMqtt_SerializePuback,
    .serialize.subscribe     = IotBleMqtt_SerializeSubscribe,
    .serialize.unsubscribe   = IotBleMqtt_SerializeUnsubscribe,
    .serialize.pingreq       = IotBleMqtt_SerializePingreq,
    .serialize.disconnect    = IotBleMqtt_SerializeDisconnect,
    .freePacket              = IotBleMqtt_FreePacket,
    .getPacketType           = IotBleMqtt_GetPacketType,
    .getRemainingLength      = IotBleMqtt_GetRemainingLength,
    .deserialize.connack     = IotBleMqtt_DeserializeConnack,
    .deserialize.publish     = IotBleMqtt_DeserializePublish,
    .deserialize.puback      = IotBleMqtt_DeserializePuback,
    .deserialize.suback      = IotBleMqtt_DeserializeSuback,
    .deserialize.unsuback    = IotBleMqtt_DeserializeUnsuback,
    .deserialize.pingresp    = IotBleMqtt_DeserializePingresp
};

/**
 * @brief Guards access to the packet identifier counter.
 *
 * Each packet should have a unique packet identifier. This mutex ensures that only
 * one thread at a time may read the global packet identifer.
 */


/**
 * @brief Generates a monotonically increasing identifier used in  MQTT message
 *
 * @return Identifier for the MQTT message
 */
static uint16_t _nextPacketIdentifier( void );


static inline uint16_t _getNumPublishParams( const IotMqttPublishInfo_t * const pPublish )
{
   return ( pPublish->qos > 0 ) ?  ( _NUM_DEFAULT_PUBLISH_PARMAS + 1 ) : _NUM_DEFAULT_PUBLISH_PARMAS;
}

static IotSerializerError_t _serializeConnect( const IotMqttConnectInfo_t * const pConnectInfo,
                                       uint8_t* const pBuffer,
                                       size_t* const pSize );
static IotSerializerError_t _serializePublish( const IotMqttPublishInfo_t * const pPublishInfo,
                                                  uint8_t * pBuffer,
                                                  size_t  * pSize,
                                                  uint16_t packetIdentifier );
static IotSerializerError_t _serializePubAck( uint16_t packetIdentifier,
                                      uint8_t * pBuffer,
                                      size_t  * pSize );



static IotSerializerError_t _serializeSubscribe( const IotMqttSubscription_t * const pSubscriptionList,
                                               size_t subscriptionCount,
                                               uint8_t * const pBuffer,
                                               size_t * const pSize,
                                               uint16_t packetIdentifier );

static IotSerializerError_t _serializeUnSubscribe( const IotMqttSubscription_t * const pSubscriptionList,
                                               size_t subscriptionCount,
                                               uint8_t * const pBuffer,
                                               size_t * const pSize,
                                               uint16_t packetIdentifier );

static IotSerializerError_t _serializeDisconnect( uint8_t * const pBuffer,
                                                size_t * const pSize );


static IotSerializerError_t _serializePingRequest( uint8_t * const pBuffer,
                                                size_t * const pSize );

#if LIBRARY_LOG_LEVEL > AWS_IOT_LOG_NONE

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


static IotMutex_t _packetIdentifierMutex;


/* Declaration of snprintf. The header stdio.h is not included because it
 * includes conflicting symbols on some platforms. */
extern int snprintf( char * s,
                     size_t n,
                     const char * format,
                     ... );

/*-----------------------------------------------------------*/

static uint16_t _nextPacketIdentifier( void )
{
    static uint16_t nextPacketIdentifier = 1;
    uint16_t newPacketIdentifier = 0;

    /* Lock the packet identifier mutex so that only one thread may read and
         * modify nextPacketIdentifier. */
     IotMutex_Lock( &_packetIdentifierMutex );

    /* Read the next packet identifier. */
    newPacketIdentifier = nextPacketIdentifier;

    /* The next packet identifier will be greater by 2. This prevents packet
     * identifiers from ever being 0, which is not allowed by MQTT 3.1.1. Packet
     * identifiers will follow the sequence 1,3,5...65535,1,3,5... */
    nextPacketIdentifier = ( uint16_t ) ( nextPacketIdentifier + ( ( uint16_t ) 2 ) );

    /* Unlock the packet identifier mutex. */
    IotMutex_Unlock( &_packetIdentifierMutex );

    return newPacketIdentifier;
}

static IotSerializerError_t _serializeConnect( const IotMqttConnectInfo_t * const pConnectInfo,
                                       uint8_t* const pBuffer,
                                       size_t* const pSize )
{
    IotSerializerError_t error = IOT_SERIALIZER_SUCCESS;
    IotSerializerEncoderObject_t encoderObj = IOT_SERIALIZER_ENCODER_CONTAINER_INITIALIZER_STREAM ;
    IotSerializerEncoderObject_t connectMap = IOT_SERIALIZER_ENCODER_CONTAINER_INITIALIZER_MAP;
    IotSerializerScalarData_t data = { 0 };

    error = IOT_BLE_MESG_ENCODER.init( &encoderObj, pBuffer, *pSize );
    if( error == IOT_SERIALIZER_SUCCESS )
    {

        error = IOT_BLE_MESG_ENCODER.openContainer(
                &encoderObj,
                &connectMap,
                _NUM_CONNECT_PARMAS );
    }

    if( _IS_VALID_SERIALIZER_RET( error, pBuffer ) )
    {
        data.type = IOT_SERIALIZER_SCALAR_SIGNED_INT;
        data.value.u.signedInt = IOT_BLE_MQTT_MSG_TYPE_CONNECT;
        error = IOT_BLE_MESG_ENCODER.appendKeyValue( &connectMap, IOT_BLE_MQTT_MSG_TYPE, data );
    }

    if( _IS_VALID_SERIALIZER_RET( error, pBuffer ) )
    {
        data.type = IOT_SERIALIZER_SCALAR_TEXT_STRING;
        data.value.u.string.pString = ( uint8_t * ) pConnectInfo->pClientIdentifier;
        data.value.u.string.length = pConnectInfo->clientIdentifierLength;
        error = IOT_BLE_MESG_ENCODER.appendKeyValue( &connectMap, IOT_BLE_MQTT_CLIENT_ID, data );
    }
    if( _IS_VALID_SERIALIZER_RET( error, pBuffer ) )
    {
        data.type = IOT_SERIALIZER_SCALAR_TEXT_STRING;
        data.value.u.string.pString = ( uint8_t * ) clientcredentialMQTT_BROKER_ENDPOINT;
        data.value.u.string.length = strlen( clientcredentialMQTT_BROKER_ENDPOINT );
        error = IOT_BLE_MESG_ENCODER.appendKeyValue( &connectMap, IOT_BLE_MQTT_BROKER_EP, data );
    }
    if( _IS_VALID_SERIALIZER_RET( error, pBuffer ) )
    {
        data.type = IOT_SERIALIZER_SCALAR_BOOL;
        data.value.u.booleanValue = pConnectInfo->cleanSession;
        error = IOT_BLE_MESG_ENCODER.appendKeyValue( &connectMap, IOT_BLE_MQTT_CLEAN_SESSION, data );
    }
    if( _IS_VALID_SERIALIZER_RET( error, pBuffer ) )
    {
        error = IOT_BLE_MESG_ENCODER.closeContainer( &encoderObj, &connectMap );
    }

    if( _IS_VALID_SERIALIZER_RET( error, pBuffer ) )
    {
        if( pBuffer == NULL )
        {
            *pSize = IOT_BLE_MESG_ENCODER.getExtraBufferSizeNeeded( &encoderObj );
        }
        else
        {
            *pSize = IOT_BLE_MESG_ENCODER.getEncodedSize( &encoderObj, pBuffer );
        }

        IOT_BLE_MESG_ENCODER.destroy( &encoderObj );
        error = IOT_SERIALIZER_SUCCESS;

    }

    return error;
}

static IotSerializerError_t _serializePublish( const IotMqttPublishInfo_t * const pPublishInfo,
                                                  uint8_t * pBuffer,
                                                  size_t  * pSize,
                                                  uint16_t packetIdentifier )
{
    IotSerializerError_t error = IOT_SERIALIZER_SUCCESS;
    IotSerializerEncoderObject_t encoderObj = IOT_SERIALIZER_ENCODER_CONTAINER_INITIALIZER_STREAM ;
    IotSerializerEncoderObject_t publishMap = IOT_SERIALIZER_ENCODER_CONTAINER_INITIALIZER_MAP;
    IotSerializerScalarData_t data = { 0 };
    uint16_t numPublishParams = _getNumPublishParams( pPublishInfo );

    error = IOT_BLE_MESG_ENCODER.init( &encoderObj, pBuffer, *pSize );

    if( error == IOT_SERIALIZER_SUCCESS )
    {


        error = IOT_BLE_MESG_ENCODER.openContainer(
                &encoderObj,
                &publishMap,
                numPublishParams );
    }


    if( _IS_VALID_SERIALIZER_RET( error, pBuffer ) )
    {
        data.type = IOT_SERIALIZER_SCALAR_SIGNED_INT;
        data.value.u.signedInt = IOT_BLE_MQTT_MSG_TYPE_PUBLISH;
        error = IOT_BLE_MESG_ENCODER.appendKeyValue( &publishMap, IOT_BLE_MQTT_MSG_TYPE, data );
    }

    if( _IS_VALID_SERIALIZER_RET( error, pBuffer ) )
    {
        data.type = IOT_SERIALIZER_SCALAR_TEXT_STRING;
        data.value.u.string.pString = ( uint8_t * ) pPublishInfo->pTopicName;
        data.value.u.string.length = pPublishInfo->topicNameLength;
        error = IOT_BLE_MESG_ENCODER.appendKeyValue( &publishMap, IOT_BLE_MQTT_TOPIC, data );
    }

    if( _IS_VALID_SERIALIZER_RET( error, pBuffer ) )
    {

        data.type = IOT_SERIALIZER_SCALAR_SIGNED_INT;
        data.value.u.signedInt = pPublishInfo->qos;
        error = IOT_BLE_MESG_ENCODER.appendKeyValue( &publishMap, IOT_BLE_MQTT_QOS, data );
    }

    if( _IS_VALID_SERIALIZER_RET( error, pBuffer ) )
    {
        data.type = IOT_SERIALIZER_SCALAR_BYTE_STRING;
        data.value.u.string.pString = ( uint8_t * ) pPublishInfo->pPayload;
        data.value.u.string.length = pPublishInfo->payloadLength;
        error = IOT_BLE_MESG_ENCODER.appendKeyValue( &publishMap, IOT_BLE_MQTT_PAYLOAD, data );
    }


    if( _IS_VALID_SERIALIZER_RET( error, pBuffer ) )
    {
        if( pPublishInfo->qos != 0 )
        {
            data.type = IOT_SERIALIZER_SCALAR_SIGNED_INT;
            data.value.u.signedInt = packetIdentifier;
            error = IOT_BLE_MESG_ENCODER.appendKeyValue( &publishMap, IOT_BLE_MQTT_MESSAGE_ID, data );

        }
    }

    if( _IS_VALID_SERIALIZER_RET( error, pBuffer ) )
    {

        error = IOT_BLE_MESG_ENCODER.closeContainer( &encoderObj, &publishMap );
    }

    if( _IS_VALID_SERIALIZER_RET( error, pBuffer ) )
    {
        if( pBuffer == NULL )
        {
            *pSize = IOT_BLE_MESG_ENCODER.getExtraBufferSizeNeeded( &encoderObj );

        }
        else
        {
            *pSize = IOT_BLE_MESG_ENCODER.getEncodedSize( &encoderObj, pBuffer );
        }
        IOT_BLE_MESG_ENCODER.destroy( &encoderObj );
        error = IOT_SERIALIZER_SUCCESS;
    }


    return error;
}

static IotSerializerError_t _serializePubAck( uint16_t packetIdentifier,
                                      uint8_t * pBuffer,
                                      size_t  * pSize )

{
    IotSerializerError_t error = IOT_SERIALIZER_SUCCESS;
    IotSerializerEncoderObject_t encoderObj = IOT_SERIALIZER_ENCODER_CONTAINER_INITIALIZER_STREAM ;
    IotSerializerEncoderObject_t pubAckMap = IOT_SERIALIZER_ENCODER_CONTAINER_INITIALIZER_MAP;
    IotSerializerScalarData_t data = { 0 };

    error = IOT_BLE_MESG_ENCODER.init( &encoderObj, pBuffer, *pSize );

    if( error == IOT_SERIALIZER_SUCCESS )
    {

        error = IOT_BLE_MESG_ENCODER.openContainer(
                &encoderObj,
                &pubAckMap,
                _NUM_PUBACK_PARMAS );
    }

    if( _IS_VALID_SERIALIZER_RET( error, pBuffer ) )
    {
        data.type = IOT_SERIALIZER_SCALAR_SIGNED_INT;
        data.value.u.signedInt = IOT_BLE_MQTT_MSG_TYPE_PUBACK;
        error = IOT_BLE_MESG_ENCODER.appendKeyValue( &pubAckMap, IOT_BLE_MQTT_MSG_TYPE, data );
    }

    if( _IS_VALID_SERIALIZER_RET( error, pBuffer ) )
    {
        data.type = IOT_SERIALIZER_SCALAR_SIGNED_INT;
        data.value.u.signedInt = packetIdentifier;
        error = IOT_BLE_MESG_ENCODER.appendKeyValue( &pubAckMap, IOT_BLE_MQTT_MESSAGE_ID, data );
    }
    if( _IS_VALID_SERIALIZER_RET( error, pBuffer ) )
    {
        error = IOT_BLE_MESG_ENCODER.closeContainer( &encoderObj, &pubAckMap );
    }

    if( _IS_VALID_SERIALIZER_RET( error, pBuffer ) )
    {
        if( pBuffer == NULL )
        {
            *pSize = IOT_BLE_MESG_ENCODER.getExtraBufferSizeNeeded( &encoderObj );
        }
        else
        {
            *pSize = IOT_BLE_MESG_ENCODER.getEncodedSize( &encoderObj, pBuffer );
        }
        IOT_BLE_MESG_ENCODER.destroy( &encoderObj );
        error = IOT_SERIALIZER_SUCCESS;
    }

    return error;
}


static IotSerializerError_t _serializeSubscribe( const IotMqttSubscription_t * const pSubscriptionList,
                                               size_t subscriptionCount,
                                               uint8_t * const pBuffer,
                                               size_t * const pSize,
                                               uint16_t packetIdentifier )
{
    IotSerializerError_t error = IOT_SERIALIZER_SUCCESS;
    IotSerializerEncoderObject_t encoderObj = IOT_SERIALIZER_ENCODER_CONTAINER_INITIALIZER_STREAM ;
    IotSerializerEncoderObject_t subscribeMap = IOT_SERIALIZER_ENCODER_CONTAINER_INITIALIZER_MAP;
    IotSerializerEncoderObject_t subscriptionArray = IOT_SERIALIZER_ENCODER_CONTAINER_INITIALIZER_ARRAY;
    IotSerializerScalarData_t data = { 0 };
    uint16_t idx;

    error = IOT_BLE_MESG_ENCODER.init( &encoderObj, pBuffer, *pSize );

    if( error == IOT_SERIALIZER_SUCCESS )
    {
        error = IOT_BLE_MESG_ENCODER.openContainer(
                &encoderObj,
                &subscribeMap,
                _NUM_SUBACK_PARAMS );
    }

    if( _IS_VALID_SERIALIZER_RET( error, pBuffer ) )
    {
        data.type = IOT_SERIALIZER_SCALAR_SIGNED_INT;
        data.value.u.signedInt = IOT_BLE_MQTT_MSG_TYPE_SUBSCRIBE;
        error = IOT_BLE_MESG_ENCODER.appendKeyValue( &subscribeMap, IOT_BLE_MQTT_MSG_TYPE, data );
    }

    if( _IS_VALID_SERIALIZER_RET( error, pBuffer ) )
    {

        error = IOT_BLE_MESG_ENCODER.openContainerWithKey(
                &subscribeMap,
                IOT_BLE_MQTT_TOPIC_LIST,
                &subscriptionArray,
                subscriptionCount );
    }

    for( idx = 0; idx < subscriptionCount; idx++ )
    {
        if( _IS_VALID_SERIALIZER_RET( error, pBuffer ) )
        {
            data.type = IOT_SERIALIZER_SCALAR_TEXT_STRING;
            data.value.u.string.pString = ( uint8_t * ) pSubscriptionList[ idx ].pTopicFilter;
            data.value.u.string.length = pSubscriptionList[ idx ].topicFilterLength;
            error = IOT_BLE_MESG_ENCODER.append( &subscriptionArray, data );
        }
        else
        {
            break;
        }
    }

    if( _IS_VALID_SERIALIZER_RET( error, pBuffer ) )
    {
        error = IOT_BLE_MESG_ENCODER.closeContainer( &subscribeMap, &subscriptionArray );
    }

    if( _IS_VALID_SERIALIZER_RET( error, pBuffer ) )
    {

        error = IOT_BLE_MESG_ENCODER.openContainerWithKey(
                &subscribeMap,
                IOT_BLE_MQTT_QOS_LIST,
                &subscriptionArray,
                subscriptionCount );
    }


    for( idx = 0; idx < subscriptionCount; idx++ )
    {
        if( _IS_VALID_SERIALIZER_RET( error, pBuffer ) )
        {

            data.type = IOT_SERIALIZER_SCALAR_SIGNED_INT;
            data.value.u.signedInt = pSubscriptionList[ idx ].qos;
            error = IOT_BLE_MESG_ENCODER.append( &subscriptionArray, data );
        }
        else
        {
            break;
        }
    }

    if( _IS_VALID_SERIALIZER_RET( error, pBuffer ) )
    {
        error = IOT_BLE_MESG_ENCODER.closeContainer( &subscribeMap, &subscriptionArray );
    }

    if( _IS_VALID_SERIALIZER_RET( error, pBuffer ) )
    {

        data.type = IOT_SERIALIZER_SCALAR_SIGNED_INT;
        data.value.u.signedInt = packetIdentifier;
        error = IOT_BLE_MESG_ENCODER.appendKeyValue( &subscribeMap, IOT_BLE_MQTT_MESSAGE_ID, data );
    }

    if( _IS_VALID_SERIALIZER_RET( error, pBuffer ) )
    {
        error = IOT_BLE_MESG_ENCODER.closeContainer( &encoderObj, &subscribeMap );
    }

    if( _IS_VALID_SERIALIZER_RET( error, pBuffer ) )
    {
        if( pBuffer == NULL )
        {
            *pSize = IOT_BLE_MESG_ENCODER.getExtraBufferSizeNeeded( &encoderObj );
        }
        else
        {
            *pSize = IOT_BLE_MESG_ENCODER.getEncodedSize( &encoderObj, pBuffer );
        }

        IOT_BLE_MESG_ENCODER.destroy( &encoderObj );
        error = IOT_SERIALIZER_SUCCESS;
    }
    return error;
}

static IotSerializerError_t _serializeUnSubscribe( const IotMqttSubscription_t * const pSubscriptionList,
                                               size_t subscriptionCount,
                                               uint8_t * const pBuffer,
                                               size_t * const pSize,
                                               uint16_t packetIdentifier )
{
    IotSerializerError_t error = IOT_SERIALIZER_SUCCESS;
    IotSerializerEncoderObject_t encoderObj = IOT_SERIALIZER_ENCODER_CONTAINER_INITIALIZER_STREAM;
    IotSerializerEncoderObject_t subscribeMap = IOT_SERIALIZER_ENCODER_CONTAINER_INITIALIZER_MAP;
    IotSerializerEncoderObject_t subscriptionArray = IOT_SERIALIZER_ENCODER_CONTAINER_INITIALIZER_ARRAY;
    IotSerializerScalarData_t data = { 0 };
    uint16_t idx;

    error = IOT_BLE_MESG_ENCODER.init( &encoderObj, pBuffer, *pSize );

    if( error == IOT_SERIALIZER_SUCCESS )
    {

        error = IOT_BLE_MESG_ENCODER.openContainer(
                &encoderObj,
                &subscribeMap,
                _NUM_UNSUBACK_PARAMS );
    }


    if( _IS_VALID_SERIALIZER_RET( error, pBuffer ) )
    {
        data.type = IOT_SERIALIZER_SCALAR_SIGNED_INT;
        data.value.u.signedInt = IOT_BLE_MQTT_MSG_TYPE_UNSUBSCRIBE;
        error = IOT_BLE_MESG_ENCODER.appendKeyValue( &subscribeMap, IOT_BLE_MQTT_MSG_TYPE, data );
    }

    if( _IS_VALID_SERIALIZER_RET( error, pBuffer ) )
    {
        error = IOT_BLE_MESG_ENCODER.openContainerWithKey (
                &subscribeMap,
                IOT_BLE_MQTT_TOPIC_LIST,
                &subscriptionArray,
                subscriptionCount );
    }

    for( idx = 0; idx < subscriptionCount; idx++ )
    {
        if( _IS_VALID_SERIALIZER_RET( error, pBuffer ) )
        {
            data.type = IOT_SERIALIZER_SCALAR_TEXT_STRING;
            data.value.u.string.pString = ( uint8_t * ) pSubscriptionList[ idx ].pTopicFilter;
            data.value.u.string.length = pSubscriptionList[ idx ].topicFilterLength;
            error = IOT_BLE_MESG_ENCODER.append( &subscriptionArray, data );
        }
        else
        {
            break;
        }
    }

    if( _IS_VALID_SERIALIZER_RET( error, pBuffer ) )
    {
        error = IOT_BLE_MESG_ENCODER.closeContainer( &subscribeMap, &subscriptionArray );
    }

    if( _IS_VALID_SERIALIZER_RET( error, pBuffer ) )
    {
        data.type = IOT_SERIALIZER_SCALAR_SIGNED_INT;
        data.value.u.signedInt = packetIdentifier;
        error = IOT_BLE_MESG_ENCODER.appendKeyValue( &subscribeMap, IOT_BLE_MQTT_MESSAGE_ID, data );
    }

    if( _IS_VALID_SERIALIZER_RET( error, pBuffer ) )
    {
        error = IOT_BLE_MESG_ENCODER.closeContainer( &encoderObj, &subscribeMap );
    }

    if( _IS_VALID_SERIALIZER_RET( error, pBuffer ) )
    {
        if( pBuffer == NULL )
        {
            *pSize = IOT_BLE_MESG_ENCODER.getExtraBufferSizeNeeded( &encoderObj );

        }
        else
        {
            *pSize = IOT_BLE_MESG_ENCODER.getEncodedSize( &encoderObj, pBuffer );
        }
        IOT_BLE_MESG_ENCODER.destroy( &encoderObj );
        error = IOT_SERIALIZER_SUCCESS;
    }

    return error;
}

static IotSerializerError_t _serializeDisconnect( uint8_t * const pBuffer,
                                                size_t * const pSize )
{
    IotSerializerError_t error = IOT_SERIALIZER_SUCCESS;
    IotSerializerEncoderObject_t encoderObj = IOT_SERIALIZER_ENCODER_CONTAINER_INITIALIZER_STREAM;
    IotSerializerEncoderObject_t disconnectMap = IOT_SERIALIZER_ENCODER_CONTAINER_INITIALIZER_MAP;
    IotSerializerScalarData_t data = { 0 };

    error = IOT_BLE_MESG_ENCODER.init( &encoderObj, pBuffer, *pSize );

    if( error == IOT_SERIALIZER_SUCCESS )
    {
        error = IOT_BLE_MESG_ENCODER.openContainer(
                &encoderObj,
                &disconnectMap,
                _NUM_DISCONNECT_PARAMS );
    }

    if( _IS_VALID_SERIALIZER_RET( error, pBuffer ) )
    {
        data.type = IOT_SERIALIZER_SCALAR_SIGNED_INT;
        data.value.u.signedInt = IOT_BLE_MQTT_MSG_TYPE_DISCONNECT;
        error = IOT_BLE_MESG_ENCODER.appendKeyValue( &disconnectMap, IOT_BLE_MQTT_MSG_TYPE, data );
    }

    if( _IS_VALID_SERIALIZER_RET( error, pBuffer ) )
    {
        error = IOT_BLE_MESG_ENCODER.closeContainer( &encoderObj, &disconnectMap );
    }

    if( _IS_VALID_SERIALIZER_RET( error, pBuffer ) )
    {
        if( pBuffer == NULL )
        {
            *pSize = IOT_BLE_MESG_ENCODER.getExtraBufferSizeNeeded( &encoderObj );
        }
        else
        {
            *pSize = IOT_BLE_MESG_ENCODER.getEncodedSize( &encoderObj, pBuffer );
        }
        IOT_BLE_MESG_ENCODER.destroy( &encoderObj );
        error = IOT_SERIALIZER_SUCCESS;
    }

    return error;
}

static IotSerializerError_t _serializePingRequest( uint8_t * const pBuffer,
                                                   size_t * const pSize )
{
    IotSerializerError_t error = IOT_SERIALIZER_SUCCESS;
    IotSerializerEncoderObject_t encoderObj = IOT_SERIALIZER_ENCODER_CONTAINER_INITIALIZER_STREAM;
    IotSerializerEncoderObject_t pingRequest = IOT_SERIALIZER_ENCODER_CONTAINER_INITIALIZER_MAP;
    IotSerializerScalarData_t data = { 0 };

    error = IOT_BLE_MESG_ENCODER.init( &encoderObj, pBuffer, *pSize );

    if( error == IOT_SERIALIZER_SUCCESS )
    {
        error = IOT_BLE_MESG_ENCODER.openContainer(
                &encoderObj,
                &pingRequest,
                _NUM_PINGREQUEST_PARAMS );
    }

    if( _IS_VALID_SERIALIZER_RET( error, pBuffer ) )
    {
        data.type = IOT_SERIALIZER_SCALAR_SIGNED_INT;
         data.value.u.signedInt = IOT_BLE_MQTT_MSG_TYPE_PINGREQ;
        error = IOT_BLE_MESG_ENCODER.appendKeyValue( &pingRequest, IOT_BLE_MQTT_MSG_TYPE, data );
    }

    if( _IS_VALID_SERIALIZER_RET( error, pBuffer ) )
    {
        error = IOT_BLE_MESG_ENCODER.closeContainer( &encoderObj, &pingRequest );
    }

    if( _IS_VALID_SERIALIZER_RET( error, pBuffer ) )
    {
        if( pBuffer == NULL )
        {
            *pSize = IOT_BLE_MESG_ENCODER.getExtraBufferSizeNeeded( &encoderObj );
        }
        else
        {
            *pSize = IOT_BLE_MESG_ENCODER.getEncodedSize( &encoderObj, pBuffer );
        }
        IOT_BLE_MESG_ENCODER.destroy( &encoderObj );
        error = IOT_SERIALIZER_SUCCESS;
    }

    return error;
}


bool IotBleMqtt_InitSerialize( void )
{
	/* Create the packet identifier mutex. */
	return IotMutex_Create( &_packetIdentifierMutex, false );
}

void IotBleMqtt_CleanupSerialize( void )
{
	/* Destroy the packet identifier mutex */
	IotMutex_Destroy( &_packetIdentifierMutex );
}


IotMqttError_t IotBleMqtt_SerializeConnect( const IotMqttConnectInfo_t * const pConnectInfo,
                                                           uint8_t ** const pConnectPacket,
                                                           size_t * const pPacketSize )
{
	uint8_t * pBuffer = NULL;
	size_t bufLen = 0;
	IotSerializerError_t error;
	IotMqttError_t ret = IOT_MQTT_SUCCESS;


	error = _serializeConnect( pConnectInfo, NULL, &bufLen );
	if( error != IOT_SERIALIZER_SUCCESS )
	{
	    IotLogError( "Failed to find length of serialized CONNECT message, error = %d", error );
	    ret = IOT_MQTT_BAD_PARAMETER;
	}

	if( ret == IOT_MQTT_SUCCESS )
	{

	    pBuffer = IotMqtt_MallocMessage( bufLen );

	    /* If Memory cannot be allocated log an error and return */
	    if( pBuffer == NULL )
	    {
	        IotLogError( "Failed to allocate memory for CONNECT packet." );
	        ret =  IOT_MQTT_NO_MEMORY;
	    }
	}

	if( ret == IOT_MQTT_SUCCESS )
	{
	    error = _serializeConnect( pConnectInfo, pBuffer, &bufLen );
	    if( error != IOT_SERIALIZER_SUCCESS )
	    {
	        IotLogError( "Failed to serialize CONNECT message, error = %d", error );
	        ret = IOT_MQTT_BAD_PARAMETER;
	    }
	}

	if( ret == IOT_MQTT_SUCCESS )
	{
	    *pConnectPacket = pBuffer;
	    *pPacketSize = bufLen;
	}
	else
	{
	    *pConnectPacket = NULL;
	    *pPacketSize = 0;
	    if( pBuffer != NULL )
	    {
	        IotMqtt_FreeMessage( pBuffer );
	    }
	}

    return ret;
}

IotMqttError_t IotBleMqtt_DeserializeConnack( _mqttPacket_t * pConnack )
{

    IotSerializerDecoderObject_t decoderObj = { 0 }, decoderValue = { 0 };
    IotSerializerError_t error;
    IotMqttError_t ret = IOT_MQTT_SUCCESS;
    int64_t respCode = 0L;

    error = IOT_BLE_MESG_DECODER.init( &decoderObj, ( uint8_t * ) pConnack->pRemainingData, pConnack->remainingLength );
    if( ( error != IOT_SERIALIZER_SUCCESS )
            || ( decoderObj.type != IOT_SERIALIZER_CONTAINER_MAP ) )
    {
        IotLogError( "Malformed CONNACK, decoding the packet failed, decoder error = %d, type: %d", error, decoderObj.type );
        ret = IOT_MQTT_BAD_RESPONSE;
    }


    if( ret == IOT_MQTT_SUCCESS )
    {

        error = IOT_BLE_MESG_DECODER.find( &decoderObj, IOT_BLE_MQTT_STATUS, &decoderValue );
        if ( ( error != IOT_SERIALIZER_SUCCESS ) ||
                ( decoderValue.type != IOT_SERIALIZER_SCALAR_SIGNED_INT ) )
        {
            IotLogError( "Invalid CONNACK, response code decode failed, error = %d, decoded value type = %d", error, decoderValue.type );
            ret = IOT_MQTT_BAD_RESPONSE;
        }
        else
        {

            respCode =  decoderValue.u.value.u.signedInt;
            if( ( respCode != IOT_BLE_MQTT_STATUS_CONNECTING )
                    && ( respCode != IOT_BLE_MQTT_STATUS_CONNECTED ) )
            {
                ret = IOT_MQTT_SERVER_REFUSED;
            }
        }
    }

    IOT_BLE_MESG_DECODER.destroy( &decoderObj );

    return ret;
}

IotMqttError_t IotBleMqtt_SerializePublish( const IotMqttPublishInfo_t * const pPublishInfo,
                                                  uint8_t ** const pPublishPacket,
                                                  size_t * const pPacketSize,
                                                  uint16_t * const pPacketIdentifier,
												  uint8_t ** pPacketIdentifierHigh )
{

    uint8_t * pBuffer = NULL;
    size_t bufLen = 0;
    uint16_t usPacketIdentifier = 0;
    IotSerializerError_t error;
    IotMqttError_t ret = IOT_MQTT_SUCCESS;

    (void)pPacketIdentifierHigh;

    if( pPublishInfo->qos != 0 )
    {
        usPacketIdentifier = _nextPacketIdentifier();
    }

    error = _serializePublish( pPublishInfo, NULL, &bufLen, usPacketIdentifier );
    if( error != IOT_SERIALIZER_SUCCESS  )
    {
        IotLogError( "Failed to find size of serialized PUBLISH message, error = %d", error );
        ret = IOT_MQTT_BAD_PARAMETER;
    }

    if( ret == IOT_MQTT_SUCCESS )
    {

        pBuffer = IotMqtt_MallocMessage( bufLen );
        /* If Memory cannot be allocated log an error and return */
        if( pBuffer == NULL )
        {
            IotLogError( "Failed to allocate memory for PUBLISH packet." );
            ret =  IOT_MQTT_NO_MEMORY;
        }
    }

    if( ret == IOT_MQTT_SUCCESS )
    {

        error = _serializePublish( pPublishInfo, pBuffer, &bufLen, usPacketIdentifier );
        if( error != IOT_SERIALIZER_SUCCESS )
        {
            IotLogError( "Failed to serialize PUBLISH message, error = %d", error );
            ret = IOT_MQTT_BAD_PARAMETER;
        }
    }

    if( ret == IOT_MQTT_SUCCESS )
    {
        *pPublishPacket = pBuffer;
        *pPacketSize = bufLen;
        *pPacketIdentifier = usPacketIdentifier;
    }
    else
    {
        if( pBuffer != NULL )
        {
            IotMqtt_FreeMessage( pBuffer );
        }
        *pPublishPacket = NULL;
        *pPacketSize = 0;
    }

    return ret;
}

void IotBleMqtt_PublishSetDup( uint8_t * const pPublishPacket, uint8_t * pPacketIdentifierHigh, uint16_t * const pNewPacketIdentifier  )
{
	/** TODO: Currently DUP flag is not supported by BLE SDKs **/
}

IotMqttError_t IotBleMqtt_DeserializePublish( _mqttPacket_t * pPublish )
{

    IotSerializerDecoderObject_t decoderObj = { 0 }, decoderValue = { 0 };
    IotSerializerError_t xSerializerRet;
    IotMqttError_t ret = IOT_MQTT_SUCCESS;

    xSerializerRet = IOT_BLE_MESG_DECODER.init( &decoderObj, ( uint8_t * ) pPublish->pRemainingData, pPublish->remainingLength );
    if ( (xSerializerRet != IOT_SERIALIZER_SUCCESS ) ||
            ( decoderObj.type != IOT_SERIALIZER_CONTAINER_MAP ) )
    {

        IotLogError( "Decoding PUBLISH packet failed, decoder error = %d, object type = %d", xSerializerRet, decoderObj.type );
        ret = IOT_MQTT_BAD_RESPONSE;
    }

    if( ret == IOT_MQTT_SUCCESS )
    {
        xSerializerRet = IOT_BLE_MESG_DECODER.find( &decoderObj, IOT_BLE_MQTT_QOS, &decoderValue );
        if ( ( xSerializerRet != IOT_SERIALIZER_SUCCESS ) ||
                 ( decoderValue.type != IOT_SERIALIZER_SCALAR_SIGNED_INT ) )
        {
            IotLogError( "QOS Value decode failed, error = %d, decoded value type = %d", xSerializerRet, decoderValue.type );
            ret = IOT_MQTT_BAD_RESPONSE;
        }
        else
        {
        	pPublish->u.pIncomingPublish->u.publish.publishInfo.qos = decoderValue.u.value.u.signedInt;
        }
    }

    if( ret == IOT_MQTT_SUCCESS )
    {
        decoderValue.u.value.u.string.pString = NULL;
        decoderValue.u.value.u.string.length = 0;
        xSerializerRet = IOT_BLE_MESG_DECODER.find( &decoderObj, IOT_BLE_MQTT_TOPIC, &decoderValue );

        if( ( xSerializerRet != IOT_SERIALIZER_SUCCESS ) ||
                ( decoderValue.type != IOT_SERIALIZER_SCALAR_TEXT_STRING ) )
        {
            IotLogError( "Topic value decode failed, error = %d", xSerializerRet );
            ret = IOT_MQTT_BAD_RESPONSE;
        }
        else
        {
        	pPublish->u.pIncomingPublish->u.publish.publishInfo.pTopicName = ( const char* ) decoderValue.u.value.u.string.pString;
        	pPublish->u.pIncomingPublish->u.publish.publishInfo.topicNameLength = decoderValue.u.value.u.string.length;
        }
    }

    if( ret == IOT_MQTT_SUCCESS )
    {
        decoderValue.u.value.u.string.pString = NULL;
        decoderValue.u.value.u.string.length = 0;
        xSerializerRet = IOT_BLE_MESG_DECODER.find( &decoderObj, IOT_BLE_MQTT_PAYLOAD, &decoderValue );

        if( ( xSerializerRet != IOT_SERIALIZER_SUCCESS ) ||
                ( decoderValue.type != IOT_SERIALIZER_SCALAR_BYTE_STRING ) )
        {
            IotLogError( "Payload value decode failed, error = %d", xSerializerRet );
            ret = IOT_MQTT_BAD_RESPONSE;
        }
        else
        {
        	pPublish->u.pIncomingPublish->u.publish.publishInfo.pPayload = ( const char* ) decoderValue.u.value.u.string.pString;
        	pPublish->u.pIncomingPublish->u.publish.publishInfo.payloadLength = decoderValue.u.value.u.string.length;
        }
    }

    if( ret == IOT_MQTT_SUCCESS )
    {
        if( pPublish->u.pIncomingPublish->u.publish.publishInfo.qos != 0 )
        {
            xSerializerRet = IOT_BLE_MESG_DECODER.find( &decoderObj, IOT_BLE_MQTT_MESSAGE_ID, &decoderValue );
            if ( ( xSerializerRet != IOT_SERIALIZER_SUCCESS ) ||
                    ( decoderValue.type != IOT_SERIALIZER_SCALAR_SIGNED_INT ) )
            {
                IotLogError( "Message identifier decode failed, error = %d, decoded value type = %d", xSerializerRet, decoderValue.type );
                ret = IOT_MQTT_BAD_RESPONSE;
            }
            else
            {
            	pPublish->packetIdentifier  = ( uint16_t ) decoderValue.u.value.u.signedInt;
            }
        }
    }

    if( ret == IOT_MQTT_SUCCESS  )
    {
    	pPublish->u.pIncomingPublish->u.publish.publishInfo.retain = false;
    }

    IOT_BLE_MESG_DECODER.destroy( &decoderObj );

    return ret;
}

IotMqttError_t IotBleMqtt_SerializePuback( uint16_t packetIdentifier,
                                                      uint8_t ** const pPubackPacket,
                                                      size_t * const pPacketSize )
{
    uint8_t * pBuffer = NULL;
    size_t bufLen = 0;
    IotSerializerError_t error;
    IotMqttError_t ret = IOT_MQTT_SUCCESS;

    error = _serializePubAck( packetIdentifier, NULL, &bufLen );

    if( error != IOT_SERIALIZER_SUCCESS )
    {
        IotLogError( "Failed to find size of serialized PUBACK message, error = %d", error );
        ret = IOT_MQTT_BAD_PARAMETER;
    }


    if( ret == IOT_MQTT_SUCCESS )
    {
        pBuffer = IotMqtt_MallocMessage( bufLen );

        /* If Memory cannot be allocated log an error and return */
        if( pBuffer == NULL )
        {
            IotLogError( "Failed to allocate memory for PUBACK packet, packet identifier = %d", packetIdentifier );
            ret = IOT_MQTT_NO_MEMORY;
        }
    }


    if( ret == IOT_MQTT_SUCCESS )
    {
        error = _serializePubAck( packetIdentifier, pBuffer, &bufLen );

        if( error != IOT_SERIALIZER_SUCCESS )
        {
            IotLogError( "Failed to find size of serialized PUBACK message, error = %d", error );
            ret = IOT_MQTT_BAD_PARAMETER;
        }
    }


    if( ret == IOT_MQTT_SUCCESS )
    {
        *pPubackPacket = pBuffer;
        *pPacketSize = bufLen;
    }
    else
    {
        if( pBuffer != NULL )
        {
            IotMqtt_FreeMessage( pBuffer );
        }

        *pPubackPacket = NULL;
        *pPacketSize = 0;
    }

	return ret;

}

IotMqttError_t IotBleMqtt_DeserializePuback( _mqttPacket_t * pPuback )
{

    IotSerializerDecoderObject_t decoderObj = { 0 }, decoderValue = { 0 };
    IotSerializerError_t error;
    IotMqttError_t ret = IOT_MQTT_SUCCESS;

    error = IOT_BLE_MESG_DECODER.init( &decoderObj, ( uint8_t * ) pPuback->pRemainingData, pPuback->remainingLength );

    if ( ( error != IOT_SERIALIZER_SUCCESS )
            || ( decoderObj.type != IOT_SERIALIZER_CONTAINER_MAP ) )
    {
        IotLogError( "Malformed PUBACK, decoding the packet failed, decoder error = %d, object type: %d", error, decoderObj.type );
        ret = IOT_MQTT_BAD_RESPONSE;
    }


    if( ret == IOT_MQTT_SUCCESS )
    {

        error = IOT_BLE_MESG_DECODER.find( &decoderObj, IOT_BLE_MQTT_MESSAGE_ID, &decoderValue );

        if ( ( error != IOT_SERIALIZER_SUCCESS ) ||
                ( decoderValue.type != IOT_SERIALIZER_SCALAR_SIGNED_INT ) )
        {
            IotLogError( "Message ID decode failed, error = %d, decoded value type = %d", error, decoderValue.type );
            ret = IOT_MQTT_BAD_RESPONSE;
        }
        else
        {
        	pPuback->packetIdentifier = ( uint16_t ) decoderValue.u.value.u.signedInt;
        }
    }

    IOT_BLE_MESG_DECODER.destroy( &decoderObj );

    return ret;

}

IotMqttError_t IotBleMqtt_SerializeSubscribe( const IotMqttSubscription_t * const pSubscriptionList,
                                                         size_t subscriptionCount,
                                                         uint8_t ** const pSubscribePacket,
                                                         size_t * const pPacketSize,
                                                         uint16_t * const pPacketIdentifier )
{
    uint8_t * pBuffer = NULL;
    size_t bufLen = 0;
    uint16_t usPacketIdentifier = 0;
    IotSerializerError_t error;
    IotMqttError_t ret = IOT_MQTT_SUCCESS;

    usPacketIdentifier = _nextPacketIdentifier();

    error = _serializeSubscribe( pSubscriptionList, subscriptionCount, NULL, &bufLen, usPacketIdentifier );
    if( error != IOT_SERIALIZER_SUCCESS )
    {
        IotLogError( "Failed to find serialized length of SUBSCRIBE message, error = %d", error );
        ret = IOT_MQTT_BAD_PARAMETER;
    }

    if( ret == IOT_MQTT_SUCCESS )
    {
        pBuffer = IotMqtt_MallocMessage( bufLen );

        /* If Memory cannot be allocated log an error and return */
        if( pBuffer == NULL )
        {
            IotLogError( "Failed to allocate memory for SUBSCRIBE message." );
            ret = IOT_MQTT_NO_MEMORY;
        }
    }

    if( ret == IOT_MQTT_SUCCESS )
    {
        error = _serializeSubscribe( pSubscriptionList, subscriptionCount, pBuffer, &bufLen, usPacketIdentifier );
        if( error != IOT_SERIALIZER_SUCCESS )
        {
            IotLogError( "Failed to serialize SUBSCRIBE message, error = %d", error );
            ret = IOT_MQTT_BAD_PARAMETER;
        }
    }

    if( ret == IOT_MQTT_SUCCESS )
    {
        *pSubscribePacket = pBuffer;
        *pPacketSize = bufLen;
        *pPacketIdentifier = usPacketIdentifier;
    }
    else
    {
        if( pBuffer != NULL )
        {
            IotMqtt_FreeMessage( pBuffer );
        }

        *pSubscribePacket = NULL;
        *pPacketSize = 0;
    }

    return ret;
}

IotMqttError_t IotBleMqtt_DeserializeSuback( _mqttPacket_t * pSuback )
{

    IotSerializerDecoderObject_t decoderObj = { 0 }, decoderValue = { 0 };
    IotSerializerError_t error;
    int64_t subscriptionStatus;
    IotMqttError_t ret = IOT_MQTT_SUCCESS;

    error = IOT_BLE_MESG_DECODER.init( &decoderObj, ( uint8_t * ) pSuback->pRemainingData, pSuback->remainingLength );

    if ( ( error != IOT_SERIALIZER_SUCCESS )
            || ( decoderObj.type != IOT_SERIALIZER_CONTAINER_MAP ) )
    {
        IotLogError( "Malformed SUBACK, decoding the packet failed, decoder error = %d, type: %d", error, decoderObj.type );
        ret = IOT_MQTT_BAD_RESPONSE;
    }

    if( ret == IOT_MQTT_SUCCESS )
    {

        error = IOT_BLE_MESG_DECODER.find( &decoderObj, IOT_BLE_MQTT_MESSAGE_ID, &decoderValue );
        if ( ( error != IOT_SERIALIZER_SUCCESS ) ||
                ( decoderValue.type != IOT_SERIALIZER_SCALAR_SIGNED_INT ) )
        {
            IotLogError( "Message ID decode failed, error = %d, decoded value type = %d", error, decoderValue.type );
            ret = IOT_MQTT_BAD_RESPONSE;
        }
        else
        {
        	pSuback->packetIdentifier = ( uint16_t ) decoderValue.u.value.u.signedInt;
        }
    }

    if( ret == IOT_MQTT_SUCCESS )
    {
        error = IOT_BLE_MESG_DECODER.find( &decoderObj, IOT_BLE_MQTT_STATUS, &decoderValue );
        if ( ( error != IOT_SERIALIZER_SUCCESS ) ||
                ( decoderValue.type != IOT_SERIALIZER_SCALAR_SIGNED_INT ) )
        {
            IotLogError( "Status code decode failed, error = %d, decoded value type = %d", error, decoderValue.type );
            ret = IOT_MQTT_BAD_RESPONSE;
        }
        else
        {
            subscriptionStatus = ( uint16_t ) decoderValue.u.value.u.signedInt;
            switch( subscriptionStatus )
            {
                case 0x00:
                case 0x01:
                case 0x02:
                    IotLog( IOT_LOG_DEBUG,
                               &_logHideAll,
                               "Topic accepted, max QoS %hhu.", subscriptionStatus );
                    ret = IOT_MQTT_SUCCESS;
                    break;
                case 0x80:
                    IotLog( IOT_LOG_DEBUG,
                               &_logHideAll,
                               "Topic refused." );

                    /* Remove a rejected subscription from the subscription manager. */
                    _IotMqtt_RemoveSubscriptionByPacket(
                    		pSuback->u.pMqttConnection,
							pSuback->packetIdentifier,
                            0 );
                    ret = IOT_MQTT_SERVER_REFUSED;
                    break;
                default:
                    IotLog( IOT_LOG_DEBUG,
                               &_logHideAll,
                               "Bad SUBSCRIBE status %hhu.", subscriptionStatus );

                    ret = IOT_MQTT_BAD_RESPONSE;
                    break;
            }
        }

    }

    IOT_BLE_MESG_DECODER.destroy( &decoderObj );

	return ret;
}

IotMqttError_t IotBleMqtt_SerializeUnsubscribe( const IotMqttSubscription_t * const pSubscriptionList,
		size_t subscriptionCount,
		uint8_t ** const pUnsubscribePacket,
		size_t * const pPacketSize,
		uint16_t * const pPacketIdentifier )
{

	uint8_t * pBuffer = NULL;
    size_t bufLen = 0;
    uint16_t usPacketIdentifier = 0;
    IotSerializerError_t error;
    IotMqttError_t ret = IOT_MQTT_SUCCESS;

    usPacketIdentifier = _nextPacketIdentifier();

    error = _serializeUnSubscribe( pSubscriptionList, subscriptionCount, NULL, &bufLen, usPacketIdentifier );
    if( error != IOT_SERIALIZER_SUCCESS )
    {
        IotLogError( "Failed to find serialized length of UNSUBSCRIBE message, error = %d", error );
        ret = IOT_MQTT_BAD_PARAMETER;
    }

    if( ret == IOT_MQTT_SUCCESS )
    {
        pBuffer = IotMqtt_MallocMessage( bufLen );

        /* If Memory cannot be allocated log an error and return */
        if( pBuffer == NULL )
        {
            IotLogError( "Failed to allocate memory for UNSUBSCRIBE message." );
            ret = IOT_MQTT_NO_MEMORY;
        }
    }

    if( ret == IOT_MQTT_SUCCESS )
    {
        error = _serializeUnSubscribe( pSubscriptionList, subscriptionCount, pBuffer, &bufLen, usPacketIdentifier );
        if( error != IOT_SERIALIZER_SUCCESS )
        {
            IotLogError( "Failed to serialize UNSUBSCRIBE message, error = %d", error );
            ret = IOT_MQTT_BAD_PARAMETER;
        }
    }

    if( ret == IOT_MQTT_SUCCESS )
    {
        *pUnsubscribePacket = pBuffer;
        *pPacketSize = bufLen;
        *pPacketIdentifier = usPacketIdentifier;
    }
    else
    {
        if( pBuffer != NULL )
        {
            IotMqtt_FreeMessage( pBuffer );
        }

        *pUnsubscribePacket = NULL;
        *pPacketSize = 0;
    }

    return ret;
}

IotMqttError_t IotBleMqtt_DeserializeUnsuback( _mqttPacket_t * pUnsuback )
{
    IotSerializerDecoderObject_t decoderObj = { 0 }, decoderValue = { 0 };
    IotSerializerError_t error;
    IotMqttError_t ret = IOT_MQTT_SUCCESS;

    error = IOT_BLE_MESG_DECODER.init( &decoderObj, ( uint8_t * ) pUnsuback->pRemainingData, pUnsuback->remainingLength );
    if( ( error != IOT_SERIALIZER_SUCCESS )
            || ( decoderObj.type != IOT_SERIALIZER_CONTAINER_MAP ) )
    {
        IotLogError( "Malformed UNSUBACK, decoding the packet failed, decoder error = %d, type:%d ", error, decoderObj.type );
        ret = IOT_MQTT_BAD_RESPONSE;
    }

    if( ret == IOT_MQTT_SUCCESS )
    {
        error = IOT_BLE_MESG_DECODER.find( &decoderObj, IOT_BLE_MQTT_MESSAGE_ID, &decoderValue );
        if ( ( error != IOT_SERIALIZER_SUCCESS ) ||
                ( decoderValue.type != IOT_SERIALIZER_SCALAR_SIGNED_INT ) )
        {
            IotLogError( "UNSUBACK Message identifier decode failed, error = %d, decoded value type = %d", error, decoderValue.type );
            ret = IOT_MQTT_BAD_RESPONSE;

        }
        else
        {
        	pUnsuback->packetIdentifier = ( uint16_t ) decoderValue.u.value.u.signedInt;
        }
    }

    IOT_BLE_MESG_DECODER.destroy( &decoderObj );

	return IOT_MQTT_SUCCESS;
}

IotMqttError_t IotBleMqtt_SerializeDisconnect( uint8_t ** const pDisconnectPacket,
                                                          size_t * const pPacketSize )
{
	uint8_t *pBuffer = NULL;
	size_t bufLen = 0;
	IotSerializerError_t error;
	IotMqttError_t ret = IOT_MQTT_SUCCESS;

	error = _serializeDisconnect( NULL, &bufLen);
	if( error != IOT_SERIALIZER_SUCCESS )
	{
	    IotLogError( "Failed to find serialized length of DISCONNECT message, error = %d", error );
	    ret = IOT_MQTT_BAD_PARAMETER;
	}

	if( ret == IOT_MQTT_SUCCESS )
	{
	    pBuffer = IotMqtt_MallocMessage( bufLen );

	    /* If Memory cannot be allocated log an error and return */
	    if( pBuffer == NULL )
	    {
	        IotLogError( "Failed to allocate memory for DISCONNECT message." );
	        ret = IOT_MQTT_NO_MEMORY;
	    }
	}


	if( ret == IOT_MQTT_SUCCESS )
	{
	    error = _serializeDisconnect( pBuffer, &bufLen );
	    if( error != IOT_SERIALIZER_SUCCESS )
	    {
	        IotLogError( "Failed to serialize DISCONNECT message, error = %d", error );
	        ret = IOT_MQTT_BAD_PARAMETER;
	    }
	}

	if( ret == IOT_MQTT_SUCCESS )
	{
	    *pDisconnectPacket = pBuffer;
	    *pPacketSize = bufLen;
	}
	else
	{
	    if( pBuffer != NULL )
	    {
	        IotMqtt_FreeMessage( pBuffer );
	    }

	    *pDisconnectPacket = NULL;
	    *pPacketSize = 0;
	}

	return ret;
}

size_t IotBleMqtt_GetRemainingLength ( void * pNetworkConnection,
                                       const IotNetworkInterface_t * pNetworkInterface )
{
    const uint8_t *pBuffer;
    size_t length;

    IotBleDataTransfer_PeekReceiveBuffer( *( IotBleDataTransferChannel_t ** ) ( pNetworkConnection ), &pBuffer, &length );

    return length;
}


uint8_t IotBleMqtt_GetPacketType( void * pNetworkConnection, const IotNetworkInterface_t * pNetworkInterface )
{

    IotSerializerDecoderObject_t decoderObj = { 0 }, decoderValue = { 0 };
    IotSerializerError_t error;
    uint8_t value = 0xFF, packetType = _INVALID_MQTT_PACKET_TYPE;
    const uint8_t *pBuffer;
    size_t length;

    IotBleDataTransfer_PeekReceiveBuffer( *( IotBleDataTransferChannel_t ** ) ( pNetworkConnection ), &pBuffer, &length );

    error = IOT_BLE_MESG_DECODER.init( &decoderObj, pBuffer, length );

    if( ( error == IOT_SERIALIZER_SUCCESS )
            && ( decoderObj.type == IOT_SERIALIZER_CONTAINER_MAP ) )
    {

        error = IOT_BLE_MESG_DECODER.find( &decoderObj, IOT_BLE_MQTT_MSG_TYPE, &decoderValue );

        if ( ( error == IOT_SERIALIZER_SUCCESS ) &&
                ( decoderValue.type == IOT_SERIALIZER_SCALAR_SIGNED_INT ) )
        {
            value = ( uint16_t ) decoderValue.u.value.u.signedInt;

            /** Left shift by 4 bits as MQTT library expects packet type to be upper 4 bits **/
            packetType = value << 4;
        }
        else
        {
            IotLogError( "Packet type decode failed, error = %d, decoded value type = %d", error, decoderValue.type );
        }
    }
    else
    {
        IotLogError( "Decoding the packet failed, decoder error = %d, type = %d", error, decoderObj.type );
    }

    IOT_BLE_MESG_DECODER.destroy( &decoderObj );

    return packetType;
}

IotMqttError_t IotBleMqtt_SerializePingreq( uint8_t ** const pPingreqPacket,
                                            size_t * const pPacketSize )
{
    uint8_t *pBuffer = NULL;
	size_t bufLen = 0;
	IotSerializerError_t error;
	IotMqttError_t ret = IOT_MQTT_SUCCESS;

	error = _serializePingRequest( NULL, &bufLen);
	if( error != IOT_SERIALIZER_SUCCESS )
	{
	    IotLogError( "Failed to find serialized length of DISCONNECT message, error = %d", error );
	    ret = IOT_MQTT_BAD_PARAMETER;
	}

	if( ret == IOT_MQTT_SUCCESS )
	{
	    pBuffer = IotMqtt_MallocMessage( bufLen );

	    /* If Memory cannot be allocated log an error and return */
	    if( pBuffer == NULL )
	    {
	        IotLogError( "Failed to allocate memory for DISCONNECT message." );
	        ret = IOT_MQTT_NO_MEMORY;
	    }
	}

	if( ret == IOT_MQTT_SUCCESS )
	{
	    error = _serializePingRequest( pBuffer, &bufLen );
	    if( error != IOT_SERIALIZER_SUCCESS )
	    {
	        IotLogError( "Failed to serialize DISCONNECT message, error = %d", error );
	        ret = IOT_MQTT_BAD_PARAMETER;
	    }
	}

	if( ret == IOT_MQTT_SUCCESS )
	{
	    *pPingreqPacket = pBuffer;
	    *pPacketSize = bufLen;
	}
	else
	{
	    if( pBuffer != NULL )
	    {
	        IotMqtt_FreeMessage( pBuffer );
	    }

	    *pPingreqPacket = NULL;
	    *pPacketSize = 0;
	}

    return ret;

}

IotMqttError_t IotBleMqtt_DeserializePingresp( _mqttPacket_t * pPingresp )
{
    /* Ping Response for BLE contains only packet type field in CBOR, which is already decoded
       in IotBleMqtt_GetPacketType() function. Returning IOT_MQTT_SUCCESS. */
    return IOT_MQTT_SUCCESS;
}

void IotBleMqtt_FreePacket( uint8_t * pPacket )
{
    IotMqtt_FreeMessage( pPacket );
}
