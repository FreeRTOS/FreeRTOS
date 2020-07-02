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
 * @file iot_mqtt_network.c
 * @brief Implements functions involving transport layer connections.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <string.h>

/* MQTT internal include. */
#include "private/iot_mqtt_internal.h"

/* Platform layer includes. */
#include "platform/iot_threads.h"

/* Atomics include. */
#include "iot_atomic.h"

/*-----------------------------------------------------------*/

/**
 * @brief Check if an incoming packet type is valid.
 *
 * @param[in] packetType The packet type to check.
 *
 * @return `true` if the packet type is valid; `false` otherwise.
 */
static bool _incomingPacketValid( uint8_t packetType );

/**
 * @brief Allocate space for an incoming MQTT packet received from the network.
 *
 * @param[in] pNetworkConnection Network connection to be used for receive.
 * @param[in] pMqttConnection The associated MQTT connection.
 * @param[out] pIncomingPacket Output parameter for the incoming packet.
 *
 * @return #IOT_MQTT_SUCCESS, #IOT_MQTT_NO_MEMORY or #IOT_MQTT_BAD_RESPONSE.
 */
static IotMqttError_t _allocateAndReceivePacket( IotNetworkConnection_t pNetworkConnection,
                                                 const _mqttConnection_t * pMqttConnection,
                                                 _mqttPacket_t * pIncomingPacket );

/**
 * @brief Get an incoming MQTT packet from the network.
 *
 * @param[in] pNetworkConnection Network connection to use for receive, which
 * may be different from the network connection associated with the MQTT connection.
 * @param[in] pMqttConnection The associated MQTT connection.
 * @param[out] pIncomingPacket Output parameter for the incoming packet.
 *
 * @return #IOT_MQTT_SUCCESS, #IOT_MQTT_NO_MEMORY or #IOT_MQTT_BAD_RESPONSE.
 */
static IotMqttError_t _getIncomingPacket( IotNetworkConnection_t pNetworkConnection,
                                          const _mqttConnection_t * pMqttConnection,
                                          _mqttPacket_t * pIncomingPacket );

/**
 * @brief Deserialize a CONNACK, PUBACK, SUBACK, or UNSUBACK packet.
 *
 * @param[in] pMqttConnection The associated MQTT connection.
 * @param[in] pIncomingPacket The packet received from the network.
 * @param[in] _deserializer The deserialization function for the packet.
 * @param[in] opType The type of operation corresponding to the packet.
 * @param[in] pPacketIdentifier Address of incoming packet's packet identifier;
 * `NULL` for a CONNACK.
 *
 * @return #IOT_MQTT_SUCCESS, #IOT_MQTT_BAD_RESPONSE, or #IOT_MQTT_SERVER_REFUSED.
 */
static IotMqttError_t _deserializeAck( _mqttConnection_t * pMqttConnection,
                                       _mqttPacket_t * pIncomingPacket,
                                       IotMqttDeserialize_t _deserializer,
                                       IotMqttOperationType_t opType,
                                       const uint16_t * pPacketIdentifier );

/**
 * @brief Deserialize a PUBLISH packet.
 *
 * @param[in] pMqttConnection The associated MQTT connection.
 * @param[in] pIncomingPacket The packet received from the network.
 *
 * @return #IOT_MQTT_SUCCESS, #IOT_MQTT_NO_MEMORY, #IOT_MQTT_NETWORK_ERROR,
 * or #IOT_MQTT_SCHEDULING_ERROR.
 */
static IotMqttError_t _deserializePublishPacket( _mqttConnection_t * pMqttConnection,
                                                 _mqttPacket_t * pIncomingPacket );

/**
 * @brief Deserialize a PINGRESP packet.
 *
 * @param[in] pMqttConnection The associated MQTT connection.
 * @param[in] pIncomingPacket The packet received from the network.
 *
 * @return #IOT_MQTT_SUCCESS or #IOT_MQTT_BAD_RESPONSE.
 */
static IotMqttError_t _deserializePingResp( _mqttConnection_t * pMqttConnection,
                                            _mqttPacket_t * pIncomingPacket );

/**
 * @brief Deserialize a packet received from the network.
 *
 * @param[in] pMqttConnection The associated MQTT connection.
 * @param[in] pIncomingPacket The packet received from the network.
 *
 * @return #IOT_MQTT_SUCCESS, #IOT_MQTT_NO_MEMORY, #IOT_MQTT_NETWORK_ERROR,
 * #IOT_MQTT_SCHEDULING_ERROR, #IOT_MQTT_BAD_RESPONSE, or #IOT_MQTT_SERVER_REFUSED.
 */
static IotMqttError_t _deserializeIncomingPacket( _mqttConnection_t * pMqttConnection,
                                                  _mqttPacket_t * pIncomingPacket );

/**
 * @brief Send a PUBACK for a received QoS 1 PUBLISH packet.
 *
 * @param[in] pMqttConnection Which connection the PUBACK should be sent over.
 * @param[in] packetIdentifier Which packet identifier to include in PUBACK.
 */
static void _sendPuback( _mqttConnection_t * pMqttConnection,
                         uint16_t packetIdentifier );

/**
 * @brief Flush a packet from the stream of incoming data.
 *
 * This function is called when memory for a packet cannot be allocated. The
 * packet is flushed from the stream of incoming data so that the next packet
 * may be read.
 *
 * @param[in] pNetworkConnection Network connection to use for receive, which
 * may be different from the network connection associated with the MQTT connection.
 * @param[in] pMqttConnection The associated MQTT connection.
 * @param[in] length The length of the packet to flush.
 */
static void _flushPacket( IotNetworkConnection_t pNetworkConnection,
                          const _mqttConnection_t * pMqttConnection,
                          size_t length );

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this section.
 *
 * Declaration of local MQTT serializer override selectors
 */
#if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
    SERIALIZER_OVERRIDE_SELECTOR( IotMqttGetPacketType_t,
                                  _getPacketTypeFunc,
                                  _IotMqtt_GetPacketType,
                                  getPacketType )
    SERIALIZER_OVERRIDE_SELECTOR( IotMqttGetRemainingLength_t,
                                  _getRemainingLengthFunc,
                                  _IotMqtt_GetRemainingLength,
                                  getRemainingLength )
    SERIALIZER_OVERRIDE_SELECTOR( IotMqttDeserialize_t,
                                  _getConnackDeserializer,
                                  _IotMqtt_DeserializeConnack,
                                  deserialize.connack )
    SERIALIZER_OVERRIDE_SELECTOR( IotMqttDeserialize_t,
                                  _getPublishDeserializer,
                                  _IotMqtt_DeserializePublish,
                                  deserialize.publish )
    SERIALIZER_OVERRIDE_SELECTOR( IotMqttDeserialize_t,
                                  _getPubackDeserializer,
                                  _IotMqtt_DeserializePuback,
                                  deserialize.puback )
    SERIALIZER_OVERRIDE_SELECTOR( IotMqttDeserialize_t,
                                  _getSubackDeserializer,
                                  _IotMqtt_DeserializeSuback,
                                  deserialize.suback )
    SERIALIZER_OVERRIDE_SELECTOR( IotMqttDeserialize_t,
                                  _getUnsubackDeserializer,
                                  _IotMqtt_DeserializeUnsuback,
                                  deserialize.unsuback )
    SERIALIZER_OVERRIDE_SELECTOR( IotMqttDeserialize_t,
                                  _getPingrespDeserializer,
                                  _IotMqtt_DeserializePingresp,
                                  deserialize.pingresp )
    SERIALIZER_OVERRIDE_SELECTOR( IotMqttSerializePuback_t,
                                  _getMqttPubackSerializer,
                                  _IotMqtt_SerializePuback,
                                  serialize.puback )
    SERIALIZER_OVERRIDE_SELECTOR( IotMqttFreePacket_t,
                                  _getMqttFreePacketFunc,
                                  _IotMqtt_FreePacket,
                                  freePacket )
#else /* if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1 */
    #define _getPacketTypeFunc( pSerializer )          _IotMqtt_GetPacketType
    #define _getRemainingLengthFunc( pSerializer )     _IotMqtt_GetRemainingLength
    #define _getConnackDeserializer( pSerializer )     _IotMqtt_DeserializeConnack
    #define _getPublishDeserializer( pSerializer )     _IotMqtt_DeserializePublish
    #define _getPubackDeserializer( pSerializer )      _IotMqtt_DeserializePuback
    #define _getSubackDeserializer( pSerializer )      _IotMqtt_DeserializeSuback
    #define _getUnsubackDeserializer( pSerializer )    _IotMqtt_DeserializeUnsuback
    #define _getPingrespDeserializer( pSerializer )    _IotMqtt_DeserializePingresp
    #define _getMqttPubackSerializer( pSerializer )    _IotMqtt_SerializePuback
    #define _getMqttFreePacketFunc( pSerializer )      _IotMqtt_FreePacket
#endif /* if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1 */
/** @endcond */

/*-----------------------------------------------------------*/

static bool _incomingPacketValid( uint8_t packetType )
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

static IotMqttError_t _allocateAndReceivePacket( IotNetworkConnection_t pNetworkConnection,
                                                 const _mqttConnection_t * pMqttConnection,
                                                 _mqttPacket_t * pIncomingPacket )
{
    IotMqttError_t status        = IOT_MQTT_SUCCESS;
    size_t         dataBytesRead = 0;

    IotMqtt_Assert( pMqttConnection != NULL );
    IotMqtt_Assert( pIncomingPacket != NULL );

    /* Allocate a buffer for the remaining data and read the data. */
    if( pIncomingPacket->remainingLength > 0U )
    {
        pIncomingPacket->pRemainingData = IotMqtt_MallocMessage( pIncomingPacket->remainingLength );

        if( pIncomingPacket->pRemainingData == NULL )
        {
            /* In some implementations IotLogError() maps to C standard printing API
             * that need specific primitive types for format specifiers. Also,
             * inttypes.h may not be available on some C99 compilers, despite stdint.h
             * being available. */
            /* coverity[misra_c_2012_directive_4_6_violation] */
            IotLogError( "(MQTT connection %p) Failed to allocate buffer of length "
                         "%lu for incoming packet type %lu.",
                         pMqttConnection,
                         ( unsigned long ) pIncomingPacket->remainingLength,
                         ( unsigned long ) pIncomingPacket->type );

            _flushPacket( pNetworkConnection, pMqttConnection, pIncomingPacket->remainingLength );

            status = IOT_MQTT_NO_MEMORY;
        }

        if( status == IOT_MQTT_SUCCESS )
        {
            dataBytesRead = pMqttConnection->pNetworkInterface->receive( pNetworkConnection,
                                                                         pIncomingPacket->pRemainingData,
                                                                         pIncomingPacket->remainingLength );

            if( dataBytesRead != pIncomingPacket->remainingLength )
            {
                status = IOT_MQTT_BAD_RESPONSE;
            }
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static IotMqttError_t _getIncomingPacket( IotNetworkConnection_t pNetworkConnection,
                                          const _mqttConnection_t * pMqttConnection,
                                          _mqttPacket_t * pIncomingPacket )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;

    /* No buffer for remaining data should be allocated. */
    IotMqtt_Assert( pIncomingPacket->pRemainingData == NULL );
    IotMqtt_Assert( pIncomingPacket->remainingLength == 0U );

    /* Read the packet type, which is the first byte available. */
    pIncomingPacket->type = _getPacketTypeFunc( pMqttConnection->pSerializer )( pNetworkConnection,
                                                                                pMqttConnection->pNetworkInterface );

    /* Check that the incoming packet type is valid. */
    if( _incomingPacketValid( pIncomingPacket->type ) == false )
    {
        IotLogError( "(MQTT connection %p) Unknown packet type %02x received.",
                     pMqttConnection,
                     pIncomingPacket->type );

        status = IOT_MQTT_BAD_RESPONSE;
    }

    if( status == IOT_MQTT_SUCCESS )
    {
        /* Read the remaining length. */
        pIncomingPacket->remainingLength = _getRemainingLengthFunc( pMqttConnection->pSerializer )( pNetworkConnection,
                                                                                                    pMqttConnection->pNetworkInterface );

        if( pIncomingPacket->remainingLength == MQTT_REMAINING_LENGTH_INVALID )
        {
            status = IOT_MQTT_BAD_RESPONSE;
        }
    }

    if( status == IOT_MQTT_SUCCESS )
    {
        status = _allocateAndReceivePacket( pNetworkConnection,
                                            pMqttConnection,
                                            pIncomingPacket );
    }

    /* Clean up on error. */
    if( status != IOT_MQTT_SUCCESS )
    {
        if( pIncomingPacket->pRemainingData != NULL )
        {
            IotMqtt_FreeMessage( pIncomingPacket->pRemainingData );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static IotMqttError_t _deserializeAck( _mqttConnection_t * pMqttConnection,
                                       _mqttPacket_t * pIncomingPacket,
                                       IotMqttDeserialize_t _deserializer,
                                       IotMqttOperationType_t opType,
                                       const uint16_t * pPacketIdentifier )
{
    IotMqttError_t     status     = IOT_MQTT_STATUS_PENDING;
    _mqttOperation_t * pOperation = NULL;

    status     = _deserializer( pIncomingPacket );

    pOperation = _IotMqtt_FindOperation( pMqttConnection,
                                         opType,
                                         pPacketIdentifier );

    if( pOperation != NULL )
    {
        pOperation->u.operation.status = status;
        _IotMqtt_Notify( pOperation );
    }

    return status;
}

/*-----------------------------------------------------------*/

static IotMqttError_t _deserializePublishPacket( _mqttConnection_t * pMqttConnection,
                                                 _mqttPacket_t * pIncomingPacket )
{
    IotMqttError_t     status     = IOT_MQTT_STATUS_PENDING;
    _mqttOperation_t * pOperation = NULL;

    /* Allocate memory to handle the incoming PUBLISH. */
    pOperation = IotMqtt_MallocOperation( sizeof( _mqttOperation_t ) );

    if( pOperation == NULL )
    {
        IotLogWarn( "Failed to allocate memory for incoming PUBLISH." );
        status = IOT_MQTT_NO_MEMORY;
    }
    else
    {
        /* Set the members of the incoming PUBLISH operation. */
        ( void ) memset( pOperation, 0x00, sizeof( _mqttOperation_t ) );
        pOperation->incomingPublish         = true;
        pOperation->pMqttConnection         = pMqttConnection;
        pIncomingPacket->u.pIncomingPublish = pOperation;
        /* Deserialize incoming PUBLISH. */
        status                              = _getPublishDeserializer( pMqttConnection->pSerializer )( pIncomingPacket );
    }

    if( status == IOT_MQTT_SUCCESS )
    {
        /* Send a PUBACK for QoS 1 PUBLISH. */
        if( pOperation->u.publish.publishInfo.qos == IOT_MQTT_QOS_1 )
        {
            _sendPuback( pMqttConnection, pIncomingPacket->packetIdentifier );
        }

        /* Transfer ownership of the received MQTT packet to the PUBLISH operation. */
        pOperation->u.publish.pReceivedData = pIncomingPacket->pRemainingData;
        pIncomingPacket->pRemainingData     = NULL;

        /* Add the PUBLISH to the list of operations pending processing.
         * Coverity finds a USE_AFTER_FREE error at this line. This is a false positive.
         *
         * This error is triggered by a dereference of 'pMqttConnection' in
         * 'IotMutex_Lock'. Coverity assumes that 'pMqttConnection' was freed in
         * '_IotMqtt_CreateOperation', which was invoked in '_sendPuback'.
         *
         * This will never happen as a valid MQTT connection passed to this
         * function always has a positive reference count; therefore,
         * '_IotMqtt_CreateOperation' will not free it. Only unreferenced MQTT
         * connections will be freed. Coverity also evaluates an incorrect
         * path by assuming a waitable (1) value for flags, while the flags
         * passed to this function were explicitly 0.
         *
         * The annotation below suppresses this Coverity error.
         */
        /* coverity[deref_after_free] */
        IotMutex_Lock( &( pMqttConnection->referencesMutex ) );
        IotListDouble_InsertHead( &( pMqttConnection->pendingProcessing ),
                                  &( pOperation->link ) );
        IotMutex_Unlock( &( pMqttConnection->referencesMutex ) );

        /* Increment the MQTT connection reference count before scheduling an
         * incoming PUBLISH. */
        if( _IotMqtt_IncrementConnectionReferences( pMqttConnection ) == true )
        {
            /* Schedule PUBLISH for callback invocation. */
            status = _IotMqtt_ScheduleOperation( pOperation, _IotMqtt_ProcessIncomingPublish, 0 );
        }
        else
        {
            status = IOT_MQTT_NETWORK_ERROR;
        }
    }

    /* Free PUBLISH operation on error. */
    if( ( status != IOT_MQTT_SUCCESS ) && ( pOperation != NULL ) )
    {
        /* Check ownership of the received MQTT packet. */
        if( pOperation->u.publish.pReceivedData != NULL )
        {
            /* Retrieve the pointer MQTT packet pointer so it may be freed later. */
            IotMqtt_Assert( pIncomingPacket->pRemainingData == NULL );
            pIncomingPacket->pRemainingData = ( uint8_t * ) pOperation->u.publish.pReceivedData;
        }

        /* Remove operation from pending processing list. */
        IotMutex_Lock( &( pMqttConnection->referencesMutex ) );

        if( IotLink_IsLinked( &( pOperation->link ) ) == true )
        {
            IotListDouble_Remove( &( pOperation->link ) );
        }

        IotMutex_Unlock( &( pMqttConnection->referencesMutex ) );

        IotMqtt_Assert( pOperation != NULL );
        IotMqtt_FreeOperation( pOperation );
    }

    return status;
}

/*-----------------------------------------------------------*/

static IotMqttError_t _deserializePingResp( _mqttConnection_t * pMqttConnection,
                                            _mqttPacket_t * pIncomingPacket )
{
    IotMqttError_t status = IOT_MQTT_STATUS_PENDING;

    status = _getPingrespDeserializer( pMqttConnection->pSerializer )( pIncomingPacket );

    if( status == IOT_MQTT_SUCCESS )
    {
        if( Atomic_CompareAndSwap_u32( &( pMqttConnection->pingreq.u.operation.periodic.ping.failure ),
                                       0U,
                                       1U ) == 1U )
        {
            IotLogDebug( "(MQTT connection %p) PINGRESP successfully parsed.",
                         pMqttConnection );
        }
        else
        {
            IotLogWarn( "(MQTT connection %p) Unexpected PINGRESP received.",
                        pMqttConnection );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static IotMqttError_t _deserializeIncomingPacket( _mqttConnection_t * pMqttConnection,
                                                  _mqttPacket_t * pIncomingPacket )
{
    IotMqttError_t status = IOT_MQTT_STATUS_PENDING;

    /* A buffer for remaining data must be allocated if remaining length is not 0. */
    IotMqtt_Assert( ( pIncomingPacket->remainingLength > 0U ) ==
                    ( pIncomingPacket->pRemainingData != NULL ) );

    /* Only valid packets should be given to this function. */
    IotMqtt_Assert( _incomingPacketValid( pIncomingPacket->type ) == true );

    /* Mask out the low bits of packet type to ignore flags. */
    switch( ( pIncomingPacket->type & 0xf0U ) )
    {
        case MQTT_PACKET_TYPE_CONNACK:
            IotLogDebug( "(MQTT connection %p) CONNACK in data stream.", pMqttConnection );

            /* Deserialize CONNACK and notify of result. */
            status                             = _deserializeAck( pMqttConnection,
                                                                  pIncomingPacket,
                                                                  _getConnackDeserializer( pMqttConnection->pSerializer ),
                                                                  IOT_MQTT_CONNECT,
                                                                  NULL );

            break;

        case MQTT_PACKET_TYPE_PUBLISH:
            IotLogDebug( "(MQTT connection %p) PUBLISH in data stream.", pMqttConnection );

            /* Deserialize PUBLISH. */
            status                             = _deserializePublishPacket( pMqttConnection, pIncomingPacket );

            break;

        case MQTT_PACKET_TYPE_PUBACK:
            IotLogDebug( "(MQTT connection %p) PUBACK in data stream.", pMqttConnection );

            /* Deserialize PUBACK and notify of result. */
            status                             = _deserializeAck( pMqttConnection,
                                                                  pIncomingPacket,
                                                                  _getPubackDeserializer( pMqttConnection->pSerializer ),
                                                                  IOT_MQTT_PUBLISH_TO_SERVER,
                                                                  &( pIncomingPacket->packetIdentifier ) );

            break;

        case MQTT_PACKET_TYPE_SUBACK:
            IotLogDebug( "(MQTT connection %p) SUBACK in data stream.", pMqttConnection );

            /* Deserialize SUBACK and notify of result. */
            pIncomingPacket->u.pMqttConnection = pMqttConnection;

            status                             = _deserializeAck( pMqttConnection,
                                                                  pIncomingPacket,
                                                                  _getSubackDeserializer( pMqttConnection->pSerializer ),
                                                                  IOT_MQTT_SUBSCRIBE,
                                                                  &( pIncomingPacket->packetIdentifier ) );

            break;

        case MQTT_PACKET_TYPE_UNSUBACK:
            IotLogDebug( "(MQTT connection %p) UNSUBACK in data stream.", pMqttConnection );

            /* Deserialize UNSUBACK and notify of result. */
            status                             = _deserializeAck( pMqttConnection,
                                                                  pIncomingPacket,
                                                                  _getUnsubackDeserializer( pMqttConnection->pSerializer ),
                                                                  IOT_MQTT_UNSUBSCRIBE,
                                                                  &( pIncomingPacket->packetIdentifier ) );

            break;

        default:
            /* The only remaining valid type is PINGRESP. */
            IotMqtt_Assert( ( pIncomingPacket->type & 0xf0U ) == MQTT_PACKET_TYPE_PINGRESP );

            IotLogDebug( "(MQTT connection %p) PINGRESP in data stream.", pMqttConnection );

            /* Deserialize PINGRESP. */
            status                             = _deserializePingResp( pMqttConnection, pIncomingPacket );

            break;
    }

    if( status != IOT_MQTT_SUCCESS )
    {
        /* Coverity finds a USE_AFTER_FREE error at this line. This is a false positive.
         *
         * This error is triggered by passing a freed argument 'pMqttConnection'
         * to 'IotLogError'. Coverity assumes that 'pMqttConnection' was freed in
         * '_IotMqtt_CreateOperation', which was invoked in '_deserializePublishPacket'.
         *
         * This will never happen as a valid MQTT connection passed to this
         * function always has a positive reference count; therefore,
         * '_IotMqtt_CreateOperation' will not free it. Only unreferenced MQTT
         * connections will be freed. Coverity also evaluates an incorrect
         * path by assuming a waitable (1) value for flags, while the flags
         * passed to this function were explicitly 0.
         *
         * The annotation below suppresses this Coverity error.
         */
        /* coverity[pass_freed_arg] */
        IotLogError( "(MQTT connection %p) Packet parser status %s.",
                     pMqttConnection,
                     IotMqtt_strerror( status ) );
    }

    return status;
}

/*-----------------------------------------------------------*/

static void _sendPuback( _mqttConnection_t * pMqttConnection,
                         uint16_t packetIdentifier )
{
    IotMqttError_t     status           = IOT_MQTT_STATUS_PENDING;
    _mqttOperation_t * pPubackOperation = NULL;

    IotLogDebug( "(MQTT connection %p) Sending PUBACK for received PUBLISH %hu.",
                 pMqttConnection,
                 packetIdentifier );

    /* Create a PUBACK operation. */
    status = _IotMqtt_CreateOperation( pMqttConnection,
                                       0,
                                       NULL,
                                       &pPubackOperation );

    if( status == IOT_MQTT_SUCCESS )
    {
        /* Set the operation type. */
        pPubackOperation->u.operation.type = IOT_MQTT_PUBACK;

        /* Generate a PUBACK packet from the packet identifier. */
        status                             = _getMqttPubackSerializer( pMqttConnection->pSerializer )( packetIdentifier,
                                                                                                       &( pPubackOperation->u.operation.pMqttPacket ),
                                                                                                       &( pPubackOperation->u.operation.packetSize ) );

        if( status == IOT_MQTT_SUCCESS )
        {
            /* Add the PUBACK operation to the send queue for network transmission. */
            status = _IotMqtt_ScheduleOperation( pPubackOperation,
                                                 _IotMqtt_ProcessSend,
                                                 0 );

            if( status != IOT_MQTT_SUCCESS )
            {
                IotLogError( "(MQTT connection %p) Failed to enqueue PUBACK for sending.",
                             pMqttConnection );
            }
        }
    }

    if( status != IOT_MQTT_SUCCESS )
    {
        if( pPubackOperation != NULL )
        {
            _IotMqtt_DestroyOperation( pPubackOperation );
        }
    }
}

/*-----------------------------------------------------------*/

static void _flushPacket( IotNetworkConnection_t pNetworkConnection,
                          const _mqttConnection_t * pMqttConnection,
                          size_t length )
{
    size_t  bytesFlushed = 0;
    uint8_t receivedByte = 0;

    for( bytesFlushed = 0; bytesFlushed < length; bytesFlushed++ )
    {
        ( void ) _IotMqtt_GetNextByte( pNetworkConnection,
                                       pMqttConnection->pNetworkInterface,
                                       &receivedByte );
    }
}

/*-----------------------------------------------------------*/

bool _IotMqtt_GetNextByte( IotNetworkConnection_t pNetworkConnection,
                           const IotNetworkInterface_t * pNetworkInterface,
                           uint8_t * pIncomingByte )
{
    bool    status        = false;
    uint8_t incomingByte  = 0;
    size_t  bytesReceived = 0;

    /* Attempt to read 1 byte. */
    bytesReceived = pNetworkInterface->receive( pNetworkConnection,
                                                &incomingByte,
                                                1 );

    /* Set the output parameter and return success if 1 byte was read. */
    if( bytesReceived == 1U )
    {
        *pIncomingByte = incomingByte;
        status         = true;
    }
    else
    {
        /* Network receive must return 0 on failure. */
        IotMqtt_Assert( bytesReceived == 0U );
    }

    return status;
}

/*-----------------------------------------------------------*/

void _IotMqtt_CloseNetworkConnection( IotMqttDisconnectReason_t disconnectReason,
                                      _mqttConnection_t * pMqttConnection )
{
    taskPoolError_t        taskPoolStatus = TASKPOOL_SUCCESS;
    IotNetworkError_t      closeStatus = IOT_NETWORK_SUCCESS;
    IotMqttCallbackParam_t callbackParam = { .u.message = { 0 } };
    IotNetworkConnection_t pNetworkConnection = NULL;
    void *                 pDisconnectCallbackContext = NULL;

    /* Disconnect callback function. */
    void              ( * disconnectCallback )( void * pContext,
                                                IotMqttCallbackParam_t * pParam ) = NULL;

    /* Network close function. */
    IotNetworkError_t ( * closeConnection) ( IotNetworkConnection_t pConnection ) = NULL;

    /* Mark the MQTT connection as disconnected and the keep-alive as failed. */
    IotMutex_Lock( &( pMqttConnection->referencesMutex ) );
    pMqttConnection->disconnected = true;

    if( pMqttConnection->pingreq.u.operation.periodic.ping.keepAliveMs != 0U )
    {
        /* Keep-alive must have a PINGREQ allocated. */
        IotMqtt_Assert( pMqttConnection->pingreq.u.operation.pMqttPacket != NULL );
        IotMqtt_Assert( pMqttConnection->pingreq.u.operation.packetSize != 0U );

        /* PINGREQ provides a reference to the connection, so reference count must
         * be nonzero. */
        IotMqtt_Assert( pMqttConnection->references > 0 );

        /* Try to cancel the keep-alive job only if it is initialised. */
        if( taskPoolIsJobInitialised( &( pMqttConnection->pingreq.job ) ) )
        {
            /* Attempt to cancel the keep-alive job. */
            taskPoolStatus = taskPoolTryCancel( &( pMqttConnection->pingreq.job ) );
        }
        else
        {
            taskPoolStatus = TASKPOOL_GENERAL_FAILURE;
        }

        /* Clean up keep-alive if its job was successfully canceled. Otherwise,
         * the executing keep-alive job will clean up itself. */
        if( taskPoolStatus == TASKPOOL_SUCCESS )
        {
            /* Free the packet */
            _getMqttFreePacketFunc( pMqttConnection->pSerializer )( pMqttConnection->pingreq.u.operation.pMqttPacket );

            /* Clear data about the keep-alive. */
            pMqttConnection->pingreq.u.operation.periodic.ping.keepAliveMs = 0U;
            pMqttConnection->pingreq.u.operation.pMqttPacket               = NULL;
            pMqttConnection->pingreq.u.operation.packetSize                = 0U;

            /* Keep-alive is cleaned up; decrement reference count. Since this
             * function must be followed with a call to DISCONNECT, a check to
             * destroy the connection is not done here. */
            pMqttConnection->references--;

            IotLogDebug( "(MQTT connection %p) Keep-alive job canceled and cleaned up.",
                         pMqttConnection );
        }
    }

    /* Copy the function pointers and contexts, as the MQTT connection may be
     * modified after the mutex is released. */
    disconnectCallback            = pMqttConnection->disconnectCallback.function;
    pDisconnectCallbackContext    = pMqttConnection->disconnectCallback.pCallbackContext;

    closeConnection               = pMqttConnection->pNetworkInterface->close;
    pNetworkConnection            = pMqttConnection->pNetworkConnection;

    IotMutex_Unlock( &( pMqttConnection->referencesMutex ) );

    /* Close the network connection. */
    if( closeConnection != NULL )
    {
        closeStatus = closeConnection( pNetworkConnection );

        if( closeStatus == IOT_NETWORK_SUCCESS )
        {
            IotLogInfo( "(MQTT connection %p) Network connection closed.", pMqttConnection );
        }
        else
        {
            IotLogWarn( "(MQTT connection %p) Failed to close network connection, error %d.",
                        pMqttConnection,
                        closeStatus );
        }
    }
    else
    {
        IotLogWarn( "(MQTT connection %p) No network close function was set. Network connection"
                    " not closed.", pMqttConnection );
    }

    /* Invoke the disconnect callback. */
    if( disconnectCallback != NULL )
    {
        /* Set the members of the callback parameter. */
        callbackParam.mqttConnection     = pMqttConnection;
        callbackParam.u.disconnectReason = disconnectReason;

        disconnectCallback( pDisconnectCallbackContext,
                            &callbackParam );
    }
}

/*-----------------------------------------------------------*/

void IotMqtt_ReceiveCallback( IotNetworkConnection_t pNetworkConnection,
                              void * pReceiveContext )
{
    IotMqttError_t      status          = IOT_MQTT_SUCCESS;
    _mqttPacket_t       incomingPacket  = { .u.pMqttConnection = NULL };

    /* Cast context to correct type. */
    _mqttConnection_t * pMqttConnection = ( _mqttConnection_t * ) pReceiveContext;

    /* Read an MQTT packet from the network. */
    status = _getIncomingPacket( pNetworkConnection,
                                 pMqttConnection,
                                 &incomingPacket );

    if( status == IOT_MQTT_SUCCESS )
    {
        /* Deserialize the received packet. */
        status = _deserializeIncomingPacket( pMqttConnection,
                                             &incomingPacket );

        /* Free any buffers allocated for the MQTT packet. */
        if( incomingPacket.pRemainingData != NULL )
        {
            IotMqtt_FreeMessage( incomingPacket.pRemainingData );
        }
    }

    /* Close the network connection on a bad response. */
    if( status == IOT_MQTT_BAD_RESPONSE )
    {
        IotLogError( "(MQTT connection %p) Error processing incoming data. Closing connection.",
                     pMqttConnection );

        _IotMqtt_CloseNetworkConnection( IOT_MQTT_BAD_PACKET_RECEIVED,
                                         pMqttConnection );
    }
}

/*-----------------------------------------------------------*/

/* Provide access to internal functions and variables if testing. */
/* IOT_BUILD_TESTS is defined outside the code base, e.g. passed in by build command. */
/* coverity[misra_c_2012_rule_20_9_violation] */
/* coverity[caretline] */
#if IOT_BUILD_TESTS == 1
    #include "iot_test_access_mqtt_network.c"
#endif
