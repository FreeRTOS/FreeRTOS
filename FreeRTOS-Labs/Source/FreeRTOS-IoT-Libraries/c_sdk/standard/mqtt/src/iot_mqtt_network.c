/*
 * IoT MQTT V2.1.0
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/* Error handling include. */
#include "iot_error.h"

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
 * @brief Get an incoming MQTT packet from the network.
 *
 * @param[in] pNetworkConnection Network connection to use for receive, which
 * may be different from the network connection associated with the MQTT connection.
 * @param[in] pMqttConnection The associated MQTT connection.
 * @param[out] pIncomingPacket Output parameter for the incoming packet.
 *
 * @return #IOT_MQTT_SUCCESS, #IOT_MQTT_NO_MEMORY or #IOT_MQTT_BAD_RESPONSE.
 */
static IotMqttError_t _getIncomingPacket( void * pNetworkConnection,
                                          const _mqttConnection_t * pMqttConnection,
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
static void _flushPacket( void * pNetworkConnection,
                          const _mqttConnection_t * pMqttConnection,
                          size_t length );

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this section.
 *
 * Declaration of local MQTT serializer override selectors
 */
#if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
    _SERIALIZER_OVERRIDE_SELECTOR( IotMqttGetPacketType_t,
                                   _getPacketTypeFunc,
                                   _IotMqtt_GetPacketType,
                                   getPacketType )
    _SERIALIZER_OVERRIDE_SELECTOR( IotMqttGetRemainingLength_t,
                                   _getRemainingLengthFunc,
                                   _IotMqtt_GetRemainingLength,
                                   getRemainingLength )
    _SERIALIZER_OVERRIDE_SELECTOR( IotMqttDeserialize_t,
                                   _getConnackDeserializer,
                                   _IotMqtt_DeserializeConnack,
                                   deserialize.connack )
    _SERIALIZER_OVERRIDE_SELECTOR( IotMqttDeserialize_t,
                                   _getPublishDeserializer,
                                   _IotMqtt_DeserializePublish,
                                   deserialize.publish )
    _SERIALIZER_OVERRIDE_SELECTOR( IotMqttDeserialize_t,
                                   _getPubackDeserializer,
                                   _IotMqtt_DeserializePuback,
                                   deserialize.puback )
    _SERIALIZER_OVERRIDE_SELECTOR( IotMqttDeserialize_t,
                                   _getSubackDeserializer,
                                   _IotMqtt_DeserializeSuback,
                                   deserialize.suback )
    _SERIALIZER_OVERRIDE_SELECTOR( IotMqttDeserialize_t,
                                   _getUnsubackDeserializer,
                                   _IotMqtt_DeserializeUnsuback,
                                   deserialize.unsuback )
    _SERIALIZER_OVERRIDE_SELECTOR( IotMqttDeserialize_t,
                                   _getPingrespDeserializer,
                                   _IotMqtt_DeserializePingresp,
                                   deserialize.pingresp )
    _SERIALIZER_OVERRIDE_SELECTOR( IotMqttSerializePuback_t,
                                   _getMqttPubackSerializer,
                                   _IotMqtt_SerializePuback,
                                   serialize.puback )
    _SERIALIZER_OVERRIDE_SELECTOR( IotMqttFreePacket_t,
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
    switch( packetType & 0xf0 )
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

static IotMqttError_t _getIncomingPacket( void * pNetworkConnection,
                                          const _mqttConnection_t * pMqttConnection,
                                          _mqttPacket_t * pIncomingPacket )
{
    IOT_FUNCTION_ENTRY( IotMqttError_t, IOT_MQTT_SUCCESS );
    size_t dataBytesRead = 0;

    /* No buffer for remaining data should be allocated. */
    IotMqtt_Assert( pIncomingPacket->pRemainingData == NULL );
    IotMqtt_Assert( pIncomingPacket->remainingLength == 0 );

    /* Read the packet type, which is the first byte available. */
    pIncomingPacket->type = _getPacketTypeFunc( pMqttConnection->pSerializer )( pNetworkConnection,
                                                                                pMqttConnection->pNetworkInterface );

    /* Check that the incoming packet type is valid. */
    if( _incomingPacketValid( pIncomingPacket->type ) == false )
    {
        IotLogError( "(MQTT connection %p) Unknown packet type %02x received.",
                     pMqttConnection,
                     pIncomingPacket->type );

        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_RESPONSE );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    /* Read the remaining length. */
    pIncomingPacket->remainingLength = _getRemainingLengthFunc( pMqttConnection->pSerializer )( pNetworkConnection,
                                                                                                pMqttConnection->pNetworkInterface );

    if( pIncomingPacket->remainingLength == MQTT_REMAINING_LENGTH_INVALID )
    {
        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_BAD_RESPONSE );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    /* Allocate a buffer for the remaining data and read the data. */
    if( pIncomingPacket->remainingLength > 0 )
    {
        pIncomingPacket->pRemainingData = IotMqtt_MallocMessage( pIncomingPacket->remainingLength );

        if( pIncomingPacket->pRemainingData == NULL )
        {
            IotLogError( "(MQTT connection %p) Failed to allocate buffer of length "
                         "%lu for incoming packet type %lu.",
                         pMqttConnection,
                         ( unsigned long ) pIncomingPacket->remainingLength,
                         ( unsigned long ) pIncomingPacket->type );

            _flushPacket( pNetworkConnection, pMqttConnection, pIncomingPacket->remainingLength );

            IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_NO_MEMORY );
        }
        else
        {
            EMPTY_ELSE_MARKER;
        }

        dataBytesRead = pMqttConnection->pNetworkInterface->receive( pNetworkConnection,
                                                                     pIncomingPacket->pRemainingData,
                                                                     pIncomingPacket->remainingLength );

        if( dataBytesRead != pIncomingPacket->remainingLength )
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

    /* Clean up on error. */
    IOT_FUNCTION_CLEANUP_BEGIN();

    if( status != IOT_MQTT_SUCCESS )
    {
        if( pIncomingPacket->pRemainingData != NULL )
        {
            IotMqtt_FreeMessage( pIncomingPacket->pRemainingData );
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

    IOT_FUNCTION_CLEANUP_END();
}

/*-----------------------------------------------------------*/

static IotMqttError_t _deserializeIncomingPacket( _mqttConnection_t * pMqttConnection,
                                                  _mqttPacket_t * pIncomingPacket )
{
    IotMqttError_t status = IOT_MQTT_STATUS_PENDING;
    _mqttOperation_t * pOperation = NULL;

    /* A buffer for remaining data must be allocated if remaining length is not 0. */
    IotMqtt_Assert( ( pIncomingPacket->remainingLength > 0 ) ==
                    ( pIncomingPacket->pRemainingData != NULL ) );

    /* Only valid packets should be given to this function. */
    IotMqtt_Assert( _incomingPacketValid( pIncomingPacket->type ) == true );

    /* Mask out the low bits of packet type to ignore flags. */
    switch( ( pIncomingPacket->type & 0xf0 ) )
    {
        case MQTT_PACKET_TYPE_CONNACK:
            IotLogDebug( "(MQTT connection %p) CONNACK in data stream.", pMqttConnection );

            /* Deserialize CONNACK and notify of result. */
            status = _getConnackDeserializer( pMqttConnection->pSerializer )( pIncomingPacket );

            pOperation = _IotMqtt_FindOperation( pMqttConnection,
                                                 IOT_MQTT_CONNECT,
                                                 NULL );

            if( pOperation != NULL )
            {
                pOperation->u.operation.status = status;
                _IotMqtt_Notify( pOperation );
            }
            else
            {
                EMPTY_ELSE_MARKER;
            }

            break;

        case MQTT_PACKET_TYPE_PUBLISH:
            IotLogDebug( "(MQTT connection %p) PUBLISH in data stream.", pMqttConnection );

            /* Allocate memory to handle the incoming PUBLISH. */
            pOperation = IotMqtt_MallocOperation( sizeof( _mqttOperation_t ) );

            if( pOperation == NULL )
            {
                IotLogWarn( "Failed to allocate memory for incoming PUBLISH." );
                status = IOT_MQTT_NO_MEMORY;

                break;
            }
            else
            {
                /* Set the members of the incoming PUBLISH operation. */
                ( void ) memset( pOperation, 0x00, sizeof( _mqttOperation_t ) );
                pOperation->incomingPublish = true;
                pOperation->pMqttConnection = pMqttConnection;
                pIncomingPacket->u.pIncomingPublish = pOperation;
            }

            /* Deserialize incoming PUBLISH. */
            status = _getPublishDeserializer( pMqttConnection->pSerializer )( pIncomingPacket );

            if( status == IOT_MQTT_SUCCESS )
            {
                /* Send a PUBACK for QoS 1 PUBLISH. */
                if( pOperation->u.publish.publishInfo.qos == IOT_MQTT_QOS_1 )
                {
                    _sendPuback( pMqttConnection, pIncomingPacket->packetIdentifier );
                }
                else
                {
                    EMPTY_ELSE_MARKER;
                }

                /* Transfer ownership of the received MQTT packet to the PUBLISH operation. */
                pOperation->u.publish.pReceivedData = pIncomingPacket->pRemainingData;
                pIncomingPacket->pRemainingData = NULL;

                /* Add the PUBLISH to the list of operations pending processing. */
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
            else
            {
                EMPTY_ELSE_MARKER;
            }

            /* Free PUBLISH operation on error. */
            if( status != IOT_MQTT_SUCCESS )
            {
                /* Check ownership of the received MQTT packet. */
                if( pOperation->u.publish.pReceivedData != NULL )
                {
                    /* Retrieve the pointer MQTT packet pointer so it may be freed later. */
                    IotMqtt_Assert( pIncomingPacket->pRemainingData == NULL );
                    pIncomingPacket->pRemainingData = ( uint8_t * ) pOperation->u.publish.pReceivedData;
                }
                else
                {
                    EMPTY_ELSE_MARKER;
                }

                /* Remove operation from pending processing list. */
                IotMutex_Lock( &( pMqttConnection->referencesMutex ) );

                if( IotLink_IsLinked( &( pOperation->link ) ) == true )
                {
                    IotListDouble_Remove( &( pOperation->link ) );
                }
                else
                {
                    EMPTY_ELSE_MARKER;
                }

                IotMutex_Unlock( &( pMqttConnection->referencesMutex ) );

                IotMqtt_Assert( pOperation != NULL );
                IotMqtt_FreeOperation( pOperation );
            }
            else
            {
                EMPTY_ELSE_MARKER;
            }

            break;

        case MQTT_PACKET_TYPE_PUBACK:
            IotLogDebug( "(MQTT connection %p) PUBACK in data stream.", pMqttConnection );

            /* Deserialize PUBACK and notify of result. */
            status = _getPubackDeserializer( pMqttConnection->pSerializer )( pIncomingPacket );

            pOperation = _IotMqtt_FindOperation( pMqttConnection,
                                                 IOT_MQTT_PUBLISH_TO_SERVER,
                                                 &( pIncomingPacket->packetIdentifier ) );

            if( pOperation != NULL )
            {
                pOperation->u.operation.status = status;
                _IotMqtt_Notify( pOperation );
            }
            else
            {
                EMPTY_ELSE_MARKER;
            }

            break;

        case MQTT_PACKET_TYPE_SUBACK:
            IotLogDebug( "(MQTT connection %p) SUBACK in data stream.", pMqttConnection );

            /* Deserialize SUBACK and notify of result. */
            pIncomingPacket->u.pMqttConnection = pMqttConnection;

            status = _getSubackDeserializer( pMqttConnection->pSerializer )( pIncomingPacket );

            pOperation = _IotMqtt_FindOperation( pMqttConnection,
                                                 IOT_MQTT_SUBSCRIBE,
                                                 &( pIncomingPacket->packetIdentifier ) );

            if( pOperation != NULL )
            {
                pOperation->u.operation.status = status;
                _IotMqtt_Notify( pOperation );
            }
            else
            {
                EMPTY_ELSE_MARKER;
            }

            break;

        case MQTT_PACKET_TYPE_UNSUBACK:
            IotLogDebug( "(MQTT connection %p) UNSUBACK in data stream.", pMqttConnection );

            /* Deserialize UNSUBACK and notify of result. */
            status = _getUnsubackDeserializer( pMqttConnection->pSerializer )( pIncomingPacket );

            pOperation = _IotMqtt_FindOperation( pMqttConnection,
                                                 IOT_MQTT_UNSUBSCRIBE,
                                                 &( pIncomingPacket->packetIdentifier ) );

            if( pOperation != NULL )
            {
                pOperation->u.operation.status = status;
                _IotMqtt_Notify( pOperation );
            }
            else
            {
                EMPTY_ELSE_MARKER;
            }

            break;

        default:
            /* The only remaining valid type is PINGRESP. */
            IotMqtt_Assert( ( pIncomingPacket->type & 0xf0 ) == MQTT_PACKET_TYPE_PINGRESP );

            IotLogDebug( "(MQTT connection %p) PINGRESP in data stream.", pMqttConnection );

            /* Deserialize PINGRESP. */
            status = _getPingrespDeserializer( pMqttConnection->pSerializer )( pIncomingPacket );

            if( status == IOT_MQTT_SUCCESS )
            {
                if( Atomic_CompareAndSwap_u32( &( pMqttConnection->pingreq.u.operation.periodic.ping.failure ),
                                               0,
                                               1 ) == 1 )
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
            else
            {
                EMPTY_ELSE_MARKER;
            }

            break;
    }

    if( status != IOT_MQTT_SUCCESS )
    {
        IotLogError( "(MQTT connection %p) Packet parser status %s.",
                     pMqttConnection,
                     IotMqtt_strerror( status ) );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    return status;
}

/*-----------------------------------------------------------*/

static void _sendPuback( _mqttConnection_t * pMqttConnection,
                         uint16_t packetIdentifier )
{
    IotMqttError_t status = IOT_MQTT_STATUS_PENDING;
    _mqttOperation_t * pPubackOperation = NULL;

    IotLogDebug( "(MQTT connection %p) Sending PUBACK for received PUBLISH %hu.",
                 pMqttConnection,
                 packetIdentifier );

    /* Create a PUBACK operation. */
    status = _IotMqtt_CreateOperation( pMqttConnection,
                                       0,
                                       NULL,
                                       &pPubackOperation );

    if( status != IOT_MQTT_SUCCESS )
    {
        IOT_GOTO_CLEANUP();
    }

    /* Set the operation type. */
    pPubackOperation->u.operation.type = IOT_MQTT_PUBACK;

    /* Generate a PUBACK packet from the packet identifier. */
    status = _getMqttPubackSerializer( pMqttConnection->pSerializer )( packetIdentifier,
                                                                       &( pPubackOperation->u.operation.pMqttPacket ),
                                                                       &( pPubackOperation->u.operation.packetSize ) );

    if( status != IOT_MQTT_SUCCESS )
    {
        IOT_GOTO_CLEANUP();
    }

    /* Add the PUBACK operation to the send queue for network transmission. */
    status = _IotMqtt_ScheduleOperation( pPubackOperation,
                                         _IotMqtt_ProcessSend,
                                         0 );

    if( status != IOT_MQTT_SUCCESS )
    {
        IotLogError( "(MQTT connection %p) Failed to enqueue PUBACK for sending.",
                     pMqttConnection );

        IOT_GOTO_CLEANUP();
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    /* Clean up on error. */
    IOT_FUNCTION_CLEANUP_BEGIN();

    if( status != IOT_MQTT_SUCCESS )
    {
        if( pPubackOperation != NULL )
        {
            _IotMqtt_DestroyOperation( pPubackOperation );
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

static void _flushPacket( void * pNetworkConnection,
                          const _mqttConnection_t * pMqttConnection,
                          size_t length )
{
    size_t bytesFlushed = 0;
    uint8_t receivedByte = 0;

    for( bytesFlushed = 0; bytesFlushed < length; bytesFlushed++ )
    {
        ( void ) _IotMqtt_GetNextByte( pNetworkConnection,
                                       pMqttConnection->pNetworkInterface,
                                       &receivedByte );
    }
}

/*-----------------------------------------------------------*/

bool _IotMqtt_GetNextByte( void * pNetworkConnection,
                           const IotNetworkInterface_t * pNetworkInterface,
                           uint8_t * pIncomingByte )
{
    bool status = false;
    uint8_t incomingByte = 0;
    size_t bytesReceived = 0;

    /* Attempt to read 1 byte. */
    bytesReceived = pNetworkInterface->receive( pNetworkConnection,
                                                &incomingByte,
                                                1 );

    /* Set the output parameter and return success if 1 byte was read. */
    if( bytesReceived == 1 )
    {
        *pIncomingByte = incomingByte;
        status = true;
    }
    else
    {
        /* Network receive must return 0 on failure. */
        IotMqtt_Assert( bytesReceived == 0 );
    }

    return status;
}

/*-----------------------------------------------------------*/

void _IotMqtt_CloseNetworkConnection( IotMqttDisconnectReason_t disconnectReason,
                                      _mqttConnection_t * pMqttConnection )
{
    IotTaskPoolError_t taskPoolStatus = IOT_TASKPOOL_SUCCESS;
    IotNetworkError_t closeStatus = IOT_NETWORK_SUCCESS;
    IotMqttCallbackParam_t callbackParam = { .u.message = { 0 } };
    void * pNetworkConnection = NULL, * pDisconnectCallbackContext = NULL;

    /* Disconnect callback function. */
    void ( * disconnectCallback )( void *,
                                   IotMqttCallbackParam_t * ) = NULL;

    /* Network close function. */
    IotNetworkError_t ( * closeConnection) ( IotNetworkConnection_t ) = NULL;

    /* Mark the MQTT connection as disconnected and the keep-alive as failed. */
    IotMutex_Lock( &( pMqttConnection->referencesMutex ) );
    pMqttConnection->disconnected = true;

    if( pMqttConnection->pingreq.u.operation.periodic.ping.keepAliveMs != 0 )
    {
        /* Keep-alive must have a PINGREQ allocated. */
        IotMqtt_Assert( pMqttConnection->pingreq.u.operation.pMqttPacket != NULL );
        IotMqtt_Assert( pMqttConnection->pingreq.u.operation.packetSize != 0 );

        /* PINGREQ provides a reference to the connection, so reference count must
         * be nonzero. */
        IotMqtt_Assert( pMqttConnection->references > 0 );

        /* Attempt to cancel the keep-alive job. */
        taskPoolStatus = IotTaskPool_TryCancel( IOT_SYSTEM_TASKPOOL,
                                                pMqttConnection->pingreq.job,
                                                NULL );

        /* Clean up keep-alive if its job was successfully canceled. Otherwise,
         * the executing keep-alive job will clean up itself. */
        if( taskPoolStatus == IOT_TASKPOOL_SUCCESS )
        {
            /* Free the packet */
            _getMqttFreePacketFunc( pMqttConnection->pSerializer )( pMqttConnection->pingreq.u.operation.pMqttPacket );

            /* Clear data about the keep-alive. */
            pMqttConnection->pingreq.u.operation.periodic.ping.keepAliveMs = 0;
            pMqttConnection->pingreq.u.operation.pMqttPacket = NULL;
            pMqttConnection->pingreq.u.operation.packetSize = 0;

            /* Keep-alive is cleaned up; decrement reference count. Since this
             * function must be followed with a call to DISCONNECT, a check to
             * destroy the connection is not done here. */
            pMqttConnection->references--;

            IotLogDebug( "(MQTT connection %p) Keep-alive job canceled and cleaned up.",
                         pMqttConnection );
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

    /* Copy the function pointers and contexts, as the MQTT connection may be
     * modified after the mutex is released. */
    disconnectCallback = pMqttConnection->disconnectCallback.function;
    pDisconnectCallbackContext = pMqttConnection->disconnectCallback.pCallbackContext;

    closeConnection = pMqttConnection->pNetworkInterface->close;
    pNetworkConnection = pMqttConnection->pNetworkConnection;

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
        callbackParam.mqttConnection = pMqttConnection;
        callbackParam.u.disconnectReason = disconnectReason;

        disconnectCallback( pDisconnectCallbackContext,
                            &callbackParam );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }
}

/*-----------------------------------------------------------*/

void IotMqtt_ReceiveCallback( IotNetworkConnection_t pNetworkConnection,
                              void * pReceiveContext )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;
    _mqttPacket_t incomingPacket = { .u.pMqttConnection = NULL };

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
        else
        {
            EMPTY_ELSE_MARKER;
        }
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    /* Close the network connection on a bad response. */
    if( status == IOT_MQTT_BAD_RESPONSE )
    {
        IotLogError( "(MQTT connection %p) Error processing incoming data. Closing connection.",
                     pMqttConnection );

        _IotMqtt_CloseNetworkConnection( IOT_MQTT_BAD_PACKET_RECEIVED,
                                         pMqttConnection );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }
}

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_GetIncomingMQTTPacketTypeAndLength( IotMqttPacketInfo_t * pIncomingPacket,
                                                           IotMqttGetNextByte_t getNextByte,
                                                           void * pNetworkConnection )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;

    /* Read the packet type, which is the first byte available. */
    if( getNextByte( pNetworkConnection, &( pIncomingPacket->type ) ) == IOT_MQTT_SUCCESS )
    {
        /* Check that the incoming packet type is valid. */
        if( _incomingPacketValid( pIncomingPacket->type ) == false )
        {
            IotLogError( "(MQTT connection) Unknown packet type %02x received.",
                         pIncomingPacket->type );

            status = IOT_MQTT_BAD_RESPONSE;
        }
        else
        {
            /* Read the remaining length. */
            pIncomingPacket->remainingLength = _IotMqtt_GetRemainingLength_Generic( pNetworkConnection,
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
