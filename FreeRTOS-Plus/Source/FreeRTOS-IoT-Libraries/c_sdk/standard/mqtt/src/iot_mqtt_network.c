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
 * @file iot_mqtt_network.c
 * @brief Implements functions involving transport layer connections.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <string.h>

/* Error handling include. */
#include "private/iot_error.h"

/* MQTT internal include. */
#include "private/iot_mqtt_internal.h"

/* Platform layer includes. */
#include "platform/iot_threads.h"

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

    /* Default functions for retrieving packet type and length. */
    uint8_t ( * getPacketType )( void *,
                                 const IotNetworkInterface_t * ) = _IotMqtt_GetPacketType;
    size_t ( * getRemainingLength )( void *,
                                     const IotNetworkInterface_t * ) = _IotMqtt_GetRemainingLength;

    /* No buffer for remaining data should be allocated. */
    IotMqtt_Assert( pIncomingPacket->pRemainingData == NULL );
    IotMqtt_Assert( pIncomingPacket->remainingLength == 0 );

    /* Choose packet type and length functions. */
    #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
        if( pMqttConnection->pSerializer != NULL )
        {
            if( pMqttConnection->pSerializer->getPacketType != NULL )
            {
                getPacketType = pMqttConnection->pSerializer->getPacketType;
            }
            else
            {
                EMPTY_ELSE_MARKER;
            }

            if( pMqttConnection->pSerializer->getRemainingLength != NULL )
            {
                getRemainingLength = pMqttConnection->pSerializer->getRemainingLength;
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
    #endif /* if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1 */

    /* Read the packet type, which is the first byte available. */
    pIncomingPacket->type = getPacketType( pNetworkConnection,
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
    pIncomingPacket->remainingLength = getRemainingLength( pNetworkConnection,
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

    /* Deserializer function. */
    IotMqttError_t ( * deserialize )( _mqttPacket_t * ) = NULL;

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

            /* Choose CONNACK deserializer. */
            deserialize = _IotMqtt_DeserializeConnack;

            #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
                if( pMqttConnection->pSerializer != NULL )
                {
                    if( pMqttConnection->pSerializer->deserialize.connack != NULL )
                    {
                        deserialize = pMqttConnection->pSerializer->deserialize.connack;
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
            #endif /* if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1 */

            /* Deserialize CONNACK and notify of result. */
            status = deserialize( pIncomingPacket );
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

            /* Choose a PUBLISH deserializer. */
            deserialize = _IotMqtt_DeserializePublish;

            #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
                if( pMqttConnection->pSerializer != NULL )
                {
                    if( pMqttConnection->pSerializer->deserialize.publish != NULL )
                    {
                        deserialize = pMqttConnection->pSerializer->deserialize.publish;
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
            #endif /* if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1 */

            /* Deserialize incoming PUBLISH. */
            status = deserialize( pIncomingPacket );

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

            /* Choose PUBACK deserializer. */
            deserialize = _IotMqtt_DeserializePuback;

            #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
                if( pMqttConnection->pSerializer != NULL )
                {
                    if( pMqttConnection->pSerializer->deserialize.puback != NULL )
                    {
                        deserialize = pMqttConnection->pSerializer->deserialize.puback;
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
            #endif /* if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1 */

            /* Deserialize PUBACK and notify of result. */
            status = deserialize( pIncomingPacket );
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

            /* Choose SUBACK deserializer. */
            deserialize = _IotMqtt_DeserializeSuback;

            #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
                if( pMqttConnection->pSerializer != NULL )
                {
                    if( pMqttConnection->pSerializer->deserialize.suback != NULL )
                    {
                        deserialize = pMqttConnection->pSerializer->deserialize.suback;
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
            #endif /* if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1 */

            /* Deserialize SUBACK and notify of result. */
            pIncomingPacket->u.pMqttConnection = pMqttConnection;
            status = deserialize( pIncomingPacket );
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

            /* Choose UNSUBACK deserializer. */
            deserialize = _IotMqtt_DeserializeUnsuback;

            #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
                if( pMqttConnection->pSerializer != NULL )
                {
                    if( pMqttConnection->pSerializer->deserialize.unsuback != NULL )
                    {
                        deserialize = pMqttConnection->pSerializer->deserialize.unsuback;
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
            #endif /* if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1 */

            /* Deserialize UNSUBACK and notify of result. */
            status = deserialize( pIncomingPacket );
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

            /* Choose PINGRESP deserializer. */
            deserialize = _IotMqtt_DeserializePingresp;

            #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
                if( pMqttConnection->pSerializer != NULL )
                {
                    if( pMqttConnection->pSerializer->deserialize.pingresp != NULL )
                    {
                        deserialize = pMqttConnection->pSerializer->deserialize.pingresp;
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
            #endif /* if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1 */

            /* Deserialize PINGRESP. */
            status = deserialize( pIncomingPacket );

            if( status == IOT_MQTT_SUCCESS )
            {
                IotMutex_Lock( &( pMqttConnection->referencesMutex ) );

                if( pMqttConnection->keepAliveFailure == false )
                {
                    IotLogWarn( "(MQTT connection %p) Unexpected PINGRESP received.",
                                pMqttConnection );
                }
                else
                {
                    IotLogDebug( "(MQTT connection %p) PINGRESP successfully parsed.",
                                 pMqttConnection );

                    pMqttConnection->keepAliveFailure = false;
                }

                IotMutex_Unlock( &( pMqttConnection->referencesMutex ) );
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
    IotMqttError_t serializeStatus = IOT_MQTT_SUCCESS;
    uint8_t * pPuback = NULL;
    size_t pubackSize = 0, bytesSent = 0;

    /* Default PUBACK serializer and free packet functions. */
    IotMqttError_t ( * serializePuback )( uint16_t,
                                          uint8_t **,
                                          size_t * ) = _IotMqtt_SerializePuback;
    void ( * freePacket )( uint8_t * ) = _IotMqtt_FreePacket;

    IotLogDebug( "(MQTT connection %p) Sending PUBACK for received PUBLISH %hu.",
                 pMqttConnection,
                 packetIdentifier );

    /* Choose PUBACK serializer and free packet functions. */
    #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
        if( pMqttConnection->pSerializer != NULL )
        {
            if( pMqttConnection->pSerializer->serialize.puback != NULL )
            {
                serializePuback = pMqttConnection->pSerializer->serialize.puback;
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
    #endif /* if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1 */
    #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
        if( pMqttConnection->pSerializer != NULL )
        {
            if( pMqttConnection->pSerializer->freePacket != NULL )
            {
                freePacket = pMqttConnection->pSerializer->freePacket;
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
    #endif /* if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1 */

    /* Generate a PUBACK packet from the packet identifier. */
    serializeStatus = serializePuback( packetIdentifier,
                                       &pPuback,
                                       &pubackSize );

    if( serializeStatus != IOT_MQTT_SUCCESS )
    {
        IotLogWarn( "(MQTT connection %p) Failed to generate PUBACK packet for "
                    "received PUBLISH %hu.",
                    pMqttConnection,
                    packetIdentifier );
    }
    else
    {
        bytesSent = pMqttConnection->pNetworkInterface->send( pMqttConnection->pNetworkConnection,
                                                              pPuback,
                                                              pubackSize );

        if( bytesSent != pubackSize )
        {
            IotLogWarn( "(MQTT connection %p) Failed to send PUBACK for received"
                        " PUBLISH %hu.",
                        pMqttConnection,
                        packetIdentifier );
        }
        else
        {
            IotLogDebug( "(MQTT connection %p) PUBACK for received PUBLISH %hu sent.",
                         pMqttConnection,
                         packetIdentifier );
        }

        freePacket( pPuback );
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

    /* Mark the MQTT connection as disconnected and the keep-alive as failed. */
    IotMutex_Lock( &( pMqttConnection->referencesMutex ) );
    pMqttConnection->disconnected = true;
    pMqttConnection->keepAliveFailure = true;

    if( pMqttConnection->keepAliveMs != 0 )
    {
        /* Keep-alive must have a PINGREQ allocated. */
        IotMqtt_Assert( pMqttConnection->pPingreqPacket != NULL );
        IotMqtt_Assert( pMqttConnection->pingreqPacketSize != 0 );

        /* PINGREQ provides a reference to the connection, so reference count must
         * be nonzero. */
        IotMqtt_Assert( pMqttConnection->references > 0 );

        /* Attempt to cancel the keep-alive job. */
        taskPoolStatus = IotTaskPool_TryCancel( IOT_SYSTEM_TASKPOOL,
                                                pMqttConnection->keepAliveJob,
                                                NULL );

        /* If the keep-alive job was not canceled, it must be already executing.
         * Any other return value is invalid. */
        IotMqtt_Assert( ( taskPoolStatus == IOT_TASKPOOL_SUCCESS ) ||
                        ( taskPoolStatus == IOT_TASKPOOL_CANCEL_FAILED ) );

        /* Clean up keep-alive if its job was successfully canceled. Otherwise,
         * the executing keep-alive job will clean up itself. */
        if( taskPoolStatus == IOT_TASKPOOL_SUCCESS )
        {
            /* Clean up PINGREQ packet and job. */
            _IotMqtt_FreePacket( pMqttConnection->pPingreqPacket );

            /* Clear data about the keep-alive. */
            pMqttConnection->keepAliveMs = 0;
            pMqttConnection->pPingreqPacket = NULL;
            pMqttConnection->pingreqPacketSize = 0;

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

    IotMutex_Unlock( &( pMqttConnection->referencesMutex ) );

    /* Close the network connection. */
    if( pMqttConnection->pNetworkInterface->close != NULL )
    {
        closeStatus = pMqttConnection->pNetworkInterface->close( pMqttConnection->pNetworkConnection );

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
    if( pMqttConnection->disconnectCallback.function != NULL )
    {
        /* Set the members of the callback parameter. */
        callbackParam.mqttConnection = pMqttConnection;
        callbackParam.u.disconnectReason = disconnectReason;

        pMqttConnection->disconnectCallback.function( pMqttConnection->disconnectCallback.pCallbackContext,
                                                      &callbackParam );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }
}

/*-----------------------------------------------------------*/

void IotMqtt_ReceiveCallback( void * pNetworkConnection,
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
