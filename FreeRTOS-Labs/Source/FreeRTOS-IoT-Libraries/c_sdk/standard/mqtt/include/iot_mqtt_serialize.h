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
 * @file iot_mqtt_serialize.h
 * @brief User-facing functions for serializing MQTT 3.1.1 packets. This header should
 * be included for building a single threaded light-weight MQTT client bypassing
 * stateful CSDK MQTT library.
 */

#ifndef _IOT_MQTT_SERIALIZE_H_
#define _IOT_MQTT_SERIALIZE_H_

/* The config header is always included first. */
#include "iot_config.h"

/* MQTT types include. */
#include "types/iot_mqtt_types.h"

/*------------------------- MQTT library functions --------------------------*/

/**
 * @functionspage{mqtt,MQTT library}
 * - @functionname{mqtt_function_getconnectpacketsize}
 * - @functionname{mqtt_function_serializeconnect}
 * - @functionname{mqtt_function_getsubscriptionpacketsize}
 * - @functionname{mqtt_function_serializesubscribe}
 * - @functionname{mqtt_function_serializeunsubscribe}
 * - @functionname{mqtt_function_getpublishpacketsize}
 * - @functionname{mqtt_function_serializepublish}
 * - @functionname{mqtt_function_serializedisconnect}
 * - @functionname{mqtt_function_serializepingreq}
 * - @functionname{mqtt_function_getincomingmqttpackettypeandlength}
 * - @functionname{mqtt_function_deserializeresponse}
 * - @functionname{mqtt_function_deserializepublish}
 */

/**
 * @functionpage{IotMqtt_GetConnectPacketSize,mqtt,getconnectpacketsize}
 * @functionpage{IotMqtt_SerializeConnect,mqtt,serializeconnect}
 * @functionpage{IotMqtt_GetSubscriptionPacketSize,mqtt,getsubscriptionpacketsize}
 * @functionpage{IotMqtt_SerializeSubscribe,mqtt,serializesubscribe}
 * @functionpage{IotMqtt_SerializeUnsubscribe,mqtt,serializeunsubscribe}
 * @functionpage{IotMqtt_GetPublishPacketSize,mqtt,getpublishpacketsize}
 * @functionpage{IotMqtt_SerializePublish,mqtt,serializepublish}
 * @functionpage{IotMqtt_SerializeDisconnect,mqtt,serializedisconnect}
 * @functionpage{IotMqtt_SerializePingreq,mqtt,serializepingreq}
 * @functionpage{IotMqtt_GetIncomingMQTTPacketTypeAndLength,mqtt,getincomingmqttpackettypeandlength}
 * @functionpage{IotMqtt_DeserializeResponse,mqtt,deserializeresponse}
 * @functionpage{IotMqtt_DeserializePublish,mqtt,deserializepublish}
 */

/**
 * @brief Calculate the size and "Remaining length" of a CONNECT packet generated
 * from the given parameters.
 *
 * @param[in] pConnectInfo User-provided CONNECT information struct.
 * @param[out] pRemainingLength Output for calculated "Remaining length" field.
 * @param[out] pPacketSize Output for calculated total packet size.
 *
 * @return IOT_MQTT_SUCCESS if the packet is within the length allowed by MQTT 3.1.1 spec;
 * IOT_MQTT_BAD_PARAMETER otherwise. If this function returns `IOT_MQTT_BAD_PARAMETER`,
 * the output parameters should be ignored.
 *
 * @note This call is part of serializer API used for implementing light-weight MQTT client.
 * 
 * <b>Example</b>
 * @code{c}
 * // Example code below shows how IotMqtt_GetConnectPacketSize() should be used to calculate
 * // the size of connect request. 
 *
 * IotMqttConnectInfo_t xConnectInfo;
 * size_t xRemainingLength = 0;
 * size_t xPacketSize = 0;
 * IotMqttError_t xResult;
 * 
 * // start with everything set to zero
 * memset( ( void * ) &xConnectInfo, 0x00, sizeof( xConnectInfo ) );
 *	
 * // Initialize connection info, details are out of scope for this example.
 * _initializeConnectInfo( &xConnectInfo );
 * // Get size requirement for the connect packet 
 * xResult = IotMqtt_GetConnectPacketSize( &xConnectInfo, &xRemainingLength, &xPacketSize );
 * IotMqtt_Assert( xResult == IOT_MQTT_SUCCESS );
 *
 *  // Application should allocate buffer with size == xPacketSize or use static buffer
 *  // with size >= xPacketSize to serialize connect request.
 * @endcode
 */
/* @[declare_mqtt_getconnectpacketsize] */
IotMqttError_t IotMqtt_GetConnectPacketSize( const IotMqttConnectInfo_t * pConnectInfo,
                                             size_t * pRemainingLength,
                                             size_t * pPacketSize );
/* @[declare_mqtt_getconnectpacketsize] */

/**
 * @brief Generate a CONNECT packet from the given parameters.
 *
 * @param[in] pConnectInfo User-provided CONNECT information.
 * @param[in] remainingLength remaining length of the packet to be serialized.
 * @param[in, out] pBuffer User provided buffer where the CONNECT packet is written.
 * @param[in] bufferSize Size of the buffer pointed to by pBuffer.
 *
 * @return #IOT_MQTT_SUCCESS or #IOT_MQTT_NO_MEMORY.
 *
 * @note pBuffer must be allocated by caller. Use @ref mqtt_function_getconnectpacketsize
 * to determine the required size.
 * @note This call is part of serializer API used for implementing light-weight MQTT client.
 * 
 * <b>Example</b>
 * @code{c}
 * // Example code below shows how IotMqtt_SerializeConnect() should be used to serialize
 * // MQTT connect packet and send it to MQTT broker.
 * // Example uses static memory but dynamically allocated memory can be used as well.
 * // Get size requirement for the connect packet.
 * 
 * #define mqttexampleSHARED_BUFFER_SIZE 100
 * static ucSharedBuffer[mqttexampleSHARED_BUFFER_SIZE];
 * void sendConnectPacket( int xMQTTSocket )
 * {
 *    IotMqttConnectInfo_t xConnectInfo;
 *    size_t xRemainingLength = 0;
 *    size_t xPacketSize = 0;
 *    IotMqttError_t xResult;
 *    size_t xSentBytes = 0;
 *    // Get size requirement for MQTT connect packet.
 *    xResult = IotMqtt_GetConnectPacketSize( &xConnectInfo, &xRemainingLength, &xPacketSize );
 *    IotMqtt_Assert( xResult == IOT_MQTT_SUCCESS );
 *    // Make sure the packet size is less than static buffer size
 *    IotMqtt_Assert( xPacketSize < mqttexampleSHARED_BUFFER_SIZE );
 *    // Serialize MQTT connect packet into provided buffer
 *    xResult = IotMqtt_SerializeConnect( &xConnectInfo, xRemainingLength, ucSharedBuffer, xPacketSize );
 *    IotMqtt_Assert( xResult == IOT_MQTT_SUCCESS ); 
 *    // xMQTTSocket here is posix socket created and connected to MQTT broker outside of this function.
 *    xSentBytes = send( xMQTTSocket, ( void * ) ucSharedBuffer, xPacketSize, 0 );
 *    IotMqtt_Assert( xSentBytes == xPacketSize );
 * }
 * @endcode
 */
/* @[declare_mqtt_serializeconnect] */
IotMqttError_t IotMqtt_SerializeConnect( const IotMqttConnectInfo_t * pConnectInfo,
                                         size_t remainingLength,
                                         uint8_t * pBuffer,
                                         size_t bufferSize );
/* @[declare_mqtt_serializeconnect] */

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
 * @return IOT_MQTT_SUCCESS if the packet is within the length allowed by MQTT 3.1.1 spec;
 * IOT_MQTT_BAD_PARAMETER otherwise. If this function returns IOT_MQTT_BAD_PARAMETER,
 * the output parameters should be ignored.
 *
 * @note This call is part of serializer API used for implementing light-weight MQTT client.
 * 
 * <b>Example</b>
 * @code{c}
 * // Example code below shows how IotMqtt_GetSubscriptionPacketSize() should be used to calculate
 * // the size of subscribe or unsubscribe request. 
 *
 * IotMqttError_t xResult;
 * IotMqttSubscription_t xMQTTSubscription[ 1 ];
 * size_t xRemainingLength = 0;
 * size_t xPacketSize = 0;
 * 
 * // Initialize Subscribe parameters. Details are out of scope for this example.
 * // It will involve setting QOS, topic filter  and topic filter length. 
 *  _initializeSubscribe( xMQTTSubscription );
 *
 * xResult = IotMqtt_GetSubscriptionPacketSize( IOT_MQTT_SUBSCRIBE,
 *												 xMQTTSubscription,
 *												 sizeof( xMQTTSubscription ) / sizeof( IotMqttSubscription_t ),
 *												 &xRemainingLength, &xPacketSize );
 * IotMqtt_Assert( xResult == IOT_MQTT_SUCCESS );
 *
 * // Application should allocate buffer with size == xPacketSize or use static buffer
 * // with size >= xPacketSize to serialize connect request.
 * @endcode
 */
/* @[declare_mqtt_getsubscriptionpacketsize] */
IotMqttError_t IotMqtt_GetSubscriptionPacketSize( IotMqttOperationType_t type,
                                                  const IotMqttSubscription_t * pSubscriptionList,
                                                  size_t subscriptionCount,
                                                  size_t * pRemainingLength,
                                                  size_t * pPacketSize );
/* @[declare_mqtt_getsubscriptionpacketsize] */

/**
 * @brief Generate a SUBSCRIBE packet from the given parameters.
 *
 * @param[in] pSubscriptionList User-provided array of subscriptions.
 * @param[in] subscriptionCount Size of `pSubscriptionList`.
 * @param[in] remainingLength remaining length of the packet to be serialized.
 * @param[out] pPacketIdentifier The packet identifier generated for this SUBSCRIBE.
 * @param[in, out] pBuffer User provide buffer where the SUBSCRIBE packet is written.
 * @param[in] bufferSize Size of the buffer pointed to by pBuffer.
 *
 * @return #IOT_MQTT_SUCCESS or #IOT_MQTT_NO_MEMORY.
 *
 * @note pBuffer must be allocated by caller.
 * @note This call is part of serializer API used for implementing light-weight MQTT client.
 * <b>Example</b>
 * @code{c}
 * // Example code below shows how IotMqtt_SerializeSubscribe() should be used to serialize
 * // MQTT Subscribe packet and send it to MQTT broker.
 * // Example uses static memory, but dynamically allocated memory can be used as well.
 * // Get size requirement for the MQTT subscribe packet.
 * 
 * #define mqttexampleSHARED_BUFFER_SIZE 100
 * static ucSharedBuffer[mqttexampleSHARED_BUFFER_SIZE];
 * void sendSubscribePacket( int xMQTTSocket )
 * {
 *    IotMqttSubscription_t xMQTTSubscription[ 1 ];
 *    size_t xRemainingLength = 0;
 *    size_t xPacketSize = 0;
 *    IotMqttError_t xResult;
 *    size_t xSentBytes = 0;
 *  
 *    // Initialize Subscribe parameters. Details are out of scope for this example.
 *    // It will involve setting QOS, topic filter  and topic filter length. 
 *    _initializeSubscribe( xMQTTSubscription );
 *    // Get size requirement for MQTT Subscribe packet.
 *    xResult = IotMqtt_GetSubscriptionPacketSize( IOT_MQTT_SUBSCRIBE,
 *												 xMQTTSubscription,
 *												 sizeof( xMQTTSubscription ) / sizeof( IotMqttSubscription_t ),
 *												 &xRemainingLength, &xPacketSize );
 *    IotMqtt_Assert( xResult == IOT_MQTT_SUCCESS );
 *    // Make sure the packet size is less than static buffer size.
 *    IotMqtt_Assert( xPacketSize < mqttexampleSHARED_BUFFER_SIZE );
 * 
 *    // Serialize subscribe into statically allocated ucSharedBuffer.
 *	   xResult = IotMqtt_SerializeSubscribe( xMQTTSubscription, 
 *										  sizeof( xMQTTSubscription ) / sizeof( IotMqttSubscription_t ),
 *										  xRemainingLength,
 *										  &usPacketIdentifier,
 *										  ucSharedBuffer,
 *										  xPacketSize );
 *    IotMqtt_Assert( xResult == IOT_MQTT_SUCCESS ); 
 *    // xMQTTSocket here is posix socket created and connected to MQTT broker outside of this function.
 *    xSentBytes = send( xMQTTSocket, ( void * ) ucSharedBuffer, xPacketSize, 0 );
 *    IotMqtt_Assert( xSentBytes == xPacketSize );
 * }
 * @endcode
 */
/* @[declare_mqtt_serializesubscribe] */
IotMqttError_t IotMqtt_SerializeSubscribe( const IotMqttSubscription_t * pSubscriptionList,
                                           size_t subscriptionCount,
                                           size_t remainingLength,
                                           uint16_t * pPacketIdentifier,
                                           uint8_t * pBuffer,
                                           size_t bufferSize );
/* @[declare_mqtt_serializesubscribe] */

/**
 * @brief Generate a UNSUBSCRIBE packet from the given parameters.
 *
 * @param[in] pSubscriptionList User-provided array of subscriptions to remove.
 * @param[in] subscriptionCount Size of `pSubscriptionList`.
 * @param[in] remainingLength remaining length of the packet to be serialized.
 * @param[out] pPacketIdentifier The packet identifier generated for this UNSUBSCRIBE.
 * @param[in, out] pBuffer User provide buffer where the UNSUBSCRIBE packet is written.
 * @param[in] bufferSize Size of the buffer pointed to by pBuffer.
 *
 * @return #IOT_MQTT_SUCCESS or #IOT_MQTT_NO_MEMORY.
 *
 * @note pBuffer must be allocated by caller.
 * @note This call is part of serializer API used for implementing light-weight MQTT client.
 * 
 * <b>Example</b>
 * @code{c}
 * // Example code below shows how IotMqtt_SerializeUnsubscribe() should be used to serialize
 * // MQTT unsubscribe packet and send it to MQTT broker.
 * // Example uses static memory, but dynamically allocated memory can be used as well.
 * // Get size requirement for the Unsubscribe packet.
 * 
 * #define mqttexampleSHARED_BUFFER_SIZE 100
 * static ucSharedBuffer[mqttexampleSHARED_BUFFER_SIZE];
 * void sendUnsubscribePacket( int xMQTTSocket )
 * {
 *    // Following example shows one topic example.
 *    IotMqttSubscription_t xMQTTSubscription[ 1 ];
 *    size_t xRemainingLength = 0;
 *    size_t xPacketSize = 0;
 *    IotMqttError_t xResult;
 *    size_t xSentBytes = 0;
 *    // Get size requirement for MQTT unsubscribe packet.
 *    xResult = IotMqtt_GetSubscriptionPacketSize( IOT_MQTT_UNSUBSCRIBE,
 *												 xMQTTSubscription,
 *												 sizeof( xMQTTSubscription ) / sizeof( IotMqttSubscription_t ),
 *												 &xRemainingLength, &xPacketSize );
 *    IotMqtt_Assert( xResult == IOT_MQTT_SUCCESS );
 *    // Make sure the packet size is less than static buffer size.
 *    IotMqtt_Assert( xPacketSize < mqttexampleSHARED_BUFFER_SIZE );
 *    // Serialize subscribe into statically allocated ucSharedBuffer.
 *	   xResult = IotMqtt_SerializeUnsubscribe( xMQTTSubscription, 
 *										  sizeof( xMQTTSubscription ) / sizeof( IotMqttSubscription_t ),
 *										  xRemainingLength,
 *										  &usPacketIdentifier,
 *										  ucSharedBuffer,
 *										  xPacketSize );
 *    IotMqtt_Assert( xResult == IOT_MQTT_SUCCESS ); 
 *    // xMQTTSocket here is posix socket created and connected to MQTT broker outside of this function.
 *    xSentBytes = send( xMQTTSocket, ( void * ) ucSharedBuffer, xPacketSize, 0 );
 *    IotMqtt_Assert( xSentBytes == xPacketSize );
 * }
 * @endcode
 */
/* @[declare_mqtt_serializeunsubscribe] */
IotMqttError_t IotMqtt_SerializeUnsubscribe( const IotMqttSubscription_t * pSubscriptionList,
                                             size_t subscriptionCount,
                                             size_t remainingLength,
                                             uint16_t * pPacketIdentifier,
                                             uint8_t * pBuffer,
                                             size_t bufferSize );
/* @[declare_mqtt_serializeunsubscribe] */

/**
 * @brief Calculate the size and "Remaining length" of a PUBLISH packet generated
 * from the given parameters.
 *
 * @param[in] pPublishInfo User-provided PUBLISH information struct.
 * @param[out] pRemainingLength Output for calculated "Remaining length" field.
 * @param[out] pPacketSize Output for calculated total packet size.
 *
 * @return IOT_MQTT_SUCCESS if the packet is within the length allowed by MQTT 3.1.1 spec;
 * IOT_MQTT_BAD_PARAMETER otherwise. If this function returns IOT_MQTT_BAD_PARAMETER,
 * the output parameters should be ignored.
 *
 * @note This call is part of serializer API used for implementing light-weight MQTT client.
 * 
 * <b>Example</b>
 * @code{c}
 * // Example code below shows how IotMqtt_GetPublishPacketSize() should be used to calculate
 * // the size of MQTT publish request. 
 *
 * IotMqttError_t xResult;
 * IotMqttPublishInfo_t xMQTTPublishInfo;
 * size_t xRemainingLength = 0;
 * size_t xPacketSize = 0;
 * 
 * // Initialize Publish parameters. Details are out of scope for this example.
 * // It will involve setting QOS, topic filter, topic filter length, payload
 * // payload length
 *  _initializePublish( &xMQTTPublishInfo );
 *
 * // Find out length of Publish packet size.
 * xResult = IotMqtt_GetPublishPacketSize( &xMQTTPublishInfo, &xRemainingLength, &xPacketSize );
 * IotMqtt_Assert( xResult == IOT_MQTT_SUCCESS );
 *
 * // Application should allocate buffer with size == xPacketSize or use static buffer
 * // with size >= xPacketSize to serialize connect request.
 * @endcode
 */
/* @[declare_mqtt_getpublishpacketsize] */
IotMqttError_t IotMqtt_GetPublishPacketSize( IotMqttPublishInfo_t * pPublishInfo,
                                             size_t * pRemainingLength,
                                             size_t * pPacketSize );
/* @[declare_mqtt_getpublishpacketsize] */

/**
 * @brief Generate a PUBLISH packet from the given parameters.
 *
 * @param[in] pPublishInfo User-provided PUBLISH information.
 * @param[in] remainingLength remaining length of the packet to be serialized.
 * @param[out] pPacketIdentifier The packet identifier generated for this PUBLISH.
 * @param[out] pPacketIdentifierHigh Where the high byte of the packet identifier
 * is written.
 * @param[in, out] pBuffer User provide buffer where the PUBLISH packet is written.
 * @param[in] bufferSize Size of the buffer pointed to by pBuffer.
 *
 * @return #IOT_MQTT_SUCCESS or #IOT_MQTT_BAD_PARAMETER.
 *
 * @note pBuffer must be allocated by caller.
 * @note This call is part of serializer API used for implementing light-weight MQTT client.
 *
 * <b>Example</b>
 * @code{c}
 * // Example code below shows how IotMqtt_SerializePublish() should be used to serialize
 * // MQTT Publish packet and send it to broker.
 * // Example uses static memory, but dynamically allocated memory can be used as well.
 * 
 * #define mqttexampleSHARED_BUFFER_SIZE 100
 * static ucSharedBuffer[mqttexampleSHARED_BUFFER_SIZE];
 * void sendUnsubscribePacket( int xMQTTSocket )
 * {
 *    IotMqttError_t xResult;
 *    IotMqttPublishInfo_t xMQTTPublishInfo;
 *    size_t xRemainingLength = 0;
 *    size_t xPacketSize = 0;
 *    size_t xSentBytes = 0;
 *    uint16_t usPacketIdentifier;
 *    uint8_t * pusPacketIdentifierHigh;
 *
 *    // Initialize Publish parameters. Details are out of scope for this example.
 *    // It will involve setting QOS, topic filter, topic filter length, payload
 *    // payload length.
 *    _initializePublish( &xMQTTPublishInfo );
 *
 *    // Find out length of Publish packet size.
 *    xResult = IotMqtt_GetPublishPacketSize( &xMQTTPublishInfo, &xRemainingLength, &xPacketSize );
 *    IotMqtt_Assert( xResult == IOT_MQTT_SUCCESS );
 *    // Make sure the packet size is less than static buffer size
 *	  IotMqtt_Assert( xPacketSize < mqttexampleSHARED_BUFFER_SIZE );
 * 
 *    xResult = IotMqtt_SerializePublish( &xMQTTPublishInfo,
 *										xRemainingLength,
 *										&usPacketIdentifier,
 *										&pusPacketIdentifierHigh,
 *										ucSharedBuffer,
 *										xPacketSize );
 *    IotMqtt_Assert( xResult == IOT_MQTT_SUCCESS ); 
 * 
 *    // xMQTTSocket here is posix socket created and connected to MQTT broker outside of this function.
 *    xSentBytes = send( xMQTTSocket, ( void * ) ucSharedBuffer, xPacketSize, 0 );
 *    IotMqtt_Assert( xSentBytes == xPacketSize );
 * }
 * @endcode
 */
/* @[declare_mqtt_serializepublish] */
IotMqttError_t IotMqtt_SerializePublish( IotMqttPublishInfo_t * pPublishInfo,
                                         size_t remainingLength,
                                         uint16_t * pPacketIdentifier,
                                         uint8_t ** pPacketIdentifierHigh,
                                         uint8_t * pBuffer,
                                         size_t bufferSize );
/* @[declare_mqtt_serializepublish] */

/**
 * @brief Generate a DISCONNECT packet
 *
 * @param[in, out] pBuffer User provide buffer where the DISCONNECT packet is written.
 * @param[in] bufferSize Size of the buffer pointed to by pBuffer.
 *
 * @return  returns #IOT_MQTT_SUCCESS or #IOT_MQTT_BAD_PARAMETER
 *
 * @note This call is part of serializer API used for implementing light-weight MQTT client.
 * 
 * <b>Example</b>
 * @code{c}
 * // Example below shows how IotMqtt_SerializeDisconnect() should be used.
 * 
 * #define mqttexampleSHARED_BUFFER_SIZE 100
 * static ucSharedBuffer[mqttexampleSHARED_BUFFER_SIZE];
 * void sendDisconnectRequest( int xMQTTSocket )
 * {
 *     size_t xSentBytes = 0;
 * 
 *    // Disconnect is fixed length packet, therefore there is no need to calculate the size,
 *    // just makes sure static buffer can accommodate disconnect request.
 *    IotMqtt_Assert( MQTT_PACKET_DISCONNECT_SIZE <= mqttexampleSHARED_BUFFER_SIZE );
 *
 *    // Serialize Disconnect packet into static buffer (dynamically allocated buffer can be used as well)
 *    xResult = IotMqtt_SerializeDisconnect( ucSharedBuffer, MQTT_PACKET_DISCONNECT_SIZE );
 *    IotMqtt_Assert( xResult == IOT_MQTT_SUCCESS );
 *
 *    // xMQTTSocket here is posix socket created and connected to MQTT broker outside of this function.
 *    xSentByte = send( xMQTTSocket, ( void * ) ucSharedBuffer, MQTT_PACKET_DISCONNECT_SIZE, 0 );
 *    IotMqtt_Assert( xSentByte == MQTT_PACKET_DISCONNECT_SIZE );
 * }
 *	
 * @endcode
 */
/* @[declare_mqtt_serializedisconnect] */
IotMqttError_t IotMqtt_SerializeDisconnect( uint8_t * pBuffer,
                                            size_t bufferSize );
/* @[declare_mqtt_serializedisconnect] */

/**
 * @brief Generate a PINGREQ packet.
 *
 * @param[in, out] pBuffer User provide buffer where the PINGREQ packet is written.
 * @param[in] bufferSize Size of the buffer pointed to by pBuffer.
 *
 * @return #IOT_MQTT_SUCCESS or #IOT_MQTT_BAD_PARAMETER.
 * 
 * @note This call is part of serializer API used for implementing light-weight MQTT client.
 * 
 * <b>Example</b>
 * @code{c}
 * // Example below shows how IotMqtt_SerializePingReq() should be used.
 * 
 * #define mqttexampleSHARED_BUFFER_SIZE 100
 * static ucSharedBuffer[mqttexampleSHARED_BUFFER_SIZE];
 * void sendPingRequest( int xMQTTSocket )
 * {
 *    size_t xSentBytes = 0;
 * 
 *    // PingReq is fixed length packet, therefore there is no need to calculate the size,
 *    // just makes sure static buffer can accommodate Ping request.
 *    IotMqtt_Assert( MQTT_PACKET_PINGREQ_SIZE <= mqttexampleSHARED_BUFFER_SIZE );
 *
 *    xResult = IotMqtt_SerializePingreq( ucSharedBuffer, MQTT_PACKET_PINGREQ_SIZE );
 *    IotMqtt_Assert( xResult == IOT_MQTT_SUCCESS );
 *    
 *    // xMQTTSocket here is posix socket created and connected to MQTT broker outside of this function.
 *    xSentByte = send( xMQTTSocket, ( void * ) ucSharedBuffer, MQTT_PACKET_DISCONNECT_SIZE, 0 );
 *    IotMqtt_Assert( xSentByte ==  MQTT_PACKET_PINGREQ_SIZE); 
 * }
 * @endcode
 */
/* @[declare_mqtt_serializepingreq] */
IotMqttError_t IotMqtt_SerializePingreq( uint8_t * pBuffer,
                                         size_t bufferSize );
/* @[declare_mqtt_serializepingreq] */

/**
 * @brief Extract MQTT packet type and length from incoming packet
 *
 * @param[in, out] pIncomingPacket Pointer to IotMqttPacketInfo_t structure
 * where type, remaining length and packet identifier are stored.
 * @param[in] getNextByte Pointer to platform specific function  which is used
 * to extract type and length from incoming received stream (see example ).
 * @param[in] pNetworkConnection Pointer to platform specific network connection
 * which is used by getNextByte to receive network data
 *
 * @return #IOT_MQTT_SUCCESS on successful extraction of type and length,
 * #IOT_MQTT_BAD_RESPONSE on failure.
 *
 * @note This call is part of serializer API used for implementing light-weight MQTT client.
 *
 * <b>Example</b>
 * @code{c}
 * // Example code below shows how to implement getNetxByte function with posix sockets.
 * // Note: IotMqttGetNextByte_t typedef IotMqttError_t (* IotMqttGetNextByte_t)( void * pNetworkContext,
 * //                                              uint8_t * pNextByte );
 * // Note: It is assumed that socket is already created and connected,
 *
 * IotMqttError_t getNextByte( void * pContext,
 *                           uint8_t * pNextByte )
 * {
 *      int socket = ( int ) ( *pvContext );
 *      int receivedBytes;
 *      IotMqttError_t result;
 *
 *      receivedBytes = recv( socket, ( void * ) pNextByte, sizeof( uint8_t ), 0 );
 *
 *      if( receivedBytes == sizeof( uint8_t ) )
 *      {
 *          result = IOT_MQTT_SUCCESS;
 *      }
 *      else
 *      {
 *          result = IOT_MQTT_TIMEOUT;
 *      }
 *
 *       return result;
 * }
 * 
 * // Example below shows how IotMqtt_GetIncomingMQTTPacketTypeAndLength() is used to extract type
 * // and length from incoming ping response.
 * // xMQTTSocket here is posix socket created and connected to MQTT broker outside of this function.
 * void getTypeAndLengthFromIncomingMQTTPingResponse( int xMQTTSocket )
 * {
 *    IotMqttPacketInfo_t xIncomingPacket;
 *    IotMqttError_t xResult = IotMqtt_GetIncomingMQTTPacketTypeAndLength( &xIncomingPacket, getNextByte, ( void * ) xMQTTSocket );
 *	  IotMqtt_Assert( xResult == IOT_MQTT_SUCCESS );
 *    IotMqtt_Assert( xIncomingPacket.type == MQTT_PACKET_TYPE_PINGRESP );
 * }
 * @endcode
 *
 */
/* @[declare_mqtt_getincomingmqttpackettypeandlength] */
IotMqttError_t IotMqtt_GetIncomingMQTTPacketTypeAndLength( IotMqttPacketInfo_t * pIncomingPacket,
                                                           IotMqttGetNextByte_t getNextByte,
                                                           void * pNetworkConnection );
/* @[declare_mqtt_getincomingmqttpackettypeandlength] */

/**
 * @brief Deserialize incoming publish packet.
 *
 * @param[in, out] pMqttPacket The caller of this API sets type, remainingLength and pRemainingData.
 * On success, packetIdentifier and pubInfo will be set by the function.
 *
 * @return One of the following:
 * - #IOT_MQTT_SUCCESS
 * - #IOT_MQTT_BAD_RESPONSE
 * - #IOT_MQTT_SERVER_REFUSED
 *
 * @note This call is part of serializer API used for implementing light-weight MQTT client.
 * 
 * <b>Example</b>
 * @code{c}
 * // Example below shows how IotMqtt_DeserializePublish() used to extract contents of incoming 
 * // Publish.  xMQTTSocket here is posix socket created and connected to MQTT broker outside of this function.
 * void processIncomingPublish( int xMQTTSocket )
 * {
 *    IotMqttError_t xResult;
 *    IotMqttPacketInfo_t xIncomingPacket;
 *
 *	  xResult = IotMqtt_GetIncomingMQTTPacketTypeAndLength( &xIncomingPacket, getNextByte, ( void * ) xMQTTSocket );
 *	  IotMqtt_Assert( xResult == IOT_MQTT_SUCCESS );
 *	  IotMqtt_Assert( ( xIncomingPacket.type & 0xf0 ) == MQTT_PACKET_TYPE_PUBLISH );
 *	  IotMqtt_Assert( xIncomingPacket.remainingLength <= mqttexampleSHARED_BUFFER_SIZE );
 *
 *	  // Receive the remaining bytes.
 *	  if( recv( xMQTTSocket, ( void * ) ucSharedBuffer, xIncomingPacket.remainingLength, 0 ) ==  xIncomingPacket.remainingLength )
 *	  {
 *		xIncomingPacket.pRemainingData = ucSharedBuffer;
 *
 *		if( IotMqtt_DeserializePublish( &xIncomingPacket ) != IOT_MQTT_SUCCESS )
 *		{
 *			xResult = IOT_MQTT_BAD_RESPONSE;
 *		}
 *		else
 *		{
 *			// Process incoming Publish.
 *			IotLogInfo( "Incoming QOS : %d\n", xIncomingPacket.pubInfo.qos );
 *			IotLogInfo( "Incoming Publish Topic Name: %.*s\n", xIncomingPacket.pubInfo.topicNameLength, xIncomingPacket.pubInfo.pTopicName );
 *			IotLogInfo( "Incoming Publish Message : %.*s\n", xIncomingPacket.pubInfo.payloadLength, xIncomingPacket.pubInfo.pPayload  );
 *		}
 *	  }
 *	  else
 *	  {
 *		xResult = IOT_MQTT_NETWORK_ERROR;
 *	  }
 *
 *	IotMqtt_Assert( xResult == IOT_MQTT_SUCCESS );
 * }
 * @endcode
 */
/* @[declare_mqtt_deserializepublish] */
IotMqttError_t IotMqtt_DeserializePublish( IotMqttPacketInfo_t * pMqttPacket );
/* @[declare_mqtt_deserializepublish] */

/**
 * @brief Deserialize incoming ack packets.
 *
 * @param[in, out] pMqttPacket The caller of this API sets type, remainingLength and pRemainingData.
 * On success, packetIdentifier will be set.
 *
 * @return One of the following:
 * - #IOT_MQTT_SUCCESS
 * - #IOT_MQTT_BAD_RESPONSE
 * - #IOT_MQTT_SERVER_REFUSED
 *
 * @note This call is part of serializer API used for implementing light-weight MQTT client.
 * 
 * <b>Example</b>
 * @code{c}
 * // Example below shows how  IotMqtt_DeserializeResponse() is used to process unsubscribe ack.
 * // xMQTTSocket here is posix socket created and connected to MQTT broker outside of this function.
 * void processUnsubscribeAck( int xMQTTSocket )
 * {
 *      IotMqttError_t xResult;
 *      IotMqttPacketInfo_t xIncomingPacket;
 * 
 * 		xResult = IotMqtt_GetIncomingMQTTPacketTypeAndLength( &xIncomingPacket, getNextByte, ( void * ) xMQTTSocket );
 *		IotMqtt_Assert( xResult == IOT_MQTT_SUCCESS );
 *		IotMqtt_Assert( xIncomingPacket.type == MQTT_PACKET_TYPE_UNSUBACK );
 *		IotMqtt_Assert( xIncomingPacket.remainingLength <= sizeof( ucSharedBuffer ) );
 *
 *		// Receive the remaining bytes.
 *		if( recv( xMQTTSocket, ( void * ) ucSharedBuffer, xIncomingPacket.remainingLength, 0 ) == xIncomingPacket.remainingLength )
 *		{
 *			xIncomingPacket.pRemainingData = ucSharedBuffer;
 *
 *			if( IotMqtt_DeserializeResponse( &xIncomingPacket ) != IOT_MQTT_SUCCESS )
 *			{
 *				xResult = IOT_MQTT_BAD_RESPONSE;
 *			}
 *		}
 *		else
 *		{
 *			xResult = IOT_MQTT_NETWORK_ERROR;
 *		}
 *      IotMqtt_Assert( xResult == IOT_MQTT_SUCCESS );
 * }
 * @endcode
 */
/* @[declare_mqtt_deserializeresponse] */
IotMqttError_t IotMqtt_DeserializeResponse( IotMqttPacketInfo_t * pMqttPacket );
/* @[declare_mqtt_deserializeresponse] */



#endif /* ifndef IOT_MQTT_SERIALIZE_H_ */
