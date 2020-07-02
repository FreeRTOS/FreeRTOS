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
 * @brief Implements internal helper functions for the MQTT library.
 */

#ifndef IOT_MQTT_HELPER_H_
#define IOT_MQTT_HELPER_H_

/* Standard includes. */
#include <string.h>
#include <limits.h>
/* Default assert and memory allocation functions. */
#include <assert.h>
#include <stdlib.h>

/* MQTT Protocol Specific defines */
#include "iot_mqtt_protocol.h"
/* MQTT types include. */
#include "types/iot_mqtt_types.h"

/*-----------------------------------------------------------*/

/*
 * Macros for reading the high and low byte of a 2-byte unsigned int.
 */
#define UINT16_HIGH_BYTE( x )    ( ( uint8_t ) ( ( x ) >> 8 ) )          /**< @brief Get high byte. */
#define UINT16_LOW_BYTE( x )     ( ( uint8_t ) ( ( x ) & 0x00ffU ) )     /**< @brief Get low byte. */

/**
 * @brief Macro for decoding a 2-byte unsigned int from a sequence of bytes.
 *
 * @param[in] ptr A uint8_t* that points to the high byte.
 */
#define UINT16_DECODE( ptr )                                \
    ( uint16_t ) ( ( ( ( uint16_t ) ( *( ptr ) ) ) << 8 ) | \
                   ( ( uint16_t ) ( *( ( ptr ) + 1 ) ) ) )

/**
 * @brief Macro for setting a bit in a 1-byte unsigned int.
 *
 * @param[in] x The unsigned int to set.
 * @param[in] position Which bit to set.
 */
#define UINT8_SET_BIT( x, position )      ( ( x ) = ( uint8_t ) ( ( x ) | ( 0x01U << ( position ) ) ) )

/**
 * @brief Macro for checking if a bit is set in a 1-byte unsigned int.
 *
 * @param[in] x The unsigned int to check.
 * @param[in] position Which bit to check.
 */
#define UINT8_CHECK_BIT( x, position )    ( ( ( x ) & ( 0x01U << ( position ) ) ) == ( 0x01U << ( position ) ) )

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this section.
 *
 * Provide default values for undefined configuration constants.
 */
#ifndef AWS_IOT_MQTT_ENABLE_METRICS
    #define AWS_IOT_MQTT_ENABLE_METRICS    ( 1 )
#endif
/** @endcond */

/*-----------------------------------------------------------*/

/**
 * @brief Calculate the number of bytes required to encode an MQTT
 * "Remaining length" field.
 *
 * @param[in] length The value of the "Remaining length" to encode.
 *
 * @return The size of the encoding of length. This is always `1`, `2`, `3`, or `4`.
 */
size_t _IotMqtt_RemainingLengthEncodedSize( size_t length );


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
bool _IotMqtt_ConnectPacketSize( const IotMqttConnectInfo_t * pConnectInfo,
                                 size_t * pRemainingLength,
                                 size_t * pPacketSize );


/**
 * @brief Generate a CONNECT packet from the given parameters.
 *
 * @param[in] pConnectInfo User-provided CONNECT information.
 * @param[in] remainingLength User provided remaining length.
 * @param[in, out] pPacket User provided buffer where the CONNECT packet is written.
 * @param[in] connectPacketSize Size of the buffer pointed to by `pPacket`.
 *
 */
void _IotMqtt_SerializeConnectCommon( const IotMqttConnectInfo_t * pConnectInfo,
                                      size_t remainingLength,
                                      uint8_t * pPacket,
                                      size_t connectPacketSize );

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
bool _IotMqtt_SubscriptionPacketSize( IotMqttOperationType_t type,
                                      const IotMqttSubscription_t * pSubscriptionList,
                                      size_t subscriptionCount,
                                      size_t * pRemainingLength,
                                      size_t * pPacketSize );

/**
 * @brief Generate a SUBSCRIBE packet from the given parameters.
 *
 * @param[in] pSubscriptionList User-provided array of subscriptions.
 * @param[in] subscriptionCount Size of `pSubscriptionList`.
 * @param[in] remainingLength User provided remaining length.
 * @param[out] pPacketIdentifier The packet identifier generated for this SUBSCRIBE.
 * @param[in, out] pPacket User provided buffer where the SUBSCRIBE packet is written.
 * @param[in] subscribePacketSize Size of the buffer pointed to by  `pPacket`.
 *
 */
void _IotMqtt_SerializeSubscribeCommon( const IotMqttSubscription_t * pSubscriptionList,
                                        size_t subscriptionCount,
                                        size_t remainingLength,
                                        uint16_t * pPacketIdentifier,
                                        uint8_t * pPacket,
                                        size_t subscribePacketSize );

/**
 * @brief Generate an UNSUBSCRIBE packet from the given parameters.
 *
 * @param[in] pSubscriptionList User-provided array of subscriptions to remove.
 * @param[in] subscriptionCount Size of `pSubscriptionList`.
 * @param[in] remainingLength User provided remaining length.
 * @param[out] pPacketIdentifier The packet identifier generated for this UNSUBSCRIBE.
 * @param[in, out] pPacket User provided buffer where the UNSUBSCRIBE packet is written.
 * @param[in] unsubscribePacketSize size of the buffer pointed to by  `pPacket`.
 *
 */
void _IotMqtt_SerializeUnsubscribeCommon( const IotMqttSubscription_t * pSubscriptionList,
                                          size_t subscriptionCount,
                                          size_t remainingLength,
                                          uint16_t * pPacketIdentifier,
                                          uint8_t * pPacket,
                                          size_t unsubscribePacketSize );

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
bool _IotMqtt_PublishPacketSize( const IotMqttPublishInfo_t * pPublishInfo,
                                 size_t * pRemainingLength,
                                 size_t * pPacketSize );

/**
 * @brief Generate a PUBLISH packet from the given parameters.
 *
 * @param[in] pPublishInfo User-provided PUBLISH information.
 * @param[in] remainingLength User provided remaining length.
 * @param[out] pPacketIdentifier The packet identifier generated for this PUBLISH.
 * @param[out] pPacketIdentifierHigh Where the high byte of the packet identifier
 * is written.
 * @param[in, out] pPacket User provided buffer where the PUBLISH packet is written.
 * @param[in] publishPacketSize Size of buffer pointed to by `pPacket`.
 *
 */
void _IotMqtt_SerializePublishCommon( const IotMqttPublishInfo_t * pPublishInfo,
                                      size_t remainingLength,
                                      uint16_t * pPacketIdentifier,
                                      uint8_t ** pPacketIdentifierHigh,
                                      uint8_t * pPacket,
                                      size_t publishPacketSize );

/**
 * @brief Check if an incoming packet type is valid.
 *
 * @param[in] packetType The packet type to check.
 *
 * @return `true` if the packet type is valid; `false` otherwise.
 */
bool _IotMqtt_IncomingPacketValid( uint8_t packetType );

/**
 * @brief Generate and return a 2-byte packet identifier.
 *
 * This packet identifier will be nonzero.
 *
 * @return The packet identifier.
 */
uint16_t _IotMqtt_NextPacketIdentifier( void );

/**
 * @brief Process incoming publish flags.
 *
 * @param[in] publishFlags Incoming publish flags.
 * @param[in, out] pOutput Pointer to #IotMqttPublishInfo_t struct.
 * where output will be written.
 *
 * @return #IOT_MQTT_SUCCESS, #IOT_MQTT_BAD_RESPONSE.
 */

IotMqttError_t _IotMqtt_ProcessPublishFlags( uint8_t publishFlags,
                                             IotMqttPublishInfo_t * pOutput );

#endif /* ifndef IOT_MQTT_HELPER_H_ */
