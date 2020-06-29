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
 * @file iot_mqtt_protocol.h
 * @brief This file contains MQTT 3.1.1 specific defines. This is a common header
 * to be included for building a single threaded light-weight MQTT client as well
 * as stateful CSDK MQTT library.
 */

#ifndef IOT_MQTT_PROTOCOL_H_
#define IOT_MQTT_PROTOCOL_H_

/*
 * MQTT control packet type and flags. Always the first byte of an MQTT
 * packet.
 *
 * For details, see
 * http://docs.oasis-open.org/mqtt/mqtt/v3.1.1/csprd02/mqtt-v3.1.1-csprd02.html#_Toc385349757
 */
#define MQTT_PACKET_TYPE_CONNECT         ( ( uint8_t ) 0x10U )                       /**< @brief CONNECT (client-to-server). */
#define MQTT_PACKET_TYPE_CONNACK         ( ( uint8_t ) 0x20U )                       /**< @brief CONNACK (server-to-client). */
#define MQTT_PACKET_TYPE_PUBLISH         ( ( uint8_t ) 0x30U )                       /**< @brief PUBLISH (bidirectional). */
#define MQTT_PACKET_TYPE_PUBACK          ( ( uint8_t ) 0x40U )                       /**< @brief PUBACK (server-to-client). */
#define MQTT_PACKET_TYPE_SUBSCRIBE       ( ( uint8_t ) 0x82U )                       /**< @brief SUBSCRIBE (client-to-server). */
#define MQTT_PACKET_TYPE_SUBACK          ( ( uint8_t ) 0x90U )                       /**< @brief SUBACK (server-to-client). */
#define MQTT_PACKET_TYPE_UNSUBSCRIBE     ( ( uint8_t ) 0xa2U )                       /**< @brief UNSUBSCRIBE (client-to-server). */
#define MQTT_PACKET_TYPE_UNSUBACK        ( ( uint8_t ) 0xb0U )                       /**< @brief UNSUBACK (server-to-client). */
#define MQTT_PACKET_TYPE_PINGREQ         ( ( uint8_t ) 0xc0U )                       /**< @brief PINGREQ (client-to-server). */
#define MQTT_PACKET_TYPE_PINGRESP        ( ( uint8_t ) 0xd0U )                       /**< @brief PINGRESP (server-to-client). */
#define MQTT_PACKET_TYPE_DISCONNECT      ( ( uint8_t ) 0xe0U )                       /**< @brief DISCONNECT (client-to-server). */

/*
 * Positions of each flag in the "Connect Flag" field of an MQTT CONNECT
 * packet.
 */
#define MQTT_CONNECT_FLAG_CLEAN          ( 1 )             /**< @brief Clean session. */
#define MQTT_CONNECT_FLAG_WILL           ( 2 )             /**< @brief Will present. */
#define MQTT_CONNECT_FLAG_WILL_QOS1      ( 3 )             /**< @brief Will QoS1. */
#define MQTT_CONNECT_FLAG_WILL_QOS2      ( 4 )             /**< @brief Will QoS2. */
#define MQTT_CONNECT_FLAG_WILL_RETAIN    ( 5 )             /**< @brief Will retain. */
#define MQTT_CONNECT_FLAG_PASSWORD       ( 6 )             /**< @brief Password present. */
#define MQTT_CONNECT_FLAG_USERNAME       ( 7 )             /**< @brief Username present. */

/*
 * Positions of each flag in the first byte of an MQTT PUBLISH packet's
 * fixed header.
 */
#define MQTT_PUBLISH_FLAG_RETAIN         ( 0 )             /**< @brief Message retain flag. */
#define MQTT_PUBLISH_FLAG_QOS1           ( 1 )             /**< @brief Publish QoS 1. */
#define MQTT_PUBLISH_FLAG_QOS2           ( 2 )             /**< @brief Publish QoS 2. */
#define MQTT_PUBLISH_FLAG_DUP            ( 3 )             /**< @brief Duplicate message. */


/**
 * @brief A value that represents an invalid remaining length.
 *
 * This value is greater than what is allowed by the MQTT specification.
 */
#define MQTT_REMAINING_LENGTH_INVALID               ( ( size_t ) 268435456 )

/**
 * @brief The maximum possible size of a CONNECT packet.
 *
 * All strings in a CONNECT packet are constrained to 2-byte lengths, giving a
 * maximum length smaller than the max "Remaining Length" constant above.
 */
#define MQTT_PACKET_CONNECT_MAX_SIZE                ( 327700UL )

/**
 * @brief The minimum remaining length for a QoS 0 PUBLISH.
 *
 * Includes two bytes for topic name length and one byte for topic name.
 */
#define MQTT_MIN_PUBLISH_REMAINING_LENGTH_QOS0      ( 3U )

/**
 * @brief Per the MQTT 3.1.1 spec, the largest "Remaining Length" of an MQTT
 * packet is this value.
 */
#define MQTT_MAX_REMAINING_LENGTH                   ( 268435455UL )

/**
 * @brief The constant specifying MQTT version 3.1.1. Placed in the CONNECT packet.
 */
#define MQTT_VERSION_3_1_1                          ( ( uint8_t ) 4U )

/*
 * Constants relating to CONNACK packets, defined by MQTT 3.1.1 spec.
 */
#define MQTT_PACKET_CONNACK_REMAINING_LENGTH        ( ( uint8_t ) 2U )    /**< @brief A CONNACK packet always has a "Remaining length" of 2. */
#define MQTT_PACKET_CONNACK_SESSION_PRESENT_MASK    ( ( uint8_t ) 0x01U ) /**< @brief The "Session Present" bit is always the lowest bit. */

/*
 * Constants relating to PUBLISH and PUBACK packets, defined by MQTT
 * 3.1.1 spec.
 */
#define MQTT_PACKET_PUBACK_SIZE                     ( 4U )              /**< @brief A PUBACK packet is always 4 bytes in size. */
#define MQTT_PACKET_PUBACK_REMAINING_LENGTH         ( ( uint8_t ) 2 )   /**< @brief A PUBACK packet always has a "Remaining length" of 2. */

/*
 * Constants relating to SUBACK and UNSUBACK packets, defined by MQTT
 * 3.1.1 spec.
 */
#define MQTT_PACKET_SUBACK_MINIMUM_SIZE             ( 5U )              /**< @brief The size of the smallest valid SUBACK packet. */
#define MQTT_PACKET_UNSUBACK_REMAINING_LENGTH       ( ( uint8_t ) 2 )   /**< @brief An UNSUBACK packet always has a "Remaining length" of 2. */

/*
 * Constants relating to PINGREQ and PINGRESP packets, defined by MQTT 3.1.1 spec.
 */
#define MQTT_PACKET_PINGREQ_SIZE                    ( 2U ) /**< @brief A PINGREQ packet is always 2 bytes in size. */
#define MQTT_PACKET_PINGRESP_REMAINING_LENGTH       ( 0U ) /**< @brief A PINGRESP packet always has a "Remaining length" of 0. */

/*
 * Constants relating to DISCONNECT packets, defined by MQTT 3.1.1 spec.
 */
#define MQTT_PACKET_DISCONNECT_SIZE                 ( 2U ) /**< @brief A DISCONNECT packet is always 2 bytes in size. */



#endif /* ifndef _IOT_MQTT_PROTOCOL_H_ */
