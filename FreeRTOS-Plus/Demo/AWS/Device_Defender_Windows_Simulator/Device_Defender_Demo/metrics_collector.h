/*
 * FreeRTOS V202011.00
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
 *
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 * 1 tab == 4 spaces!
 */

/**
 * @file metrics_collector.h
 *
 * @brief Functions used by the defender demo to collect metrics on the
 * device's open ports and sockets.
 */

#ifndef METRICS_COLLECTOR_H_
#define METRICS_COLLECTOR_H_

/**
 * @brief Return codes from metrics collector APIs.
 */
typedef enum
{
    eMetricsCollectorSuccess = 0,
    eMetricsCollectorBadParameter,
    eMetricsCollectorCollectionFailed
} eMetricsCollectorStatus;

/**
 * @brief Represents network stats.
 */
typedef struct NetworkStats
{
    uint32_t ulBytesReceived;   /**< Number of bytes received. */
    uint32_t ulBytesSent;       /**< Number of bytes sent. */
    uint32_t ulPacketsReceived; /**< Number of packets (ethernet frames) received. */
    uint32_t ulPacketsSent;     /**< Number of packets (ethernet frames) sent. */
} NetworkStats_t;

/**
 * @brief Represents a network connection.
 */
typedef struct Connection
{
    uint32_t ulLocalIp;
    uint32_t ulRemoteIp;
    uint16_t usLocalPort;
    uint16_t usRemotePort;
} Connection_t;

/**
 * @brief Get network stats.
 *
 * This function returns the network stats.
 *
 * @param[out] pxOutNetworkStats The network stats.
 *
 * @return #MetricsCollectorSuccess if the network stats are successfully obtained;
 * #MetricsCollectorBadParameter if invalid parameters are passed;
 * #MetricsCollectorCollectionFailed if the collection methods failed.
 */
eMetricsCollectorStatus xGetNetworkStats( NetworkStats_t * pxOutNetworkStats );

/**
 * @brief Get a list of the open TCP ports.
 *
 * This function finds the open TCP ports. It can be called with
 * @p pusOutTcpPortsArray NULL to get the number of the open TCP ports.
 *
 * @param[out] pusOutTcpPortsArray The array to write the open TCP ports into. This
 * can be NULL, if only the number of open ports is needed.
 * @param[in] ulTcpPortsArrayLength Length of the pusOutTcpPortsArray, if it is not
 * NULL.
 * @param[out] pulOutNumTcpOpenPorts Number of the open TCP ports.
 *
 * @return #MetricsCollectorSuccess if open TCP ports are successfully obtained;
 * #MetricsCollectorBadParameter if invalid parameters are passed;
 * #MetricsCollectorCollectionFailed if the collection methods failed.
 */
eMetricsCollectorStatus xGetOpenTcpPorts( uint16_t * pusOutTcpPortsArray,
                                           uint32_t ulTcpPortsArrayLength,
                                           uint32_t * pulOutNumTcpOpenPorts );

/**
 * @brief Get a list of the open UDP ports.
 *
 * This function finds the open UDP ports. It can be called with
 * @p pusOutUdpPortsArray NULL to get the number of the open UDP ports.
 *
 * @param[out] pusOutUdpPortsArray The array to write the open UDP ports into. Can
 * be NULL, if only number of open ports is needed.
 * @param[in] ulUdpPortsArrayLength Length of the pusOutUdpPortsArray, if it is not
 * NULL.
 * @param[out] pulOutNumUdpOpenPorts Number of the open UDP ports.
 *
 * @return #MetricsCollectorSuccess if open UDP ports are successfully obtained;
 * #MetricsCollectorBadParameter if invalid parameters are passed;
 * #MetricsCollectorCollectionFailed if the collection methods failed.
 */
eMetricsCollectorStatus xGetOpenUdpPorts( uint16_t * pusOutUdpPortsArray,
                                           uint32_t ulUdpPortsArrayLength,
                                           uint32_t * pulOutNumUdpOpenPorts );

/**
 * @brief Get a list of established connections.
 *
 * This function finds the established TCP connections.
 * It can be called with @p pxOutConnectionsArray NULL to get the number of
 * established connections.
 *
 * @param[out] pxOutConnectionsArray The array to write the established connections
 * into. This can be NULL, if only the number of established connections is
 * needed.
 * @param[in] ulConnectionsArrayLength Length of the pxOutConnectionsArray, if it
 * is not NULL.
 * @param[out] pulOutNumEstablishedConnections Number of the established connections.
 *
 * @return #MetricsCollectorSuccess if established connections are successfully obtained;
 * #MetricsCollectorBadParameter if invalid parameters are passed;
 * #MetricsCollectorCollectionFailed if the collection methods failed.
 */
eMetricsCollectorStatus GetEstablishedConnections( Connection_t * pxOutConnectionsArray,
                                                    uint32_t ulConnectionsArrayLength,
                                                    uint32_t * pulOutNumEstablishedConnections );

#endif /* ifndef METRICS_COLLECTOR_H_ */
