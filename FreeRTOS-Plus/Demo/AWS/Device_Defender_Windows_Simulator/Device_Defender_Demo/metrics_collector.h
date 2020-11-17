/*
 * FreeRTOS Kernel V10.3.0
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
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

#ifndef METRICS_COLLECTOR_H_
#define METRICS_COLLECTOR_H_

/**
 * @brief Return codes from metrics collector APIs.
 */
typedef enum
{
    MetricsCollectorSuccess = 0,
    MetricsCollectorBadParameter,
    MetricsCollectorCollectionFailed
} MetricsCollectorStatus_t;

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
 * This function finds the network stats by reading "/proc/net/dev".
 *
 * @param[out] pxOutNetworkStats The network stats.
 *
 * @return #MetricsCollectorSuccess if the network stats are successfully obtained;
 * #MetricsCollectorBadParameter if invalid parameters are passed;
 * #MetricsCollectorFileOpenFailed if the function fails to open "/proc/net/dev";
 * MetricsCollectorParsingFailed if the function fails to parses the data read
 * from "/proc/net/dev".
 */
MetricsCollectorStatus_t xGetNetworkStats( NetworkStats_t * pxOutNetworkStats );

/**
 * @brief Get a list of the open TCP ports.
 *
 * This function finds the open TCP ports by reading "/proc/net/tcp". It can be
 * called with @p pusOutTcpPortsArray NULL to get the number of the open TCP ports.
 *
 * @param[in] pusOutTcpPortsArray The array to write the open TCP ports into. This
 * can be NULL, if only the number of open ports is needed.
 * @param[in] ulTcpPortsArrayLength Length of the pusOutTcpPortsArray, if it is not
 * NULL.
 * @param[out] pulOutNumTcpOpenPorts Number of the open TCP ports.
 *
 * @return #MetricsCollectorSuccess if open TCP ports are successfully obtained;
 * #MetricsCollectorBadParameter if invalid parameters are passed;
 * #MetricsCollectorFileOpenFailed if the function fails to open "/proc/net/tcp";
 * MetricsCollectorParsingFailed if the function fails to parses the data read
 * from "/proc/net/tcp".
 */
MetricsCollectorStatus_t xGetOpenTcpPorts( uint16_t * pusOutTcpPortsArray,
                                           uint32_t ulTcpPortsArrayLength,
                                           uint32_t * pulOutNumTcpOpenPorts );

/**
 * @brief Get a list of the open UDP ports.
 *
 * This function finds the open UDP ports by reading "/proc/net/udp". It can be
 * called with pusOutUdpPortsArray NULL to get the number of the open UDP ports.
 *
 * @param[in] pusOutUdpPortsArray The array to write the open UDP ports into. Can
 * be NULL, if only number of open ports is needed.
 * @param[in] ulUdpPortsArrayLength Length of the pusOutUdpPortsArray, if it is not
 * NULL.
 * @param[out] pulOutNumUdpOpenPorts Number of the open UDP ports.
 *
 * @return #MetricsCollectorSuccess if open UDP ports are successfully obtained;
 * #MetricsCollectorBadParameter if invalid parameters are passed;
 * #MetricsCollectorFileOpenFailed if the function fails to open "/proc/net/udp";
 * MetricsCollectorParsingFailed if the function fails to parses the data read
 * from "/proc/net/udp".
 */
MetricsCollectorStatus_t xGetOpenUdpPorts( uint16_t * pusOutUdpPortsArray,
                                           uint32_t ulUdpPortsArrayLength,
                                           uint32_t * pulOutNumUdpOpenPorts );

/**
 * @brief Get a list of established connections.
 *
 * This function finds the established connections by reading "/proc/net/tcp".
 * It can be called with @p pxOutConnectionsArray NULL to get the number of
 * established connections.
 *
 * @param[in] pxOutConnectionsArray The array to write the established connections
 * into. This can be NULL, if only the number of established connections is
 * needed.
 * @param[in] ulConnectionsArrayLength Length of the pxOutConnectionsArray, if it
 * is not NULL.
 * @param[out] pulOutNumEstablishedConnections Number of the established connections.
 *
 * @return #MetricsCollectorSuccess if established connections are successfully obtained;
 * #MetricsCollectorBadParameter if invalid parameters are passed;
 * #MetricsCollectorFileOpenFailed if the function fails to open "/proc/net/tcp";
 * MetricsCollectorParsingFailed if the function fails to parses the data read
 * from "/proc/net/tcp".
 */
MetricsCollectorStatus_t GetEstablishedConnections( Connection_t * pxOutConnectionsArray,
                                                    uint32_t ulConnectionsArrayLength,
                                                    uint32_t * pulOutNumEstablishedConnections );

#endif /* ifndef METRICS_COLLECTOR_H_ */
