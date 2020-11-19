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
 * @file metrics_collector.c
 *
 * @brief Functions used by the defender demo to collect metrics on the
 * device's open ports and sockets. FreeRTOS+TCP tcp_netstat utility
 * is used to collect this metrics.
 */

/* Standard includes. */
#include <stdio.h>
#include <ctype.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "FreeRTOS_IP.h"

/* FreeRTOS+TCP tcp_netstat utility include. */
#include "tcp_netstat.h"

/* Demo config. */
#include "demo_config.h"

/* Interface include. */
#include "metrics_collector.h"
/*-----------------------------------------------------------*/

eMetricsCollectorStatus eGetNetworkStats( NetworkStats_t * pxOutNetworkStats )
{
    eMetricsCollectorStatus eStatus = eMetricsCollectorSuccess;

    MetricsType_t xMetrics = { 0 };
    BaseType_t xMetricsStatus = 0;

    configASSERT( pxOutNetworkStats != NULL );

    if( eStatus == eMetricsCollectorSuccess )
    {
        /* Start with everything as zero. */
        memset( pxOutNetworkStats, 0, sizeof( NetworkStats_t ) );

        /* Get metrics from FreeRTOS+TCP tcp_netstat utility. */
        xMetricsStatus = vGetMetrics( &xMetrics );

        if( xMetricsStatus != 0 )
        {
            eStatus = eMetricsCollectorCollectionFailed;
        }
    }

    /* Fill our response with values gotten from FreeRTOS+TCP. */
    if( eStatus == eMetricsCollectorSuccess )
    {
        pxOutNetworkStats->ulBytesReceived = xMetrics.xInput.uxByteCount;
        pxOutNetworkStats->ulPacketsReceived = xMetrics.xInput.uxPacketCount;
        pxOutNetworkStats->ulBytesSent = xMetrics.XOutput.uxByteCount;
        pxOutNetworkStats->ulPacketsSent = xMetrics.XOutput.uxPacketCount;
    }

    return eStatus;
}
/*-----------------------------------------------------------*/

eMetricsCollectorStatus eGetOpenTcpPorts( uint16_t * pusOutTcpPortsArray,
                                          uint32_t ulTcpPortsArrayLength,
                                          uint32_t * pulOutNumTcpOpenPorts )
{
    eMetricsCollectorStatus eStatus = eMetricsCollectorSuccess;

    MetricsType_t xMetrics = { 0 };
    BaseType_t xMetricsStatus = 0;

    /* pusOutTcpPortsArray can be NULL. */
    configASSERT( pulOutNumTcpOpenPorts != NULL );

    if( eStatus == eMetricsCollectorSuccess )
    {
        /* Get metrics from FreeRTOS+TCP tcp_netstat utility. */
        xMetricsStatus = vGetMetrics( &xMetrics );

        if( xMetricsStatus != 0 )
        {
            eStatus = eMetricsCollectorCollectionFailed;
        }
    }

    if( eStatus == eMetricsCollectorSuccess )
    {
        /* Set the out value for number of open TCP ports. */
        *pulOutNumTcpOpenPorts = xMetrics.xTCPPortList.uxCount;

        /* Fill the output array with as many tcp ports as will fit in the
         * given array. */
        if( pusOutTcpPortsArray != NULL )
        {
            /* Lower the amount of ports copied if less are open than will fit
             * in the given array. */
            if( xMetrics.xTCPPortList.uxCount < ulTcpPortsArrayLength )
            {
                ulTcpPortsArrayLength = xMetrics.xTCPPortList.uxCount;
            }

            memcpy( pusOutTcpPortsArray, &xMetrics.xTCPPortList.usTCPPortList, ulTcpPortsArrayLength * sizeof( uint16_t ) );
        }
    }

    return eMetricsCollectorSuccess;
}
/*-----------------------------------------------------------*/

eMetricsCollectorStatus eGetOpenUdpPorts( uint16_t * pusOutUdpPortsArray,
                                          uint32_t ulUdpPortsArrayLength,
                                          uint32_t * pulOutNumUdpOpenPorts )
{
    eMetricsCollectorStatus eStatus = eMetricsCollectorSuccess;

    MetricsType_t xMetrics = { 0 };
    BaseType_t xMetricsStatus = 0;

    /* pusOutUdpPortsArray can be NULL. */
    configASSERT( pulOutNumUdpOpenPorts != NULL );

    if( eStatus == eMetricsCollectorSuccess )
    {
        /* Get metrics from FreeRTOS+TCP tcp_netstat utility. */
        xMetricsStatus = vGetMetrics( &xMetrics );

        if( xMetricsStatus != 0 )
        {
            eStatus = eMetricsCollectorCollectionFailed;
        }
    }

    if( eStatus == eMetricsCollectorSuccess )
    {
        *pulOutNumUdpOpenPorts = xMetrics.xUDPPortList.uxCount;

        /* Fill the output array with as many udp ports as will fit in the
         * given array. */
        if( pusOutUdpPortsArray != NULL )
        {
            /* Lower the amount of ports copied if less are open than will fit
             * in the given array. */
            if( xMetrics.xUDPPortList.uxCount < ulUdpPortsArrayLength )
            {
                ulUdpPortsArrayLength = xMetrics.xUDPPortList.uxCount;
            }

            memcpy( pusOutUdpPortsArray, &xMetrics.xUDPPortList.usUDPPortList, ulUdpPortsArrayLength * sizeof( uint16_t ) );
        }
    }

    return eMetricsCollectorSuccess;
}

/*-----------------------------------------------------------*/

eMetricsCollectorStatus eGetEstablishedConnections( Connection_t * pxOutConnectionsArray,
                                                    uint32_t ulConnectionsArrayLength,
                                                    uint32_t * pulOutNumEstablishedConnections )
{
    eMetricsCollectorStatus eStatus = eMetricsCollectorSuccess;

    MetricsType_t xMetrics = { 0 };
    BaseType_t xMetricsStatus = 0;
    uint32_t ulLocalIp = 0UL;

    /* pxOutConnectionsArray can be NULL. */
    configASSERT( pulOutNumEstablishedConnections != NULL );

    if( eStatus == eMetricsCollectorSuccess )
    {
        /* Get metrics from FreeRTOS+TCP tcp_netstat utility. */
        xMetricsStatus = vGetMetrics( &xMetrics );

        if( xMetricsStatus != 0 )
        {
            eStatus = eMetricsCollectorCollectionFailed;
        }
    }

    if( eStatus == eMetricsCollectorSuccess )
    {
        /* We consider only TCP sockets for open connections. */
        *pulOutNumEstablishedConnections = xMetrics.xTCPSocketList.uxCount;

        /* Fill the output array with as many tcp socket infos as will fit in
         * the given array. */
        if( pxOutConnectionsArray != NULL )
        {
            /* Get local IP as the tcp_netstat utility does not give it. */
            ulLocalIp = FreeRTOS_GetIPAddress();

            /* Lower the amount of socket infos populated if less are open than will fit
             * in the given array. */
            if( xMetrics.xTCPSocketList.uxCount < ulConnectionsArrayLength )
            {
                ulConnectionsArrayLength = xMetrics.xTCPSocketList.uxCount;
            }

            /* If xMetrics.xTCPSocketList.uxCount > ulConnectionsArrayLength, we
             * return the first ulConnectionsArrayLength ports. */
            while( ulConnectionsArrayLength > 0 )
            {
                ulConnectionsArrayLength--;
                pxOutConnectionsArray[ ulConnectionsArrayLength ].ulLocalIp = ulLocalIp;
                pxOutConnectionsArray[ ulConnectionsArrayLength ].usLocalPort =
                    xMetrics.xTCPSocketList.xTCPList[ ulConnectionsArrayLength ].usLocalPort;
                pxOutConnectionsArray[ ulConnectionsArrayLength ].ulRemoteIp =
                    xMetrics.xTCPSocketList.xTCPList[ ulConnectionsArrayLength ].ulRemoteIP;
                pxOutConnectionsArray[ ulConnectionsArrayLength ].usRemotePort =
                    xMetrics.xTCPSocketList.xTCPList[ ulConnectionsArrayLength ].usRemotePort;
            }
        }
    }

    return eStatus;
}
/*-----------------------------------------------------------*/
