/*
 * FreeRTOS V202012.00
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

    /* Start with everything as zero. */
    memset( pxOutNetworkStats, 0, sizeof( NetworkStats_t ) );

    /* Get metrics from FreeRTOS+TCP tcp_netstat utility. */
    xMetricsStatus = vGetMetrics( &xMetrics );

    if( xMetricsStatus != 0 )
    {
        LogError( ( "Failed to acquire metrics from FreeRTOS+TCP tcp_netstat utility. Status: %d.",
                    ( int ) xMetricsStatus ) );
        eStatus = eMetricsCollectorCollectionFailed;
    }

    /* Fill our response with values gotten from FreeRTOS+TCP. */
    if( eStatus == eMetricsCollectorSuccess )
    {
        LogDebug( ( "Network stats read. Bytes received: %u, packets received: %u, "
                    "bytes sent: %u, packets sent: %u.",
                    ( unsigned int ) xMetrics.xInput.uxByteCount,
                    ( unsigned int ) xMetrics.xInput.uxPacketCount,
                    ( unsigned int ) xMetrics.xOutput.uxByteCount,
                    ( unsigned int ) xMetrics.xOutput.uxPacketCount ) );

        pxOutNetworkStats->ulBytesReceived = xMetrics.xInput.uxByteCount;
        pxOutNetworkStats->ulPacketsReceived = xMetrics.xInput.uxPacketCount;
        pxOutNetworkStats->ulBytesSent = xMetrics.xOutput.uxByteCount;
        pxOutNetworkStats->ulPacketsSent = xMetrics.xOutput.uxPacketCount;
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
    uint32_t ulCopyAmount = 0UL;

    /* pusOutTcpPortsArray can be NULL. */
    configASSERT( pulOutNumTcpOpenPorts != NULL );

    /* Get metrics from FreeRTOS+TCP tcp_netstat utility. */
    xMetricsStatus = vGetMetrics( &xMetrics );

    if( xMetricsStatus != 0 )
    {
        LogError( ( "Failed to acquire metrics from FreeRTOS+TCP tcp_netstat utility. Status: %d.",
                    ( int ) xMetricsStatus ) );
        eStatus = eMetricsCollectorCollectionFailed;
    }

    if( eStatus == eMetricsCollectorSuccess )
    {
        /* Fill the output array with as many TCP ports as will fit in the
         * given array. */
        if( pusOutTcpPortsArray != NULL )
        {
            ulCopyAmount = xMetrics.xTCPPortList.uxCount;

            /* Limit the copied ports to what can fit in the output array. */
            if( ulTcpPortsArrayLength < xMetrics.xTCPPortList.uxCount )
            {
                LogWarn( ( "Ports returned truncated due to insufficient buffer size." ) );
                ulCopyAmount = ulTcpPortsArrayLength;
            }

            memcpy( pusOutTcpPortsArray, &xMetrics.xTCPPortList.usTCPPortList, ulCopyAmount * sizeof( uint16_t ) );

            /* Return the number of elements copied to the array. */
            *pulOutNumTcpOpenPorts = ulCopyAmount;
        }
        else
        {
            /* Return the total number of open ports. */
            *pulOutNumTcpOpenPorts = xMetrics.xTCPPortList.uxCount;
        }
    }

    return eStatus;
}
/*-----------------------------------------------------------*/

eMetricsCollectorStatus eGetOpenUdpPorts( uint16_t * pusOutUdpPortsArray,
                                          uint32_t ulUdpPortsArrayLength,
                                          uint32_t * pulOutNumUdpOpenPorts )
{
    eMetricsCollectorStatus eStatus = eMetricsCollectorSuccess;

    MetricsType_t xMetrics = { 0 };
    BaseType_t xMetricsStatus = 0;
    uint32_t ulCopyAmount = 0UL;

    /* pusOutUdpPortsArray can be NULL. */
    configASSERT( pulOutNumUdpOpenPorts != NULL );

    /* Get metrics from FreeRTOS+TCP tcp_netstat utility. */
    xMetricsStatus = vGetMetrics( &xMetrics );

    if( xMetricsStatus != 0 )
    {
        LogError( ( "Failed to acquire metrics from FreeRTOS+TCP tcp_netstat utility. Status: %d.",
                    ( int ) xMetricsStatus ) );
        eStatus = eMetricsCollectorCollectionFailed;
    }

    if( eStatus == eMetricsCollectorSuccess )
    {
        /* Fill the output array with as many UDP ports as will fit in the
         * given array. */
        if( pusOutUdpPortsArray != NULL )
        {
            ulCopyAmount = xMetrics.xUDPPortList.uxCount;

            /* Limit the copied ports to what can fit in the output array. */
            if( ulUdpPortsArrayLength < xMetrics.xUDPPortList.uxCount )
            {
                LogWarn( ( "Ports returned truncated due to insufficient buffer size." ) );
                ulCopyAmount = ulUdpPortsArrayLength;
            }

            memcpy( pusOutUdpPortsArray, &xMetrics.xUDPPortList.usUDPPortList, ulCopyAmount * sizeof( uint16_t ) );

            /* Return the number of elements copied to the array. */
            *pulOutNumUdpOpenPorts = ulCopyAmount;
        }
        else
        {
            /* Return the total number of open ports. */
            *pulOutNumUdpOpenPorts = xMetrics.xUDPPortList.uxCount;
        }
    }

    return eStatus;
}

/*-----------------------------------------------------------*/

eMetricsCollectorStatus eGetEstablishedConnections( Connection_t * pxOutConnectionsArray,
                                                    uint32_t ulConnectionsArrayLength,
                                                    uint32_t * pulOutNumEstablishedConnections )
{
    eMetricsCollectorStatus eStatus = eMetricsCollectorSuccess;

    MetricsType_t xMetrics = { 0 };
    BaseType_t xMetricsStatus = 0;
    uint32_t ulCopyAmount = 0UL;
    uint32_t ulLocalIp = 0UL;
    uint32_t i;

    /* pxOutConnectionsArray can be NULL. */
    configASSERT( pulOutNumEstablishedConnections != NULL );

    /* Get metrics from FreeRTOS+TCP tcp_netstat utility. */
    xMetricsStatus = vGetMetrics( &xMetrics );

    if( xMetricsStatus != 0 )
    {
        LogError( ( "Failed to acquire metrics from FreeRTOS+TCP tcp_netstat utility. Status: %d.",
                    ( int ) xMetricsStatus ) );
        eStatus = eMetricsCollectorCollectionFailed;
    }

    if( eStatus == eMetricsCollectorSuccess )
    {
        /* Fill the output array with as many TCP socket infos as will fit in
         * the given array. */
        if( pxOutConnectionsArray != NULL )
        {
            ulCopyAmount = xMetrics.xTCPSocketList.uxCount;

            /* Get local IP as the tcp_netstat utility does not give it. */
            ulLocalIp = FreeRTOS_GetIPAddress();

            /* Limit the outputted connections to what can fit in the output array. */
            if( ulConnectionsArrayLength < xMetrics.xTCPSocketList.uxCount )
            {
                LogWarn( ( "Ports returned truncated due to insufficient buffer size." ) );
                ulCopyAmount = ulConnectionsArrayLength;
            }

            for( i = 0; i < ulCopyAmount; i++ )
            {
                pxOutConnectionsArray[ i ].ulLocalIp = ulLocalIp;
                pxOutConnectionsArray[ i ].usLocalPort =
                    xMetrics.xTCPSocketList.xTCPList[ i ].usLocalPort;
                pxOutConnectionsArray[ i ].ulRemoteIp =
                    xMetrics.xTCPSocketList.xTCPList[ i ].ulRemoteIP;
                pxOutConnectionsArray[ i ].usRemotePort =
                    xMetrics.xTCPSocketList.xTCPList[ i ].usRemotePort;
            }

            /* Return the number of elements copied to the array. */
            *pulOutNumEstablishedConnections = ulCopyAmount;
        }
        else
        {
            /* Return the total number of established connections. */
            *pulOutNumEstablishedConnections = xMetrics.xTCPSocketList.uxCount;
        }
    }

    return eStatus;
}
/*-----------------------------------------------------------*/
