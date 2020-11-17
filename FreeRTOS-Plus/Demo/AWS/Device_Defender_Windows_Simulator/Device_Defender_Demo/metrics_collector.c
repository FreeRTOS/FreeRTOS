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

/* Standard includes. */
#include <stdio.h>
#include <ctype.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"

/* Metrics includes. */
#include "tcp_netstat.h"

/* Demo config. */
#include "demo_config.h"

/* Interface include. */
#include "metrics_collector.h"

/**
 * @brief The maximum length of line read from any of /proc/net/dev, /proc/net/tcp
 * and /proc/net/udp.
 */
#define MAX_LINE_LENGTH                  ( 256 )

/**
 * @brief Various connection eStatus.
 */
#define CONNECTION_STATUS_LISTEN         ( 10 )
#define CONNECTION_STATUS_ESTABLISHED    ( 1 )

/*-----------------------------------------------------------*/

MetricsCollectorStatus_t xGetNetworkStats( NetworkStats_t * pxOutNetworkStats )
{
    MetricsCollectorStatus_t eStatus = MetricsCollectorSuccess;

    MetricsType_t xMetrics = { 0 };
    BaseType_t xMetricsStatus = 0;

    if( pxOutNetworkStats == NULL )
    {
        LogError( ( "Invalid parameter. pxOutNetworkStats NULL" ) );
        eStatus = MetricsCollectorBadParameter;
    }

    if( eStatus == MetricsCollectorSuccess )
    {
        /* Start with everything as zero. */
        memset( pxOutNetworkStats, 0, sizeof( NetworkStats_t ) );

        xMetricsStatus = vGetMetrics( &xMetrics );

        if( xMetricsStatus != 0 )
        {
            eStatus = MetricsCollectorCollectionFailed;
        }
    }

    if( eStatus == MetricsCollectorSuccess )
    {
        pxOutNetworkStats->ulBytesReceived = xMetrics.xInput.uxByteCount;
        pxOutNetworkStats->ulPacketsReceived = xMetrics.xInput.uxPacketCount;
        pxOutNetworkStats->ulBytesSent = xMetrics.XOutput.uxByteCount;
        pxOutNetworkStats->ulPacketsSent = xMetrics.XOutput.uxPacketCount;
    }

    return eStatus;
}
/*-----------------------------------------------------------*/

MetricsCollectorStatus_t xGetOpenTcpPorts( uint16_t * pusOutTcpPortsArray,
                                           uint32_t ulTcpPortsArrayLength,
                                           uint32_t * pulOutNumTcpOpenPorts )
{
    MetricsCollectorStatus_t status = MetricsCollectorSuccess;

    MetricsType_t xMetrics = { 0 };
    BaseType_t xMetricsStatus = 0;

    if( pulOutNumTcpOpenPorts == NULL )
    {
        LogError( ( "Invalid parameter. pulOutNumTcpOpenPorts NULL." ) );
        status = MetricsCollectorBadParameter;
    }

    if( status == MetricsCollectorSuccess )
    {
        xMetricsStatus = vGetMetrics( &xMetrics );

        if( xMetricsStatus != 0 )
        {
            status = MetricsCollectorCollectionFailed;
        }
    }

    if( status == MetricsCollectorSuccess )
    {
        *pulOutNumTcpOpenPorts = xMetrics.xTCPPortList.uxCount;

        if( pusOutTcpPortsArray != NULL )
        {
            if( xMetrics.xTCPPortList.uxCount < ulTcpPortsArrayLength )
            {
                ulTcpPortsArrayLength = xMetrics.xTCPPortList.uxCount;
            }

            memcpy( pusOutTcpPortsArray, &xMetrics.xTCPPortList.usTCPPortList, ulTcpPortsArrayLength * sizeof( uint16_t ) );
        }
    }

    return MetricsCollectorSuccess;
}
/*-----------------------------------------------------------*/

MetricsCollectorStatus_t xGetOpenUdpPorts( uint16_t * pusOutUdpPortsArray,
                                           uint32_t ulUdpPortsArrayLength,
                                           uint32_t * pulOutNumUdpOpenPorts )
{
    MetricsCollectorStatus_t eStatus = MetricsCollectorSuccess;

    MetricsType_t xMetrics = { 0 };
    BaseType_t xMetricsStatus = 0;

    if( pulOutNumUdpOpenPorts == NULL )
    {
        LogError( ( "Invalid parameter. pOutNumudpOpenPorts NULL." ) );
        eStatus = MetricsCollectorBadParameter;
    }

    if( eStatus == MetricsCollectorSuccess )
    {
        xMetricsStatus = vGetMetrics( &xMetrics );

        if( xMetricsStatus != 0 )
        {
            eStatus = MetricsCollectorCollectionFailed;
        }
    }

    if( eStatus == MetricsCollectorSuccess )
    {
        *pulOutNumUdpOpenPorts = xMetrics.xTCPPortList.uxCount;

        if( pusOutUdpPortsArray != NULL )
        {
            if( xMetrics.xUDPPortList.uxCount < ulUdpPortsArrayLength )
            {
                ulUdpPortsArrayLength = xMetrics.xUDPPortList.uxCount;
            }

            memcpy( pusOutUdpPortsArray, &xMetrics.xUDPPortList.usUDPPortList, ulUdpPortsArrayLength * sizeof( uint16_t ) );
        }
    }

    return MetricsCollectorSuccess;
}

/*-----------------------------------------------------------*/

MetricsCollectorStatus_t GetEstablishedConnections( Connection_t * pxOutConnectionsArray,
                                                    uint32_t ulConnectionsArrayLength,
                                                    uint32_t * pulOutNumEstablishedConnections )
{
    MetricsCollectorStatus_t eStatus = MetricsCollectorSuccess;

    MetricsType_t xMetrics = { 0 };
    BaseType_t xMetricsStatus = 0;
    uint32_t ulLocalIp = 0;

    if( pulOutNumEstablishedConnections == NULL )
    {
        LogError( ( "Invalid parameter. pulOutNumEstablishedConnections NULL." ) );
        eStatus = MetricsCollectorBadParameter;
    }

    if( eStatus == MetricsCollectorSuccess )
    {
        xMetricsStatus = vGetMetrics( &xMetrics );

        if( xMetricsStatus != 0 )
        {
            eStatus = MetricsCollectorCollectionFailed;
        }
    }

    if( eStatus == MetricsCollectorSuccess )
    {
        *pulOutNumEstablishedConnections = xMetrics.xTCPSocketList.uxCount;

        if( pxOutConnectionsArray != NULL )
        {
            ulLocalIp = FreeRTOS_GetIPAddress();

            if( xMetrics.xTCPSocketList.uxCount < ulConnectionsArrayLength )
            {
                ulConnectionsArrayLength = xMetrics.xTCPSocketList.uxCount;
            }

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
