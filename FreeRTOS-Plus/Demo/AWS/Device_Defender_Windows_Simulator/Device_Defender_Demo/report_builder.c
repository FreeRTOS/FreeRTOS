/*
 * FreeRTOS V202112.00
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

/* Standard includes. */
#include <stdio.h>
#include <string.h>
#include <stdint.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo config. */
#include "demo_config.h"

/* Device Defender Client Library. */
#include "defender.h"

/* Interface include. */
#include "report_builder.h"

/* Various JSON characters. */
#define reportbuilderJSON_ARRAY_OPEN_MARKER         '['
#define reportbuilderJSON_ARRAY_CLOSE_MARKER        ']'
#define reportbuilderJSON_ARRAY_OBJECT_SEPARATOR    ','

/* Helper macro to check if snprintf was successful. */
#define reportbuilderSNPRINTF_SUCCESS( retVal, bufLen )    ( ( retVal > 0 ) && ( ( uint32_t ) retVal < bufLen ) )

/* Formats used to generate the JSON report. */
#define reportbuilderJSON_PORT_OBJECT_FORMAT \
    "{"                                      \
    "\""DEFENDER_REPORT_PORT_KEY"\": %u"     \
    "},"

#define reportbuilderJSON_CONNECTION_OBJECT_FORMAT              \
    "{"                                                         \
    "\""DEFENDER_REPORT_LOCAL_PORT_KEY"\": %u,"                 \
    "\""DEFENDER_REPORT_REMOTE_ADDR_KEY"\": \"%u.%u.%u.%u:%u\"" \
    "},"

#define reportbuilderJSON_REPORT_FORMAT_PART1          \
    "{"                                                \
    "\""DEFENDER_REPORT_HEADER_KEY"\": {"              \
    "\""DEFENDER_REPORT_ID_KEY"\": %u,"                \
    "\""DEFENDER_REPORT_VERSION_KEY"\": \"%u.%u\""     \
    "},"                                               \
    "\""DEFENDER_REPORT_METRICS_KEY"\": {"             \
    "\""DEFENDER_REPORT_TCP_LISTENING_PORTS_KEY"\": {" \
    "\""DEFENDER_REPORT_PORTS_KEY"\": "

#define reportbuilderJSON_REPORT_FORMAT_PART2          \
    ","                                                \
    "\""DEFENDER_REPORT_TOTAL_KEY"\": %u"              \
    "},"                                               \
    "\""DEFENDER_REPORT_UDP_LISTENING_PORTS_KEY"\": {" \
    "\""DEFENDER_REPORT_PORTS_KEY"\": "

#define reportbuilderJSON_REPORT_FORMAT_PART3              \
    ","                                                    \
    "\""DEFENDER_REPORT_TOTAL_KEY"\": %u"                  \
    "},"                                                   \
    "\""DEFENDER_REPORT_NETWORK_STATS_KEY"\": {"           \
    "\""DEFENDER_REPORT_BYTES_IN_KEY"\": %u,"              \
    "\""DEFENDER_REPORT_BYTES_OUT_KEY"\": %u,"             \
    "\""DEFENDER_REPORT_PKTS_IN_KEY"\": %u,"               \
    "\""DEFENDER_REPORT_PKTS_OUT_KEY"\": %u"               \
    "},"                                                   \
    "\""DEFENDER_REPORT_TCP_CONNECTIONS_KEY"\": {"         \
    "\""DEFENDER_REPORT_ESTABLISHED_CONNECTIONS_KEY"\": {" \
    "\""DEFENDER_REPORT_CONNECTIONS_KEY"\": "

#define reportbuilderJSON_REPORT_FORMAT_PART4     \
    ","                                           \
    "\""DEFENDER_REPORT_TOTAL_KEY"\": %u"         \
    "}"                                           \
    "}"                                           \
    "},"                                          \
    "\""DEFENDER_REPORT_CUSTOM_METRICS_KEY"\": {" \
    "\"stack_high_water_mark\": ["                \
    "{"                                           \
    "\""DEFENDER_REPORT_NUMBER_KEY"\": %u"        \
    "}"                                           \
    "],"                                          \
    "\"task_numbers\": ["                         \
    "{"                                           \
    "\""DEFENDER_REPORT_NUMBER_LIST_KEY"\": "

#define reportbuilderJSON_REPORT_FORMAT_PART5 \
    "}"                                       \
    "]"                                       \
    "}"                                       \
    "}"

/*-----------------------------------------------------------*/

/**
 * @brief Write ports array to the given buffer in the format expected by the
 * AWS IoT Device Defender Service.
 *
 * This function writes an array of the following format:
 * [
 *    {
 *        "port":44207
 *    },
 *    {
 *        "port":53
 *    }
 * ]
 *
 * @param[in] pcBuffer The buffer to write the ports array.
 * @param[in] xBufferLength The length of the buffer.
 * @param[in] pusOpenPortsArray The array containing the open ports.
 * @param[in] xOpenPortsArrayLength Length of the pusOpenPortsArray array.
 * @param[out] pxOutCharsWritten Number of characters written to the buffer.
 *
 * @return #ReportBuilderSuccess if the array is successfully written;
 * #ReportBuilderBufferTooSmall if the buffer cannot hold the full array.
 */
static eReportBuilderStatus prvWritePortsArray( char * pcBuffer,
                                                size_t xBufferLength,
                                                const uint16_t * pusOpenPortsArray,
                                                size_t xOpenPortsArrayLength,
                                                size_t * pxOutCharsWritten );

/**
 * @brief Write established connections array to the given buffer in the format
 * expected by the AWS IoT Device Defender Service.
 *
 * This function write array of the following format:
 * [
 *     {
 *         "local_port":44207,
 *         "remote_addr":"127.0.0.1:45148"
 *     },
 *     {
 *         "local_port":22,
 *         "remote_addr":"24.16.237.194:63552"
 *     }
 * ]
 *
 * @param[in] pcBuffer The buffer to write the connections array.
 * @param[in] xBufferLength The length of the buffer.
 * @param[in] pxConnectionsArray The array containing the established connections.
 * @param[in] xConnectionsArrayLength Length of the pxConnectionsArray array.
 * @param[out] pxOutCharsWritten Number of characters written to the buffer.
 *
 * @return #ReportBuilderSuccess if the array is successfully written;
 * #ReportBuilderBufferTooSmall if the buffer cannot hold the full array.
 */
static eReportBuilderStatus prvWriteConnectionsArray( char * pcBuffer,
                                                      size_t xBufferLength,
                                                      const Connection_t * pxConnectionsArray,
                                                      size_t xConnectionsArrayLength,
                                                      size_t * pxOutCharsWritten );

/**
 * @brief Write task ID array to the given buffer as a JSON array.
 *
 * @param[in] pcBuffer The buffer to write the array of task IDs.
 * @param[in] xBufferLength The length of the buffer.
 * @param[in] pxTaskStatusArray The array containing the task statuses.
 * @param[in] xTaskStatusArrayLength Length of the pxTaskStatusArray array.
 * @param[out] pxOutCharsWritten Number of characters written to the buffer.
 *
 * @return #ReportBuilderSuccess if the array is successfully written;
 * #ReportBuilderBufferTooSmall if the buffer cannot hold the full array.
 */
static eReportBuilderStatus prvWriteTaskIdArray( char * pcBuffer,
                                                 size_t xBufferLength,
                                                 const TaskStatus_t * pxTaskStatusArray,
                                                 size_t xTaskStatusArrayLength,
                                                 size_t * pxOutCharsWritten );
/*-----------------------------------------------------------*/

static eReportBuilderStatus prvWritePortsArray( char * pcBuffer,
                                                uint32_t xBufferLength,
                                                const uint16_t * pusOpenPortsArray,
                                                uint32_t xOpenPortsArrayLength,
                                                uint32_t * pxOutCharsWritten )
{
    char * pcCurrentWritePos = pcBuffer;
    uint32_t i;
    size_t xRemainingBufferLength = xBufferLength;
    int32_t lCharactersWritten;
    eReportBuilderStatus eStatus = eReportBuilderSuccess;

    configASSERT( pcBuffer != NULL );
    configASSERT( pusOpenPortsArray != NULL );
    configASSERT( pxOutCharsWritten != NULL );

    /* Write the JSON array open marker. */
    if( xRemainingBufferLength > 1 )
    {
        *pcCurrentWritePos = reportbuilderJSON_ARRAY_OPEN_MARKER;
        xRemainingBufferLength -= 1;
        pcCurrentWritePos += 1;
    }
    else
    {
        eStatus = eReportBuilderBufferTooSmall;
    }

    /* Write the array elements. */
    for( i = 0; ( ( i < xOpenPortsArrayLength ) && ( eStatus == eReportBuilderSuccess ) ); i++ )
    {
        lCharactersWritten = snprintf( pcCurrentWritePos,
                                       xRemainingBufferLength,
                                       reportbuilderJSON_PORT_OBJECT_FORMAT,
                                       pusOpenPortsArray[ i ] );

        if( !reportbuilderSNPRINTF_SUCCESS( lCharactersWritten, xRemainingBufferLength ) )
        {
            eStatus = eReportBuilderBufferTooSmall;
        }
        else
        {
            xRemainingBufferLength -= ( uint32_t ) lCharactersWritten;
            pcCurrentWritePos += lCharactersWritten;
        }
    }

    if( eStatus == eReportBuilderSuccess )
    {
        /* Discard the last comma. */
        if( xOpenPortsArrayLength > 0 )
        {
            pcCurrentWritePos -= 1;
            xRemainingBufferLength += 1;
        }

        /* Write the JSON array close marker. */
        if( xRemainingBufferLength > 1 )
        {
            *pcCurrentWritePos = reportbuilderJSON_ARRAY_CLOSE_MARKER;
            xRemainingBufferLength -= 1;
            pcCurrentWritePos += 1;
            *pxOutCharsWritten = xBufferLength - xRemainingBufferLength;
        }
        else
        {
            eStatus = eReportBuilderBufferTooSmall;
        }
    }

    return eStatus;
}
/*-----------------------------------------------------------*/

static eReportBuilderStatus prvWriteConnectionsArray( char * pcBuffer,
                                                      size_t xBufferLength,
                                                      const Connection_t * pxConnectionsArray,
                                                      size_t xConnectionsArrayLength,
                                                      size_t * pxOutCharsWritten )
{
    char * pcCurrentWritePos = pcBuffer;
    uint32_t i;
    size_t xRemainingBufferLength = xBufferLength;
    int32_t lCharactersWritten;
    eReportBuilderStatus eStatus = eReportBuilderSuccess;
    const Connection_t * pxConn;

    configASSERT( pcBuffer != NULL );
    configASSERT( pxConnectionsArray != NULL );
    configASSERT( pxOutCharsWritten != NULL );

    /* Write the JSON array open marker. */
    if( xRemainingBufferLength > 1 )
    {
        *pcCurrentWritePos = reportbuilderJSON_ARRAY_OPEN_MARKER;
        xRemainingBufferLength -= 1;
        pcCurrentWritePos += 1;
    }
    else
    {
        eStatus = eReportBuilderBufferTooSmall;
    }

    /* Write the array elements. */
    for( i = 0; ( ( i < xConnectionsArrayLength ) && ( eStatus == eReportBuilderSuccess ) ); i++ )
    {
        pxConn = &( pxConnectionsArray[ i ] );
        lCharactersWritten = snprintf( pcCurrentWritePos,
                                       xRemainingBufferLength,
                                       reportbuilderJSON_CONNECTION_OBJECT_FORMAT,
                                       pxConn->usLocalPort,
                                       ( pxConn->ulRemoteIp >> 24 ) & 0xFF,
                                       ( pxConn->ulRemoteIp >> 16 ) & 0xFF,
                                       ( pxConn->ulRemoteIp >> 8 ) & 0xFF,
                                       ( pxConn->ulRemoteIp ) & 0xFF,
                                       pxConn->usRemotePort );

        if( !reportbuilderSNPRINTF_SUCCESS( lCharactersWritten, xRemainingBufferLength ) )
        {
            eStatus = eReportBuilderBufferTooSmall;
        }
        else
        {
            xRemainingBufferLength -= lCharactersWritten;
            pcCurrentWritePos += lCharactersWritten;
        }
    }

    if( eStatus == eReportBuilderSuccess )
    {
        /* Discard the last comma. */
        if( xConnectionsArrayLength > 0 )
        {
            pcCurrentWritePos -= 1;
            xRemainingBufferLength += 1;
        }

        /* Write the JSON array close marker. */
        if( xRemainingBufferLength > 1 )
        {
            *pcCurrentWritePos = reportbuilderJSON_ARRAY_CLOSE_MARKER;
            xRemainingBufferLength -= 1;
            pcCurrentWritePos += 1;
            *pxOutCharsWritten = xBufferLength - xRemainingBufferLength;
        }
        else
        {
            eStatus = eReportBuilderBufferTooSmall;
        }
    }

    return eStatus;
}
/*-----------------------------------------------------------*/

static eReportBuilderStatus prvWriteTaskIdArray( char * pcBuffer,
                                                 size_t xBufferLength,
                                                 const TaskStatus_t * pxTaskStatusArray,
                                                 size_t xTaskStatusArrayLength,
                                                 size_t * pxOutCharsWritten )
{
    char * pcCurrentWritePos = pcBuffer;
    uint32_t i;
    size_t xRemainingBufferLength = xBufferLength;
    int32_t lCharactersWritten;
    eReportBuilderStatus eStatus = eReportBuilderSuccess;

    configASSERT( pcBuffer != NULL );
    configASSERT( pxTaskStatusArray != NULL );
    configASSERT( pxOutCharsWritten != NULL );

    /* Write the JSON array open marker. */
    if( xRemainingBufferLength > 1 )
    {
        *pcCurrentWritePos = reportbuilderJSON_ARRAY_OPEN_MARKER;
        xRemainingBufferLength -= 1;
        pcCurrentWritePos += 1;
    }
    else
    {
        eStatus = eReportBuilderBufferTooSmall;
    }

    /* Write the array elements. */
    for( i = 0; ( ( i < xTaskStatusArrayLength ) && ( eStatus == eReportBuilderSuccess ) ); i++ )
    {
        lCharactersWritten = snprintf( pcCurrentWritePos,
                                       xRemainingBufferLength,
                                       "%u,",
                                       pxTaskStatusArray[ i ].xTaskNumber );

        if( !reportbuilderSNPRINTF_SUCCESS( lCharactersWritten, xRemainingBufferLength ) )
        {
            eStatus = eReportBuilderBufferTooSmall;
        }
        else
        {
            xRemainingBufferLength -= ( uint32_t ) lCharactersWritten;
            pcCurrentWritePos += lCharactersWritten;
        }
    }

    if( eStatus == eReportBuilderSuccess )
    {
        /* Discard the last comma. */
        if( xTaskStatusArrayLength > 0 )
        {
            pcCurrentWritePos -= 1;
            xRemainingBufferLength += 1;
        }

        /* Write the JSON array close marker. */
        if( xRemainingBufferLength > 1 )
        {
            *pcCurrentWritePos = reportbuilderJSON_ARRAY_CLOSE_MARKER;
            xRemainingBufferLength -= 1;
            pcCurrentWritePos += 1;
            *pxOutCharsWritten = xBufferLength - xRemainingBufferLength;
        }
        else
        {
            eStatus = eReportBuilderBufferTooSmall;
        }
    }

    return eStatus;
}
/*-----------------------------------------------------------*/

eReportBuilderStatus eGenerateJsonReport( char * pcBuffer,
                                          size_t xBufferLength,
                                          const ReportMetrics_t * pxMetrics,
                                          uint32_t ulMajorReportVersion,
                                          uint32_t ulMinorReportVersion,
                                          uint32_t ulReportId,
                                          size_t * pxOutReportLength )
{
    char * pcCurrentWritePos = pcBuffer;
    size_t xRemainingBufferLength = xBufferLength;
    uint32_t bufferWritten;
    eReportBuilderStatus eStatus = eReportBuilderSuccess;
    int32_t lCharactersWritten;

    configASSERT( pcBuffer != NULL );
    configASSERT( pxMetrics != NULL );
    configASSERT( pxOutReportLength != NULL );
    configASSERT( xBufferLength != 0 );

    if( ( pcBuffer == NULL ) ||
        ( xBufferLength == 0 ) ||
        ( pxMetrics == NULL ) ||
        ( pxOutReportLength == NULL ) )
    {
        LogError( ( "Invalid parameters. pcBuffer: %p, xBufferLength: %u"
                    " pMetrics: %p, pOutReprotLength: %p.",
                    pcBuffer,
                    xBufferLength,
                    pxMetrics,
                    pxOutReportLength ) );
        eStatus = eReportBuilderBadParameter;
    }

    /* Write part1. */
    if( eStatus == eReportBuilderSuccess )
    {
        lCharactersWritten = snprintf( pcCurrentWritePos,
                                       xRemainingBufferLength,
                                       reportbuilderJSON_REPORT_FORMAT_PART1,
                                       ulReportId,
                                       ulMajorReportVersion,
                                       ulMinorReportVersion );

        if( !reportbuilderSNPRINTF_SUCCESS( lCharactersWritten, xRemainingBufferLength ) )
        {
            LogError( ( "Failed to write part 1." ) );
            eStatus = eReportBuilderBufferTooSmall;
        }
        else
        {
            xRemainingBufferLength -= lCharactersWritten;
            pcCurrentWritePos += lCharactersWritten;
        }
    }

    /* Write TCP ports array. */
    if( eStatus == eReportBuilderSuccess )
    {
        eStatus = prvWritePortsArray( pcCurrentWritePos,
                                      xRemainingBufferLength,
                                      pxMetrics->pusOpenTcpPortsArray,
                                      pxMetrics->xOpenTcpPortsArrayLength,
                                      &( bufferWritten ) );

        if( eStatus == eReportBuilderSuccess )
        {
            pcCurrentWritePos += bufferWritten;
            xRemainingBufferLength -= bufferWritten;
        }
        else
        {
            LogError( ( "Failed to write TCP ports array." ) );
        }
    }

    /* Write part2. */
    if( eStatus == eReportBuilderSuccess )
    {
        lCharactersWritten = snprintf( pcCurrentWritePos,
                                       xRemainingBufferLength,
                                       reportbuilderJSON_REPORT_FORMAT_PART2,
                                       pxMetrics->xOpenTcpPortsArrayLength );

        if( !reportbuilderSNPRINTF_SUCCESS( lCharactersWritten, xRemainingBufferLength ) )
        {
            LogError( ( "Failed to write part 2." ) );
            eStatus = eReportBuilderBufferTooSmall;
        }
        else
        {
            xRemainingBufferLength -= lCharactersWritten;
            pcCurrentWritePos += lCharactersWritten;
        }
    }

    /* Write UDP ports array. */
    if( eStatus == eReportBuilderSuccess )
    {
        eStatus = prvWritePortsArray( pcCurrentWritePos,
                                      xRemainingBufferLength,
                                      pxMetrics->pusOpenUdpPortsArray,
                                      pxMetrics->xOpenUdpPortsArrayLength,
                                      &( bufferWritten ) );

        if( eStatus == eReportBuilderSuccess )
        {
            pcCurrentWritePos += bufferWritten;
            xRemainingBufferLength -= bufferWritten;
        }
        else
        {
            LogError( ( "Failed to write UDP ports array." ) );
        }
    }

    /* Write part3. */
    if( eStatus == eReportBuilderSuccess )
    {
        lCharactersWritten = snprintf( pcCurrentWritePos,
                                       xRemainingBufferLength,
                                       reportbuilderJSON_REPORT_FORMAT_PART3,
                                       pxMetrics->xOpenUdpPortsArrayLength,
                                       pxMetrics->pxNetworkStats->ulBytesReceived,
                                       pxMetrics->pxNetworkStats->ulBytesSent,
                                       pxMetrics->pxNetworkStats->ulPacketsReceived,
                                       pxMetrics->pxNetworkStats->ulPacketsSent,
                                       DEFENDER_REPORT_ESTABLISHED_CONNECTIONS_KEY );

        if( !reportbuilderSNPRINTF_SUCCESS( lCharactersWritten, xRemainingBufferLength ) )
        {
            LogError( ( "Failed to write part 3." ) );
            eStatus = eReportBuilderBufferTooSmall;
        }
        else
        {
            xRemainingBufferLength -= lCharactersWritten;
            pcCurrentWritePos += lCharactersWritten;
        }
    }

    /* Write connections array. */
    if( eStatus == eReportBuilderSuccess )
    {
        eStatus = prvWriteConnectionsArray( pcCurrentWritePos,
                                            xRemainingBufferLength,
                                            pxMetrics->pxEstablishedConnectionsArray,
                                            pxMetrics->xEstablishedConnectionsArrayLength,
                                            &( bufferWritten ) );

        if( eStatus == eReportBuilderSuccess )
        {
            pcCurrentWritePos += bufferWritten;
            xRemainingBufferLength -= bufferWritten;
        }
        else
        {
            LogError( ( "Failed to write established connections array." ) );
        }
    }

    /* Write part4. */
    if( eStatus == eReportBuilderSuccess )
    {
        lCharactersWritten = snprintf( pcCurrentWritePos,
                                       xRemainingBufferLength,
                                       reportbuilderJSON_REPORT_FORMAT_PART4,
                                       pxMetrics->xEstablishedConnectionsArrayLength,
                                       pxMetrics->ulStackHighWaterMark );

        if( !reportbuilderSNPRINTF_SUCCESS( lCharactersWritten, xRemainingBufferLength ) )
        {
            LogError( ( "Failed to write part 4." ) );
            eStatus = eReportBuilderBufferTooSmall;
        }
        else
        {
            xRemainingBufferLength -= lCharactersWritten;
            pcCurrentWritePos += lCharactersWritten;
        }
    }

    /* Write task ids array. */
    if( eStatus == eReportBuilderSuccess )
    {
        eStatus = prvWriteTaskIdArray( pcCurrentWritePos,
                                       xRemainingBufferLength,
                                       pxMetrics->pxTaskStatusArray,
                                       pxMetrics->xTaskStatusArrayLength,
                                       &( bufferWritten ) );

        if( eStatus == eReportBuilderSuccess )
        {
            pcCurrentWritePos += bufferWritten;
            xRemainingBufferLength -= bufferWritten;
        }
        else
        {
            LogError( ( "Failed to write task ID array." ) );
        }
    }

    /* Write part5. */
    if( eStatus == eReportBuilderSuccess )
    {
        lCharactersWritten = snprintf( pcCurrentWritePos,
                                       xRemainingBufferLength,
                                       reportbuilderJSON_REPORT_FORMAT_PART5 );

        if( !reportbuilderSNPRINTF_SUCCESS( lCharactersWritten, xRemainingBufferLength ) )
        {
            LogError( ( "Failed to write part 5." ) );
            eStatus = eReportBuilderBufferTooSmall;
        }
        else
        {
            xRemainingBufferLength -= lCharactersWritten;
            pcCurrentWritePos += lCharactersWritten;
            *pxOutReportLength = xBufferLength - xRemainingBufferLength;
        }
    }

    return eStatus;
}
/*-----------------------------------------------------------*/
