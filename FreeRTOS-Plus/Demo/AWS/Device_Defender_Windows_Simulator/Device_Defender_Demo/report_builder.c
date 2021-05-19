/*
 * FreeRTOS V202104.00
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
    "\"%s\": %u"                             \
    "},"

#define reportbuilderJSON_CONNECTION_OBJECT_FORMAT \
    "{"                                            \
    "\"%s\": %u,"                                  \
    "\"%s\": \"%u.%u.%u.%u:%u\""                   \
    "},"

#define reportbuilderJSON_REPORT_FORMAT_PART1 \
    "{"                                       \
    "\"%s\": {"                               \
    "\"%s\": %u,"                             \
    "\"%s\": \"%u.%u\""                       \
    "},"                                      \
    "\"%s\": {"                               \
    "\"%s\": {"                               \
    "\"%s\": "

#define reportbuilderJSON_REPORT_FORMAT_PART2 \
    ","                                       \
    "\"%s\": %u"                              \
    "},"                                      \
    "\"%s\": {"                               \
    "\"%s\": "

#define reportbuilderJSON_REPORT_FORMAT_PART3 \
    ","                                       \
    "\"%s\": %u"                              \
    "},"                                      \
    "\"%s\": {"                               \
    "\"%s\": %u,"                             \
    "\"%s\": %u,"                             \
    "\"%s\": %u,"                             \
    "\"%s\": %u"                              \
    "},"                                      \
    "\"%s\": {"                               \
    "\"%s\": {"                               \
    "\"%s\": "

#define reportbuilderJSON_REPORT_FORMAT_PART4 \
    ","                                       \
    "\"%s\": %u"                              \
    "}"                                       \
    "}"                                       \
    "},"                                      \
    "\"%s\": {"                               \
    "\"stack_high_water_mark\": ["            \
    "{"                                       \
    "\"%s\": %u"                              \
    "}"                                       \
    "],"                                      \
    "\"task_numbers\": ["                     \
    "{"                                       \
    "\"%s\": "

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
 * @param[in] ulBufferLength The length of the buffer.
 * @param[in] pusOpenPortsArray The array containing the open ports.
 * @param[in] ulOpenPortsArrayLength Length of the pusOpenPortsArray array.
 * @param[out] pulOutCharsWritten Number of characters written to the buffer.
 *
 * @return #ReportBuilderSuccess if the array is successfully written;
 * #ReportBuilderBufferTooSmall if the buffer cannot hold the full array.
 */
static eReportBuilderStatus prvWritePortsArray( char * pcBuffer,
                                                uint32_t ulBufferLength,
                                                const uint16_t * pusOpenPortsArray,
                                                uint32_t ulOpenPortsArrayLength,
                                                uint32_t * pulOutCharsWritten );

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
 * @param[in] ulBufferLength The length of the buffer.
 * @param[in] pxConnectionsArray The array containing the established connections.
 * @param[in] ulConnectionsArrayLength Length of the pxConnectionsArray array.
 * @param[out] pulOutCharsWritten Number of characters written to the buffer.
 *
 * @return #ReportBuilderSuccess if the array is successfully written;
 * #ReportBuilderBufferTooSmall if the buffer cannot hold the full array.
 */
static eReportBuilderStatus prvWriteConnectionsArray( char * pcBuffer,
                                                      uint32_t ulBufferLength,
                                                      const Connection_t * pxConnectionsArray,
                                                      uint32_t ulConnectionsArrayLength,
                                                      uint32_t * pulOutCharsWritten );

/**
 * @brief Write task ID array to the given buffer as a JSON array.
 *
 * @param[in] pcBuffer The buffer to write the array of task IDs.
 * @param[in] ulBufferLength The length of the buffer.
 * @param[in] pulTaskIdArray The array containing the task IDs.
 * @param[in] pulTaskIdArrayLength Length of the pulTaskIdsArray array.
 * @param[out] pulOutCharsWritten Number of characters written to the buffer.
 *
 * @return #ReportBuilderSuccess if the array is successfully written;
 * #ReportBuilderBufferTooSmall if the buffer cannot hold the full array.
 */
static eReportBuilderStatus prvWriteTaskIdArray( char * pcBuffer,
                                                  uint32_t ulBufferLength,
                                                  const uint32_t * pulTaskIdArray,
                                                  uint32_t pulTaskIdArrayLength,
                                                  uint32_t * pulOutCharsWritten );
/*-----------------------------------------------------------*/

static eReportBuilderStatus prvWritePortsArray( char * pcBuffer,
                                                uint32_t ulBufferLength,
                                                const uint16_t * pusOpenPortsArray,
                                                uint32_t ulOpenPortsArrayLength,
                                                uint32_t * pulOutCharsWritten )
{
    char * pcCurrentWritePos = pcBuffer;
    uint32_t i, ulRemainingBufferLength = ulBufferLength;
    int32_t lCharactersWritten;
    eReportBuilderStatus eStatus = eReportBuilderSuccess;

    configASSERT( pcBuffer != NULL );
    configASSERT( pusOpenPortsArray != NULL );
    configASSERT( pulOutCharsWritten != NULL );

    /* Write the JSON array open marker. */
    if( ulRemainingBufferLength > 1 )
    {
        *pcCurrentWritePos = reportbuilderJSON_ARRAY_OPEN_MARKER;
        ulRemainingBufferLength -= 1;
        pcCurrentWritePos += 1;
    }
    else
    {
        eStatus = eReportBuilderBufferTooSmall;
    }

    /* Write the array elements. */
    for( i = 0; ( ( i < ulOpenPortsArrayLength ) && ( eStatus == eReportBuilderSuccess ) ); i++ )
    {
        lCharactersWritten = snprintf( pcCurrentWritePos,
                                       ulRemainingBufferLength,
                                       reportbuilderJSON_PORT_OBJECT_FORMAT,
                                       DEFENDER_REPORT_PORT_KEY,
                                       pusOpenPortsArray[ i ] );

        if( !reportbuilderSNPRINTF_SUCCESS( lCharactersWritten, ulRemainingBufferLength ) )
        {
            eStatus = eReportBuilderBufferTooSmall;
        }
        else
        {
            ulRemainingBufferLength -= ( uint32_t ) lCharactersWritten;
            pcCurrentWritePos += lCharactersWritten;
        }
    }

    if( eStatus == eReportBuilderSuccess )
    {
        /* Discard the last comma. */
        if( ulOpenPortsArrayLength > 0 )
        {
            pcCurrentWritePos -= 1;
            ulRemainingBufferLength += 1;
        }

        /* Write the JSON array close marker. */
        if( ulRemainingBufferLength > 1 )
        {
            *pcCurrentWritePos = reportbuilderJSON_ARRAY_CLOSE_MARKER;
            ulRemainingBufferLength -= 1;
            pcCurrentWritePos += 1;
            *pulOutCharsWritten = ulBufferLength - ulRemainingBufferLength;
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
                                                      uint32_t ulBufferLength,
                                                      const Connection_t * pxConnectionsArray,
                                                      uint32_t ulConnectionsArrayLength,
                                                      uint32_t * pulOutCharsWritten )
{
    char * pcCurrentWritePos = pcBuffer;
    uint32_t i, ulRemainingBufferLength = ulBufferLength;
    int32_t lCharactersWritten;
    eReportBuilderStatus eStatus = eReportBuilderSuccess;
    const Connection_t * pxConn;

    configASSERT( pcBuffer != NULL );
    configASSERT( pxConnectionsArray != NULL );
    configASSERT( pulOutCharsWritten != NULL );

    /* Write the JSON array open marker. */
    if( ulRemainingBufferLength > 1 )
    {
        *pcCurrentWritePos = reportbuilderJSON_ARRAY_OPEN_MARKER;
        ulRemainingBufferLength -= 1;
        pcCurrentWritePos += 1;
    }
    else
    {
        eStatus = eReportBuilderBufferTooSmall;
    }

    /* Write the array elements. */
    for( i = 0; ( ( i < ulConnectionsArrayLength ) && ( eStatus == eReportBuilderSuccess ) ); i++ )
    {
        pxConn = &( pxConnectionsArray[ i ] );
        lCharactersWritten = snprintf( pcCurrentWritePos,
                                       ulRemainingBufferLength,
                                       reportbuilderJSON_CONNECTION_OBJECT_FORMAT,
                                       DEFENDER_REPORT_LOCAL_PORT_KEY,
                                       pxConn->usLocalPort,
                                       DEFENDER_REPORT_REMOTE_ADDR_KEY,
                                       ( pxConn->ulRemoteIp >> 24 ) & 0xFF,
                                       ( pxConn->ulRemoteIp >> 16 ) & 0xFF,
                                       ( pxConn->ulRemoteIp >> 8 ) & 0xFF,
                                       ( pxConn->ulRemoteIp ) & 0xFF,
                                       pxConn->usRemotePort );

        if( !reportbuilderSNPRINTF_SUCCESS( lCharactersWritten, ulRemainingBufferLength ) )
        {
            eStatus = eReportBuilderBufferTooSmall;
        }
        else
        {
            ulRemainingBufferLength -= lCharactersWritten;
            pcCurrentWritePos += lCharactersWritten;
        }
    }

    if( eStatus == eReportBuilderSuccess )
    {
        /* Discard the last comma. */
        if( ulConnectionsArrayLength > 0 )
        {
            pcCurrentWritePos -= 1;
            ulRemainingBufferLength += 1;
        }

        /* Write the JSON array close marker. */
        if( ulRemainingBufferLength > 1 )
        {
            *pcCurrentWritePos = reportbuilderJSON_ARRAY_CLOSE_MARKER;
            ulRemainingBufferLength -= 1;
            pcCurrentWritePos += 1;
            *pulOutCharsWritten = ulBufferLength - ulRemainingBufferLength;
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
                                                  uint32_t ulBufferLength,
                                                  const uint32_t * pulTaskIdArray,
                                                  uint32_t pulTaskIdArrayLength,
                                                  uint32_t * pulOutCharsWritten )
{
    char * pcCurrentWritePos = pcBuffer;
    uint32_t i, ulRemainingBufferLength = ulBufferLength;
    int32_t lCharactersWritten;
    eReportBuilderStatus eStatus = eReportBuilderSuccess;

    configASSERT( pcBuffer != NULL );
    configASSERT( pulTaskIdArray != NULL );
    configASSERT( pulOutCharsWritten != NULL );

    /* Write the JSON array open marker. */
    if( ulRemainingBufferLength > 1 )
    {
        *pcCurrentWritePos = reportbuilderJSON_ARRAY_OPEN_MARKER;
        ulRemainingBufferLength -= 1;
        pcCurrentWritePos += 1;
    }
    else
    {
        eStatus = eReportBuilderBufferTooSmall;
    }

    /* Write the array elements. */
    for( i = 0; ( ( i < pulTaskIdArrayLength ) && ( eStatus == eReportBuilderSuccess ) ); i++ )
    {
        lCharactersWritten = snprintf( pcCurrentWritePos,
                                       ulRemainingBufferLength,
                                       "%u,",
                                       pulTaskIdArray[ i ] );

        if( !reportbuilderSNPRINTF_SUCCESS( lCharactersWritten, ulRemainingBufferLength ) )
        {
            eStatus = eReportBuilderBufferTooSmall;
        }
        else
        {
            ulRemainingBufferLength -= ( uint32_t ) lCharactersWritten;
            pcCurrentWritePos += lCharactersWritten;
        }
    }

    if( eStatus == eReportBuilderSuccess )
    {
        /* Discard the last comma. */
        if( pulTaskIdArrayLength > 0 )
        {
            pcCurrentWritePos -= 1;
            ulRemainingBufferLength += 1;
        }

        /* Write the JSON array close marker. */
        if( ulRemainingBufferLength > 1 )
        {
            *pcCurrentWritePos = reportbuilderJSON_ARRAY_CLOSE_MARKER;
            ulRemainingBufferLength -= 1;
            pcCurrentWritePos += 1;
            *pulOutCharsWritten = ulBufferLength - ulRemainingBufferLength;
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
                                          uint32_t ulBufferLength,
                                          const ReportMetrics_t * pxMetrics,
                                          uint32_t ulMajorReportVersion,
                                          uint32_t ulMinorReportVersion,
                                          uint32_t ulReportId,
                                          uint32_t * pulOutReportLength )
{
    char * pcCurrentWritePos = pcBuffer;
    uint32_t ulRemainingBufferLength = ulBufferLength;
    uint32_t bufferWritten;
    eReportBuilderStatus eStatus = eReportBuilderSuccess;
    int32_t lCharactersWritten;

    configASSERT( pcBuffer != NULL );
    configASSERT( pxMetrics != NULL );
    configASSERT( pulOutReportLength != NULL );
    configASSERT( ulBufferLength != 0 );

    if( ( pcBuffer == NULL ) ||
        ( ulBufferLength == 0 ) ||
        ( pxMetrics == NULL ) ||
        ( pulOutReportLength == NULL ) )
    {
        LogError( ( "Invalid parameters. pcBuffer: %p, ulBufferLength: %u"
                    " pMetrics: %p, pOutReprotLength: %p.",
                    pcBuffer,
                    ulBufferLength,
                    pxMetrics,
                    pulOutReportLength ) );
        eStatus = eReportBuilderBadParameter;
    }

    /* Write part1. */
    if( eStatus == eReportBuilderSuccess )
    {
        lCharactersWritten = snprintf( pcCurrentWritePos,
                                       ulRemainingBufferLength,
                                       reportbuilderJSON_REPORT_FORMAT_PART1,
                                       DEFENDER_REPORT_HEADER_KEY,
                                       DEFENDER_REPORT_ID_KEY,
                                       ulReportId,
                                       DEFENDER_REPORT_VERSION_KEY,
                                       ulMajorReportVersion,
                                       ulMinorReportVersion,
                                       DEFENDER_REPORT_METRICS_KEY,
                                       DEFENDER_REPORT_TCP_LISTENING_PORTS_KEY,
                                       DEFENDER_REPORT_PORTS_KEY
                                       );

        if( !reportbuilderSNPRINTF_SUCCESS( lCharactersWritten, ulRemainingBufferLength ) )
        {
            LogError( ( "Failed to write part 1." ) );
            eStatus = eReportBuilderBufferTooSmall;
        }
        else
        {
            ulRemainingBufferLength -= lCharactersWritten;
            pcCurrentWritePos += lCharactersWritten;
        }
    }

    /* Write TCP ports array. */
    if( eStatus == eReportBuilderSuccess )
    {
        eStatus = prvWritePortsArray( pcCurrentWritePos,
                                      ulRemainingBufferLength,
                                      pxMetrics->pusOpenTcpPortsArray,
                                      pxMetrics->ulOpenTcpPortsArrayLength,
                                      &( bufferWritten ) );

        if( eStatus == eReportBuilderSuccess )
        {
            pcCurrentWritePos += bufferWritten;
            ulRemainingBufferLength -= bufferWritten;
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
                                       ulRemainingBufferLength,
                                       reportbuilderJSON_REPORT_FORMAT_PART2,
                                       DEFENDER_REPORT_TOTAL_KEY,
                                       pxMetrics->ulOpenTcpPortsArrayLength,
                                       DEFENDER_REPORT_UDP_LISTENING_PORTS_KEY,
                                       DEFENDER_REPORT_PORTS_KEY
                                       );

        if( !reportbuilderSNPRINTF_SUCCESS( lCharactersWritten, ulRemainingBufferLength ) )
        {
            LogError( ( "Failed to write part 2." ) );
            eStatus = eReportBuilderBufferTooSmall;
        }
        else
        {
            ulRemainingBufferLength -= lCharactersWritten;
            pcCurrentWritePos += lCharactersWritten;
        }
    }

    /* Write UDP ports array. */
    if( eStatus == eReportBuilderSuccess )
    {
        eStatus = prvWritePortsArray( pcCurrentWritePos,
                                      ulRemainingBufferLength,
                                      pxMetrics->pusOpenUdpPortsArray,
                                      pxMetrics->ulOpenUdpPortsArrayLength,
                                      &( bufferWritten ) );

        if( eStatus == eReportBuilderSuccess )
        {
            pcCurrentWritePos += bufferWritten;
            ulRemainingBufferLength -= bufferWritten;
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
                                       ulRemainingBufferLength,
                                       reportbuilderJSON_REPORT_FORMAT_PART3,
                                       DEFENDER_REPORT_TOTAL_KEY,
                                       pxMetrics->ulOpenUdpPortsArrayLength,
                                       DEFENDER_REPORT_NETWORK_STATS_KEY,
                                       DEFENDER_REPORT_BYTES_IN_KEY,
                                       pxMetrics->pxNetworkStats->ulBytesReceived,
                                       DEFENDER_REPORT_BYTES_OUT_KEY,
                                       pxMetrics->pxNetworkStats->ulBytesSent,
                                       DEFENDER_REPORT_PKTS_IN_KEY,
                                       pxMetrics->pxNetworkStats->ulPacketsReceived,
                                       DEFENDER_REPORT_PKTS_OUT_KEY,
                                       pxMetrics->pxNetworkStats->ulPacketsSent,
                                       DEFENDER_REPORT_TCP_CONNECTIONS_KEY,
                                       DEFENDER_REPORT_ESTABLISHED_CONNECTIONS_KEY,
                                       DEFENDER_REPORT_CONNECTIONS_KEY
                                       );

        if( !reportbuilderSNPRINTF_SUCCESS( lCharactersWritten, ulRemainingBufferLength ) )
        {
            LogError( ( "Failed to write part 3." ) );
            eStatus = eReportBuilderBufferTooSmall;
        }
        else
        {
            ulRemainingBufferLength -= lCharactersWritten;
            pcCurrentWritePos += lCharactersWritten;
        }
    }

    /* Write connections array. */
    if( eStatus == eReportBuilderSuccess )
    {
        eStatus = prvWriteConnectionsArray( pcCurrentWritePos,
                                            ulRemainingBufferLength,
                                            pxMetrics->pxEstablishedConnectionsArray,
                                            pxMetrics->ulEstablishedConnectionsArrayLength,
                                            &( bufferWritten ) );

        if( eStatus == eReportBuilderSuccess )
        {
            pcCurrentWritePos += bufferWritten;
            ulRemainingBufferLength -= bufferWritten;
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
                                       ulRemainingBufferLength,
                                       reportbuilderJSON_REPORT_FORMAT_PART4,
                                       DEFENDER_REPORT_TOTAL_KEY,
                                       pxMetrics->ulEstablishedConnectionsArrayLength,
                                       DEFENDER_REPORT_CUSTOM_METRICS_KEY,
                                       DEFENDER_REPORT_NUMBER_KEY,
                                       pxMetrics->ulStackHighWaterMark,
                                       DEFENDER_REPORT_NUMBER_LIST_KEY
                                       );

        if( !reportbuilderSNPRINTF_SUCCESS( lCharactersWritten, ulRemainingBufferLength ) )
        {
            LogError( ( "Failed to write part 4." ) );
            eStatus = eReportBuilderBufferTooSmall;
        }
        else
        {
            ulRemainingBufferLength -= lCharactersWritten;
            pcCurrentWritePos += lCharactersWritten;
        }
    }

    /* Write task ids array. */
    if( eStatus == eReportBuilderSuccess )
    {
        eStatus = prvWriteTaskIdArray( pcCurrentWritePos,
                                        ulRemainingBufferLength,
                                        pxMetrics->pulTaskIdArray,
                                        pxMetrics->ulTaskIdArrayLength,
                                        &( bufferWritten ) );

        if( eStatus == eReportBuilderSuccess )
        {
            pcCurrentWritePos += bufferWritten;
            ulRemainingBufferLength -= bufferWritten;
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
                                       ulRemainingBufferLength,
                                       reportbuilderJSON_REPORT_FORMAT_PART5 );

        if( !reportbuilderSNPRINTF_SUCCESS( lCharactersWritten, ulRemainingBufferLength ) )
        {
            LogError( ( "Failed to write part 5." ) );
            eStatus = eReportBuilderBufferTooSmall;
        }
        else
        {
            ulRemainingBufferLength -= lCharactersWritten;
            pcCurrentWritePos += lCharactersWritten;
            *pulOutReportLength = ulBufferLength - ulRemainingBufferLength;
        }
    }

    return eStatus;
}
/*-----------------------------------------------------------*/
