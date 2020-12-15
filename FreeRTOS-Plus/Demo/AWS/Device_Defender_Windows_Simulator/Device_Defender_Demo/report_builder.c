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

/* Standard includes. */
#include <stdio.h>
#include <string.h>
#include <stdint.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo config. */
#include "demo_config.h"

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
    "\"port\": %u"                           \
    "},"

#define reportbuilderJSON_CONNECTION_OBJECT_FORMAT \
    "{"                                            \
    "\"local_port\": %u,"                          \
    "\"remote_addr\": \"%u.%u.%u.%u:%u\""          \
    "},"

#define reportbuilderJSON_REPORT_FORMAT_PART1 \
    "{"                                       \
    "\"header\": {"                           \
    "\"report_id\": %u,"                      \
    "\"version\": \"%u.%u\""                  \
    "},"                                      \
    "\"metrics\": {"                          \
    "\"listening_tcp_ports\": {"              \
    "\"ports\": "

#define reportbuilderJSON_REPORT_FORMAT_PART2 \
    ","                                       \
    "\"total\": %u"                           \
    "},"                                      \
    "\"listening_udp_ports\": {"              \
    "\"ports\": "

#define reportbuilderJSON_REPORT_FORMAT_PART3 \
    ","                                       \
    "\"total\": %u"                           \
    "},"                                      \
    "\"network_stats\": {"                    \
    "\"bytes_in\": %u,"                       \
    "\"bytes_out\": %u,"                      \
    "\"packets_in\": %u,"                     \
    "\"packets_out\": %u"                     \
    "},"                                      \
    "\"tcp_connections\": {"                  \
    "\"established_connections\": {"          \
    "\"connections\": "

#define reportbuilderJSON_REPORT_FORMAT_PART4 \
    ","                                       \
    "\"total\": %u"                           \
    "}"                                       \
    "}"                                       \
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
/*-----------------------------------------------------------*/

static eReportBuilderStatus prvWritePortsArray( char * pcBuffer,
                                                uint32_t ulBufferLength,
                                                const uint16_t * pusOpenPortsArray,
                                                uint32_t ulOpenPortsArrayLength,
                                                uint32_t * pulOutCharsWritten )
{
    char * pcCurrentWritePos = pcBuffer;
    uint32_t i, ulRemainingBufferLength = ulBufferLength;
    int32_t ulCharactersWritten;
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
        ulCharactersWritten = snprintf( pcCurrentWritePos,
                                        ulRemainingBufferLength,
                                        reportbuilderJSON_PORT_OBJECT_FORMAT,
                                        pusOpenPortsArray[ i ] );

        if( !reportbuilderSNPRINTF_SUCCESS( ulCharactersWritten, ulRemainingBufferLength ) )
        {
            eStatus = eReportBuilderBufferTooSmall;
            break;
        }
        else
        {
            ulRemainingBufferLength -= ( uint32_t ) ulCharactersWritten;
            pcCurrentWritePos += ulCharactersWritten;
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
        }
        else
        {
            eStatus = eReportBuilderBufferTooSmall;
        }
    }

    if( eStatus == eReportBuilderSuccess )
    {
        *pulOutCharsWritten = ulBufferLength - ulRemainingBufferLength;
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
    int32_t ulCharactersWritten;
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
        ulCharactersWritten = snprintf( pcCurrentWritePos,
                                        ulRemainingBufferLength,
                                        reportbuilderJSON_CONNECTION_OBJECT_FORMAT,
                                        pxConn->usLocalPort,
                                        ( pxConn->ulRemoteIp >> 24 ) & 0xFF,
                                        ( pxConn->ulRemoteIp >> 16 ) & 0xFF,
                                        ( pxConn->ulRemoteIp >> 8 ) & 0xFF,
                                        ( pxConn->ulRemoteIp ) & 0xFF,
                                        pxConn->usRemotePort );

        if( !reportbuilderSNPRINTF_SUCCESS( ulCharactersWritten, ulRemainingBufferLength ) )
        {
            eStatus = eReportBuilderBufferTooSmall;
            break;
        }
        else
        {
            ulRemainingBufferLength -= ulCharactersWritten;
            pcCurrentWritePos += ulCharactersWritten;
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
        }
        else
        {
            eStatus = eReportBuilderBufferTooSmall;
        }
    }

    if( eStatus == eReportBuilderSuccess )
    {
        *pulOutCharsWritten = ulBufferLength - ulRemainingBufferLength;
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
    uint32_t ulRemainingBufferLength = ulBufferLength, bufferWritten;
    eReportBuilderStatus eStatus = eReportBuilderSuccess;
    int32_t ulCharactersWritten;

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
        ulCharactersWritten = snprintf( pcCurrentWritePos,
                                        ulRemainingBufferLength,
                                        reportbuilderJSON_REPORT_FORMAT_PART1,
                                        ulReportId,
                                        ulMajorReportVersion,
                                        ulMinorReportVersion );

        if( !reportbuilderSNPRINTF_SUCCESS( ulCharactersWritten, ulRemainingBufferLength ) )
        {
            LogError( ( "Failed to write part 1." ) );
            eStatus = eReportBuilderBufferTooSmall;
        }
        else
        {
            ulRemainingBufferLength -= ulCharactersWritten;
            pcCurrentWritePos += ulCharactersWritten;
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
        ulCharactersWritten = snprintf( pcCurrentWritePos,
                                        ulRemainingBufferLength,
                                        reportbuilderJSON_REPORT_FORMAT_PART2,
                                        pxMetrics->ulOpenTcpPortsArrayLength );

        if( !reportbuilderSNPRINTF_SUCCESS( ulCharactersWritten, ulRemainingBufferLength ) )
        {
            LogError( ( "Failed to write part 2." ) );
            eStatus = eReportBuilderBufferTooSmall;
        }
        else
        {
            ulRemainingBufferLength -= ulCharactersWritten;
            pcCurrentWritePos += ulCharactersWritten;
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
        ulCharactersWritten = snprintf( pcCurrentWritePos,
                                        ulRemainingBufferLength,
                                        reportbuilderJSON_REPORT_FORMAT_PART3,
                                        pxMetrics->ulOpenUdpPortsArrayLength,
                                        pxMetrics->pxNetworkStats->ulBytesReceived,
                                        pxMetrics->pxNetworkStats->ulBytesSent,
                                        pxMetrics->pxNetworkStats->ulPacketsReceived,
                                        pxMetrics->pxNetworkStats->ulPacketsSent );

        if( !reportbuilderSNPRINTF_SUCCESS( ulCharactersWritten, ulRemainingBufferLength ) )
        {
            LogError( ( "Failed to write part 3." ) );
            eStatus = eReportBuilderBufferTooSmall;
        }
        else
        {
            ulRemainingBufferLength -= ulCharactersWritten;
            pcCurrentWritePos += ulCharactersWritten;
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
        ulCharactersWritten = snprintf( pcCurrentWritePos,
                                        ulRemainingBufferLength,
                                        reportbuilderJSON_REPORT_FORMAT_PART4,
                                        pxMetrics->ulEstablishedConnectionsArrayLength );

        if( !reportbuilderSNPRINTF_SUCCESS( ulCharactersWritten, ulRemainingBufferLength ) )
        {
            LogError( ( "Failed to write part 4." ) );
            eStatus = eReportBuilderBufferTooSmall;
        }
        else
        {
            ulRemainingBufferLength -= ulCharactersWritten;
            pcCurrentWritePos += ulCharactersWritten;
        }
    }

    if( eStatus == eReportBuilderSuccess )
    {
        *pulOutReportLength = ulBufferLength - ulRemainingBufferLength;
    }

    return eStatus;
}
/*-----------------------------------------------------------*/
