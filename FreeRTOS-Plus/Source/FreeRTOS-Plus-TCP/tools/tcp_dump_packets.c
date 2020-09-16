/*
 * FreeRTOS+TCP V2.2.2
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

/*
 * tcp_dump_packets.c
 * Used in the PC/Win project to dump Ethernet packets, along with some description.
 * See tools/tcp_dump_packets.md for further description.
 */

/* Standard includes. */
#include <stdio.h>
#include <stdint.h>
#include <stdarg.h>
#include <ctype.h>

/* FreeRTOS includes. */
#include <FreeRTOS.h>
#include "task.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_Stream_Buffer.h"
#include "FreeRTOS_IP_Private.h"

#if( ipconfigUSE_DUMP_PACKETS != 0 )

#include "tcp_dump_packets.h"

/* The priority of the windows thread. */
#define dumpPROCESS_THREAD_PRIORITY		THREAD_PRIORITY_NORMAL

/* There is a stream buffer between the FreeRTOS tasks sending network packets,
and the Windows thread that writes these packets to disk. The macro 'dumpITEM_COUNT'
determines the number of full-size packets that can be stored in this stream buffer. */
#ifndef dumpITEM_COUNT
	#define	dumpITEM_COUNT				32
#endif

/* Packets are written in hex notation, no more than 16 bytes on a row. */
#ifndef dumpBYTES_PER_ROW
	#define dumpBYTES_PER_ROW			16
#endif

/* The TCP port number reserved for a DNS server. */
#define dnsDNS_PORT						0x0035u

/* Some const values describing the 'flags' in a TCP packet. */
#define tcpTCP_FLAG_FIN					0x0001u /* No more data from sender */
#define tcpTCP_FLAG_SYN					0x0002u /* Synchronize sequence numbers */
#define tcpTCP_FLAG_RST					0x0004u /* Reset the connection */
#define tcpTCP_FLAG_PSH					0x0008u /* Push function: please push buffered data to the recv application */
#define tcpTCP_FLAG_ACK					0x0010u /* Acknowledgment field is significant */

/* A macro to add a type, both as a numeric value, as well as a string. */
#define ADD_TYPE( FLAGS ) \
	vAddType( flag_##FLAGS, #FLAGS )

/*-----------------------------------------------------------*/

static char pcTypeString[ 255 ];
static uint32_t ulTypeMask;

/* The name of the C source file to be written. */
static char pcCodeFileName[ MAX_PATH ];

/* The name of the header file to be written. */
static char pcHeaderFileName[ MAX_PATH ];

/* A stream buffer between the FreeRTOS tasks and the Windows thread. */
static StreamBuffer_t *xPacketBuffer;

/* A process handle of the Windows thread. */
static HANDLE pvProcessHandle;

static UBaseType_t uxNextPacketNumber;
static BaseType_t xFirstPacket = 1;

/* Bollean 'xDumpingReady' becomes true once all desired packet have been collected.
Further packets will be dropped (ignored). */
static volatile BaseType_t xDumpingReady = pdFALSE;

static DumpEntries_t *pxCurrentEntries;

static uint16_t usSourcePort;
static uint16_t usDestinationPort;

typedef struct xBufferheader
{
	size_t uxLength;
	UBaseType_t bIncoming : 1;
} Bufferheader_t;

static DumpEntries_t xExampleEntries = {
	.uxEntryCount = 4,	/* No more than 'dumpMAX_DUMP_ENTRIES' elements. */
	.xEntries = {
		{ .ulMask = flag_IN | flag_UDP,   .uxMax = 2u },
		{ .ulMask = flag_IN | flag_ARP,   .uxMax = 2u },
		{ .ulMask = flag_IN | flag_TCP,   .uxMax = 5u },
		{ .ulMask = flag_IN | flag_SYN,   .uxMax = 1u },
	}
};

const char pcHeaderCode[] =
	"/*\n"
	" * This file was created automatically by 'dump_packets.c'\n"
	" */\n"
	"\n"
	"/* Standard includes. */\n"
	"#include <stdio.h>\n"
	"#include <stdint.h>\n"
	"#include <stdarg.h>\n"
	"#include <io.h>\n"
	"#include <ctype.h>\n"
	"\n"
	"/* FreeRTOS includes. */\n"
	"#include <FreeRTOS.h>\n"
	"#include <task.h>\n\n"
	"#include \"%s\"\n\n";

const char pcHeaderHeader[] =
	"/*\n"
	" * This file was created automatically by 'dump_packets.c'\n"
	" */\n"
	"\n"
	"#ifndef PACKET_LIST_H\n\n"
	"#define PACKET_LIST_H\n\n"
	"typedef struct xDumpPacket\n"
	"{\n"
	"	const uint8_t *pucData;\n"
	"	size_t uxLength;\n"
	"	uint32_t ulType;\n"
	"	uint16_t usSource;\n"
	"	uint16_t usDestination;\n"
	"} DumpPacket_t;\n\n";

/*-----------------------------------------------------------*/

/* The Windows thread that actually writes the network packets to a C source and header file. */
static DWORD WINAPI prvWritePackets( LPVOID lpParameter );

static void vAddProtocolTags( uint8_t *pucEthernetBuffer, BaseType_t xIPType );
static void vDetermineMessageType( uint8_t *pucBuffer, BaseType_t xIncoming );
static void vActualDump( uint8_t *pucBuffer, size_t uxLength, BaseType_t xIncoming );
static void vAddType( uint32_t ulFlags, const char *pcFlagName );
static void vWriteHeaderFile( void );

/*-----------------------------------------------------------*/

void dump_packet_init( const char *pcFileName, DumpEntries_t *pxEntries )
{
size_t uxIndex;

	snprintf( pcCodeFileName, sizeof pcCodeFileName, "%s.c", pcFileName );
	snprintf( pcHeaderFileName, sizeof pcHeaderFileName, "%s.h", pcFileName );

	if( pxEntries == NULL )
	{
		pxEntries = &( xExampleEntries );
	}
	configASSERT( pxEntries->uxEntryCount > 0 );
	configASSERT( pxEntries->uxEntryCount <= dumpMAX_DUMP_ENTRIES );

	for( uxIndex = 0; uxIndex < pxEntries->uxEntryCount; uxIndex++ )
	{
		pxEntries->xEntries[ uxIndex ].uxCount = 0;
	}

	pxCurrentEntries = pxEntries;

	if( xPacketBuffer == NULL )
	{
	size_t uxLength, uxSize;

		/* Enough space for e.g. 32 buffers and length words. */
		uxLength = dumpITEM_COUNT * ( sizeof( void * ) + ipconfigNETWORK_MTU + ipSIZE_OF_ETH_HEADER );
		uxSize = ( sizeof( *xPacketBuffer )  + uxLength ) - sizeof( xPacketBuffer->ucArray );
		xPacketBuffer = ( StreamBuffer_t * ) pvPortMalloc( uxSize );
		configASSERT( xPacketBuffer != NULL );
		vStreamBufferClear( xPacketBuffer );
		xPacketBuffer->LENGTH = uxLength;
	}

	if( pvProcessHandle == NULL )
	{
		pvProcessHandle = CreateThread( NULL, 0, prvWritePackets, NULL, CREATE_SUSPENDED, NULL );
		if( pvProcessHandle != NULL )
		{
			SetThreadPriority( pvProcessHandle, dumpPROCESS_THREAD_PRIORITY );
			SetThreadPriorityBoost( pvProcessHandle, TRUE );
			SetThreadAffinityMask( pvProcessHandle, 0x0E );
			ResumeThread( pvProcessHandle );
		}
	}
}
/*-----------------------------------------------------------*/

void dump_packet( const uint8_t *pucBuffer, size_t uxLength, BaseType_t xIncoming )
{
	/* This function shall be called from a normal FreeRTOS task only. */
	if( xPacketBuffer != NULL )
	{
		if( xDumpingReady == pdFALSE )
		{
		size_t uxSpace = uxStreamBufferGetSpace( xPacketBuffer );
		size_t uxNeeded = uxLength + sizeof( size_t );

			if( uxNeeded < uxSpace )
			{
			Bufferheader_t xheader;

				xheader.uxLength = uxLength;
				xheader.bIncoming = xIncoming;
				uxStreamBufferAdd( xPacketBuffer, 0u, ( const uint8_t * ) &( xheader ), sizeof( xheader ) );
				uxStreamBufferAdd( xPacketBuffer, 0u, pucBuffer, uxLength );
			}
			else
			{
				/* Drop this packet. */
			}
		}
		else
		{
			/* The Windows thread 'prvWritePackets()' had received enough packets.
			The packet buffer may be freed. */
			vPortFree( xPacketBuffer );
			xPacketBuffer = NULL;
		}
	}
}
/*-----------------------------------------------------------*/

static DWORD WINAPI prvWritePackets( LPVOID lpParameter )
{
	/* This is a Windows thread, not a FreeRTOS task. FreeRTOS API's may not be called. */
	for( ;; )
	{
		Sleep( 100 );

		while( ( xPacketBuffer != NULL ) && ( xDumpingReady == pdFALSE ) )
		{
		Bufferheader_t xHeader;
		size_t uxBytes = uxStreamBufferGetSize( xPacketBuffer );

			if( uxBytes <= sizeof( xHeader ) )
				break;

			/* Peek the number of bytes available. */
			uxStreamBufferGet( xPacketBuffer, 0u, ( uint8_t * ) &( xHeader ), sizeof( xHeader ), pdTRUE );
			if( uxBytes >= sizeof( xHeader ) + xHeader.uxLength );
			{
			size_t xBytesRead;
			uint8_t pcBuffer[ ipconfigNETWORK_MTU ];
			size_t xActualCount;

				uxStreamBufferGet( xPacketBuffer, 0u, NULL, sizeof( xHeader ), pdFALSE );
				xActualCount = uxStreamBufferGet( xPacketBuffer, 0u, pcBuffer, xHeader.uxLength, pdFALSE );
				vActualDump( pcBuffer, xActualCount, xHeader.bIncoming );
			}
		}
	}
}
/*-----------------------------------------------------------*/

static int _fprintf( FILE *pxHandle, const char* pcFormat, ... )
{
char pcString[ 255 ];
BaseType_t iCount;

	va_list args;
	va_start (args, pcFormat);
	iCount = vsnprintf( pcString, sizeof pcString, pcFormat, args);
	va_end (args);
	fwrite( pcString, 1u, iCount, pxHandle );

	return iCount;
}
/*-----------------------------------------------------------*/

static void vWriteHeaderFile( void )
{
FILE *outfile;

	outfile = fopen( pcHeaderFileName, "w" );
	if( outfile != NULL )
	{
		fwrite( pcHeaderHeader, 1u, sizeof( pcHeaderHeader ) - 1u, outfile );
		_fprintf( outfile, "#define dumpPACKET_COUNT %lu\n\n",
			( uxNextPacketNumber < 1u ) ? 1u : uxNextPacketNumber );
		_fprintf( outfile, "extern DumpPacket_t *xPacketList[ dumpPACKET_COUNT ];\n\n" );
		_fprintf( outfile, "#endif PACKET_LIST_H\n" );

		fclose ( outfile );
	}
}
/*-----------------------------------------------------------*/

static void vAddType( uint32_t ulFlags, const char *pcFlagName )
{
size_t uxLength = strlen( pcTypeString );
char pcString[ 64 ];
BaseType_t iCount;

	ulTypeMask |= ulFlags;
 
	if( uxLength == 0 )
	{
		snprintf( pcTypeString, sizeof pcTypeString, "%s", pcFlagName );
	}
	else
	{
		snprintf( pcTypeString + uxLength, sizeof pcTypeString - 1, " | %s", pcFlagName );
	}
}
/*-----------------------------------------------------------*/

static void vAddProtocolTags( uint8_t *pucEthernetBuffer, BaseType_t xIPType )
{
ProtocolHeaders_t *pxProtocolHeaders;
#if( ipconfigUSE_IPv6 != 0 )
	const IPHeader_IPv6_t * pxIPHeader_IPv6;
#endif
UBaseType_t uxHeaderLength;
uint8_t ucProtocol;
IPPacket_t * pxIPPacket;
IPHeader_t * pxIPHeader;

	pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
	pxIPHeader = &( pxIPPacket->xIPHeader );
	#if( ipconfigUSE_IPv6 != 0 )
	pxIPHeader_IPv6 = ipPOINTER_CAST( const IPHeader_IPv6_t *, &( pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] ) );
	if( pxIPPacket->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE )
	{
		uxHeaderLength = ipSIZE_OF_IPv6_HEADER;
		ucProtocol = pxIPHeader_IPv6->ucNextHeader;
		pxProtocolHeaders = ipPOINTER_CAST( ProtocolHeaders_t *, &( pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER ] ) );
	}
	else
	#endif
	{
	size_t uxLength = ( size_t ) pxIPHeader->ucVersionHeaderLength;

		/* Check if the IP headers are acceptable and if it has our destination.
		The lowest four bits of 'ucVersionHeaderLength' indicate the IP-header
		length in multiples of 4. */
		uxHeaderLength = ( size_t ) ( ( uxLength & 0x0Fu ) << 2 );
		ucProtocol = pxIPPacket->xIPHeader.ucProtocol;
		pxProtocolHeaders = ipPOINTER_CAST( ProtocolHeaders_t *, &( pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxHeaderLength ] ) );
	}

	switch( ucProtocol )
	{
		case ipPROTOCOL_ICMP :
			ADD_TYPE( ICMP4 );
			break;

#if( ipconfigUSE_IPv6 != 0 )
		case ipPROTOCOL_ICMP_IPv6:
			ADD_TYPE( ICMP6 );
			break;
#endif

		case ipPROTOCOL_UDP :
			{
				ADD_TYPE( UDP );
				usSourcePort = pxProtocolHeaders->xUDPHeader.usSourcePort;
				usDestinationPort = pxProtocolHeaders->xUDPHeader.usDestinationPort;
				if( usSourcePort == FreeRTOS_htons( dnsDNS_PORT) )
				{
					ADD_TYPE( DNS );
					ADD_TYPE( REPLY );
				}
				else if( usDestinationPort == FreeRTOS_htons( dnsDNS_PORT) )
				{
					ADD_TYPE( DNS );
					ADD_TYPE( REQUEST );
				}
			}
			break;
#if ipconfigUSE_TCP == 1
		case ipPROTOCOL_TCP :
			{
				ADD_TYPE( TCP );
				usSourcePort = pxProtocolHeaders->xTCPHeader.usSourcePort;
				usDestinationPort = pxProtocolHeaders->xTCPHeader.usDestinationPort;
				if( ( pxProtocolHeaders->xTCPHeader.ucTCPFlags & tcpTCP_FLAG_SYN ) != 0u )
				{
					ADD_TYPE( SYN );
				}
				if( ( pxProtocolHeaders->xTCPHeader.ucTCPFlags & tcpTCP_FLAG_FIN ) != 0u )
				{
					ADD_TYPE( FIN );
				}
				if( ( pxProtocolHeaders->xTCPHeader.ucTCPFlags & tcpTCP_FLAG_RST ) != 0u )
				{
					ADD_TYPE( RST );
				}
				if( ( pxProtocolHeaders->xTCPHeader.ucTCPFlags & tcpTCP_FLAG_ACK ) != 0u )
				{
					ADD_TYPE( ACK );
				}
			}
			break;
#endif
	}
}
/*-----------------------------------------------------------*/

static void vDetermineMessageType( uint8_t *pucBuffer, BaseType_t xIncoming )
{
EthernetHeader_t *pxEthernetHeader;

	if( xIncoming != 0 )
	{
		ADD_TYPE( IN );
	}
	else
	{
		ADD_TYPE( OUT );
	}
	pxEthernetHeader = ( EthernetHeader_t * ) pucBuffer;

	/* Interpret the received Ethernet packet. */
	switch( pxEthernetHeader->usFrameType )
	{
		case ipARP_FRAME_TYPE :
			{
			ARPPacket_t * pxARPFrame;
			ARPHeader_t *pxARPHeader;

				/* The Ethernet frame contains an ARP packet. */
				ADD_TYPE( FRAME_ARP );
				pxARPFrame = ( ARPPacket_t * ) pucBuffer;
				pxARPHeader = &( pxARPFrame->xARPHeader );
				ADD_TYPE( ARP );
				switch( pxARPHeader->usOperation )
				{
				case ipARP_REQUEST:
					ADD_TYPE( REQUEST );
					break;
				case ipARP_REPLY:
					ADD_TYPE( REPLY );
					break;
				default:
					ADD_TYPE( UNKNOWN );
					break;
				}
			}
			break;

		case ipIPv4_FRAME_TYPE :
			{
				ADD_TYPE( FRAME_4 );
				vAddProtocolTags( pucBuffer, 4 );
			}
			break;
			
	#if( ipconfigUSE_IPv6 != 0 )
		case ipIPv6_FRAME_TYPE :
			{
				ADD_TYPE( FRAME_6 );
				vAddProtocolTags( pucBuffer, 6 );
			}
			break;
	#endif
		default :
			/* No other packet types are handled.  Nothing to do. */
			ADD_TYPE( Unknown_FRAME );
			break;
	}
}
/*-----------------------------------------------------------*/

static void vActualDump( uint8_t *pucBuffer, size_t uxLength, BaseType_t xIncoming )
{
char pcString[ 513 ];
size_t uxOffset;
size_t uxIndex;
size_t uxCompleteCount = 0;
BaseType_t xUseIt = pdFALSE;

	usSourcePort = 0u;
	usDestinationPort = 0u;
	pcTypeString[ 0 ] = 0;
	ulTypeMask = 0uL;

	if( pxCurrentEntries == NULL )
	{
		return;
	}

	vDetermineMessageType( pucBuffer, xIncoming );

	for( uxIndex = 0; uxIndex < pxCurrentEntries->uxEntryCount; uxIndex++ )
	{
		if( pxCurrentEntries->xEntries[ uxIndex ].uxCount < pxCurrentEntries->xEntries[ uxIndex ].uxMax )
		{
		uint32_t ulMask = pxCurrentEntries->xEntries[ uxIndex ].ulMask;

			if( ( ulMask & ulTypeMask ) == ulMask )
			{
				pxCurrentEntries->xEntries[ uxIndex ].uxCount++;
				xUseIt = pdTRUE;
			}
		}
		else
		{
			uxCompleteCount++;
		}
	}
	FreeRTOS_printf( ( "prvWritePackets: done %d/%d : (%d,%d) (%d,%d) (%d,%d) (%d,%d)\n",
		uxCompleteCount,
		pxCurrentEntries->uxEntryCount,
		pxCurrentEntries->xEntries[ 0 ].uxCount, pxCurrentEntries->xEntries[ 0 ].uxMax,
		pxCurrentEntries->xEntries[ 1 ].uxCount, pxCurrentEntries->xEntries[ 1 ].uxMax,
		pxCurrentEntries->xEntries[ 2 ].uxCount, pxCurrentEntries->xEntries[ 2 ].uxMax,
		pxCurrentEntries->xEntries[ 3 ].uxCount, pxCurrentEntries->xEntries[ 3 ].uxMax ) );
	if( uxCompleteCount >= pxCurrentEntries->uxEntryCount )
	{
		FreeRTOS_printf( ( "prvWritePackets: all %lu packets have been collected\n", pxCurrentEntries->uxEntryCount ) );
		if( pxCurrentEntries != NULL )
		{
			FILE *outfile = fopen( pcCodeFileName, ( xFirstPacket != 0 ) ? "w" : "a+" );
			if ( outfile == NULL )
			{
				FreeRTOS_printf( ( "Can not create '%s'\n", pcCodeFileName ) );
			}
			else
			{
				/*
					Create a list with pointers to each network packet.
					DumpPacket_t *xPacketList[ dumpPACKET_COUNT ] =
					{
						&xPacket_0000,
						&xPacket_0001,
						&xPacket_0002,
						&xPacket_0003,
					}
				*/
				_fprintf( outfile, "\nDumpPacket_t *xPacketList[ dumpPACKET_COUNT ] =\n{\n" );
				for( uxIndex = 0; uxIndex < uxNextPacketNumber; uxIndex++ )
				{
					_fprintf( outfile, "\t&xPacket_%04lu,\n", uxIndex );
				}
				_fprintf( outfile, "};\n" );
				fclose( outfile );
				vWriteHeaderFile();
			}
			pxCurrentEntries = NULL;
			/* Tell the thread and the function dump_packet() that packet
			dumping is ready. */
			xDumpingReady = pdTRUE;
		}
		return;
	}
	if( xUseIt == pdFALSE )
	{
		return;
	}

	printf("prvWritePackets: Read %lu bytes, type %s\n", uxLength, pcTypeString );

	FILE *outfile = fopen( pcCodeFileName, ( xFirstPacket != 0 ) ? "w" : "a+" );
	if ( outfile == NULL )
	{
		FreeRTOS_printf( ( "Can not create '%s'\n", pcCodeFileName ) );
		return;
	}
	if( xFirstPacket != 0 )
	{
	char *pcPtr;
	size_t xLength;

		vWriteHeaderFile( pcHeaderFileName );
		xLength = snprintf( pcString, sizeof pcString, pcHeaderCode, pcHeaderFileName );
		fwrite( pcString, 1u, xLength, outfile );
		xFirstPacket = pdFALSE;
	}

	_fprintf( outfile, "\n/* Packet_%04d */\n", uxNextPacketNumber );
	_fprintf( outfile, "uint8_t ucPacket_%04lx[ %lu ] =\n{\n", uxNextPacketNumber, uxLength );

	for( uxOffset = 0u; uxOffset < uxLength; )
	{
	size_t uxCurLength = 0u;
	size_t uxLast = uxOffset + dumpBYTES_PER_ROW;
	BaseType_t xFirst = pdTRUE;

		if( uxLast > uxLength )
		{
			uxLast = uxLength;
		}
		while( uxOffset < uxLast )
		{
			uxCurLength += snprintf( pcString + uxCurLength, sizeof pcString - uxCurLength, "%s0x%02x",
				( uxCurLength == 0 ) ? "\t" : ", ", pucBuffer[ uxOffset ] );
			uxOffset++;
		}
		if( uxCurLength != 0u )
		{
			uxCurLength += snprintf( pcString + uxCurLength, sizeof pcString - uxCurLength, "%s\n",
				( uxOffset == uxLength )  ? "\n};" : "," );
			fwrite( pcString, 1u, uxCurLength, outfile );
		}
	}

	_fprintf( outfile, "\n");

	_fprintf( outfile,
		"DumpPacket_t xPacket_%04lx =\n{\n"
		"\t.pucData = ucPacket_%04lx,\n"
		"\t.uxLength = %lu,\n"
		"\t.ulType = 0x%lX, /* %s */\n",
		uxNextPacketNumber, uxNextPacketNumber, uxLength, ulTypeMask, pcTypeString );

	if( usSourcePort != 0u )
	{
		_fprintf( outfile,
			"\t.usSource = %u,\n", FreeRTOS_ntohs( usSourcePort ) );
	}
	if( usSourcePort != 0u )
	{
		_fprintf( outfile,
			"\t.usDestination = %u,\n", FreeRTOS_ntohs( usDestinationPort ) );
	}

	_fprintf( outfile,
		"};\n"
		"/*-----------------------------------------------------------*/\n\n" );
	fclose( outfile );
	uxNextPacketNumber++;
}
/*-----------------------------------------------------------*/

#endif	/* ( ipconfigUSE_DUMP_PACKETS != 0 ) */

