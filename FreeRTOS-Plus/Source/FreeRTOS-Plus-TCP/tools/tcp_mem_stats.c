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
 * tcp_mem_stats.c
 * Used to create a CSV file with detaild information about the memory usage of FreeRTOS+TCP.
 * See tools/tcp_mem_stats.md for further description.
 */

/* Standard includes. */
#include <stdio.h>
#include <stdint.h>
#include <stdarg.h>

/* FreeRTOS includes. */
#include <FreeRTOS.h>
#include "task.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_Stream_Buffer.h"
#include "FreeRTOS_ARP.h"
#include "FreeRTOS_IP_Private.h"

#include "tcp_mem_stats.h"

#ifndef ipconfigTCP_MEM_STATS_MAX_ALLOCATION
	#define ipconfigTCP_MEM_STATS_MAX_ALLOCATION     128u
	#pragma warning "ipconfigTCP_MEM_STATS_MAX_ALLOCATION undefined?"
#endif

#if( ipconfigUSE_TCP_MEM_STATS != 0 )

/* When a streambuffer is allocated, 4 extra bytes will be reserved. */

#define STREAM_BUFFER_ROUNDUP_BYTES		4

#define STATS_PRINTF( MSG ) \
	xCurrentLine++; \
	configPRINTF( MSG )

#define ETH_MAX_PACKET_SIZE		( ( ipconfigNETWORK_MTU + ipSIZE_OF_ETH_HEADER + ipBUFFER_PADDING + 31 ) & ~0x1FuL )
/*-----------------------------------------------------------*/

/* Objects are allocated and deleted. This structure stores the type
and the size of the object. */
typedef struct xTCP_ALLOCATION
{
	TCP_MEMORY_t xMemType;
	void *pxObject;
	UBaseType_t uxNumber;
	size_t uxSize;
} TCP_ALLOCATION_t;
/*-----------------------------------------------------------*/


static void vWriteHeader( void );

static size_t uxCurrentMallocSize;
static TCP_ALLOCATION_t xAllocations[ ipconfigTCP_MEM_STATS_MAX_ALLOCATION ];
static size_t uxAllocationCount;
static BaseType_t xFirstItem = pdTRUE;
UBaseType_t uxNextObjectNumber;
static BaseType_t xCurrentLine = 0;
static BaseType_t xFirstDumpLine = 0;
static BaseType_t xLastHeaderLineNr = 0;
static BaseType_t xLoggingStopped = 0;
/*-----------------------------------------------------------*/

static void vAddAllocation( TCP_MEMORY_t xMemType, void *pxObject, size_t uxSize )
{
size_t uxIndex;

	vTaskSuspendAll();
	{
		for( uxIndex = 0; uxIndex < uxAllocationCount; uxIndex++ )
		{
			if( xAllocations[ uxIndex ].pxObject == pxObject )
			{
				/* Already added, strange. */
				FreeRTOS_printf( ( "vAddAllocation: Pointer %p already added\n", pxObject ) );
				return;
			}
		}
		if( uxAllocationCount >= ipconfigTCP_MEM_STATS_MAX_ALLOCATION )
		{
			/* The table is full. */
			return;
		}
		xAllocations[ uxIndex ].pxObject = pxObject;
		xAllocations[ uxIndex ].xMemType = xMemType;
		xAllocations[ uxIndex ].uxSize = uxSize;
		xAllocations[ uxIndex ].uxNumber = uxNextObjectNumber++;
		uxAllocationCount++;
	}
	xTaskResumeAll();
}
/*-----------------------------------------------------------*/

static TCP_ALLOCATION_t *pxRemoveAllocation( void *pxObject )
{
size_t uxSource = 0, uxTarget = 0;
static TCP_ALLOCATION_t xAllocation = { 0 };
BaseType_t xFound = pdFALSE;
TCP_ALLOCATION_t *pxReturn;

	vTaskSuspendAll();
	{
		for( ; uxSource < uxAllocationCount; uxSource++ )
		{
			if( xAllocations[ uxSource ].pxObject == pxObject )
			{
				/* This is entry will be removed. */
				( void ) memcpy( &( xAllocation ), &( xAllocations[ uxSource ] ), sizeof xAllocation );
				xFound = pdTRUE;
			}
			else
			{
				xAllocations[ uxTarget ] = xAllocations[ uxSource ];
				uxTarget++;
			}
		}
		if( xFound != pdFALSE )
		{
			uxAllocationCount--;
			pxReturn = &( xAllocation );
		}
		else
		{
			pxReturn = NULL;
		}
	}
	xTaskResumeAll();
	return pxReturn;
}
/*-----------------------------------------------------------*/

static const char *pcTypeName( TCP_MEMORY_t xMemType )
{
	switch( xMemType )
	{
	case tcpSOCKET_TCP:         return "TCP-Socket";
	case tcpSOCKET_UDP:         return "UDP-Socket";
	case tcpSOCKET_SET:			return "SocketSet";
	case tcpSEMAPHORE:          return "Semaphore";
	case tcpRX_STREAM_BUFFER:   return "RX-Buffer";
	case tcpTX_STREAM_BUFFER:   return "TX-Buffer";
	case tcpNETWORK_BUFFER:     return "networkBuffer";
	}
	return "Unknown object";
}
/*-----------------------------------------------------------*/

static void vWriteHeader()
{
size_t uxPacketSize;
size_t uxTXSize;
size_t uxStaticSize = 0;
BaseType_t xFirstLineNr = 0;

char pucComment[ 64 ] = "";
StreamBuffer_t *pxBuffer = NULL;
size_t uxTara = sizeof( *pxBuffer ) - sizeof( pxBuffer->ucArray );

	/* The approximate size of a buffer for a Network Packet. */
	STATS_PRINTF( ( "TCPMemStat,Some important ipconfig items:\n" ) );
	STATS_PRINTF( ( "TCPMemStat,ipconfig item,Value,Comment\n" ) );
	STATS_PRINTF( ( "TCPMemStat,NETWORK_MTU,%u\n",						ipconfigNETWORK_MTU ) );
	STATS_PRINTF( ( "TCPMemStat,TCP_MSS,%u\n",							ipconfigTCP_MSS ) );
	STATS_PRINTF( ( "TCPMemStat,USE_TCP,%u\n",							ipconfigUSE_TCP ) );
	STATS_PRINTF( ( "TCPMemStat,USE_TCP_WIN,%u\n",						ipconfigUSE_TCP_WIN ) );

	uxTXSize = ( size_t ) FreeRTOS_round_up( ipconfigTCP_TX_BUFFER_LENGTH, ipconfigTCP_MSS );

	STATS_PRINTF( ( "TCPMemStat,TCP_RX_BUFFER_LENGTH,%u,Plus %u bytes\n", ipconfigTCP_RX_BUFFER_LENGTH, uxTara + STREAM_BUFFER_ROUNDUP_BYTES ) );
	if( uxTXSize > ipconfigTCP_TX_BUFFER_LENGTH )
	{
		snprintf( pucComment, sizeof pucComment, ",Rounded up to %u x MSS (plus %u bytes)", uxTXSize / ipconfigTCP_MSS, uxTara + STREAM_BUFFER_ROUNDUP_BYTES );
	}
	STATS_PRINTF( ( "TCPMemStat,TCP_TX_BUFFER_LENGTH,%u%s\n",			ipconfigTCP_TX_BUFFER_LENGTH, pucComment ) );
	STATS_PRINTF( ( "TCPMemStat,USE_DHCP,%u\n",							ipconfigUSE_DHCP ) );

	/*
	 * Start of fixed RAM allocations.
	 */

	STATS_PRINTF( ( "TCPMemStat,\n" ) );
	STATS_PRINTF( ( "TCPMemStat,RAM that is always allocated either statically or on the heap:\n" ) );
	STATS_PRINTF( ( "TCPMemStat,ipconfig item,Value,PerUnit,Total\n" ) );
	xFirstLineNr = xCurrentLine;
	if( xBufferAllocFixedSize != 0 )
	{
	size_t uxBytes;

		/* Using BufferAllocation_1.c */
		uxPacketSize = ( ipconfigNETWORK_MTU + ipSIZE_OF_ETH_HEADER + ipBUFFER_PADDING + 31 ) & ~0x1FuL;
		uxBytes = ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS * ( uxPacketSize + sizeof( NetworkBufferDescriptor_t ) );

		STATS_PRINTF( ( "TCPMemStat,NUM_NETWORK_BUFFER_DESCRIPTORS,%u,%u,=B%d*C%d,Descriptors + buffers\n",
			ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS,
			uxPacketSize + sizeof( NetworkBufferDescriptor_t ),
			xCurrentLine,
			xCurrentLine ) );
		uxStaticSize += uxBytes;
	}
	else
	{
	size_t uxBytes;

		/* Using BufferAllocation_2.c */
		uxBytes = ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS * sizeof( NetworkBufferDescriptor_t );
		STATS_PRINTF( ( "TCPMemStat,NUM_NETWORK_BUFFER_DESCRIPTORS,%u,%u,=B%d*C%d,Descriptors only\n",
			ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS,
			sizeof( NetworkBufferDescriptor_t ),
			xCurrentLine,
			xCurrentLine ) );
		uxStaticSize += uxBytes;
	}
	{
		#if( ipconfigUSE_TCP_WIN != 0 )
		{
			STATS_PRINTF( ( "TCPMemStat,TCP_WIN_SEG_COUNT,%u,%u,=B%d*C%d\n",
				ipconfigTCP_WIN_SEG_COUNT, sizeof( TCPSegment_t ), xCurrentLine, xCurrentLine ) );
		}
		#else
		{
			STATS_PRINTF( ( "TCPMemStat,TCP_WIN_SEG_COUNT,%u,%u\n",			0, 0 ) );
		}
		#endif
	}
	{
	size_t uxBytes;
	size_t uxEntrySize;

		uxBytes = ipconfigEVENT_QUEUE_LENGTH * sizeof( IPStackEvent_t );
		STATS_PRINTF( ( "TCPMemStat,EVENT_QUEUE_LENGTH,%u,%u,=B%d*C%d\n",
			ipconfigEVENT_QUEUE_LENGTH,
			sizeof( IPStackEvent_t ),
			xCurrentLine,
			xCurrentLine ) );
		uxStaticSize += uxBytes;

		uxBytes = ipconfigIP_TASK_STACK_SIZE_WORDS * sizeof( void *);
		STATS_PRINTF( ( "TCPMemStat,IP_TASK_STACK_SIZE_WORDS,%u,%u,=B%d*C%d\n",
			ipconfigIP_TASK_STACK_SIZE_WORDS,
			sizeof( void *),
			xCurrentLine,
			xCurrentLine ) );
		uxStaticSize += uxBytes;

		uxBytes = ipconfigARP_CACHE_ENTRIES * sizeof( ARPCacheRow_t );
		STATS_PRINTF( ( "TCPMemStat,ARP_CACHE_ENTRIES,%u,%u,=B%d*C%d\n",
			ipconfigARP_CACHE_ENTRIES,
			sizeof( ARPCacheRow_t ),
			xCurrentLine,
			xCurrentLine ) );
		uxStaticSize += uxBytes;

		#if( ipconfigUSE_DNS_CACHE == 1 )
		{
			uxEntrySize = 3u * sizeof( uint32_t ) + ( ( ipconfigDNS_CACHE_NAME_LENGTH + 3 ) & ~0x3u );
			STATS_PRINTF( ( "TCPMemStat,DNS_CACHE_ENTRIES,%u,%u,=B%d*C%d\n",
				ipconfigDNS_CACHE_ENTRIES,
				uxEntrySize,
				xCurrentLine,
				xCurrentLine ) );
		}
		#endif
	}
	/*
	 * End of fixed RAM allocations.
	 */
	if( xBufferAllocFixedSize != 0 )
	{
		pucComment[0] = 0;
	}
	else
	{
	size_t uxBytes;

		/* BufferAllocation_2.c uses HEAP to store network packets. */
		uxPacketSize = ( ipconfigNETWORK_MTU + ipSIZE_OF_ETH_HEADER + ipBUFFER_PADDING + 3 ) & ~0x03uL;
		uxBytes = ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS * uxPacketSize;
		STATS_PRINTF( ( "TCPMemStat,Network buffers in HEAP,%u,%u,=B%d*C%d\n",
			ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS,
			uxPacketSize,
			xCurrentLine,
			xCurrentLine ) );
		uxStaticSize += uxBytes;
		snprintf( pucComment, sizeof pucComment, "Actual size fluctuates because BufferAllocation_2.c is used" );
	}
	xLastHeaderLineNr = xCurrentLine;

	STATS_PRINTF( ( "TCPMemStat,Total,,,=SUM(D%d:D%d),%s\n", xFirstLineNr + 1, xLastHeaderLineNr, pucComment ) );

	STATS_PRINTF( ( "TCPMemStat,\n" ) );
	STATS_PRINTF( ( "TCPMemStat,\n" ) );
	STATS_PRINTF( ( "TCPMemStat,The following allocations are done on the heap while running:\n" ) );
	STATS_PRINTF( ( "TCPMemStat,Create/Remove,Object,Size,Heap use,Pointer,Heap-min,Heap-Cur,comment\n" ) );
}
/*-----------------------------------------------------------*/

void vTCPMemStatCreate( TCP_MEMORY_t xMemType, void *pxObject, size_t uxSize )
{
	if( xLoggingStopped == pdFALSE )
	{
	StreamBuffer_t *pxBuffer = NULL;
	char pcExtra[ 81 ] = "";

		if( xFirstItem != pdFALSE )
		{
			xFirstItem = pdFALSE;
			vWriteHeader();
		}
		if( ( xMemType == tcpRX_STREAM_BUFFER ) || ( xMemType == tcpTX_STREAM_BUFFER ) )
		{
		size_t uxTara = sizeof( *pxBuffer ) - sizeof( pxBuffer->ucArray );
		size_t uxNett = uxSize - uxTara;

			snprintf( pcExtra, sizeof pcExtra, ",%u nett", uxNett );
		}

		if( xFirstDumpLine == 0 )
		{
			xFirstDumpLine = xCurrentLine + 1;
		}

		xCurrentLine++;
		configPRINTF( ( "TCPMemStat,CREATE,%s,%lu,%lu,%u,%u,%u%s\n",
			pcTypeName( xMemType ),
			uxSize,
			uxCurrentMallocSize + uxSize,
			uxNextObjectNumber,
			xPortGetMinimumEverFreeHeapSize(),
			xPortGetFreeHeapSize(),
			pcExtra ) );
		uxCurrentMallocSize += uxSize;
		vAddAllocation( xMemType, pxObject, uxSize );
	}
}
/*-----------------------------------------------------------*/

void vTCPMemStatDelete( void *pxObject )
{
	if( xLoggingStopped == pdFALSE )
	{
	TCP_ALLOCATION_t *pxFound = pxRemoveAllocation( pxObject );

		if( xFirstDumpLine == 0 )
		{
			xFirstDumpLine = xCurrentLine + 1;
		}
		if( pxFound == NULL )
		{
			FreeRTOS_printf( ( "TCPMemStat: can not find pointer %p\n", pxObject ) );
		}
		else
		{
			xCurrentLine++;
			configPRINTF( ( "TCPMemStat,REMOVE,%s,-%lu,%lu,%x,%u,%u\n",
				pcTypeName( pxFound->xMemType ),
				pxFound->uxSize,
				uxCurrentMallocSize - pxFound->uxSize,
				pxFound->uxNumber,
				xPortGetMinimumEverFreeHeapSize(),
				xPortGetFreeHeapSize() ) );
			if( uxCurrentMallocSize < pxFound->uxSize )
			{
				uxCurrentMallocSize = 0uL;
			}
			else
			{
				uxCurrentMallocSize -= pxFound->uxSize;
			}
		}
	}
}
/*-----------------------------------------------------------*/

void vTCPMemStatClose()
{
	if( xLoggingStopped == pdFALSE )
	{
	// name;object;size;Heap;Ppointer;HeapMin;HeapDur;Comment
	BaseType_t xLastLineNr = xCurrentLine;

		xLoggingStopped = pdTRUE;

		STATS_PRINTF( ( "TCPMemStat,Totals,,,=MAX(D%d:D%d),,=MIN(F%d:F%d),=MAX(G%d:G%d)\n",
			xFirstDumpLine,
			xLastLineNr,
			xFirstDumpLine,
			xLastLineNr,
			xFirstDumpLine,
			xLastLineNr ) );
		STATS_PRINTF( ( "TCPMemStat,Maximum RAM usage:,,,=SUM(D%d;D%d)\n",
			xLastHeaderLineNr + 1,
			xLastLineNr + 1 ) );
	}
}
/*-----------------------------------------------------------*/

#endif	/* ( ipconfigUSE_TCP_MEM_STATS != 0 ) */
