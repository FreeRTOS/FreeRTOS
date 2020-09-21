/*
 * FreeRTOS Kernel V10.3.0
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
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

/* 
 * This file, along with DemoIPTrace.h, provides a basic example use of the
 * FreeRTOS+UDP trace macros.  The statistics gathered here can be viewed in
 * the command line interface.
 * See http://www.FreeRTOS.org/FreeRTOS-Plus/FreeRTOS_Plus_UDP/UDP_IP_Trace.shtml
 */

/* Standard includes. */
#include <stdint.h>

/* FreeRTOS includes. */ 
#include "FreeRTOS.h"
#include "task.h"

/* FreeRTOS+UDP includes. */
#include "FreeRTOS_UDP_IP.h"
#include "DemoIPTrace.h"

/* It is possible to remove the trace macros using the 
configINCLUDE_DEMO_DEBUG_STATS setting in FreeRTOSIPConfig.h. */
#if configINCLUDE_DEMO_DEBUG_STATS == 1

/*
 * Each row in the xIPTraceValues[] table contains a pointer to a function that
 * updates the value for that row.  Rows that latch the lowest value point to
 * this function (for example, this function can be used to latch the lowest
 * number of network buffers that were available during the execution of the
 * stack).
 */
static void prvStoreLowest( uint32_t *pulCurrentValue, uint32_t ulCount );

/*
 * Each row in the xIPTraceValues[] table contains a pointer to a function that
 * updates the value for that row.  Rows that simply increment an event count
 * point to this function.
 */
static void prvIncrementEventCount( uint32_t *pulCurrentValue, uint32_t ulCount );


xExampleDebugStatEntry_t xIPTraceValues[] =
{
	/* Comment out array entries to remove individual trace items. */

	{ iptraceID_NETWORK_INTERFACE_RECEIVE,			( const uint8_t * const ) "Packets received by the network interface",			prvIncrementEventCount, 0 },
	{ iptraceID_NETWORK_INTERFACE_TRANSMIT,			( const uint8_t * const ) "Count of transmitted packets",						prvIncrementEventCount, 0 },
	{ iptraceID_PACKET_DROPPED_TO_GENERATE_ARP,		( const uint8_t * const ) "Count of packets dropped to generate ARP",			prvIncrementEventCount, 0 },
	{ iptraceID_NETWORK_BUFFER_OBTAINED,			( const uint8_t * const ) "Lowest ever available network buffers",				prvStoreLowest, 0xffffUL },
	{ iptraceID_NETWORK_EVENT_RECEIVED,				( const uint8_t * const ) "Lowest ever free space in network event queue",		prvStoreLowest, 0xffffUL },
	{ iptraceID_FAILED_TO_OBTAIN_NETWORK_BUFFER,	( const uint8_t * const ) "Count of failed attempts to obtain a network buffer",prvIncrementEventCount, 0 },
	{ iptraceID_ARP_TABLE_ENTRY_EXPIRED,			( const uint8_t * const ) "Count of expired ARP entries",						prvIncrementEventCount, 0 },
	{ iptraceID_FAILED_TO_CREATE_SOCKET,			( const uint8_t * const ) "Count of failures to create a socket",				prvIncrementEventCount, 0 },
	{ iptraceID_RECVFROM_DISCARDING_BYTES,			( const uint8_t * const ) "Count of times recvfrom() has discarding bytes",		prvIncrementEventCount, 0 },
	{ iptraceID_ETHERNET_RX_EVENT_LOST,				( const uint8_t * const ) "Count of lost Ethenret Rx events (event queue full?)",prvIncrementEventCount, 0 },
	{ iptraceID_STACK_TX_EVENT_LOST,				( const uint8_t * const ) "Count of lost IP stack events (event queue full?)",	prvIncrementEventCount, 0 },
	{ ipconfigID_BIND_FAILED,						( const uint8_t * const ) "Count of failed calls to bind()",					prvIncrementEventCount, 0 },
	{ iptraceID_RECVFROM_TIMEOUT,					( const uint8_t * const ) "Count of receive timeouts",							prvIncrementEventCount, 0 },
	{ iptraceID_SENDTO_DATA_TOO_LONG,				( const uint8_t * const ) "Count of failed sends due to oversized payload",		prvIncrementEventCount, 0 },
	{ iptraceID_SENDTO_SOCKET_NOT_BOUND,			( const uint8_t * const ) "Count of failed sends due to unbound socket",		prvIncrementEventCount, 0 },
	{ iptraceID_NO_BUFFER_FOR_SENDTO,				( const uint8_t * const ) "Count of failed transmits due to timeout",			prvIncrementEventCount, 0 },
	{ iptraceID_WAIT_FOR_TX_DMA_DESCRIPTOR,			( const uint8_t * const ) "Number of times task had to wait to obtain a DMA Tx descriptor", prvIncrementEventCount, 0 },
	{ iptraceID_FAILED_TO_NOTIFY_SELECT_GROUP,		( const uint8_t * const ) "Failed to notify select group",						prvIncrementEventCount, 0 }
};

/*-----------------------------------------------------------*/

BaseType_t xExampleDebugStatEntries( void )
{
	/* Return the number of entries in the xIPTraceValues[] table. */
	return ( BaseType_t ) ( sizeof( xIPTraceValues ) / sizeof( xExampleDebugStatEntry_t ) );
}
/*-----------------------------------------------------------*/

void vExampleDebugStatUpdate( uint8_t ucIdentifier, uint32_t ulValue )
{
BaseType_t xIndex;
const BaseType_t xEntries = sizeof( xIPTraceValues ) / sizeof( xExampleDebugStatEntry_t );

	/* Update an entry in the xIPTraceValues[] table.  Each row in the table
	includes a pointer to a function that performs the actual update.  This
	function just executes the update function from that table row. */
	for( xIndex = 0; xIndex < xEntries; xIndex++ )
	{
		if( xIPTraceValues[ xIndex ].ucIdentifier == ucIdentifier )
		{
			xIPTraceValues[ xIndex ].vPerformAction( &( xIPTraceValues[ xIndex ].ulData ), ulValue );
			break;
		}
	}

	configASSERT( xIndex != xEntries );
}
/*-----------------------------------------------------------*/

static void prvIncrementEventCount( uint32_t *pulCurrentValue, uint32_t ulCount )
{
	/* Each row in the xIPTraceValues[] table contains a pointer to a function
	that updates the value for that row.  Rows that simply increment an event
	count point to this function. */
	( void ) ulCount;
	( *pulCurrentValue )++;
}
/*-----------------------------------------------------------*/

static void prvStoreLowest( uint32_t *pulCurrentValue, uint32_t ulCount )
{
	/* Each row in the xIPTraceValues[] table contains a pointer to a function
	that updates the value for that row.  Rows that latch the lowest value
	point to this function (for example, this function can be used to latch
	the lowest number of network buffers that were available during the
	execution of the stack). */
	if( ulCount < *pulCurrentValue )
	{
		*pulCurrentValue = ulCount;
	}
}
/*-----------------------------------------------------------*/


#endif /* configINCLUDE_DEMO_DEBUG_STATS == 1 */




