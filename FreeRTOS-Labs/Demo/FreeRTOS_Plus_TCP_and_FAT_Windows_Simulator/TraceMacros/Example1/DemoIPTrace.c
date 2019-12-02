/*
    FreeRTOS V9.0.0 - Copyright (C) 2016 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    ***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
    ***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that is more than just the market leader, it     *
     *    is the industry's de facto standard.                               *
     *                                                                       *
     *    Help yourself get started quickly while simultaneously helping     *
     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
     *    tutorial book, reference manual, or both:                          *
     *    http://www.FreeRTOS.org/Documentation                              *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
    the FAQ page "My application does not run, what could be wrong?".  Have you
    defined configASSERT()?

    http://www.FreeRTOS.org/support - In return for receiving this top quality
    embedded software for free we request you assist our global community by
    participating in the support forum.

    http://www.FreeRTOS.org/training - Investing in training allows your team to
    be as productive as possible as early as possible.  Now you can receive
    FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
    Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

/*
 * This file, along with DemoIPTrace.h, provides a basic example use of the
 * FreeRTOS+TCP trace macros.  The statistics gathered here can be viewed in
 * the command line interface.
 * See http://www.FreeRTOS.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/UDP_CLI.html
 *
 * A simple generic mechanism is used that allocates a structure (see the
 * ExampleDebugStatEntry_t definition in DemoIPTrace.h) to each ID defined in
 * the same header file.  The structures are stored in an array (see the
 * xIPTraceValues[] below.
 *
 * The structure associates a function with a data value.  See the
 * vPerformAction and ulData members of ExampleDebugStatEntry_t respectively.
 * The function is used to manipulate the data.  At the time of writing two
 * functions can be used - these are prvIncrementEventCount() which simply
 * increments the data each time it is called, and prvStoreLowest() which
 * sets the data to the lowest value of an input parameter ever seen.  For
 * example, to store the lowest ever number of free network buffer descriptors
 * the parameter value is the current number of network buffer descriptors.
 *
 * The trace macros themselves are defined in DemoIPTrace.h and just invoke
 * vExampleDebugStatUpdate(), passing in an ID value.  vExampleDebugStatUpdate()
 * then just executes the function associated with that value (prvStoreLowest(),
 * prvIncrementEventCount(), etc.) as defined in the xIPTraceValues[] array.
 */

/* Standard includes. */
#include <stdint.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* FreeRTOS+TCP includes. */
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

/* The header file defines the IDs within this table.  The string is used to
print a friendly message for the stat, and the function pointer is used to
perform the action for the state - for example, note the lowest ever value for
a stat, or just count the number of times the event occurs. */
ExampleDebugStatEntry_t xIPTraceValues[] =
{
	/* Comment out array entries to remove individual trace items. */

	{ iptraceID_NETWORK_INTERFACE_RECEIVE,			"Packets received by the network interface",			prvIncrementEventCount, 0 },
	{ iptraceID_NETWORK_INTERFACE_TRANSMIT,			"Count of transmitted packets",							prvIncrementEventCount, 0 },
	{ iptraceID_PACKET_DROPPED_TO_GENERATE_ARP,		"Count of packets dropped to generate ARP",				prvIncrementEventCount, 0 },
	{ iptraceID_NETWORK_BUFFER_OBTAINED,			"Lowest ever available network buffers",				prvStoreLowest, 0xffffUL },
	{ iptraceID_NETWORK_EVENT_RECEIVED,				"Lowest ever free space in network event queue",		prvStoreLowest, 0xffffUL },
	{ iptraceID_FAILED_TO_OBTAIN_NETWORK_BUFFER,	"Count of failed attempts to obtain a network buffer",	prvIncrementEventCount, 0 },
	{ iptraceID_ARP_TABLE_ENTRY_EXPIRED,			"Count of expired ARP entries",							prvIncrementEventCount, 0 },
	{ iptraceID_FAILED_TO_CREATE_SOCKET,			"Count of failures to create a socket",					prvIncrementEventCount, 0 },
	{ iptraceID_RECVFROM_DISCARDING_BYTES,			"Count of times recvfrom() has discarding bytes",		prvIncrementEventCount, 0 },
	{ iptraceID_ETHERNET_RX_EVENT_LOST,				"Count of lost Etheret Rx events (event queue full?)",	prvIncrementEventCount, 0 },
	{ iptraceID_STACK_TX_EVENT_LOST,				"Count of lost IP stack events (event queue full?)",	prvIncrementEventCount, 0 },
	{ ipconfigID_BIND_FAILED,						"Count of failed calls to bind()",						prvIncrementEventCount, 0 },
	{ iptraceID_RECVFROM_TIMEOUT,					"Count of receive timeouts",							prvIncrementEventCount, 0 },
	{ iptraceID_SENDTO_DATA_TOO_LONG,				"Count of failed sends due to oversized payload",		prvIncrementEventCount, 0 },
	{ iptraceID_SENDTO_SOCKET_NOT_BOUND,			"Count of failed sends due to unbound socket",			prvIncrementEventCount, 0 },
	{ iptraceID_NO_BUFFER_FOR_SENDTO,				"Count of failed transmits due to timeout",				prvIncrementEventCount, 0 },
	{ iptraceID_WAIT_FOR_TX_DMA_DESCRIPTOR,			"Number of times task had to wait to obtain a DMA Tx descriptor", prvIncrementEventCount, 0 },
	{ iptraceID_FAILED_TO_NOTIFY_SELECT_GROUP,		"Failed to notify select group",						prvIncrementEventCount, 0 },
	{ iptraceID_TOTAL_NETWORK_BUFFERS_OBTAINED,		"Total network buffers obtained",						prvIncrementEventCount, 0 },
	{ iptraceID_TOTAL_NETWORK_BUFFERS_RELEASED,		"Total network buffers released",						prvIncrementEventCount, 0 }

};

/*-----------------------------------------------------------*/

BaseType_t xExampleDebugStatEntries( void )
{
	/* Return the number of entries in the xIPTraceValues[] table. */
	return ( BaseType_t ) ( sizeof( xIPTraceValues ) / sizeof( ExampleDebugStatEntry_t ) );
}
/*-----------------------------------------------------------*/

void vExampleDebugStatUpdate( uint8_t ucIdentifier, uint32_t ulValue )
{
BaseType_t xIndex;
const BaseType_t xEntries = sizeof( xIPTraceValues ) / sizeof( ExampleDebugStatEntry_t );

	/* Update an entry in the xIPTraceValues[] table.  Each row in the table
	includes a pointer to a function that performs the actual update.  This
	function just executes the update function from that table row.

	Search the array to find the identifier - this could be made more efficient
	by using the identifier as an index into the array - but that would come
	with the usability cost of needing to change all the identifiers above any
	identifiers that are later inserted into the table. */
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




