/*
 * FreeRTOS Kernel V10.0.1
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

#ifndef DEMO_IP_TRACE_MACROS_H
#define DEMO_IP_TRACE_MACROS_H

typedef void ( *vTraceAction_t )( uint32_t *, uint32_t );

/* Type that defines each statistic being gathered. */
typedef struct ExampleDebugStatEntry
{
	uint8_t ucIdentifier;					/* Unique identifier for statistic. */
	const uint8_t * const pucDescription;	/* Text description for the statistic. */
	vTraceAction_t vPerformAction;			/* Action to perform when the statistic is updated (increment counter, store minimum value, store maximum value, etc. */
	uint32_t ulData; 						/* The meaning of this data is dependent on the trace macro ID. */
} xExampleDebugStatEntry_t;

/* Unique identifiers used to locate the entry for each trace macro in the
xIPTraceValues[] table defined in DemoIPTrace.c. */
#define iptraceID_NETWORK_INTERFACE_RECEIVE					0
#define iptraceID_NETWORK_INTERFACE_TRANSMIT				1
#define iptraceID_PACKET_DROPPED_TO_GENERATE_ARP			2
/* Do not change IDs above this line as the ID is shared with a FreeRTOS+Nabto
demo. */
#define iptraceID_NETWORK_BUFFER_OBTAINED					3
#define iptraceID_NETWORK_BUFFER_OBTAINED_FROM_ISR			4
#define iptraceID_NETWORK_EVENT_RECEIVED					5
#define iptraceID_FAILED_TO_OBTAIN_NETWORK_BUFFER			6
#define iptraceID_ARP_TABLE_ENTRY_EXPIRED					7
#define iptraceID_FAILED_TO_CREATE_SOCKET					8
#define iptraceID_RECVFROM_DISCARDING_BYTES					9
#define iptraceID_ETHERNET_RX_EVENT_LOST					10
#define iptraceID_STACK_TX_EVENT_LOST						11
#define ipconfigID_BIND_FAILED								12
#define iptraceID_RECVFROM_TIMEOUT							13
#define iptraceID_SENDTO_DATA_TOO_LONG						14
#define iptraceID_SENDTO_SOCKET_NOT_BOUND					15
#define iptraceID_NO_BUFFER_FOR_SENDTO						16
#define iptraceID_WAIT_FOR_TX_DMA_DESCRIPTOR				17
#define iptraceID_FAILED_TO_NOTIFY_SELECT_GROUP				18

/* It is possible to remove the trace macros using the
configINCLUDE_DEMO_DEBUG_STATS setting in FreeRTOSIPConfig.h. */
#if configINCLUDE_DEMO_DEBUG_STATS == 1

	/* The trace macro definitions themselves.  Any trace macros left undefined
	will default to be empty macros. */
	#define iptraceNETWORK_BUFFER_OBTAINED( pxBufferAddress ) vExampleDebugStatUpdate( iptraceID_NETWORK_BUFFER_OBTAINED, uxQueueMessagesWaiting( ( xQueueHandle ) xNetworkBufferSemaphore ) )
	#define iptraceNETWORK_BUFFER_OBTAINED_FROM_ISR( pxBufferAddress ) vExampleDebugStatUpdate( iptraceID_NETWORK_BUFFER_OBTAINED, uxQueueMessagesWaiting( ( xQueueHandle ) xNetworkBufferSemaphore ) )

	#define iptraceNETWORK_EVENT_RECEIVED( eEvent )	{																				\
														uint16_t usSpace;															\
															usSpace = ( uint16_t ) uxQueueMessagesWaiting( xNetworkEventQueue );	\
															/* Minus one as an event was removed before the space was queried. */	\
															usSpace = ( ipconfigEVENT_QUEUE_LENGTH - usSpace ) - 1;					\
															vExampleDebugStatUpdate( iptraceID_NETWORK_EVENT_RECEIVED, usSpace );	\
														}

	#define iptraceFAILED_TO_OBTAIN_NETWORK_BUFFER()					vExampleDebugStatUpdate( iptraceID_FAILED_TO_OBTAIN_NETWORK_BUFFER, 0 )
	#define iptraceARP_TABLE_ENTRY_EXPIRED( ulIPAddress )				vExampleDebugStatUpdate( iptraceID_ARP_TABLE_ENTRY_EXPIRED, 0 )
	#define iptracePACKET_DROPPED_TO_GENERATE_ARP( ulIPAddress )		vExampleDebugStatUpdate( iptraceID_PACKET_DROPPED_TO_GENERATE_ARP, 0 )
	#define iptraceFAILED_TO_CREATE_SOCKET()							vExampleDebugStatUpdate( iptraceID_FAILED_TO_CREATE_SOCKET, 0 )
	#define iptraceRECVFROM_DISCARDING_BYTES( xNumberOfBytesDiscarded )	vExampleDebugStatUpdate( iptraceID_RECVFROM_DISCARDING_BYTES, 0 )
	#define iptraceETHERNET_RX_EVENT_LOST()								vExampleDebugStatUpdate( iptraceID_ETHERNET_RX_EVENT_LOST, 0 )
	#define iptraceSTACK_TX_EVENT_LOST( xEvent )						vExampleDebugStatUpdate( iptraceID_STACK_TX_EVENT_LOST, 0 )
	#define iptraceBIND_FAILED( xSocket, usPort )						vExampleDebugStatUpdate( ipconfigID_BIND_FAILED, 0 )
	#define iptraceNETWORK_INTERFACE_TRANSMIT()							vExampleDebugStatUpdate( iptraceID_NETWORK_INTERFACE_TRANSMIT, 0 )
	#define iptraceRECVFROM_TIMEOUT()									vExampleDebugStatUpdate( iptraceID_RECVFROM_TIMEOUT, 0 )
	#define iptraceSENDTO_DATA_TOO_LONG()								vExampleDebugStatUpdate( iptraceID_SENDTO_DATA_TOO_LONG, 0 )
	#define iptraceSENDTO_SOCKET_NOT_BOUND()							vExampleDebugStatUpdate( iptraceID_SENDTO_SOCKET_NOT_BOUND, 0 )
	#define iptraceNO_BUFFER_FOR_SENDTO()								vExampleDebugStatUpdate( iptraceID_NO_BUFFER_FOR_SENDTO, 0 )
	#define iptraceWAITING_FOR_TX_DMA_DESCRIPTOR()						vExampleDebugStatUpdate( iptraceID_WAIT_FOR_TX_DMA_DESCRIPTOR, 0 )
	#define iptraceFAILED_TO_NOTIFY_SELECT_GROUP( xSocket )				vExampleDebugStatUpdate( iptraceID_FAILED_TO_NOTIFY_SELECT_GROUP, 0 )
	#define iptraceNETWORK_INTERFACE_RECEIVE()							vExampleDebugStatUpdate( iptraceID_NETWORK_INTERFACE_RECEIVE, 0 )

	/*
	 * The function that updates a line in the xIPTraceValues table.
	 */
	void vExampleDebugStatUpdate( uint8_t ucIdentifier, uint32_t ulValue );

	/*
	 * Returns the number of entries in the xIPTraceValues table.
	 */
	BaseType_t xExampleDebugStatEntries( void );

#endif /* configINCLUDE_DEMO_DEBUG_STATS == 1 */


#endif /* DEMO_IP_TRACE_MACROS_H */

