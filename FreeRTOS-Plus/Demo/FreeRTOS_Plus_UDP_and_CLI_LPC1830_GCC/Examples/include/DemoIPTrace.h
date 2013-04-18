/*
    FreeRTOS V7.4.1 - Copyright (C) 2013 Real Time Engineers Ltd.

    FEATURES AND PORTS ARE ADDED TO FREERTOS ALL THE TIME.  PLEASE VISIT
    http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS tutorial books are available in pdf and paperback.        *
     *    Complete, revised, and edited pdf reference manuals are also       *
     *    available.                                                         *
     *                                                                       *
     *    Purchasing FreeRTOS documentation will not only help you, by       *
     *    ensuring you get running as quickly as possible and with an        *
     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
     *    the FreeRTOS project to continue with its mission of providing     *
     *    professional grade, cross platform, de facto standard solutions    *
     *    for microcontrollers - completely free of charge!                  *
     *                                                                       *
     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
     *                                                                       *
     *    Thank you for using FreeRTOS, and thank you for your support!      *
     *                                                                       *
    ***************************************************************************


    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.

    >>>>>>NOTE<<<<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
    details. You should have received a copy of the GNU General Public License
    and the FreeRTOS license exception along with FreeRTOS; if not it can be
    viewed here: http://www.freertos.org/a00114.html and also obtained by
    writing to Real Time Engineers Ltd., contact details for whom are available
    on the FreeRTOS WEB site.

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************


    http://www.FreeRTOS.org - Documentation, books, training, latest versions, 
    license and Real Time Engineers Ltd. contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, and our new
    fully thread aware and reentrant UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High 
    Integrity Systems, who sell the code with commercial support, 
    indemnification and middleware, under the OpenRTOS brand.
    
    http://www.SafeRTOS.com - High Integrity Systems also provide a safety 
    engineered and independently SIL3 certified version for use in safety and 
    mission critical applications that require provable dependability.
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
#define iptraceID_NETWORK_BUFFER_OBTAINED					1
#define iptraceID_NETWORK_BUFFER_OBTAINED_FROM_ISR			2
#define iptraceID_NETWORK_EVENT_RECEIVED					3
#define iptraceID_FAILED_TO_OBTAIN_NETWORK_BUFFER			4
#define iptraceID_ARP_TABLE_ENTRY_EXPIRED					5
#define iptraceID_PACKET_DROPPED_TO_GENERATE_ARP			6
#define iptraceID_FAILED_TO_CREATE_SOCKET					7
#define iptraceID_RECVFROM_DISCARDING_BYTES					8
#define iptraceID_ETHERNET_RX_EVENT_LOST					9
#define iptraceID_STACK_TX_EVENT_LOST						10
#define ipconfigID_BIND_FAILED								11
#define iptraceID_NETWORK_INTERFACE_TRANSMIT				12
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

	/*
	 * The function that updates a line in the xIPTraceValues table.
	 */
	void vExampleDebugStatUpdate( uint8_t ucIdentifier, uint32_t ulValue );

	/*
	 * Returns the number of entries in the xIPTraceValues table.
	 */
	portBASE_TYPE xExampleDebugStatEntries( void );

#endif /* configINCLUDE_DEMO_DEBUG_STATS == 1 */


#endif /* DEMO_IP_TRACE_MACROS_H */

