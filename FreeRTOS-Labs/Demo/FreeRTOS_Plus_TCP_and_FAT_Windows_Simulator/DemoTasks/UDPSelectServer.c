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
 * A number of sockets are created and added to a set. One task then blocks on
 * the set while the other task sends data to a (pseudo) random member of the
 * set.  The value sent increments from 0 to selMAX_TX_VALUE, and when all the
 * values have been sent a check is made that each expected value has indeed
 * been received before the cycle re-starts.
 *
 * See the following web page for essential demo usage and configuration
 * details:
 * http://www.FreeRTOS.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/examples_FreeRTOS_simulator.html
 */

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"

/* Demo project includes. */
#include "UDPSelectServer.h"

/* Exclude the whole file if select() is not being supported. */
#if( ipconfigSUPPORT_SELECT_FUNCTION == 1 )

/* The numbers of sockets added to the set. */
#define selNUMBER_OF_SOCKETS		( 3 )

/* Each cycle of the demo sends the value 0 to selMAX_TX_VALUE to a socket in
the set. */
#define selMAX_TX_VALUE				( 100 )

/*-----------------------------------------------------------*/

/*
 * The Tx task that sends the data to the sockets created by the Rx task and
 * added to the select set.
 */
static void prvMultipleSocketTxTask( void *pvParameters );

/*
 * Uses the FreeRTOS_select() API function to receive from multiple sockets.
 * This task expects to receive every value from 0 to selMAX_TX_VALUE during
 * each cycle of the demo.  An array with an index for each value it expects to
 * receive is used to record which values were and were not received.
 */
static void prvMultipleSocketRxTask( void *pvParameters );

/*-----------------------------------------------------------*/

/* The sockets used in FreeRTOS_select(). */
static Socket_t xRxSockets[ selNUMBER_OF_SOCKETS ] = { 0 };

/* Used to monitor the status of the task. */
static volatile uint32_t ulTxCycles = 0, ulRxCycles = 0, ulFailedRxCycles = 0, ulErrorOccurred = pdFALSE;

/* The block time used by the Tx task when sending - other delays are derived
from this value. */
const TickType_t xSendBlockTime = pdMS_TO_TICKS( 400 );
const TickType_t xReceiveBlockTime = pdMS_TO_TICKS( 600 );

/* The Tx task needs to know the handle of the Rx task. */
static TaskHandle_t xRxTaskHandle;

/*-----------------------------------------------------------*/

void vStartUDPSelectServerTasks( uint16_t usStackSize, uint32_t ulFirstPortNumber, UBaseType_t uxPriority )
{
	/* Create a task that sends to multiple sockets, and the task that uses the
	FreeRTOS_select() function to receive from multiple sockets.  The first port
	number to use is passed into both tasks using the task's parameter.	Other
	port numbers are consecutive from the first. */
	xTaskCreate( prvMultipleSocketTxTask, "MultiTx", usStackSize, ( void * ) ulFirstPortNumber, uxPriority, NULL );
	xTaskCreate( prvMultipleSocketRxTask, "MultiRx", usStackSize, ( void * ) ulFirstPortNumber, uxPriority, &xRxTaskHandle );
}
/*-----------------------------------------------------------*/

static void prvMultipleSocketRxTask( void *pvParameters )
{
SocketSet_t xFD_Set;
Socket_t xSocket;
struct freertos_sockaddr xAddress;
uint32_t xClientLength = sizeof( struct freertos_sockaddr ), ulFirstRxPortNumber, x;
uint32_t ulReceivedValue = 0, ulCount;
uint8_t ucReceivedValues[ selMAX_TX_VALUE ]; /* If the array position is pdTRUE then the corresponding value has been received. */
int32_t lBytes;
const TickType_t xRxBlockTime = 0;
BaseType_t xResult;

	/* The number of the port the first Rx socket will be bound to is passed in
	as the task parameter.  Other port numbers used are consecutive from this. */
	ulFirstRxPortNumber = ( uint32_t ) pvParameters;

	/* Create the set for sockets that will be passed into FreeRTOS_select(). */
	xFD_Set = FreeRTOS_CreateSocketSet();

	/* Create the sockets and add them to the set. */
	for( x = 0; x < selNUMBER_OF_SOCKETS; x++ )
	{
		/* Create the next Rx socket. */
		xRxSockets[ x ] = FreeRTOS_socket( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP );
		configASSERT( xRxSockets[ x ] != FREERTOS_INVALID_SOCKET );

		/* Bind to the next port number. */
		xAddress.sin_port = FreeRTOS_htons( ( uint16_t ) ( ulFirstRxPortNumber + x ) );
		FreeRTOS_bind( xRxSockets[ x ], &xAddress, sizeof( struct freertos_sockaddr ) );

		/* There should always be data available after FreeRTOS_select() so
		blocking on a read should not be necessary. */
		FreeRTOS_setsockopt( xRxSockets[ x ], 0, FREERTOS_SO_RCVTIMEO, &xRxBlockTime, sizeof( xRxBlockTime ) );

		/* Add the created socket to the set. */
		FreeRTOS_FD_SET( xRxSockets[ x ], xFD_Set, eSELECT_ALL );
	}

	for( ;; )
	{
		/* No values have yet been received so set each array position to
		pdFALSE.  Each expected Rx value has a corresponding array position. */
		memset( ( void * ) ucReceivedValues, pdFALSE, sizeof( ucReceivedValues ) );

		/* Wait for the other task to resume this task - indicating that it is
		about to start sending. */
		vTaskSuspend( NULL );

		/* Expect to receive selMAX_TX_VALUE values. */
		ulCount = 0;

		while( ulCount < selMAX_TX_VALUE )
		{
			/* Wait for a socket from the set to become available for
			reading. */
			xResult = FreeRTOS_select( xFD_Set, xReceiveBlockTime );

			if( xResult != 0 )
			{
				/* See which sockets have data waiting to be read. */
				for( x = 0; x < selNUMBER_OF_SOCKETS; x++ )
				{
					xSocket = xRxSockets[ x ];

					/* Find the expected value for this socket */
					if( FreeRTOS_FD_ISSET( xSocket, xFD_Set ) != 0 )
					{
						while( ( lBytes = FreeRTOS_recvfrom( xSocket, &( ulReceivedValue ), sizeof( uint32_t ), 0, &xAddress, &xClientLength ) ) > 0 )
						{
							/* Received another message. */
							ulCount++;

							/* It is always expected that the read will pass. */
							configASSERT( ( size_t ) lBytes == ( sizeof( uint32_t ) ) );

							/* Don't expect to receive anything greater than
							selMAX_TX_VALUE - 1. */
							configASSERT( ulReceivedValue < selMAX_TX_VALUE );

							/* Don't expect to receive any value twice. */
							configASSERT( ucReceivedValues[ ulReceivedValue ] != pdTRUE );
							if( ucReceivedValues[ ulReceivedValue ] != pdTRUE )
							{
								/* Mark the value as received by setting its
								index in the received array to pdTRUE. */
								ucReceivedValues[ ulReceivedValue ] = pdTRUE;
							}
							else
							{
								ulErrorOccurred = pdTRUE;
							}
						}
					}
				}
			}
			else
			{
				/* No value was received in time. */
				break;
			}
		}

		/* Were all values received? */
		if( ulCount == selMAX_TX_VALUE )
		{
			/* Check all selMAX_TX_VALUE values are present and correct
			before starting a new cycle.  It is valid for a few values at
			the beginning of the array to be missing as they may have been
			dropped for ARP messages, so start a few indexes in. */
			for( ulCount = 4; ulCount < selMAX_TX_VALUE; ulCount++ )
			{
				configASSERT( ucReceivedValues[ ulCount ] == pdTRUE );

				if( ucReceivedValues[ ulCount ] != pdTRUE )
				{
					/* The value corresponding to this array position was
					never received.  In a real application UDP is not
					reliable, but in this tightly controlled test it is
					unusual for a packet to be dropped. */
					ulErrorOccurred = pdTRUE;
				}
			}

			ulRxCycles++;
		}
		else
		{
			/* Just for viewing in the debugger. */
			ulFailedRxCycles++;
		}
	}
}
/*-----------------------------------------------------------*/

static void prvMultipleSocketTxTask( void *pvParameters )
{
uint32_t ulTxValue = 0;
struct freertos_sockaddr xDestinationAddress;
uint32_t ulIPAddress, ulFirstDestinationPortNumber, xPortNumber;
Socket_t xTxSocket;
uint32_t ulSendCount[ selNUMBER_OF_SOCKETS ];

	memset( ulSendCount, '\0', sizeof( ulSendCount ) );

	/* The first destination port number is passed in as the task parameter.
	Other destination port numbers used are consecutive from this. */
	ulFirstDestinationPortNumber = ( uint32_t ) pvParameters;

	/* Create the socket used to send to the sockets created by the Rx task.
	Let the IP stack select a port to bind to. */
	xTxSocket = FreeRTOS_socket( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP );
	FreeRTOS_bind( xTxSocket, NULL, sizeof( struct freertos_sockaddr ) );

	/* The Rx and Tx tasks execute at the same priority so it is possible that
	the Tx task will fill up the send queue - set a Tx block time to ensure
	flow control is managed if this happens. */
	FreeRTOS_setsockopt( xTxSocket, 0, FREERTOS_SO_SNDTIMEO, &xSendBlockTime, sizeof( xSendBlockTime ) );

	/* It is assumed that this task is not created until the network is up,
	so the IP address can be obtained immediately.  Store the IP address being
	used in ulIPAddress.  This is done so the socket can send to a different
	port on the same IP address. */
	FreeRTOS_GetAddressConfiguration( &ulIPAddress, NULL, NULL, NULL );

	/* This test sends to itself, so data sent from here is received by a server
	socket on the same IP address.  Setup the freertos_sockaddr structure with
	this nodes IP address. */
	xDestinationAddress.sin_addr = ulIPAddress;

	/* Block for a short time to ensure the task implemented by the
	prvMultipleSocketRxTask() function has finished creating the Rx sockets. */
	while( eTaskGetState( xRxTaskHandle ) != eSuspended )
	{
		vTaskDelay( xSendBlockTime );
	}
	vTaskResume( xRxTaskHandle );

	for( ;; )
	{
		/* Pseudo randomly select the destination port number from the range of
		valid destination port numbers. */
		xPortNumber = ipconfigRAND32() % selNUMBER_OF_SOCKETS;
		ulSendCount[ xPortNumber ]++;
		xDestinationAddress.sin_port = ( uint16_t ) ( ulFirstDestinationPortNumber + xPortNumber );
		xDestinationAddress.sin_port = FreeRTOS_htons( xDestinationAddress.sin_port );

		/* Send an incrementing value to the pseudo randomly selected port. */
		FreeRTOS_sendto( xTxSocket, &ulTxValue, sizeof( ulTxValue ), 0, &xDestinationAddress, sizeof( xDestinationAddress ) );
		ulTxValue++;

		if( ulTxValue >= selMAX_TX_VALUE )
		{
			/* Start over. */
			ulTxValue = 0;

			/* As a sanity check that this demo is valid, ensure each socket has
			been used at least once. */
			for( xPortNumber = 0; xPortNumber < selNUMBER_OF_SOCKETS; xPortNumber++ )
			{
				if( ulSendCount[ xPortNumber ] == 0 )
				{
					ulErrorOccurred = pdTRUE;
				}

				ulSendCount[ xPortNumber ] = 0;
			}

			/* Allow the Rx task to check it has received all the values. */
			while( eTaskGetState( xRxTaskHandle ) != eSuspended )
			{
				vTaskDelay( xSendBlockTime );
			}
			vTaskResume( xRxTaskHandle );

			/* Increment to show this task is still executing. */
			ulTxCycles++;
		}

		/* Delay here because in the Windows simulator the MAC interrupt
		simulator delays, so network traffic cannot be received any faster than
		this. */
		vTaskDelay( configWINDOWS_MAC_INTERRUPT_SIMULATOR_DELAY << 2 );
	}
}
/*-----------------------------------------------------------*/

BaseType_t xAreUDPSelectTasksStillRunning( void )
{
static uint32_t ulLastRxCycles = 0, ulLastTxCycles = 0;
BaseType_t ulError;

	ulError = ulErrorOccurred;

	if( ulRxCycles == ulLastRxCycles )
	{
		ulError |= pdTRUE;
	}

	if( ulTxCycles == ulLastTxCycles )
	{
		ulError |= pdTRUE;
	}

	ulLastRxCycles = ulRxCycles;
	ulLastTxCycles = ulTxCycles;

	return !ulError;
}

/* The whole file is excluded if select() is not being supported. */
#endif /* ipconfigSUPPORT_SELECT_FUNCTION */

