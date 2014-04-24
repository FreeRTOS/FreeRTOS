/*
    FreeRTOS V8.0.1 - Copyright (C) 2014 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that has become a de facto standard.             *
     *                                                                       *
     *    Help yourself get started quickly and support the FreeRTOS         *
     *    project by purchasing a FreeRTOS tutorial book, reference          *
     *    manual, or both from: http://www.FreeRTOS.org/Documentation        *
     *                                                                       *
     *    Thank you!                                                         *
     *                                                                       *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available from the following
    link: http://www.freertos.org/a00114.html

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
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

/*
 * A number of sockets are created and added to a set. One task then blocks on
 * the set while the other task sends data to a (pseudo) random member of the
 * set.
 */

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* FreeRTOS+UDP includes. */
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_Sockets.h"

#define selTINY_DELAY				( ( portTickType ) 2 )
#define selNUMBER_OF_SOCKETS		( 3 )
#define selSELECT_QUEUE_SIZE		( selNUMBER_OF_SOCKETS * 2 )

/*
 * Sends data to multiple different sockets.
 */
static void prvMultipleSocketTxTask( void *pvParameters );

/*
 * Uses the FreeRTOS_select() API function to receive from multiple sockets.
 */
static void prvMultipleSocketRxTask( void *pvParameters );

/*-----------------------------------------------------------*/

static xSocket_t xRxSockets[ selNUMBER_OF_SOCKETS ] = { 0 };

/*-----------------------------------------------------------*/

void vStartSelectUDPServerTasks( uint16_t usStackSize, uint32_t ulFirstPortNumber, unsigned portBASE_TYPE uxPriority )
{
	/* Create task that sends to multiple sockets, and the task that uses the
	FreeRTOS_select() function to receive from multiple sockets.  The first
	port number to use is passed into both tasks using the task's parameter.
	Other port numbers are consecutive from the first. */
	xTaskCreate( prvMultipleSocketTxTask, "MultiTx", usStackSize, ( void * ) ulFirstPortNumber, uxPriority, NULL );
	xTaskCreate( prvMultipleSocketRxTask, "MultiRx", usStackSize, ( void * ) ulFirstPortNumber, uxPriority, NULL );
}
/*-----------------------------------------------------------*/

static void prvMultipleSocketRxTask( void *pvParameters )
{
xSocketSet_t xFD_Set;
xSocket_t xSocket;
struct freertos_sockaddr xAddress;
uint32_t xClientLength = sizeof( struct freertos_sockaddr ), ulFirstRxPortNumber, x;
uint32_t ulReceivedValue = 0, ulExpectedValue = 0UL, ulReceivedCount[ selNUMBER_OF_SOCKETS ] = { 0 };
int32_t lBytes;
const portTickType xRxBlockTime = 0;

	/* The number of the port the first Rx socket will be bound to is passed in
	as the task parameter.  Other port numbers used are consecutive from this. */
	ulFirstRxPortNumber = ( uint32_t ) pvParameters;

	/* Create the set of sockets that will be passed into FreeRTOS_select(). */
	xFD_Set = FreeRTOS_CreateSocketSet( selSELECT_QUEUE_SIZE );

	for( x = 0; x < selNUMBER_OF_SOCKETS; x++ )
	{
		/* Create the next Rx socket. */
		xRxSockets[ x ] = FreeRTOS_socket( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP );
		configASSERT( xRxSockets[ x ] );

		/* Bind to the next port number. */
		xAddress.sin_port = FreeRTOS_htons( ( uint16_t ) ( ulFirstRxPortNumber + x ) );
		FreeRTOS_bind( xRxSockets[ x ], &xAddress, sizeof( struct freertos_sockaddr ) );

		/* There should always be data available on the socket returned from
		FreeRTOS_select() so blocking on a read should not be necessary. */
		FreeRTOS_setsockopt( xRxSockets[ x ], 0, FREERTOS_SO_RCVTIMEO, &xRxBlockTime, sizeof( xRxBlockTime ) );

		/* Add the created socket to the set. */
		FreeRTOS_FD_SET( xRxSockets[ x ], xFD_Set );
	}

	for( ;; )
	{
		/* Wait for a socket from the set to become available for reading. */
		xSocket = FreeRTOS_select( xFD_Set, portMAX_DELAY );

		/* xSocket should never be NULL because FreeRTOS_select() was called
		with an indefinite delay (assuming INCLUDE_vTaskSuspend is set to 1). */
		configASSERT( xSocket );

		lBytes = FreeRTOS_recvfrom( xSocket, &( ulReceivedValue ), sizeof( uint32_t ), 0, &xAddress, &xClientLength );

		/* It is possible that the first value received will not be zero
		because the first few transmitted packets may have been dropped to
		send an ARP and then wait the ARP reply. */
		if( ulExpectedValue == 0 )
		{
			if( ulExpectedValue != ulReceivedValue )
			{
				/* Correct for packets lost to ARP traffic. */
				ulExpectedValue = ulReceivedValue;
			}
		}

		/* Data should always be available even though the block time was set
		to zero because the socket was returned from FreeRTOS_select(). */
		configASSERT( lBytes == 4 );
		configASSERT( ulReceivedValue == ulExpectedValue );

		ulExpectedValue++;

		/* Keep a record of the number of times each socket has been used so it
		can be verified (using the debugger) that they all get used. */
		for( x= 0; x < selNUMBER_OF_SOCKETS; x++ )
		{
			if( xSocket == xRxSockets[ x ] )
			{
				( ulReceivedCount[ x ] )++;
				break;
			}
		}
	}
}
/*-----------------------------------------------------------*/

static void prvMultipleSocketTxTask( void *pvParameters )
{
uint32_t ulTxValue = 0;
struct freertos_sockaddr xDestinationAddress;
uint32_t ulIPAddress, ulFirstDestinationPortNumber, xPortNumber;
xSocket_t xTxSocket;
const portTickType xShortDelay = 100 / portTICK_RATE_MS, xSendBlockTime = 500 / portTICK_RATE_MS;

	srand( ( unsigned int ) &xPortNumber );

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
	vTaskDelay( xShortDelay );

	for( ;; )
	{
		/* Pseudo randomly select the destination port number from the range of
		valid destination port numbers. */
		xPortNumber = rand() % selNUMBER_OF_SOCKETS;
		xDestinationAddress.sin_port = ( uint16_t ) ( ulFirstDestinationPortNumber + xPortNumber );
		xDestinationAddress.sin_port = FreeRTOS_htons( xDestinationAddress.sin_port );

		/* Send an incrementing value. */
		FreeRTOS_sendto( xTxSocket, &ulTxValue, sizeof( ulTxValue ), 0, &xDestinationAddress, sizeof( xDestinationAddress ) );
		ulTxValue++;

		/* Delay here because in the Windows simulator the MAC interrupt
		simulator delays, so network trafic cannot be received any faster
		than this. */
		vTaskDelay( configWINDOWS_MAC_INTERRUPT_SIMULATOR_DELAY );
	}
}



