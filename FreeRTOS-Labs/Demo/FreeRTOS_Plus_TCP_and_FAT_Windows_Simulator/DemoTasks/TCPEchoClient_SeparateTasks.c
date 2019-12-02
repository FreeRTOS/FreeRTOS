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
 * A set of Tx and a set of Rx tasks are created.  The Tx tasks send TCP echo
 * requests to the standard echo port (port 7) on the IP address set by the
 * configECHO_SERVER_ADDR0 to configECHO_SERVER_ADDR3 constants.  The Rx tasks
 * then use the same socket to receive and validate the echoed reply.
 *
 * See the following web page for essential demo usage and configuration
 * details:
 * http://www.FreeRTOS.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/examples_FreeRTOS_simulator.html
 */

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "event_groups.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"

/* Exclude the whole file if FreeRTOSIPConfig.h is configured to use UDP only. */
#if( ipconfigUSE_TCP == 1 )

/* Short delay used between demo cycles to ensure the network does not get too
congested. */
#define echoLOOP_DELAY	pdMS_TO_TICKS( 500UL )

/* The echo server is assumed to be on port 7, which is the standard echo
protocol port. */
#define echoECHO_PORT	( 7 )

/* Dimensions the buffer used by prvEchoClientTxTask() to send a multiple of
MSS bytes at once. */
#define echoLARGE_BUFFER_SIZE_MULTIPLIER ( 10 )

/* Bit definitions used with the xSyncEventGroup event group to allow the
prvEchoClientTxTask() and prvEchoClientRxTask() tasks to synchronise before
commencing a new cycle with a different socket. */
#define echoTX_TASK_BIT		( 0x01 << 1 )
#define echoRX_TASK_BIT		( 0x01 << 2 )

/*-----------------------------------------------------------*/

/*
 * Uses a socket to send more than MSS bytes in one go to the standard echo
 * port number 7.  The echoed data is received on the same socket but in a
 * different task (see prvEchoClientRxTask() below).
 */
static void prvEchoClientTxTask( void *pvParameters );

/*
 * Uses the socket created in prvEchoClientTxTask() to receive the data sent
 * to the echo server by the prvEchoClientTxTask().
 */
static void prvEchoClientRxTask( void *pvParameters );

/* Rx and Tx time outs are used to ensure the sockets do not wait too long for
missing data. */
static const TickType_t xReceiveTimeOut = pdMS_TO_TICKS( 500 );
static const TickType_t xSendTimeOut = pdMS_TO_TICKS( 2000 );

/* Counters for each task created - for inspection only. */
static uint32_t ulTxTaskCycles = 0,	ulRxTaskCycles = 0;

/* The queue used by prvEchoClientTxTask() to send the next socket to use to
prvEchoClientRxTask(). */
static QueueHandle_t xSocketPassingQueue = NULL;

/* The event group used by the prvEchoClientTxTask() and prvEchoClientRxTask()
to synchronise prior to commencing a cycle using a new socket. */
static EventGroupHandle_t xSyncEventGroup = NULL;

/* Flag used to inform the Rx task that the socket is about to be shut down. */
int32_t lShuttingDown = pdFALSE;

/*-----------------------------------------------------------*/

void vStartTCPEchoClientTasks_SeparateTasks( uint16_t usTaskStackSize, UBaseType_t uxTaskPriority )
{
	/* Create the queue used to pass the socket to use from the Tx task to the
	Rx task. */
	xSocketPassingQueue = xQueueCreate( 1, sizeof( Socket_t ) );
	configASSERT( xSocketPassingQueue );

	/* Create the event group used by the Tx and Rx tasks to synchronise prior
	to commencing a cycle using a new socket. */
	xSyncEventGroup = xEventGroupCreate();
	configASSERT( xSyncEventGroup );

	/* Create the task that sends to an echo server, but lets a different task
	receive the reply on the same socket. */
	xTaskCreate( 	prvEchoClientTxTask,	/* The function that implements the task. */
					"Echo0",				/* Just a text name for the task to aid debugging. */
					usTaskStackSize,		/* The stack size is defined in FreeRTOSIPConfig.h. */
					NULL,					/* The task parameter, not used in this case. */
					uxTaskPriority,			/* The priority assigned to the task is defined in FreeRTOSConfig.h. */
					NULL );					/* The task handle is not used. */

	/* Create the task that receives the reply to echos initiated by the
	prvEchoClientTxTask() task. */
	xTaskCreate( prvEchoClientRxTask, "EchoRx", configMINIMAL_STACK_SIZE, NULL, uxTaskPriority + 1, NULL );
}
/*-----------------------------------------------------------*/

static void prvEchoClientTxTask( void *pvParameters )
{
Socket_t xSocket;
struct freertos_sockaddr xEchoServerAddress;
static char cTransmittedString[ ipconfigTCP_MSS * echoLARGE_BUFFER_SIZE_MULTIPLIER ];
uint32_t ulTxCount = 0UL, ulJunk;
BaseType_t lTransmitted, lReturned = 0, lCharacter;
const BaseType_t lStringLength = ipconfigTCP_MSS * echoLARGE_BUFFER_SIZE_MULTIPLIER;
size_t xLenToSend;
const uint32_t ulNumTxPerSocket = 5UL;
WinProperties_t xWinProps;
const TickType_t xTxEmptyDelay = 20 / portTICK_PERIOD_MS;
TickType_t xTimeEnteringLoop;

	/* Avoid warning about unused parameter. */
	( void ) pvParameters;

	/* Fill in the required buffer and window sizes. */
	xWinProps.lTxBufSize = 6 * ipconfigTCP_MSS;
	xWinProps.lTxWinSize = 3;
	xWinProps.lRxBufSize = 6 * ipconfigTCP_MSS;
	xWinProps.lRxWinSize = 3;

	/* Echo requests are sent to the echo server.  The address of the echo
	server is configured by the constants configECHO_SERVER_ADDR0 to
	configECHO_SERVER_ADDR3 in FreeRTOSConfig.h. */
	xEchoServerAddress.sin_port = FreeRTOS_htons( echoECHO_PORT );
	xEchoServerAddress.sin_addr = FreeRTOS_inet_addr_quick( configECHO_SERVER_ADDR0,
															configECHO_SERVER_ADDR1,
															configECHO_SERVER_ADDR2,
															configECHO_SERVER_ADDR3 );

	/* Create the string that is sent to the echo server. */
	for( ulTxCount = 0; ulTxCount < echoLARGE_BUFFER_SIZE_MULTIPLIER; ulTxCount++ )
	{
		/* Generate character. */
		lCharacter = ( int32_t ) '0' + ulTxCount;

		/* Write a whole ipconfigTCP_MSS block of the character into the Tx
		buffer. */
		memset( ( void * ) &( cTransmittedString[ ipconfigTCP_MSS * ulTxCount ] ), lCharacter, ipconfigTCP_MSS );
	}

	for( ;; )
	{
		ulTxCount = 0;

		/* Create a socket. */
		xSocket = FreeRTOS_socket( FREERTOS_AF_INET, FREERTOS_SOCK_STREAM, FREERTOS_IPPROTO_TCP );
		configASSERT( xSocket != FREERTOS_INVALID_SOCKET );

		/* Set a time out so a missing reply does not cause the task to block
		indefinitely. */
		FreeRTOS_setsockopt( xSocket, 0, FREERTOS_SO_RCVTIMEO, &xReceiveTimeOut, sizeof( xReceiveTimeOut ) );
		FreeRTOS_setsockopt( xSocket, 0, FREERTOS_SO_SNDTIMEO, &xSendTimeOut, sizeof( xSendTimeOut ) );

		/* Set the buffer and window sizes. */
		FreeRTOS_setsockopt( xSocket, 0, FREERTOS_SO_WIN_PROPERTIES, ( void * ) &xWinProps,	sizeof( xWinProps ) );

		/* Attempt to connect to the echo server. */
		if( FreeRTOS_connect( xSocket, &xEchoServerAddress, sizeof( xEchoServerAddress ) ) == 0 )
		{
			/* Send the connected socket to the Rx task so it can receive the
			echoed replies from a different task. */
			lReturned = xQueueSend( xSocketPassingQueue, &xSocket, portMAX_DELAY );
			configASSERT( lReturned == pdPASS );

			while( ulTxCount < ulNumTxPerSocket )
			{
				lTransmitted = 0;

				/* Keep sending until the entire buffer has been sent. */
				while( lTransmitted < lStringLength )
				{
					/* How many bytes are left to send?  Attempt to send them
					all at once (so the length is potentially greater than the
					MSS). */
					xLenToSend = lStringLength - lTransmitted;

					lReturned = FreeRTOS_send(	xSocket,	/* The socket being sent to. */
												( void * ) &( cTransmittedString[ lTransmitted ] ),	/* The data being sent. */
												xLenToSend, /* The length of the data being sent. */
												0 );		/* ulFlags. */

					if( lReturned >= 0 )
					{
						/* Data was sent successfully. */
						lTransmitted += lReturned;
					}
					else
					{
						/* Error - close the socket. */
						break;
					}
				}

				if( lReturned < 0 )
				{
					/* The data was not sent for some reason - close the
					socket. */
					break;
				}
				else
				{
					/* Keep a count of how many echo requests have been transmitted
					so it can be compared to the number of echo replies received.
					It would be expected to loose at least one to an ARP message
					the	first time the connection is created. */
					ulTxTaskCycles++;

					/* Increment the number of times the message has been sent
					to this socket - after so many cycles the socket will be
					closed and a new one opened. */
					ulTxCount++;
				}
			}

			/* Wait until all Tx data has left the buffer. */
			xTimeEnteringLoop = xTaskGetTickCount();
			while( ( FreeRTOS_tx_size( xSocket ) > 0 ) && ( FreeRTOS_issocketconnected( xSocket ) == pdTRUE ) )
			{
				vTaskDelay( xTxEmptyDelay );

				if( ( xTaskGetTickCount() - xTimeEnteringLoop ) > xSendTimeOut )
				{
					/* Give up waiting. */
					break;
				}
			}

			/* Inform the other task that is using the same socket that this
			task is waiting to shut the socket. */
			lShuttingDown = pdTRUE;

			/* Wait for the Rx task to recognise the socket is closing and stop
			using it.  NOTE:  This should really have a time out but for simplicity
			of demonstration the time out is omitted. */
			xEventGroupSync( 	xSyncEventGroup, /* The event group used for the rendezvous. */
								echoTX_TASK_BIT, /* The bit representing the Tx task reaching the rendezvous. */
								( echoTX_TASK_BIT | echoRX_TASK_BIT ), /* Also wait for the Rx task. */
								portMAX_DELAY ); /* See comment above about lack of time out. */
			lShuttingDown = pdFALSE;

			xTimeEnteringLoop = xTaskGetTickCount();

			/* Initiate graceful shut down. */
			FreeRTOS_shutdown( xSocket, FREERTOS_SHUT_RDWR );

			/* Wait for the receive calls to return an error - indicating that
			the	socket is no longer connected. */
			xTimeEnteringLoop = xTaskGetTickCount();
			do
			{
				lReturned = FreeRTOS_recv( xSocket,	/* The socket being received from. */
					&ulJunk,					/* The buffer into which the received data will be written. */
					sizeof( ulJunk ),			/* The size of the buffer provided to receive the data. */
					0 );

				if( lReturned < 0 )
				{
					break;
				}

			} while( ( xTaskGetTickCount() - xTimeEnteringLoop ) < ( xReceiveTimeOut * 2 ) );
		}

		/* The Rx task is no longer using the socket so the socket can be
		closed. */
		FreeRTOS_closesocket( xSocket );

		/* Pause for a short while to ensure the network is not too
		congested. */
		vTaskDelay( echoLOOP_DELAY );
	}
}
/*-----------------------------------------------------------*/

static void prvEchoClientRxTask( void *pvParameters )
{
Socket_t xSocket;
static char cReceivedString[ ipconfigTCP_MSS ], cExpectedString[ ipconfigTCP_MSS ];
BaseType_t lReceived, lReturned = 0, lExpectedCharacter;

	( void ) pvParameters;

	for( ;; )
	{
		lExpectedCharacter = 0;

		/* Wait to receive the socket that will be used from the Tx task. */
		xQueueReceive( xSocketPassingQueue, &xSocket, portMAX_DELAY );

		for( ;; )
		{
			/* Clear down the Rx buffer. */
			memset( ( void * ) cReceivedString, 0x00, ipconfigTCP_MSS );

			/* Fill the buffer that contains the expected string with the next
			expected value. */
			memset( ( void * ) cExpectedString, ( int32_t ) '0' + lExpectedCharacter, ipconfigTCP_MSS );
			lExpectedCharacter++;

			if( lExpectedCharacter >= echoLARGE_BUFFER_SIZE_MULTIPLIER )
			{
				lExpectedCharacter = 0;
			}

			/* Nothing received yet. */
			lReceived = 0;

			/* Receive MSS bytes at a time as the data changes each MSS size. */
			while( lReceived < ipconfigTCP_MSS )
			{
				lReturned = FreeRTOS_recv( xSocket, &( cReceivedString[ lReceived ] ), ipconfigTCP_MSS - lReceived, 0 );

				if( ( lReturned == 0 ) && ( lShuttingDown == pdTRUE ) )
				{
					/* No bytes received but the Tx task is waiting to shut the
					socket.  Set lReturned to a negative number so the logic
					below breaks out of the loop. */
					lReturned = -1;
					break;
				}
				else if( lReturned >= 0 )
				{
					/* Data was received. */
					lReceived += lReturned;
				}
				else
				{
					/* Error.  The socket has probably been shut down already by
					the	Tx task, but try again just in case not. */
					break;
				}
			}

			if( lReturned < 0 )
			{
				/* Socket is probably being shut down. */
				break;
			}
			else
			{
				/* Check the string actually received matches the string
				expected. */
				configASSERT( memcmp( ( void * ) cReceivedString, ( void * ) cExpectedString, ipconfigTCP_MSS ) == 0 );
				ulRxTaskCycles++;
			}
		}

		/* Rendezvous with the Tx task ready to start a new cycle with a
		different socket. NOTE:  This should really have a time out but for
		simplicity of demonstration the time out is omitted. */
		xEventGroupSync( 	xSyncEventGroup, /* The event group used for the rendezvous. */
							echoRX_TASK_BIT, /* The bit representing the Rx task reaching the rendezvous. */
							( echoTX_TASK_BIT | echoRX_TASK_BIT ), /* Also wait for the Tx task. */
							portMAX_DELAY ); /* See comment above about lack of time out. */
	}
}
/*-----------------------------------------------------------*/

BaseType_t xAreSeparateTaskTCPEchoClientsStillRunning( void )
{
static uint32_t ulLastTxTaskCycles = 0, ulLastRxTaskCycles = 0;
BaseType_t xReturn = pdPASS;

	if( ulTxTaskCycles == ulLastTxTaskCycles )
	{
		xReturn = pdFAIL;
	}
	else
	{
		ulLastTxTaskCycles = ulTxTaskCycles;
	}

	if( ulRxTaskCycles == ulLastRxTaskCycles )
	{
		xReturn = pdFAIL;
	}
	else
	{
		ulLastRxTaskCycles = ulRxTaskCycles;
	}

	return xReturn;
}

#endif /* ipconfigUSE_TCP */

