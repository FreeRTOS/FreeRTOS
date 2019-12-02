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
 * A set of tasks are created that send TCP echo requests to the standard echo
 * port (port 7) on the IP address set by the configECHO_SERVER_ADDR0 to
 * configECHO_SERVER_ADDR3 constants, then wait for and verify the reply
 * (another demo is available that demonstrates the reception being performed in
 * a task other than that from with the request was made).
 *
 * See the following web page for essential demo usage and configuration
 * details:
 * http://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_Echo_Clients.html
 */

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"

/* Exclude the whole file if FreeRTOSIPConfig.h is configured to use UDP only. */
#if( ipconfigUSE_TCP == 1 )

/* The echo tasks create a socket, send out a number of echo requests, listen
for the echo reply, then close the socket again before starting over.  This
delay is used between each iteration to ensure the network does not get too
congested. */
#define echoLOOP_DELAY	( ( TickType_t ) 150 / portTICK_PERIOD_MS )

/* The echo server is assumed to be on port 7, which is the standard echo
protocol port. */
#ifndef configTCP_ECHO_CLIENT_PORT
	#define echoECHO_PORT	( 7 )
#else
	#define echoECHO_PORT	( configTCP_ECHO_CLIENT_PORT )
#endif

/* The size of the buffers is a multiple of the MSS - the length of the data
sent is a pseudo random size between 20 and echoBUFFER_SIZES. */
#define echoBUFFER_SIZE_MULTIPLIER	( 2 )
#define echoBUFFER_SIZES			( ipconfigTCP_MSS * echoBUFFER_SIZE_MULTIPLIER )

/* The number of instances of the echo client task to create. */
#define echoNUM_ECHO_CLIENTS		( 1 )

/* If ipconfigUSE_TCP_WIN is 1 then the Tx socket will use a buffer size set by
ipconfigTCP_TX_BUFFER_LENGTH, and the Tx window size will be
configECHO_CLIENT_TX_WINDOW_SIZE times the buffer size.  Note
ipconfigTCP_TX_BUFFER_LENGTH is set in FreeRTOSIPConfig.h as it is a standard TCP/IP
stack constant, whereas configECHO_CLIENT_TX_WINDOW_SIZE is set in
FreeRTOSConfig.h as it is a demo application constant. */
#ifndef configECHO_CLIENT_TX_WINDOW_SIZE
	#define configECHO_CLIENT_TX_WINDOW_SIZE	2
#endif

/* If ipconfigUSE_TCP_WIN is 1 then the Rx socket will use a buffer size set by
ipconfigTCP_RX_BUFFER_LENGTH, and the Rx window size will be
configECHO_CLIENT_RX_WINDOW_SIZE times the buffer size.  Note
ipconfigTCP_RX_BUFFER_LENGTH is set in FreeRTOSIPConfig.h as it is a standard TCP/IP
stack constant, whereas configECHO_CLIENT_RX_WINDOW_SIZE is set in
FreeRTOSConfig.h as it is a demo application constant. */
#ifndef configECHO_CLIENT_RX_WINDOW_SIZE
	#define configECHO_CLIENT_RX_WINDOW_SIZE	2
#endif

/*-----------------------------------------------------------*/

/*
 * Uses a socket to send data to, then receive data from, the standard echo
 * port number 7.
 */
static void prvEchoClientTask( void *pvParameters );

/*
 * Creates a pseudo random sized buffer of data to send to the echo server.
 */
static BaseType_t prvCreateTxData( char *ucBuffer, uint32_t ulBufferLength );

/*-----------------------------------------------------------*/

/* Rx and Tx time outs are used to ensure the sockets do not wait too long for
missing data. */
static const TickType_t xReceiveTimeOut = pdMS_TO_TICKS( 4000 );
static const TickType_t xSendTimeOut = pdMS_TO_TICKS( 2000 );

/* Counters for each created task - for inspection only. */
static uint32_t ulTxRxCycles[ echoNUM_ECHO_CLIENTS ]  = { 0 },
				ulTxRxFailures[ echoNUM_ECHO_CLIENTS ] = { 0 },
				ulConnections[ echoNUM_ECHO_CLIENTS ] = { 0 };

/* Rx and Tx buffers for each created task. */
static char cTxBuffers[ echoNUM_ECHO_CLIENTS ][ echoBUFFER_SIZES ],
			cRxBuffers[ echoNUM_ECHO_CLIENTS ][ echoBUFFER_SIZES ];

/*-----------------------------------------------------------*/

void vStartTCPEchoClientTasks_SingleTasks( uint16_t usTaskStackSize, UBaseType_t uxTaskPriority )
{
BaseType_t x;

	/* Create the echo client tasks. */
	for( x = 0; x < echoNUM_ECHO_CLIENTS; x++ )
	{
		xTaskCreate( 	prvEchoClientTask,	/* The function that implements the task. */
						"Echo0",			/* Just a text name for the task to aid debugging. */
						usTaskStackSize,	/* The stack size is defined in FreeRTOSIPConfig.h. */
						( void * ) x,		/* The task parameter, not used in this case. */
						uxTaskPriority,		/* The priority assigned to the task is defined in FreeRTOSConfig.h. */
						NULL );				/* The task handle is not used. */
	}
}
/*-----------------------------------------------------------*/

static void prvEchoClientTask( void *pvParameters )
{
Socket_t xSocket;
struct freertos_sockaddr xEchoServerAddress;
int32_t lLoopCount = 0UL;
const int32_t lMaxLoopCount = 1;
volatile uint32_t ulTxCount = 0UL;
BaseType_t xReceivedBytes, xReturned, xInstance;
BaseType_t lTransmitted, lStringLength;
char *pcTransmittedString, *pcReceivedString;
TickType_t xTimeOnEntering;

	#if( ipconfigUSE_TCP_WIN == 1 )

	WinProperties_t xWinProps;

		/* Fill in the buffer and window sizes that will be used by the socket. */
		xWinProps.lTxBufSize = ipconfigTCP_TX_BUFFER_LENGTH;
		xWinProps.lTxWinSize = configECHO_CLIENT_TX_WINDOW_SIZE;
		xWinProps.lRxBufSize = ipconfigTCP_RX_BUFFER_LENGTH;
		xWinProps.lRxWinSize = configECHO_CLIENT_RX_WINDOW_SIZE;

	#endif /* ipconfigUSE_TCP_WIN */

	/* This task can be created a number of times.  Each instance is numbered
	to enable each instance to use a different Rx and Tx buffer.  The number is
	passed in as the task's parameter. */
	xInstance = ( BaseType_t ) pvParameters;

	/* Point to the buffers to be used by this instance of this task. */
	pcTransmittedString = &( cTxBuffers[ xInstance ][ 0 ] );
	pcReceivedString = &( cRxBuffers[ xInstance ][ 0 ] );

	/* Echo requests are sent to the echo server.  The address of the echo
	server is configured by the constants configECHO_SERVER_ADDR0 to
	configECHO_SERVER_ADDR3 in FreeRTOSConfig.h. */
	xEchoServerAddress.sin_port = FreeRTOS_htons( echoECHO_PORT );
	xEchoServerAddress.sin_addr = FreeRTOS_inet_addr_quick( configECHO_SERVER_ADDR0,
															configECHO_SERVER_ADDR1,
															configECHO_SERVER_ADDR2,
															configECHO_SERVER_ADDR3 );

	for( ;; )
	{
		/* Create a TCP socket. */
		xSocket = FreeRTOS_socket( FREERTOS_AF_INET, FREERTOS_SOCK_STREAM, FREERTOS_IPPROTO_TCP );
		configASSERT( xSocket != FREERTOS_INVALID_SOCKET );

		/* Set a time out so a missing reply does not cause the task to block
		indefinitely. */
		FreeRTOS_setsockopt( xSocket, 0, FREERTOS_SO_RCVTIMEO, &xReceiveTimeOut, sizeof( xReceiveTimeOut ) );
		FreeRTOS_setsockopt( xSocket, 0, FREERTOS_SO_SNDTIMEO, &xSendTimeOut, sizeof( xSendTimeOut ) );

		#if( ipconfigUSE_TCP_WIN == 1 )
		{
			/* Set the window and buffer sizes. */
			FreeRTOS_setsockopt( xSocket, 0, FREERTOS_SO_WIN_PROPERTIES, ( void * ) &xWinProps,	sizeof( xWinProps ) );
		}
		#endif /* ipconfigUSE_TCP_WIN */

		/* Connect to the echo server. */
		if( FreeRTOS_connect( xSocket, &xEchoServerAddress, sizeof( xEchoServerAddress ) ) == 0 )
		{
			ulConnections[ xInstance ]++;

			/* Send a number of echo requests. */
			for( lLoopCount = 0; lLoopCount < lMaxLoopCount; lLoopCount++ )
			{
				/* Create the string that is sent to the echo server. */
				lStringLength = prvCreateTxData( pcTransmittedString, echoBUFFER_SIZES );

				/* Add in some unique text at the front of the string. */
				sprintf( pcTransmittedString, "TxRx message number %u", ( unsigned ) ulTxCount );
				ulTxCount++;

				/* Send the string to the socket. */
				lTransmitted = FreeRTOS_send(	xSocket,						/* The socket being sent to. */
												( void * ) pcTransmittedString,	/* The data being sent. */
												lStringLength,					/* The length of the data being sent. */
												0 );							/* No flags. */

				if( lTransmitted < 0 )
				{
					/* Error? */
					break;
				}

				/* Clear the buffer into which the echoed string will be
				placed. */
				memset( ( void * ) pcReceivedString, 0x00, echoBUFFER_SIZES );
				xReceivedBytes = 0;

				/* Receive data echoed back to the socket. */
				while( xReceivedBytes < lTransmitted )
				{
					xReturned = FreeRTOS_recv( xSocket,								/* The socket being received from. */
											&( pcReceivedString[ xReceivedBytes ] ),/* The buffer into which the received data will be written. */
											 lStringLength - xReceivedBytes,		/* The size of the buffer provided to receive the data. */
											 0 );									/* No flags. */

					if( xReturned < 0 )
					{
						/* Error occurred.  Latch it so it can be detected
						below. */
						xReceivedBytes = xReturned;
						break;
					}
					else if( xReturned == 0 )
					{
						/* Timed out. */
						break;
					}
					else
					{
						/* Keep a count of the bytes received so far. */
						xReceivedBytes += xReturned;
					}
				}

				/* If an error occurred it will be latched in xReceivedBytes,
				otherwise xReceived bytes will be just that - the number of
				bytes received from the echo server. */
				if( xReceivedBytes > 0 )
				{
					/* Compare the transmitted string to the received string. */
					configASSERT( strncmp( pcReceivedString, pcTransmittedString, lTransmitted ) == 0 );
					if( strncmp( pcReceivedString, pcTransmittedString, lTransmitted ) == 0 )
					{
						/* The echo reply was received without error. */
						ulTxRxCycles[ xInstance ]++;
					}
					else
					{
						/* The received string did not match the transmitted
						string. */
						ulTxRxFailures[ xInstance ]++;
						break;
					}
				}
				else if( xReceivedBytes < 0 )
				{
					/* FreeRTOS_recv() returned an error. */
					break;
				}
				else
				{
					/* Timed out without receiving anything? */
					break;
				}
			}

			/* Finished using the connected socket, initiate a graceful close:
			FIN, FIN+ACK, ACK. */
			FreeRTOS_shutdown( xSocket, FREERTOS_SHUT_RDWR );

			/* Expect FreeRTOS_recv() to return an error once the shutdown is
			complete. */
			xTimeOnEntering = xTaskGetTickCount();
			do
			{
				xReturned = FreeRTOS_recv( xSocket,	/* The socket being received from. */
					&( pcReceivedString[ 0 ] ),		/* The buffer into which the received data will be written. */
					echoBUFFER_SIZES,				/* The size of the buffer provided to receive the data. */
					0 );

				if( xReturned < 0 )
				{
					break;
				}

			} while( ( xTaskGetTickCount() - xTimeOnEntering ) < xReceiveTimeOut );
		}

		/* Close this socket before looping back to create another. */
		FreeRTOS_closesocket( xSocket );

		/* Pause for a short while to ensure the network is not too
		congested. */
		vTaskDelay( echoLOOP_DELAY );
	}
}
/*-----------------------------------------------------------*/

static BaseType_t prvCreateTxData( char *cBuffer, uint32_t ulBufferLength )
{
BaseType_t lCharactersToAdd, lCharacter;
char cChar = '0';
const BaseType_t lMinimumLength = 60;

	/* Randomise the number of characters that will be sent in the echo
	request. */
	do
	{
		lCharactersToAdd = ipconfigRAND32() % ( ulBufferLength - 20UL );
	} while ( ( lCharactersToAdd == 0 ) || ( lCharactersToAdd < lMinimumLength ) ); /* Must be at least enough to add the unique text to the start of the string later. */

	/* Fill the buffer. */
	for( lCharacter = 0; lCharacter < lCharactersToAdd; lCharacter++ )
	{
		cBuffer[ lCharacter ] = cChar;
		cChar++;

		if( cChar > '~' )
		{
			cChar = '0';
		}
	}

	return lCharactersToAdd;
}
/*-----------------------------------------------------------*/

BaseType_t xAreSingleTaskTCPEchoClientsStillRunning( void )
{
static uint32_t ulLastEchoSocketCount[ echoNUM_ECHO_CLIENTS ] = { 0 }, ulLastConnections[ echoNUM_ECHO_CLIENTS ] = { 0 };
BaseType_t xReturn = pdPASS, x;

	/* Return fail is the number of cycles does not increment between
	consecutive calls. */
	for( x = 0; x < echoNUM_ECHO_CLIENTS; x++ )
	{
		if( ulTxRxCycles[ x ] == ulLastEchoSocketCount[ x ] )
		{
			xReturn = pdFAIL;
		}
		else
		{
			ulLastEchoSocketCount[ x ] = ulTxRxCycles[ x ];
		}

		if( ulConnections[ x ] == ulLastConnections[ x ] )
		{
			xReturn = pdFAIL;
		}
		else
		{
			ulConnections[ x ] = ulLastConnections[ x ];
		}
	}

	return xReturn;
}

#endif /* ipconfigUSE_TCP */

