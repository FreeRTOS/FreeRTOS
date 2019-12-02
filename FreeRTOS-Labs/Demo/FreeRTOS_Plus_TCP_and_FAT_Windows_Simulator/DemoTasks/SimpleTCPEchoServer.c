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
 * FreeRTOS tasks are used with FreeRTOS+TCP to create a TCP echo server.  Echo
 * clients are also created, but the echo clients use Windows threads (as
 * opposed to FreeRTOS tasks) and use the Windows TCP library (Winsocks).  This
 * creates a communication between the FreeRTOS+TCP TCP/IP stack and the Windows
 * TCP/IP stack.
 *
 * See the following web page for essential demo usage and configuration
 * details:
 * http://www.FreeRTOS.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/examples_FreeRTOS_simulator.html
 */

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>
#include <WinSock2.h>
#include <Mswsock.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"

/* Remove the whole file if FreeRTOSIPConfig.h is set to exclude TCP. */
#if( ipconfigUSE_TCP == 1 )

/* This example uses Winsocks clients to talk to a FreeRTOS+TCP server. */
#pragma comment( lib, "ws2_32.lib" )

/* The number of Winsock clients that communicate with the FreeRTOS+TCP
server. */
#define tcpechoNUMBER_OF_CLIENTS		1

/* Specifies the size of the data sent to the server in MSS units. */
#define tcpechoBUFFER_SIZE_MULTIPLIER	3

/* Delay between cycles so as not to flood the network. */
#define tcpechoLOOP_DELAY	( ( TickType_t ) 750 / portTICK_PERIOD_MS )

/* The maximum time to wait for a closing socket to close. */
#define tcpechoSHUTDOWN_DELAY	( pdMS_TO_TICKS( 5000 ) )

/* The time to wait between reads of a Winsock socket when shutting the socket
down. */
#define tcpechoWINSOCK_SHUTDOWN_DELAY	( 5 )

/* The standard echo port number. */
#define tcpechoPORT_NUMBER		7

/* The size of the Rx and Tx buffers. */
#define tcpechoBUFFER_SIZE ( ipconfigTCP_MSS * tcpechoBUFFER_SIZE_MULTIPLIER )

/*-----------------------------------------------------------*/

/*
 * Uses Winsocks from Windows threads to send data from the real IP and MAC
 * addresses to the IP and MAC addresses spoofed by FreeRTOS+TCP.  Multiple
 * instances of this task are created.
 */
DWORD WINAPI prvSimpleWinsockTCPClientTask( void *pvParameters );

/*
 * Uses FreeRTOS+TCP to listen for incoming echo connections, creating a task
 * to handle each connection.
 */
static void prvConnectionListeningTask( void *pvParameters );

/*
 * Created by the connection listening task to handle a single connection.
 */
static void prvServerConnectionInstance( void *pvParameters );

/*
 * Create a string to transmit of pseudo random length.
 */
static BaseType_t prvCreateTxData( char *cBuffer, uint32_t ulBufferLength );

/*
 * Create the Windows threads that use the Windows TCP/IP stack to talk to the
 * FreeRTOS task that is using the FreeRTOS+TCP TCP/IP stack.
 */
static void prvCreateWindowsThreadClients( void );

/*-----------------------------------------------------------*/

/* Stores the stack size passed into vStartSimpleTCPServerTasks() so it can be
reused when the server listening task creates tasks to handle connections. */
static uint16_t usUsedStackSize = 0;

/* Used for error reporting. */
static uint32_t ulConnectionCount = 0, ulClientCycles = 0, ulClientTransmitErrors = 0, ulIncorrectDataReceived;
static uint32_t ulClientSocketsClosedDuringReceive = 0, ulClientReceiveErrors = 0;

/* The buffers used to hold the string to Tx and the received string. */
static char cTxBuffers[ tcpechoNUMBER_OF_CLIENTS ][ tcpechoBUFFER_SIZE ], cRxBuffers[ tcpechoNUMBER_OF_CLIENTS ][ tcpechoBUFFER_SIZE ];

/*-----------------------------------------------------------*/

void vStartSimpleTCPServerTasks( uint16_t usStackSize, UBaseType_t uxPriority )
{
WORD wVersionRequested;
WSADATA xWSAData;

	/* The clients use Winsock sockets and must therefore run at the idle
	priority. */
	configASSERT( uxPriority == tskIDLE_PRIORITY );

	/* Create the TCP echo server.  The echo server uses FreeRTOS+TCP through
	the spoofed IP and MAC address.  The WinSock client tasks are created from
	inside the listening task. */
	xTaskCreate( prvConnectionListeningTask, "ServerListener", usStackSize, NULL, uxPriority + 1, NULL );

	/* Prepare to use WinSock library. */
	wVersionRequested = MAKEWORD( 2, 2 );
	configASSERT( WSAStartup( wVersionRequested, &xWSAData ) == ( WORD ) 0 );

	/* Remember the requested stack size so it can be re-used by the server
	listening task when it creates tasks to handle connections. */
	usUsedStackSize = usStackSize;
}
/*-----------------------------------------------------------*/

static void prvCreateWindowsThreadClients( void )
{
BaseType_t xClientTask;
HANDLE xWinHandle;

	/* Create a set of (Windows thread) clients, all of which talk to the same
	(FreeRTOS task) server.  The clients use Winsocks through the real IP and
	MAC address. */
	for( xClientTask = 0; xClientTask < tcpechoNUMBER_OF_CLIENTS; xClientTask++ )
	{
		xWinHandle = CreateThread(
			NULL,							/* Pointer to thread security attributes. */
			0,								/* Initial thread stack size, in bytes. */
			prvSimpleWinsockTCPClientTask,	/* Pointer to thread function. */
			( void * ) xClientTask,			/* Argument for new thread. */
			0,								/* Creation flags. */
			NULL );

		/* Set the priority and the cores used of the Windows threads such that
		they do no interfere with the FreeRTOS simulator. */
		SetThreadPriority( xWinHandle, THREAD_PRIORITY_IDLE );
		SetThreadPriorityBoost( xWinHandle, TRUE );
		SetThreadAffinityMask( xWinHandle, ~0x01u );
	}
}
/*-----------------------------------------------------------*/

static void prvConnectionListeningTask( void *pvParameters )
{
struct freertos_sockaddr xClient, xBindAddress;
Socket_t xListeningSocket, xConnectedSocket;
socklen_t xSize = sizeof( xClient );
static const TickType_t xReceiveTimeOut = portMAX_DELAY;
const BaseType_t xBacklog = 20;
WinProperties_t xWinProps;

	/* Just to prevent compiler warnings. */
	( void ) pvParameters;

	/* Attempt to open the socket. */
	xListeningSocket = FreeRTOS_socket( FREERTOS_AF_INET, FREERTOS_SOCK_STREAM, FREERTOS_IPPROTO_TCP );
	configASSERT( xListeningSocket != FREERTOS_INVALID_SOCKET );

	/* Set a time out so accept() will just wait for a connection. */
	FreeRTOS_setsockopt( xListeningSocket, 0, FREERTOS_SO_RCVTIMEO, &xReceiveTimeOut, sizeof( xReceiveTimeOut ) );

	/* Fill in the buffer and window sizes that will be used by the socket. */
	xWinProps.lTxBufSize = 6 * ipconfigTCP_MSS;
	xWinProps.lTxWinSize = 3;
	xWinProps.lRxBufSize = 6 * ipconfigTCP_MSS;
	xWinProps.lRxWinSize = 3;

	/* Set the window and buffer sizes. */
	FreeRTOS_setsockopt( xListeningSocket, 0, FREERTOS_SO_WIN_PROPERTIES, ( void * ) &xWinProps, sizeof( xWinProps ) );

	/* Bind the socket to the port that the client task will send to, then
	listen for incoming connections. */
	xBindAddress.sin_port = tcpechoPORT_NUMBER;
	xBindAddress.sin_port = FreeRTOS_htons( xBindAddress.sin_port );
	FreeRTOS_bind( xListeningSocket, &xBindAddress, sizeof( xBindAddress ) );
	FreeRTOS_listen( xListeningSocket, xBacklog );

	/* Create the clients that will connect to the listening socket. */
	prvCreateWindowsThreadClients();

	for( ;; )
	{
		/* Wait for a client to connect. */
		xConnectedSocket = FreeRTOS_accept( xListeningSocket, &xClient, &xSize );
		configASSERT( xConnectedSocket != FREERTOS_INVALID_SOCKET );

		/* Spawn a task to handle the connection. */
		xTaskCreate( prvServerConnectionInstance, "EchoServer", usUsedStackSize, ( void * ) xConnectedSocket, tskIDLE_PRIORITY, NULL );
	}
}
/*-----------------------------------------------------------*/

static void prvServerConnectionInstance( void *pvParameters )
{
int32_t lBytes, lSent, lTotalSent;
uint8_t cReceivedString[ ipconfigTCP_MSS ];
Socket_t xConnectedSocket;
static const TickType_t xReceiveTimeOut = pdMS_TO_TICKS( 5000 );
static const TickType_t xSendTimeOut = pdMS_TO_TICKS( 5000 );
TickType_t xTimeOnShutdown;

	ulConnectionCount++;
	xConnectedSocket = ( Socket_t ) pvParameters;
	FreeRTOS_setsockopt( xConnectedSocket, 0, FREERTOS_SO_RCVTIMEO, &xReceiveTimeOut, sizeof( xReceiveTimeOut ) );
	FreeRTOS_setsockopt( xConnectedSocket, 0, FREERTOS_SO_SNDTIMEO, &xSendTimeOut, sizeof( xReceiveTimeOut ) );

	for( ;; )
	{
		/* Zero out the receive array so there is NULL at the end of the string
		when it is printed out. */
		memset( cReceivedString, 0x00, sizeof( cReceivedString ) );

		/* Receive data on the socket. */
		lBytes = FreeRTOS_recv( xConnectedSocket, cReceivedString, sizeof( cReceivedString ), 0 );

		/* If data was received, echo it back. */
		if( lBytes >= 0 )
		{
			lSent = 0;
			lTotalSent = 0;

			/* Call send() until all the data has been sent. */
			while( ( lSent >= 0 ) && ( lTotalSent < lBytes ) )
			{
				lSent = FreeRTOS_send( xConnectedSocket, cReceivedString, lBytes - lTotalSent, 0 );
				lTotalSent += lSent;
			}

			if( lSent < 0 )
			{
				/* Socket closed? */
				break;
			}
		}
		else
		{
			/* Socket closed? */
			break;
		}
	}

	/* Initiate a shutdown in case it has not already been initiated. */
	FreeRTOS_shutdown( xConnectedSocket, FREERTOS_SHUT_RDWR );

	/* Wait for the shutdown to take effect, indicated by FreeRTOS_recv()
	returning an error. */
	xTimeOnShutdown = xTaskGetTickCount();
	do
	{
		if( FreeRTOS_recv( xConnectedSocket, cReceivedString, ipconfigTCP_MSS, 0 ) < 0 )
		{
			break;
		}
	} while( ( xTaskGetTickCount() - xTimeOnShutdown ) < tcpechoSHUTDOWN_DELAY );

	/* Finished with the socket and the task. */
	FreeRTOS_closesocket( xConnectedSocket );
	vTaskDelete( NULL );
}
/*-----------------------------------------------------------*/

static BaseType_t prvCreateTxData( char *cBuffer, uint32_t ulBufferLength )
{
BaseType_t lCharactersToAdd, lCharacter;
char cChar = '0';

	/* Randomise the number of characters that will be sent. */
	do
	{
		lCharactersToAdd = ipconfigRAND32() % ( ulBufferLength - 20UL );
	} while ( lCharactersToAdd == 0 );

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

BaseType_t xAreTCPEchoServersStillRunning( void )
{
static uint32_t ulLastConnectionCount = 0, ulLastClientCycles = 0;
BaseType_t xReturn = pdPASS;

	if( ulConnectionCount == ulLastConnectionCount )
	{
		xReturn = pdFAIL;
	}
	else
	{
		ulLastConnectionCount = ulConnectionCount;
	}

	if( ulClientCycles == ulLastClientCycles )
	{
		xReturn = pdFAIL;
	}
	else
	{
		ulLastClientCycles = ulClientCycles;
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

DWORD WINAPI prvSimpleWinsockTCPClientTask( void *pvParameters )
{
char *pcTransmittedString, *pcReceivedString;
BaseType_t lReceived, lTransmitted = 0, lStringLength, lReturned = 0, lInstance;
uint32_t ulCount = 0UL, ulMaxCount, ulIPAddress;
const uint32_t ulMaxLoopsPerSocket = 100UL;
struct sockaddr_in xConnection;
SOCKET xClientSocket;
int iReturned;
TickType_t xTimeOnShutdown;

	/* Multiple instances of this task are created.  The instance is passed in
	as the parameter. */
	lInstance = ( BaseType_t ) pvParameters;

	/* Locate the buffers for this instance of this task. */
	pcTransmittedString = &( cTxBuffers[ lInstance ][ 0 ] );
	pcReceivedString = &( cRxBuffers[ lInstance ][ 0 ] );

	/* It is assumed that this task is not created until the network is up,
	so the IP address of the server (which is the FreeRTOS+TCP side of the
	connection) can be obtained immediately.  Store the IP address being
	used in ulIPAddress. */
	FreeRTOS_GetAddressConfiguration( &ulIPAddress, NULL, NULL, NULL );

	/* Set family and port for client socket. */
	memset( ( void * ) &xConnection, 0x00, sizeof( struct sockaddr_in ) );
	xConnection.sin_family = AF_INET;
	xConnection.sin_addr.s_addr = ulIPAddress;
	xConnection.sin_port = htons( tcpechoPORT_NUMBER );

	for( ;; )
	{
		/* Create the socket then connect it to the FreeRTOS+TCP server. */
		xClientSocket = socket( AF_INET, SOCK_STREAM, 0 );
		configASSERT( xClientSocket != INVALID_SOCKET );

		do
		{
			iReturned = connect( xClientSocket, (const struct sockaddr*) &xConnection, sizeof( xConnection ) );
		} while( iReturned != 0 );

		ulMaxCount = ipconfigRAND32() % ulMaxLoopsPerSocket;

		for( ulCount = 0; ulCount < ulMaxCount; ulCount++ )
		{
			/* Create a string then send it to the server. */
			lStringLength = prvCreateTxData( pcTransmittedString, tcpechoBUFFER_SIZE );
			lTransmitted = send( xClientSocket, pcTransmittedString, lStringLength, 0 );

			configASSERT( lTransmitted != SOCKET_ERROR );
			configASSERT( lTransmitted == lStringLength );

			if( lTransmitted == lStringLength )
			{
				memset( ( void * ) pcReceivedString, 0x00, tcpechoBUFFER_SIZE );
				lReceived = 0;

				/* Wait for the echoed string. */
				while( lReceived < lTransmitted )
				{
					lReturned = recv( xClientSocket, ( char * ) &( pcReceivedString[ lReceived ] ), lTransmitted - lReceived, 0 );

					if( lReturned >= 0 )
					{
						/* Data was received. */
						lReceived += lReturned;
					}
					else
					{
						/* Error was returned. */
						ulClientReceiveErrors++;
						break;
					}
				}

				/* If the socket was not closed, check the number of bytes
				received. */
				if( lReceived == lTransmitted )
				{
					/* Were the expected characters received? */
					configASSERT( memcmp( pcTransmittedString, pcReceivedString, lTransmitted ) == 0x00 );
					if( memcmp( pcTransmittedString, pcReceivedString, lReceived ) != 0x00 )
					{
						ulIncorrectDataReceived++;
						break;
					}
					else
					{
						/* Received expected string, increment the count of
						successful cycles. */
						ulClientCycles++;
					}
				}
				else
				{
					/* Socket is being closed or an error occurred.  Don't try
					using the same socket again. */
					break;
				}
			}
			else
			{
				ulClientTransmitErrors++;
				break;
			}
		}

		shutdown( xClientSocket, SD_BOTH );
		xTimeOnShutdown = xTaskGetTickCount();

		do
		{
			Sleep( tcpechoWINSOCK_SHUTDOWN_DELAY );
			lReturned = recv( xClientSocket, pcReceivedString, lTransmitted, 0 );

			if( lReturned < 0 )
			{
				break;
			}
		} while( ( xTaskGetTickCount() - xTimeOnShutdown ) < tcpechoSHUTDOWN_DELAY );

		configASSERT( closesocket( xClientSocket ) == 0 );

		Sleep( tcpechoLOOP_DELAY );
	}
}
/*-----------------------------------------------------------*/

/* The whole file is excluded if TCP is not compiled in. */
#endif /* ipconfigUSE_TCP */

