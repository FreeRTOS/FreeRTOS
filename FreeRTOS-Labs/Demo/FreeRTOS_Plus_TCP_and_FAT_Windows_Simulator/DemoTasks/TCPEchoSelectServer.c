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
#include "FreeRTOS_char_buf.h"

#include "SimpleTCPEchoServer.h"	/* For prvSimpleTcpServerClientTask */


#define tcpechoNUMBER_OF_CLIENTS		0

void tcpWinShowEvent( BaseType_t aDoLog );

/*
 * Listens for incoming echo connections.  Creates a task to handle each
 * connection.
 */
static void prvConnectionListeningTask( void *pvParameters );

/* Stores the stack size passed into vStartSimpleTCPServerTasks() so it can be
reused when the server listening task creates tasks to handle connections. */
static unsigned short usUsedStackSize = 0;

/*-----------------------------------------------------------*/

void vStartSelectTCPServerTasks( uint16_t usStackSize, uint32_t ulPort, UBaseType_t uxPriority )
{
WORD wVersionRequested;
WSADATA xWSAData;
BaseType_t xClient;
//extern void prvSimpleTCPClientTask( void *pvParameters );

	/* The clients use non-blocking Winsock sockets and must therefore run at
	the idle priority. */
	configASSERT( uxPriority == tskIDLE_PRIORITY );

	/* Create the TCP echo server.  The echo server uses FreeRTOS+TCP through
	the spoofed IP and MAC address. */
	xTaskCreate( prvConnectionListeningTask, "ServerListener", usStackSize, ( void * ) ulPort, uxPriority + 1, NULL );

	/* Prepare to use WinSock library. */
	wVersionRequested = MAKEWORD( 2, 2 );
	configASSERT( WSAStartup( wVersionRequested, &xWSAData ) == ( WORD ) 0 );

	/* Remember the requested stack size so it can be re-used by the server
	listening task when it creates tasks to handle connections. */
	usUsedStackSize = usStackSize;
}

#define SEND_BUFFER_SIZE	( 8 * ipconfigTCP_MSS )

typedef struct xTCP_SERVER {
	Socket_t xSocket;
	struct xTCP_SERVER *pxNext;
	SSimpleBuf *pxSendData;
	BaseType_t bHasSendRequest;
} TCPServer_t;

static uint8_t cReceivedString[ ipconfigTCP_MSS ];

static void prvTcpInit( TCPServer_t *pxTcpServer )
{
struct freertos_sockaddr addr;
BaseType_t xReceiveTimeOut = 0;
BaseType_t xSendTimeOut = 0;

	pxTcpServer->pxSendData = ( SSimpleBuf * )pvPortMalloc( sizeof( *pxTcpServer->pxSendData ) - sizeof( pxTcpServer->pxSendData->array ) + SEND_BUFFER_SIZE + 1 );

	configASSERT( pxTcpServer->pxSendData != NULL );
	memset( pxTcpServer->pxSendData, '\0', sizeof( *pxTcpServer->pxSendData ) );
	pxTcpServer->pxSendData->LENGTH = SEND_BUFFER_SIZE + 1;

	FreeRTOS_GetRemoteAddress( pxTcpServer->xSocket, &addr );
	FreeRTOS_debug_printf( ( "prvTcpInit: serving %xip:%u\n",
		FreeRTOS_ntohl( addr.sin_addr ), addr.sin_port) );

	FreeRTOS_setsockopt( pxTcpServer->xSocket, 0, FREERTOS_SO_RCVTIMEO, &xReceiveTimeOut, sizeof( xReceiveTimeOut ) );
	FreeRTOS_setsockopt( pxTcpServer->xSocket, 0, FREERTOS_SO_SNDTIMEO, &xSendTimeOut, sizeof( xReceiveTimeOut ) );
}

static void prvTcpClose( TCPServer_t *pxThisServer )
{
	FreeRTOS_closesocket( pxThisServer->xSocket );
	vPortFree( pxThisServer->pxSendData );
	vPortFree( pxThisServer );
}

static BaseType_t prvTcpSend( TCPServer_t *pxTcpServer )
{
BaseType_t lBytes, lReturned, xReturn = 0;

	lBytes = sbGet( pxTcpServer->pxSendData, 0, cReceivedString, sizeof( cReceivedString ), pdTRUE );
	if( lBytes )
	{
		/* Send as much as possible, non-blocking */
		lReturned = FreeRTOS_send( pxTcpServer->xSocket, cReceivedString, lBytes, 0 );
		if( lReturned > 0 )
		{
			xReturn = sbGet( pxTcpServer->pxSendData, 0, NULL, lReturned, pdFALSE );
		}
	}
	return xReturn;
}

static BaseType_t prvTcpHasSendData( TCPServer_t *pxTcpServer )
{
	return ( sbGetSize( pxTcpServer->pxSendData ) > 0 ) ? 1 : 0;
}

static BaseType_t prvTcpWork( TCPServer_t *pxTcpServer )
{
BaseType_t lBytes, lReturned, lMayWrite;

	lMayWrite = FreeRTOS_maywrite( pxTcpServer->xSocket );
	if( lMayWrite < 0 )
		return lMayWrite;
	while( lMayWrite > 0 )
	{
		lReturned = prvTcpSend( pxTcpServer );
		if( lReturned < 0 )
			return lReturned;
		if( lReturned == 0 )
			break;
		lMayWrite = FreeRTOS_maywrite( pxTcpServer->xSocket );
		if( lMayWrite < 0 )
			return lMayWrite;
	}
	for( ; ; )
	{
		/* Zero out the receive array so there is NULL at the end of the string
		when it is printed out. */
		memset( cReceivedString, 0x00, sizeof( cReceivedString ) );

		/* Receive data on the socket. */
		lBytes = FreeRTOS_recv( pxTcpServer->xSocket, cReceivedString, sizeof( cReceivedString ), 0 );
		if( lBytes <= 0 )
				return lBytes;
		/* Return the received characters. */
		if( lMayWrite > 0 && sbGetSize( pxTcpServer->pxSendData ) == 0 )
		{
			/* The cirular buffer is empty, send the received data directly */
			lReturned = FreeRTOS_send( pxTcpServer->xSocket, cReceivedString, lBytes, 0 );
			if( lReturned < 0 )
			{
				return -1;
			}
			if( lBytes > lReturned )
			{
				/* Not all dta could be delivered, save them for later
					* FD_SET( eSELECT_WRITE ) will be called */
				sbAdd( pxTcpServer->pxSendData, 0, cReceivedString + lReturned, lBytes - lReturned );
			}
			lMayWrite = FreeRTOS_maywrite( pxTcpServer->xSocket );
			if( lMayWrite < 0 )
				return lMayWrite;
		} else
		{
			sbAdd( pxTcpServer->pxSendData, 0, cReceivedString, lBytes );
		}
	}
}

static TickType_t lastTickTime;
static BaseType_t xTaskCount = 0, xConfirmedCount = 0;
static void prvConnectionListeningTask( void *pvParameters )
{
struct freertos_sockaddr xClient, xBindAddress;
Socket_t xListeningSocket;

socklen_t xSize = sizeof( xClient );
static const TickType_t xReceiveTimeOut = 0; //portMAX_DELAY;
const BaseType_t xBacklog = 10;
SocketSet_t xSocketSet;
struct xTCP_SERVER *pxServerList = NULL;
struct xTCP_SERVER *pxIterator;

WinProperties_t winProps;

	/* Just to prevent compiler warnings. */
	( void ) pvParameters;

	/* Attempt to open the socket. */
	xListeningSocket = FreeRTOS_socket( PF_INET, SOCK_STREAM, IPPROTO_TCP );
	configASSERT( xListeningSocket != FREERTOS_INVALID_SOCKET );

	/* Set a time out so accept() will just wait for a connection. */
	FreeRTOS_setsockopt( xListeningSocket, 0, FREERTOS_SO_RCVTIMEO, &xReceiveTimeOut, sizeof( xReceiveTimeOut ) );

	memset(&winProps, '\0', sizeof( winProps ) );
	// Size in units of MSS
	winProps.lTxBufSize   = 1 * 1460;//1000;
	winProps.lTxWinSize   = 2;

	winProps.lRxBufSize   = 2 * 1460;
	winProps.lRxWinSize   =  2;

	FreeRTOS_setsockopt( xListeningSocket, 0, FREERTOS_SO_WIN_PROPERTIES, ( void * ) &winProps, sizeof( winProps ) );

	/* The strange casting is to remove compiler errors. */
	xBindAddress.sin_port = ( uint16_t ) ( ( uint32_t ) pvParameters ) & 0xffffUL;
	xBindAddress.sin_port = FreeRTOS_htons( xBindAddress.sin_port );

	/* Bind the socket to the port that the client task will send to, then
	listen for incoming connections. */
	while( FreeRTOS_bind( xListeningSocket, &xBindAddress, sizeof( xBindAddress ) ) != 0 );
	FreeRTOS_listen( xListeningSocket, xBacklog );
	lastTickTime = xTaskGetTickCount ();

	pxServerList = NULL;

	xSocketSet = FreeRTOS_createsocketset( );
	configASSERT( xSocketSet != NULL );
	FreeRTOS_FD_SET( xListeningSocket, xSocketSet, eSELECT_READ );

	for( ;; )
	{
		TickType_t xMask = FreeRTOS_select( xSocketSet, 3000 );

		if( FreeRTOS_FD_ISSET( xListeningSocket, xSocketSet ) )
		{
			Socket_t xNewSocket;

			xNewSocket = FreeRTOS_accept( xListeningSocket, &xClient, &xSize );
			if ( xNewSocket && xNewSocket != FREERTOS_INVALID_SOCKET )
			{
				TCPServer_t *pxServer;

				FreeRTOS_debug_printf( ( "prvConnectionListeningTask: new connection %xip:%u\n",
					FreeRTOS_ntohl( xClient.sin_addr ), FreeRTOS_ntohs( xClient.sin_port ) ) );

				pxServer = (TCPServer_t *)pvPortMalloc( sizeof( *pxServer ) );
				memset( pxServer, '\0', sizeof( *pxServer ));

				pxServer->xSocket = xNewSocket;
				FreeRTOS_FD_SET( xNewSocket, xSocketSet, eSELECT_READ | eSELECT_EXCEPT );
				if( pxServerList == NULL )
				{
					/* This is the first server */
					pxServerList = pxServer;
				}
				else
				{
					/* Attach it to the end of the list */
					for( pxIterator = pxServerList; pxIterator->pxNext != NULL; pxIterator = pxIterator->pxNext )
					{
					}
					pxIterator->pxNext = pxServer;
				}
				prvTcpInit( pxServer );
			}
		}
		{
			TCPServer_t *pxThisServer = NULL;

			for( pxIterator = pxServerList; pxIterator != NULL;  )
			{
				BaseType_t rc;
				pxThisServer = pxIterator;
				/* Move to the next one before the current gets deleted */
				pxIterator = pxIterator->pxNext;

				if( FreeRTOS_FD_ISSET( pxThisServer->xSocket, xSocketSet )  == 0 )
				{
					continue;
				}

				rc = prvTcpWork( pxThisServer );

				if( rc < 0)
				{
					FreeRTOS_FD_CLR( pxThisServer->xSocket, xSocketSet, eSELECT_ALL );

					if( pxServerList = pxThisServer )
					{
						pxServerList = pxThisServer->pxNext;
					}
					else
					{
						struct xTCP_SERVER *pxOther;
						for( pxOther = pxServerList; pxOther->pxNext != NULL; pxOther = pxOther->pxNext )
						{
							if( pxOther->pxNext == pxThisServer )
							{
								pxOther->pxNext == pxThisServer->pxNext;
								break;
							}
						}
					}
					/* Close the socket and free the space */
					prvTcpClose( pxThisServer );
				} else
				{
					pxThisServer->bHasSendRequest = prvTcpHasSendData( pxThisServer );
					if( pxThisServer->bHasSendRequest )
						FreeRTOS_FD_SET( pxThisServer->xSocket, xSocketSet, eSELECT_WRITE );
					else
						FreeRTOS_FD_CLR( pxThisServer->xSocket, xSocketSet, eSELECT_WRITE );
					//FreeRTOS_debug_printf( ( "SET_FD WRITE %d\n", pxServerFound->bHasSendRequest != 0 ) );
				}
			}
		}
		if( ( xTaskGetTickCount () - lastTickTime ) > 30000 )
		{
			lastTickTime = xTaskGetTickCount ();
			//plusPrintf( "ListeningTask %ld,%ld tasks\n", xTaskCount, xConfirmedCount );
		}
	}
}
/*-----------------------------------------------------------*/

static BaseType_t prvCreateTxData( uint8_t *ucBuffer, uint32_t ulBufferLength )
{
BaseType_t lCharactersToAdd, lCharacter;
uint8_t ucChar = '0';

	/* Randomise the number of characters that will be sent. */
	do
	{
		lCharactersToAdd = ipconfigRAND32() % ( ulBufferLength - 20UL );
	} while ( lCharactersToAdd == 0 );

	/* Fill the buffer. */
	for( lCharacter = 0; lCharacter < lCharactersToAdd; lCharacter++ )
	{
		ucBuffer[ lCharacter ] = ucChar;
		ucChar++;

		if( ucChar > '~' )
		{
			ucChar = '0';
		}
	}

	return lCharactersToAdd;
}
/*-----------------------------------------------------------*/
