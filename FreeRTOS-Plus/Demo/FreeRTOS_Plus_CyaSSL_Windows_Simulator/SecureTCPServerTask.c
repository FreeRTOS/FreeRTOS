/*
    FreeRTOS V7.1.1 - Copyright (C) 2012 Real Time Engineers Ltd.


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
    >>>NOTE<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.  FreeRTOS is distributed in the hope that it will be useful, but
    WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public
    License and the FreeRTOS license exception along with FreeRTOS; if not it
    can be viewed here: http://www.freertos.org/a00114.html and also obtained
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!
    
    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?                                      *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    
    http://www.FreeRTOS.org - Documentation, training, latest information, 
    license and contact details.
    
    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool.

    Real Time Engineers ltd license FreeRTOS to High Integrity Systems, who sell 
    the code with commercial support, indemnification, and middleware, under 
    the OpenRTOS brand: http://www.OpenRTOS.com.  High Integrity Systems also
    provide a safety engineered and independently SIL3 certified version under 
    the SafeRTOS brand: http://www.SafeRTOS.com.
*/

#pragma comment( lib, "ws2_32.lib" )

/* Win32 includes. */
#include <WinSock2.h>

/* CyaSSL includes. */
#include "cyassl/ssl.h"

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* This application is using the FreeRTOS Windows simulator, which uses the
FreeRTOS scheduler to schedule FreeRTOS task within the Windows environment.
The Windows envrionment must not be allowed to block any Windows threads that
are running FreeRTOS tasks, unless the FreeRTOS task is running at the FreeRTOS
idle priority.  For simplicity, this demo uses the Windows TCP/IP stack, the
API for which can cause Windows threads to block.  Therefore, any FreeRTOS task
that makes calls to the Windows TCP/IP stack must be assigned the idle prioity.
Note this is only a restriction of the simulated Windows environment - real
FreeRTOS ports do not have this restriction. */
#define sstSECURE_CLIENT_TASK_PRIORITY		( tskIDLE_PRIORITY )

/*-----------------------------------------------------------*/

/*
 * Open, configures and binds the server's TCP socket.
 */
static SOCKET prvOpenServerSocket( void );

/* 
 * Prepare the CyaSSL library for use.
 */
static void prvInitialiseCyaSSL( void );

/*
 * The task that implements the client side of the connection.
 */
extern void vSecureTCPClientTask( void *pvParameters );

/*-----------------------------------------------------------*/

/* The CyaSSL context for the server. */
static CYASSL_CTX* xCyaSSL_ServerContext = NULL;

/*-----------------------------------------------------------*/

/* See the comments at the top of main.c. */
void vSecureTCPServerTask( void *pvParameters )
{
portBASE_TYPE xReturned;
long lBytes;
uint8_t cReceivedString[ 60 ];
struct sockaddr_in xClient;
int xClientAddressLength = sizeof( struct sockaddr_in );
SOCKET xListeningSocket, xConnectedSocket;
CYASSL* xCyaSSL_Object; /* Only one connection is accepted at a time, so only one object is needed at a time. */

	/* Just to prevent compiler warnings. */
	( void ) pvParameters;

	/* Perform the initialisation necessary before CyaSSL can be used. */
	prvInitialiseCyaSSL();
	configASSERT( xCyaSSL_ServerContext );

	/* Attempt to open the socket. */
	xListeningSocket = prvOpenServerSocket();

	/* Now the server socket has been created and the CyaSSL library has been
	initialised, the task that implements the client side can be created. */
	xTaskCreate( vSecureTCPClientTask, "Client", configMINIMAL_STACK_SIZE, NULL, sstSECURE_CLIENT_TASK_PRIORITY, NULL );

	if( xListeningSocket != INVALID_SOCKET )
	{
		for( ;; )
		{
			/* Wait until the client connects. */
			printf( "Waiting for new connection\r\n" );
			xConnectedSocket = accept( xListeningSocket, ( struct sockaddr * ) &xClient, &xClientAddressLength );

			if( xConnectedSocket != INVALID_SOCKET )
			{
				printf( "Connection established\r\n" );

				/* A connection has been accepted by the server.  Create a 
				CyaSSL object for use with the newly connected socket. */
				xCyaSSL_Object = NULL;
				xCyaSSL_Object = CyaSSL_new( xCyaSSL_ServerContext );
    
				if( xCyaSSL_Object != NULL )
				{
					/* Associate the created CyaSSL object with the connected 
					socket. */
					xReturned = CyaSSL_set_fd( xCyaSSL_Object, xConnectedSocket );
					configASSERT( xReturned == SSL_SUCCESS );

					do
					{
						/* The next line is the secure equivalent to the 
						standard sockets call:
						lBytes = recv( xConnectedSocket, cReceivedString, 50, 0 ); */
						lBytes = CyaSSL_read( xCyaSSL_Object, cReceivedString, sizeof( cReceivedString ) );
						
						/* Print the received characters. */
						if( lBytes > 0 )
						{
							printf( "Received by the secure server: %s\r\n", cReceivedString );
						}

					} while ( lBytes > 0 );

					/* The connection was closed, close the socket and free the
					CyaSSL object. */
					closesocket( xConnectedSocket );					
					CyaSSL_free( xCyaSSL_Object );
					printf( "Connection closed, back to start\r\n\r\n" );
				}								
			}
		} 
	}
	else
	{
		/* The socket could not be opened. */
		vTaskDelete( NULL );
	}
}
/*-----------------------------------------------------------*/

static SOCKET prvOpenServerSocket( void )
{
WSADATA xWSAData;
WORD wVersionRequested;
struct sockaddr_in xConnection;
SOCKET xSocket = INVALID_SOCKET;

	wVersionRequested = MAKEWORD( 2, 2 );

	/* Prepare to use WinSock. */
	if( WSAStartup( wVersionRequested, &xWSAData ) != 0 )
	{
		fprintf( stderr, "Could not open Windows connection.\n" );
	}
	else
	{
		xSocket = socket( AF_INET, SOCK_STREAM, 0 );
		if( xSocket == INVALID_SOCKET)
		{
			fprintf( stderr, "Could not create socket.\n" );
			WSACleanup();
		}
		else
		{
			/* Zero out the server structure. */
			memset( ( void * ) &xConnection, 0x00, sizeof( struct sockaddr_in ) );

			xConnection.sin_family = AF_INET;
			xConnection.sin_addr.s_addr = inet_addr("127.0.0.1");
			xConnection.sin_port = htons( configTCP_PORT_NUMBER );

			/* Bind the address to the socket. */
			if( bind( xSocket, ( struct sockaddr * ) &xConnection, sizeof( struct sockaddr_in ) ) == -1 )
			{
				fprintf( stderr, "Could not socket to port %d.\n", configTCP_PORT_NUMBER );
				closesocket( xSocket );
				xSocket = INVALID_SOCKET;
				WSACleanup();
			}

			if( listen( xSocket, 20 ) != 0 )
			{
				closesocket( xSocket );
				xSocket = INVALID_SOCKET;
				WSACleanup();
			}
		}
	}

	return xSocket;
}
/*-----------------------------------------------------------*/

static void prvInitialiseCyaSSL( void )
{
int32_t iReturn;

	#ifdef DEBUG_CYASSL
	{
		CyaSSL_Debugging_ON();
	}
	#endif

    /* Initialise CyaSSL.  This must be done before any other CyaSSL functions
    are called. */
    CyaSSL_Init();

    /* Attempt to create a context that uses the TLS V1 server protocol. */
    xCyaSSL_ServerContext = CyaSSL_CTX_new( CyaTLSv1_server_method() );

    if( xCyaSSL_ServerContext != NULL )
    {
        /* Load the CA certificate.  Real applications should ensure that
        CyaSSL_CTX_load_verify_locations() returns SSL_SUCCESS before 
		proceeding. */
        iReturn = CyaSSL_CTX_load_verify_locations( xCyaSSL_ServerContext, "ca-cert.pem", 0 );
		configASSERT( iReturn == SSL_SUCCESS );

		iReturn = CyaSSL_CTX_use_certificate_file( xCyaSSL_ServerContext, "server-cert.pem", SSL_FILETYPE_PEM );
		configASSERT( iReturn == SSL_SUCCESS );

		iReturn = CyaSSL_CTX_use_PrivateKey_file( xCyaSSL_ServerContext, "server-key.pem", SSL_FILETYPE_PEM );
		configASSERT( iReturn == SSL_SUCCESS );
    }
}


