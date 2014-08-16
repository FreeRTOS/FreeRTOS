/*
    FreeRTOS V8.1.0 - Copyright (C) 2014 Real Time Engineers Ltd. 
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
BaseType_t xReturned;
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


