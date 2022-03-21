/*
 * FreeRTOS V202112.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

#pragma comment( lib, "ws2_32.lib" )

/* Win32 includes. */
#include <WinSock2.h>

/* wolfSSL includes. */
#include "wolfssl/ssl.h"

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
 * Prepare the wolfSSL library for use.
 */
static void prvInitialiseWolfSSL( void );

/*
 * The task that implements the client side of the connection.
 */
extern void vSecureTCPClientTask( void *pvParameters );

/*-----------------------------------------------------------*/

/* The wolfSSL context for the server. */
static WOLFSSL_CTX* xWolfSSL_ServerContext = NULL;

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
WOLFSSL* xWolfSSL_Object; /* Only one connection is accepted at a time, so only one object is needed at a time. */

	/* Just to prevent compiler warnings. */
	( void ) pvParameters;

	/* Perform the initialisation necessary before wolfSSL can be used. */
	prvInitialiseWolfSSL();
	configASSERT( xWolfSSL_ServerContext );

	/* Attempt to open the socket. */
	xListeningSocket = prvOpenServerSocket();

	/* Now the server socket has been created and the wolfSSL library has been
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
				wolfSSL object for use with the newly connected socket. */
				xWolfSSL_Object = NULL;
				xWolfSSL_Object = wolfSSL_new( xWolfSSL_ServerContext );

				if( xWolfSSL_Object != NULL )
				{
					/* Associate the created wolfSSL object with the connected
					socket. */
					xReturned = wolfSSL_set_fd( xWolfSSL_Object, xConnectedSocket );
					configASSERT( xReturned == SSL_SUCCESS );

					do
					{
						/* The next line is the secure equivalent to the
						standard sockets call:
						lBytes = recv( xConnectedSocket, cReceivedString, 50, 0 ); */
						lBytes = wolfSSL_read( xWolfSSL_Object, cReceivedString, sizeof( cReceivedString ) );

						/* Print the received characters. */
						if( lBytes > 0 )
						{
							printf( "Received by the secure server: %s\r\n", cReceivedString );
						}

					} while ( lBytes > 0 );

					/* The connection was closed, close the socket and free the
					wolfSSL object. */
					closesocket( xConnectedSocket );
					wolfSSL_free( xWolfSSL_Object );
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

static void prvInitialiseWolfSSL( void )
{
int32_t iReturn;

	#ifdef DEBUG_WOLFSSL
	{
		wolfSSL_Debugging_ON();
	}
	#endif

    /* Initialise wolfSSL.  This must be done before any other wolfSSL functions
    are called. */
    wolfSSL_Init();

    /* Attempt to create a context that uses the TLS 1.3 server protocol. */
    xWolfSSL_ServerContext = wolfSSL_CTX_new( wolfTLSv1_3_server_method() );

    if( xWolfSSL_ServerContext != NULL )
    {
        /* Load the CA certificate.  Real applications should ensure that
        wolfSSL_CTX_load_verify_locations() returns SSL_SUCCESS before
		proceeding. */
        iReturn = wolfSSL_CTX_load_verify_locations( xWolfSSL_ServerContext, "ca-cert.pem", 0 );
		configASSERT( iReturn == SSL_SUCCESS );

		iReturn = wolfSSL_CTX_use_certificate_file( xWolfSSL_ServerContext, "server-cert.pem", SSL_FILETYPE_PEM );
		configASSERT( iReturn == SSL_SUCCESS );

		iReturn = wolfSSL_CTX_use_PrivateKey_file( xWolfSSL_ServerContext, "server-key.pem", SSL_FILETYPE_PEM );
		configASSERT( iReturn == SSL_SUCCESS );
    }
}

