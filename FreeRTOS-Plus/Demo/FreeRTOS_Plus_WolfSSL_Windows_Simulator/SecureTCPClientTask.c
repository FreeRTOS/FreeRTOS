/*
 * FreeRTOS Kernel V10.2.0
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
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

/*-----------------------------------------------------------*/

/* The wolfSSL context for the client. */
static WOLFSSL_CTX* xWolfSSL_ClientContext = NULL;

/*-----------------------------------------------------------*/

/* See the comments at the top of main.c. */
void vSecureTCPClientTask( void *pvParameters )
{
SOCKET xClientSocket;
struct sockaddr_in xConnection;
WOLFSSL* xWolfSSL_Object;
WORD wVersionRequested;
WSADATA xWSAData;
char cString[ 50 ];
BaseType_t lReturned;
uint32_t ulCount = 0UL;

	/* Remove compiler warning about unused parameters. */
	( void ) pvParameters;

	/* Prepare to use WinSock. */
	wVersionRequested = MAKEWORD( 2, 2 );
	configASSERT( WSAStartup( wVersionRequested, &xWSAData ) == 0 );

	/* Set family and port for client socket. */
	memset( ( void * ) &xConnection, 0x00, sizeof( struct sockaddr_in ) );
	xConnection.sin_family = AF_INET;
	xConnection.sin_addr.s_addr = inet_addr("127.0.0.1");
	xConnection.sin_port = htons( configTCP_PORT_NUMBER );

    /* Attempt to create a context that uses the TLS 1.2 server protocol. */
    xWolfSSL_ClientContext = wolfSSL_CTX_new( wolfTLSv1_2_client_method() );
	configASSERT( xWolfSSL_ClientContext );

    /* Load the CA certificate. */
    lReturned = wolfSSL_CTX_load_verify_locations( xWolfSSL_ClientContext, "ca-cert.pem", 0 );
	configASSERT( lReturned == SSL_SUCCESS );

	for( ;; )
	{
		/* Create the socket. */
		xClientSocket = socket( AF_INET, SOCK_STREAM, 0 );
		configASSERT( xClientSocket != INVALID_SOCKET );

		/* Connect to the secure server. */
		if( connect( xClientSocket, ( SOCKADDR * ) &xConnection, sizeof( xConnection ) ) == 0 )
		{
			/* The connect was successful.  Create a wolfSSL object to associate
			with this connection. */
			xWolfSSL_Object = wolfSSL_new( xWolfSSL_ClientContext );

			if( xWolfSSL_Object != NULL )
			{
				/* Associate the created wolfSSL object with the connected
				socket. */
				lReturned = wolfSSL_set_fd( xWolfSSL_Object, xClientSocket );
				configASSERT( lReturned == SSL_SUCCESS );

				/* The count is used to differentiate between messages sent to
				the server, and to break out of the do while loop below. */
				ulCount = 0UL;

				do
				{
					/* Create the string that is sent to the secure server. */
					sprintf( cString, "Message number %lu\r\n", ulCount );

					/* The next line is the secure equivalent of the standard
					sockets call:
					lReturned = send( xClientSocket, cString, strlen( cString ) + 1, 0 ); */
					lReturned = wolfSSL_write( xWolfSSL_Object, cString, strlen( cString ) + 1 );


					/* Short delay to prevent the messages streaming up the
					console too quickly. */
					vTaskDelay( 50 );
					ulCount++;

				} while( ( lReturned != SOCKET_ERROR ) && ( ulCount < 10UL ) );
			}

			wolfSSL_free( xWolfSSL_Object );
			closesocket( xClientSocket );

			/* Delay for a short time before starting over. */
			vTaskDelay( 250 );
		}
	}
}
/*-----------------------------------------------------------*/

