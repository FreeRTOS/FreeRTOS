/*
    FreeRTOS V8.2.2 - Copyright (C) 2015 Real Time Engineers Ltd.
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

