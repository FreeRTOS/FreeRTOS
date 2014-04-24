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


#pragma comment( lib, "ws2_32.lib" )

/* Win32 includes. */
#include <WinSock2.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS+CLI includes. */
#include "FreeRTOS_CLI.h"

/* Dimensions the buffer into which input characters are placed. */
#define cmdMAX_INPUT_SIZE	60

/* Dimensions the buffer into which string outputs can be placed. */
#define cmdMAX_OUTPUT_SIZE	1024

/* Dimensions the buffer passed to the recvfrom() call. */
#define cmdSOCKET_INPUT_BUFFER_SIZE 60

/* DEL acts as a backspace. */
#define cmdASCII_DEL		( 0x7F )

/*
 * Open and configure the UDP socket.
 */
static SOCKET prvOpenUDPSocket( void );

/*-----------------------------------------------------------*/

/*
 * Task that provides the input and output for the FreeRTOS+CLI command
 * interpreter.  In this case a WinSock UDP port is used for convenience as this
 * demo runs in a simulated environment on a Windows PC.  See the URL in the
 * comments within main.c for the location of the online documentation.
 */
void vUDPCommandInterpreterTask( void *pvParameters )
{
long lBytes, lByte;
signed char cInChar, cInputIndex = 0;
static signed char cInputString[ cmdMAX_INPUT_SIZE ], cOutputString[ cmdMAX_OUTPUT_SIZE ], cLocalBuffer[ cmdSOCKET_INPUT_BUFFER_SIZE ];
portBASE_TYPE xMoreDataToFollow;
volatile int iErrorCode = 0;
struct sockaddr_in xClient;
int xClientAddressLength = sizeof( struct sockaddr_in );
SOCKET xSocket;

	/* Just to prevent compiler warnings. */
	( void ) pvParameters;

	/* Attempt to open the socket. */
	xSocket = prvOpenUDPSocket();

	if( xSocket != INVALID_SOCKET )
	{
		for( ;; )
		{
			/* Wait for incoming data on the opened socket. */
			lBytes = recvfrom( xSocket, cLocalBuffer, sizeof( cLocalBuffer ), 0, ( struct sockaddr * ) &xClient, &xClientAddressLength );

			if( lBytes == SOCKET_ERROR )
			{
				/* Something went wrong, but it is not handled by this simple
				example. */
				iErrorCode = WSAGetLastError();
			}
			else
			{
				/* Process each received byte in turn. */
				lByte = 0;
				while( lByte < lBytes )
				{
					/* The next character in the input buffer. */
					cInChar = cLocalBuffer[ lByte ];
					lByte++;

					/* Newline characters are taken as the end of the command
					string. */
					if( cInChar == '\n' )
					{
						/* Process the input string received prior to the
						newline. */
						do
						{
							/* Pass the string to FreeRTOS+CLI. */
							xMoreDataToFollow = FreeRTOS_CLIProcessCommand( cInputString, cOutputString, cmdMAX_OUTPUT_SIZE );

							/* Send the output generated by the command's
							implementation. */
							sendto( xSocket, cOutputString,  strlen( cOutputString ), 0, ( SOCKADDR * ) &xClient, xClientAddressLength );

						} while( xMoreDataToFollow != pdFALSE ); /* Until the command does not generate any more output. */

						/* All the strings generated by the command processing
						have been sent.  Clear the input string ready to receive
						the next command. */
						cInputIndex = 0;
						memset( cInputString, 0x00, cmdMAX_INPUT_SIZE );

						/* Transmit a spacer, just to make the command console
						easier to read. */
						sendto( xSocket, "\r\n",  strlen( "\r\n" ), 0, ( SOCKADDR * ) &xClient, xClientAddressLength );
					}
					else
					{
						if( cInChar == '\r' )
						{
							/* Ignore the character.  Newlines are used to
							detect the end of the input string. */
						}
						else if( ( cInChar == '\b' ) || ( cInChar == cmdASCII_DEL ) )
						{
							/* Backspace was pressed.  Erase the last character
							in the string - if any. */
							if( cInputIndex > 0 )
							{
								cInputIndex--;
								cInputString[ cInputIndex ] = '\0';
							}
						}
						else
						{
							/* A character was entered.  Add it to the string
							entered so far.  When a \n is entered the complete
							string will be passed to the command interpreter. */
							if( cInputIndex < cmdMAX_INPUT_SIZE )
							{
								cInputString[ cInputIndex ] = cInChar;
								cInputIndex++;
							}
						}
					}
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

static SOCKET prvOpenUDPSocket( void )
{
WSADATA xWSAData;
WORD wVersionRequested;
struct sockaddr_in xServer;
SOCKET xSocket = INVALID_SOCKET;

	wVersionRequested = MAKEWORD( 2, 2 );

	/* Prepare to use WinSock. */
	if( WSAStartup( wVersionRequested, &xWSAData ) != 0 )
	{
		fprintf( stderr, "Could not open Windows connection.\n" );
	}
	else
	{
		xSocket = socket( AF_INET, SOCK_DGRAM, 0 );
		if( xSocket == INVALID_SOCKET)
		{
			fprintf( stderr, "Could not create socket.\n" );
			WSACleanup();
		}
		else
		{
			/* Zero out the server structure. */
			memset( ( void * ) &xServer, 0x00, sizeof( struct sockaddr_in ) );

			/* Set family and port. */
			xServer.sin_family = AF_INET;
			xServer.sin_port = htons( configUDP_CLI_PORT_NUMBER );

			/* Assign the loopback address */
			xServer.sin_addr.S_un.S_un_b.s_b1 = 127;
			xServer.sin_addr.S_un.S_un_b.s_b2 = 0;
			xServer.sin_addr.S_un.S_un_b.s_b3 = 0;
			xServer.sin_addr.S_un.S_un_b.s_b4 = 1;

			/* Bind the address to the socket. */
			if( bind( xSocket, ( struct sockaddr * ) &xServer, sizeof( struct sockaddr_in ) ) == -1 )
			{
				fprintf( stderr, "Could not socket to port %d.\n", configUDP_CLI_PORT_NUMBER );
				closesocket( xSocket );
				xSocket = INVALID_SOCKET;
				WSACleanup();
			}
		}
	}

	return xSocket;
}


