/*
    FreeRTOS V7.3.0 - Copyright (C) 2012 Real Time Engineers Ltd.

    FEATURES AND PORTS ARE ADDED TO FREERTOS ALL THE TIME.  PLEASE VISIT 
    http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

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
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    
    http://www.FreeRTOS.org - Documentation, training, latest versions, license 
    and contact details.  
    
    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool.

    Real Time Engineers ltd license FreeRTOS to High Integrity Systems, who sell 
    the code with commercial support, indemnification, and middleware, under 
    the OpenRTOS brand: http://www.OpenRTOS.com.  High Integrity Systems also
    provide a safety engineered and independently SIL3 certified version under 
    the SafeRTOS brand: http://www.SafeRTOS.com.
*/

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* FreeRTOS+CLI includes. */
#include "FreeRTOS_CLI.h"

/* FreeRTOS+UDP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"

/* Demo app includes. */
#include "UDPCommandInterpreter.h"

/* Dimensions the buffer into which input characters are placed. */
#define cmdMAX_INPUT_SIZE	60

/* Dimensions the buffer into which string outputs can be placed. */
#define cmdMAX_OUTPUT_SIZE	1024

/* Dimensions the buffer passed to the recvfrom() call. */
#define cmdSOCKET_INPUT_BUFFER_SIZE 60

/*
 * The task that runs FreeRTOS+CLI.
 */
void vUDPCommandInterpreterTask( void *pvParameters );

/*
 * Open and configure the UDP socket.
 */
static Socket_t prvOpenUDPServerSocket( uint16_t usPort );

/*-----------------------------------------------------------*/

void vStartUDPCommandInterpreterTask( uint16_t usStackSize, uint32_t ulPort, unsigned portBASE_TYPE uxPriority )
{
	xTaskCreate( vUDPCommandInterpreterTask, ( signed char * ) "CLI", usStackSize, ( void * ) ulPort, uxPriority, NULL );
}
/*-----------------------------------------------------------*/

/* 
 * Task that provides the input and output for the FreeRTOS+CLI command
 * interpreter.  In this case a UDP port is used.  See the URL in the comments
 * within main.c for the location of the online documentation.
 */
void vUDPCommandInterpreterTask( void *pvParameters )
{
long lBytes, lByte;
signed char cInChar, cInputIndex = 0;
static signed char cInputString[ cmdMAX_INPUT_SIZE ], cOutputString[ cmdMAX_OUTPUT_SIZE ], cLocalBuffer[ cmdSOCKET_INPUT_BUFFER_SIZE ];
portBASE_TYPE xMoreDataToFollow;
struct freertos_sockaddr xClient;
socklen_t xClientAddressLength = 0; /* This is required as a parameter to maintain the sendto() Berkeley sockets API - but it is not actually used so can take any value. */
Socket_t xSocket;
extern const uint8_t ucIPAddress[ 4 ];
extern const uint8_t ucMACAddress[ 6 ];

	/* Just to prevent compiler warnings. */
	( void ) pvParameters;

	/* Attempt to open the socket.  The port number is passed in the task
	parameter.  The strange casting is to remove compiler warnings on 32-bit
	machines. */
	xSocket = prvOpenUDPServerSocket( ( uint16_t ) ( ( uint32_t ) pvParameters ) & 0xffffUL );

	if( xSocket != FREERTOS_INVALID_SOCKET )
	{
		for( ;; )
		{
			/* Wait for incoming data on the opened socket. */
			lBytes = FreeRTOS_recvfrom( xSocket, ( void * ) cLocalBuffer, sizeof( cLocalBuffer ), 0, &xClient, &xClientAddressLength );

			if( lBytes != FREERTOS_SOCKET_ERROR )
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
							FreeRTOS_sendto( xSocket, cOutputString,  strlen( ( const char * ) cOutputString ), 0, &xClient, xClientAddressLength );

						} while( xMoreDataToFollow != pdFALSE ); /* Until the command does not generate any more output. */

						/* All the strings generated by the command processing 
						have been sent.  Clear the input string ready to receive 
						the next command. */
						cInputIndex = 0;
						memset( cInputString, 0x00, cmdMAX_INPUT_SIZE );
						
						/* Transmit a spacer, just to make the command console
						easier to read. */
						FreeRTOS_sendto( xSocket, "\r\n",  strlen( "\r\n" ), 0, &xClient, xClientAddressLength );
					}
					else
					{
						if( cInChar == '\r' )
						{
							/* Ignore the character.  Newlines are used to 
							detect the end of the input string. */
						}
						else if( cInChar == '\b' )
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

static Socket_t prvOpenUDPServerSocket( uint16_t usPort )
{
struct freertos_sockaddr xServer;
Socket_t xSocket = FREERTOS_INVALID_SOCKET;

	xSocket = FreeRTOS_socket( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP );
	if( xSocket != FREERTOS_INVALID_SOCKET)
	{
		/* Zero out the server structure. */
		memset( ( void * ) &xServer, 0x00, sizeof( xServer ) );

		/* Set family and port. */
		xServer.sin_port = FreeRTOS_htons( usPort );

		/* Bind the address to the socket. */
		if( FreeRTOS_bind( xSocket, &xServer, sizeof( xServer ) ) == -1 )
		{			
			FreeRTOS_closesocket( xSocket );
			xSocket = FREERTOS_INVALID_SOCKET;
		}
	}

	return xSocket;
}


