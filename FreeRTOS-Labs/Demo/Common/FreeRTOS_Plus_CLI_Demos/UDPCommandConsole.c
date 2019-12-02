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
#include <stdarg.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* FreeRTOS+CLI includes. */
#include "FreeRTOS_CLI.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"

/* Demo app includes. */
#include "UDPCommandConsole.h"

/* Dimensions the buffer into which input characters are placed. */
#define cmdMAX_INPUT_SIZE	60

/* Dimensions the buffer into which string outputs can be placed. */
#define cmdMAX_OUTPUT_SIZE	1024

/* Dimensions the buffer passed to the recvfrom() call. */
#define cmdSOCKET_INPUT_BUFFER_SIZE 60

/* DEL acts as a backspace. */
#define cmdASCII_DEL		( 0x7F )

/* The socket used by the CLI and debug print messages. */
static Socket_t xSocket = FREERTOS_INVALID_SOCKET;

/*
 * The task that runs FreeRTOS+CLI.
 */
static void prvUDPCommandInterpreterTask( void *pvParameters );

/*
 * Open and configure the UDP socket.
 */
static Socket_t prvOpenUDPServerSocket( uint16_t usPort );

/*-----------------------------------------------------------*/

/* This is required as a parameter to maintain the sendto() Berkeley sockets
API - but it is not actually used so can take any value. */
static socklen_t xClientAddressLength = 0;

/* Const messages output by the command console. */
static const char * const pcEndOfOutputMessage = "\r\n[Press ENTER to execute the previous command again]\r\n>";
static const char * const pcNewLine = "\r\n";

/*-----------------------------------------------------------*/

void vStartUDPCommandInterpreterTask( uint16_t usStackSize, uint32_t ulPort, UBaseType_t uxPriority )
{
	xTaskCreate( prvUDPCommandInterpreterTask, "UDP CLI", usStackSize, ( void * ) ulPort, uxPriority, NULL );
}
/*-----------------------------------------------------------*/

void prvUDPCommandInterpreterTask( void *pvParameters )
{
int32_t lBytes, lByte;
char cRxedChar, cInputIndex = 0;
static char cOutputString[ cmdMAX_OUTPUT_SIZE ], cLocalBuffer[ cmdSOCKET_INPUT_BUFFER_SIZE ];
static char cLastInputString[ cmdMAX_INPUT_SIZE ], cInputString[ cmdMAX_INPUT_SIZE ];
BaseType_t xMoreDataToFollow;
struct freertos_sockaddr xClient;

	memset( cInputString, 0x00, cmdMAX_INPUT_SIZE );

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

			if( lBytes > 0 )
			{
				/* Process each received byte in turn. */
				lByte = 0;
				while( lByte < lBytes )
				{
					/* The next character in the input buffer. */
					cRxedChar = cLocalBuffer[ lByte ];
					lByte++;

					/* Newline characters are taken as the end of the command
					string. */
					if( cRxedChar == '\n' )
					{
						/* Just to space the output from the input. */
						FreeRTOS_sendto( xSocket, pcNewLine,  strlen( pcNewLine ), 0, &xClient, xClientAddressLength );

						/* See if the command is empty, indicating that the last command
						is to be executed again. */
						if( cInputIndex == 0 )
						{
							/* Copy the last command back into the input string. */
							strcpy( cInputString, cLastInputString );
						}

						/* Process the input string received prior to the
						newline. */
						do
						{
							/* Pass the string to FreeRTOS+CLI. */
							cOutputString[ 0 ] = 0x00;
							xMoreDataToFollow = FreeRTOS_CLIProcessCommand( cInputString, cOutputString, cmdMAX_OUTPUT_SIZE );

							/* Send the output generated by the command's
							implementation. */
							FreeRTOS_sendto( xSocket, cOutputString,  strlen( ( const char * ) cOutputString ), 0, &xClient, xClientAddressLength );

						  /* Until the command does not generate any more output. */
						} while( xMoreDataToFollow != pdFALSE );

						/* All the strings generated by the command processing
						have been sent.  Clear the input string ready to receive
						the next command.  Remember the previous command so it
						can be repeated if the user just presses the ENTER key. */
						strcpy( cLastInputString, cInputString );
						cInputIndex = 0;
						memset( cInputString, 0x00, cmdMAX_INPUT_SIZE );

						/* Transmit a spacer to make the console easier to
						read. */
						FreeRTOS_sendto( xSocket, ( void * ) pcEndOfOutputMessage,  strlen( pcEndOfOutputMessage ), 0, &xClient, xClientAddressLength );
					}
					else
					{
						if( cRxedChar == '\r' )
						{
							/* Ignore the character.  Newlines are used to
							detect the end of the input string. */
						}
						else if( ( cRxedChar == '\b' ) || ( cRxedChar == cmdASCII_DEL ) )
						{
							/* Backspace was pressed.  Erase the last character
							in the string - if any. */
							if( cInputIndex > 0 )
							{
								cInputIndex--;
								cInputString[ ( int ) cInputIndex ] = '\0';
							}
						}
						else
						{
							/* A character was entered.  Add it to the string
							entered so far.  When a \n is entered the complete
							string will be passed to the command interpreter. */
							if( cInputIndex < cmdMAX_INPUT_SIZE )
							{
								cInputString[ ( int ) cInputIndex ] = cRxedChar;
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
Socket_t xServerSocket = FREERTOS_INVALID_SOCKET;
TickType_t xSendTimeOut = 0;

	xServerSocket = FreeRTOS_socket( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP );
	if( xServerSocket != FREERTOS_INVALID_SOCKET)
	{
		/* Set to non-blocking sends with a timeout of zero as the socket might
		also be used for debug prints which should not block. */
		FreeRTOS_setsockopt( xServerSocket, 0, FREERTOS_SO_SNDTIMEO, &xSendTimeOut, sizeof( xSendTimeOut ) );

		/* Zero out the server structure. */
		memset( ( void * ) &xServer, 0x00, sizeof( xServer ) );

		/* Set family and port. */
		xServer.sin_port = FreeRTOS_htons( usPort );

		/* Bind the address to the socket. */
		if( FreeRTOS_bind( xServerSocket, &xServer, sizeof( xServer ) ) == -1 )
		{
			FreeRTOS_closesocket( xServerSocket );
			xServerSocket = FREERTOS_INVALID_SOCKET;
		}
	}

	return xServerSocket;
}
/*-----------------------------------------------------------*/

