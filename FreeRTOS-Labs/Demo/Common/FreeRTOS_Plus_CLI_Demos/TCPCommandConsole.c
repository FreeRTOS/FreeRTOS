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
#include "TCPCommandConsole.h"

/* Dimensions the buffer into which input characters are placed. */
#define cmdMAX_INPUT_SIZE	60

/* Dimensions the buffer into which string outputs can be placed. */
#define cmdMAX_OUTPUT_SIZE	1024

/* Dimensions the buffer passed to the recv() call. */
#define cmdSOCKET_INPUT_BUFFER_SIZE 60

/* DEL acts as a backspace. */
#define cmdASCII_DEL		( 0x7F )

/* The maximum time to wait for a closing socket to close. */
#define cmdSHUTDOWN_DELAY	( pdMS_TO_TICKS( 5000 ) )

/*
 * The task that runs FreeRTOS+CLI.
 */
static void prvTCPCommandInterpreterTask( void *pvParameters );

/*
 * Open and configure the TCP socket.
 */
static Socket_t prvOpenTCPServerSocket( uint16_t usPort );

/*
 * A connected socket is being closed.  Ensure the socket is closed at both ends
 * properly.
 */
static void prvGracefulShutdown( Socket_t xSocket );

/*-----------------------------------------------------------*/

/*
 * Various buffers used by the command lin interpreter.
 */
static char cOutputString[ cmdMAX_OUTPUT_SIZE ], cLocalBuffer[ cmdSOCKET_INPUT_BUFFER_SIZE ];
static char cInputString[ cmdMAX_INPUT_SIZE ], cLastInputString[ cmdMAX_INPUT_SIZE ];

/* Const messages output by the command console. */
static const char * const pcWelcomeMessage = "FreeRTOS command server.\r\nType help to view a list of registered commands.\r\nType quit to end a session.\r\n\r\n>";
static const char * const pcEndOfOutputMessage = "\r\n[Press ENTER to execute the previous command again]\r\n>";
static const char * const pcNewLine = "\r\n";

/*-----------------------------------------------------------*/

void vStartTCPCommandInterpreterTask( uint16_t usStackSize, uint32_t ulPort, UBaseType_t uxPriority )
{
	xTaskCreate( prvTCPCommandInterpreterTask, "TCP CLI", usStackSize, ( void * ) ulPort, uxPriority, NULL );
}
/*-----------------------------------------------------------*/

void prvTCPCommandInterpreterTask( void *pvParameters )
{
int32_t lBytes, lByte, lSent;
char cRxedChar, cInputIndex = 0;
BaseType_t xMoreDataToFollow;
struct freertos_sockaddr xClient;
Socket_t xListeningSocket, xConnectedSocket;
socklen_t xSize = sizeof( xClient );

	memset( cInputString, 0x00, cmdMAX_INPUT_SIZE );

	for( ;; )
	{
		/* Attempt to open the socket.  The port number is passed in the task
		parameter.  The strange casting is to remove compiler warnings on 32-bit
		machines.  NOTE:  The FREERTOS_SO_REUSE_LISTEN_SOCKET option is used,
		so the listening and connecting socket are the same - meaning only one
		connection will be accepted at a time, and that xListeningSocket must
		be created on each iteration. */
		xListeningSocket = prvOpenTCPServerSocket( ( uint16_t ) ( ( uint32_t ) pvParameters ) & 0xffffUL );

		/* Nothing for this task to do if the socket cannot be created. */
		if( xListeningSocket == FREERTOS_INVALID_SOCKET )
		{
			vTaskDelete( NULL );
		}

		/* Wait for an incoming connection. */
		xConnectedSocket = FreeRTOS_accept( xListeningSocket, &xClient, &xSize );

		/* The FREERTOS_SO_REUSE_LISTEN_SOCKET option is set, so the
		connected and listening socket should be the same socket. */
		configASSERT( xConnectedSocket == xListeningSocket );

		/* Send the welcome message. */
		lSent = FreeRTOS_send( xConnectedSocket,  ( void * ) pcWelcomeMessage,  strlen( pcWelcomeMessage ), 0 );

		/* Process the socket as long as it remains connected. */
		while( lSent >= 0 )
		{
			/* Receive data on the socket. */
			lBytes = FreeRTOS_recv( xConnectedSocket, cLocalBuffer, sizeof( cLocalBuffer ), 0 );

			if( lBytes >= 0 )
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
						FreeRTOS_send( xConnectedSocket, pcNewLine,  strlen( pcNewLine ), 0 );

						/* See if the command is empty, indicating that the last
						command is to be executed again. */
						if( cInputIndex == 0 )
						{
							/* Copy the last command back into the input string. */
							strcpy( cInputString, cLastInputString );
						}

						/* If the command was "quit" then close the console. */
						if( strcasecmp( cInputString, "quit" ) == 0 )
						{
							/* Fake an error code so the outer loop exits on the
							assumption there was an error on the socket.  The
							socket will then be shut down gracefully. */
							lSent = -1;
							break;
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
							lSent = FreeRTOS_send( xConnectedSocket, cOutputString,  strlen( ( const char * ) cOutputString ), 0 );

						  /* Until the command does not generate any more output. */
						} while( ( xMoreDataToFollow != pdFALSE ) && ( lSent >= 0 ) );

						if( lSent >= 0 )
						{
							/* All the strings generated by the command
							processing have been sent.  Clear the input string
							ready to receive the next command.  Remember the
							previous command so it can be executed again by
							pressing [ENTER]. */
							strcpy( cLastInputString, cInputString );
							cInputIndex = 0;
							memset( cInputString, 0x00, cmdMAX_INPUT_SIZE );

							/* Transmit a spacer to make the console easier to
							read. */
							lSent = FreeRTOS_send( xConnectedSocket, ( void * ) pcEndOfOutputMessage,  strlen( pcEndOfOutputMessage ), 0 );
						}

						if( lSent < 0 )
						{
							/* Socket closed? */
							break;
						}
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
								if( ( cRxedChar >= ' ' ) && ( cRxedChar <= '~' ) )
								{
									cInputString[ ( int ) cInputIndex ] = cRxedChar;
									cInputIndex++;
								}
							}
						}
					}
				}
			}
			else
			{
				/* Socket closed? */
				break;
			}
		}

		/* Close the socket correctly. */
		prvGracefulShutdown( xListeningSocket );
	}
}
/*-----------------------------------------------------------*/

static void prvGracefulShutdown( Socket_t xSocket )
{
TickType_t xTimeOnShutdown;

	/* Initiate a shutdown in case it has not already been initiated. */
	FreeRTOS_shutdown( xSocket, FREERTOS_SHUT_RDWR );

	/* Wait for the shutdown to take effect, indicated by FreeRTOS_recv()
	returning an error. */
	xTimeOnShutdown = xTaskGetTickCount();
	do
	{
		if( FreeRTOS_recv( xSocket, cInputString, ipconfigTCP_MSS, 0 ) < 0 )
		{
			break;
		}
	} while( ( xTaskGetTickCount() - xTimeOnShutdown ) < cmdSHUTDOWN_DELAY );

	/* Finished with the socket and the task. */
	FreeRTOS_closesocket( xSocket );
}
/*-----------------------------------------------------------*/

static Socket_t prvOpenTCPServerSocket( uint16_t usPort )
{
struct freertos_sockaddr xBindAddress;
Socket_t xSocket;
static const TickType_t xReceiveTimeOut = portMAX_DELAY;
const BaseType_t xBacklog = 20;
BaseType_t xReuseSocket = pdTRUE;

	/* Attempt to open the socket. */
	xSocket = FreeRTOS_socket( FREERTOS_AF_INET, FREERTOS_SOCK_STREAM, FREERTOS_IPPROTO_TCP );
	configASSERT( xSocket != FREERTOS_INVALID_SOCKET );

	/* Set a time out so accept() will just wait for a connection. */
	FreeRTOS_setsockopt( xSocket, 0, FREERTOS_SO_RCVTIMEO, &xReceiveTimeOut, sizeof( xReceiveTimeOut ) );

	/* Only one connection will be used at a time, so re-use the listening
	socket as the connected socket.  See SimpleTCPEchoServer.c for an example
	that accepts multiple connections. */
	FreeRTOS_setsockopt( xSocket, 0, FREERTOS_SO_REUSE_LISTEN_SOCKET, &xReuseSocket, sizeof( xReuseSocket ) );

	/* NOTE:  The CLI is a low bandwidth interface (typing characters is slow),
	so the TCP window properties are left at their default.  See
	SimpleTCPEchoServer.c for an example of a higher throughput TCP server that
	uses are larger RX and TX buffer. */

	/* Bind the socket to the port that the client task will send to, then
	listen for incoming connections. */
	xBindAddress.sin_port = usPort;
	xBindAddress.sin_port = FreeRTOS_htons( xBindAddress.sin_port );
	FreeRTOS_bind( xSocket, &xBindAddress, sizeof( xBindAddress ) );
	FreeRTOS_listen( xSocket, xBacklog );

	return xSocket;
}
/*-----------------------------------------------------------*/




