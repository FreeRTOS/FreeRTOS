/*
    FreeRTOS V9.0.0rc1 - Copyright (C) 2016 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>>> AND MODIFIED BY <<<< the FreeRTOS exception.

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
#include "stdlib.h"
#include "string.h"

/* lwIP core includes */
#include "lwip/opt.h"
#include "lwip/sockets.h"

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Utils includes. */
#include "FreeRTOS_CLI.h"

/* Dimensions the buffer into which input characters are placed. */
#define cmdMAX_INPUT_SIZE	100

/* Dimensions the buffer into which string outputs can be placed. */
#define cmdMAX_OUTPUT_SIZE	1024

/*-----------------------------------------------------------*/

void vBasicSocketsCommandInterpreterTask( void *pvParameters )
{
long lSocket, lClientFd, lBytes, lAddrLen = sizeof( struct sockaddr_in ), lInputIndex;
struct sockaddr_in sLocalAddr;
struct sockaddr_in client_addr;
const char *pcWelcomeMessage = "FreeRTOS command server - connection accepted.\r\nType Help to view a list of registered commands.\r\n\r\n>";
char cInChar;
static char cInputString[ cmdMAX_INPUT_SIZE ], cOutputString[ cmdMAX_OUTPUT_SIZE ];
portBASE_TYPE xReturned;
extern void vRegisterSampleCLICommands( void );

	( void ) pvParameters;

	/* Register the standard CLI commands. */
	vRegisterSampleCLICommands();

	lSocket = lwip_socket(AF_INET, SOCK_STREAM, 0);

	if( lSocket >= 0 )
	{
		memset((char *)&sLocalAddr, 0, sizeof(sLocalAddr));
		sLocalAddr.sin_family = AF_INET;
		sLocalAddr.sin_len = sizeof(sLocalAddr);
		sLocalAddr.sin_addr.s_addr = htonl(INADDR_ANY);
		sLocalAddr.sin_port = ntohs( ( ( unsigned short ) 23 ) );

		if( lwip_bind( lSocket, ( struct sockaddr *) &sLocalAddr, sizeof( sLocalAddr ) ) < 0 )
		{
			lwip_close( lSocket );
			vTaskDelete( NULL );
		}

		if( lwip_listen( lSocket, 20 ) != 0 )
		{
			lwip_close( lSocket );
			vTaskDelete( NULL );
		}

		for( ;; )
		{

			lClientFd = lwip_accept(lSocket, ( struct sockaddr * ) &client_addr, ( u32_t * ) &lAddrLen );

			if( lClientFd > 0L )
			{
				lwip_send( lClientFd, pcWelcomeMessage, strlen( ( const char * ) pcWelcomeMessage ), 0 );

				lInputIndex = 0;
				memset( cInputString, 0x00, cmdMAX_INPUT_SIZE );

				do
				{
					lBytes = lwip_recv( lClientFd, &cInChar, sizeof( cInChar ), 0 );

					if( lBytes > 0L )
					{
						if( cInChar == '\n' )
						{
							/* The input string has been terminated.  Was the
							input a quit command? */
							if( strcmp( "quit", ( const char * ) cInputString ) == 0 )
							{
								/* Set lBytes to 0 to close the connection. */
								lBytes = 0L;
							}
							else
							{
								/* The input string was not a quit command.
								Pass the string to the command interpreter. */
								do
								{
									/* Get the next output string from the command interpreter. */
									xReturned = FreeRTOS_CLIProcessCommand( cInputString, cOutputString, cmdMAX_INPUT_SIZE );
									lwip_send( lClientFd, cOutputString, strlen( ( const char * ) cOutputString ), 0 );

								} while( xReturned != pdFALSE );


								/* All the strings generated by the input
								command have been sent.  Clear the input
								string ready to receive the next command. */
								lInputIndex = 0;
								memset( cInputString, 0x00, cmdMAX_INPUT_SIZE );
								lwip_send( lClientFd, "\r\n>", strlen( "\r\n>" ), 0 );
							}
						}
						else
						{
							if( cInChar == '\r' )
							{
								/* Ignore the character. */
							}
							else if( cInChar == '\b' )
							{
								/* Backspace was pressed.  Erase the last
								character in the string - if any. */
								if( lInputIndex > 0 )
								{
									lInputIndex--;
									cInputString[ lInputIndex ] = '\0';
								}
							}
							else
							{
								/* A character was entered.  Add it to the string
								entered so far.  When a \n is entered the complete
								string will be passed to the command interpreter. */
								if( lInputIndex < cmdMAX_INPUT_SIZE )
								{
									cInputString[ lInputIndex ] = cInChar;
									lInputIndex++;
								}
							}
						}
					}

				} while( lBytes > 0L );

				 lwip_close( lClientFd );
			}
		}
	}

	/* Will only get here if a listening socket could not be created. */
	vTaskDelete( NULL );
}

