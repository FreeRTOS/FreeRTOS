/*
    FreeRTOS V7.0.2 - Copyright (C) 2011 Real Time Engineers Ltd.


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

    http://www.FreeRTOS.org - Documentation, latest information, license and
    contact details.

    http://www.SafeRTOS.com - A version that is certified for use in safety
    critical systems.

    http://www.OpenRTOS.com - Commercial support, development, porting,
    licensing and training services.
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

