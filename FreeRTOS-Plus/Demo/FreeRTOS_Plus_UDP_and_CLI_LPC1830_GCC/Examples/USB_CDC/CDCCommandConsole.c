/*
    FreeRTOS V7.1.0 - Copyright (C) 2011 Real Time Engineers Ltd.


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

/*
 * NOTE:  This file uses a third party USB CDC driver.
 */

/* Standard includes. */
#include "string.h"
#include "stdio.h"

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* Driver includes. */
#include "usbhw.h"
#include "cdcuser.h"
#include "usbcfg.h"
#include "usbuser.h"

/* Example includes. */
#include "FreeRTOS_CLI.h"
#include "CDCCommandConsole.h"

/* Dimensions the buffer into which input characters are placed. */
#define cmdMAX_INPUT_SIZE		50

/* The maximum time in ticks to wait for the CDC access mutex. */
#define cmdMAX_MUTEX_WAIT		( 200 / portTICK_RATE_MS )

/*-----------------------------------------------------------*/

/*
 * The task that implements the command console processing.
 */
static void prvCDCCommandConsoleTask( void *pvParameters );

/*
 * Obtain a character from the CDC input.  The calling task will be held in the
 * Blocked state (so other tasks can execute) until a character is avilable.
 */
int8_t cGetCDCChar( void );

/*
 * Initialise the third party virtual comport files driver
 */
static void prvSetupUSBDrivers( void );

/*-----------------------------------------------------------*/

/* 'Given' by the CDC interrupt to unblock the receiving task when new data
is available. */
static xSemaphoreHandle xNewDataSemaphore = NULL;

/* Used to guard access to the CDC output, which is used by more than one
task. */
static xSemaphoreHandle xCDCMutex = NULL;

/* Const messages output by the command console. */
static const uint8_t * const pcWelcomeMessage = ( uint8_t * ) "FreeRTOS command server.\r\nType Help to view a list of registered commands.\r\n\r\n>";
static const uint8_t * const pcEndOfOutputMessage = ( uint8_t * ) "\r\n[Press ENTER to execute the previous command again]\r\n>";
static const uint8_t * const pcNewLine = ( uint8_t * ) "\r\n";

/*-----------------------------------------------------------*/

void vCDCCommandConsoleStart( uint16_t usStackSize, unsigned portBASE_TYPE uxPriority )
{
	/* Create the semaphores and mutexes used by the CDC to task interface. */
	xCDCMutex = xSemaphoreCreateMutex();
	vSemaphoreCreateBinary( xNewDataSemaphore );
	configASSERT( xCDCMutex );
	configASSERT( xNewDataSemaphore );

	/* Add the semaphore and mutex to the queue registry for viewing in the
	kernel aware state viewer. */
	vQueueAddToRegistry( xCDCMutex, "CDCMu" );
	vQueueAddToRegistry( xNewDataSemaphore, "CDCDat" );

	/* Create that task that handles the console itself. */
	xTaskCreate( 	prvCDCCommandConsoleTask,	/* The task that implements the command console. */
					"CDCCmd",					/* Text name assigned to the task.  This is just to assist debugging.  The kernel does not use this name itself. */
					usStackSize,				/* The size of the stack allocated to the task. */
					NULL,						/* The parameter is not used, so NULL is passed. */
					uxPriority,					/* The priority allocated to the task. */
					NULL );						/* A handle is not required, so just pass NULL. */
}
/*-----------------------------------------------------------*/

static void prvCDCCommandConsoleTask( void *pvParameters )
{
int8_t cRxedChar, cInputIndex = 0, *pcOutputString;
static int8_t cInputString[ cmdMAX_INPUT_SIZE ], cLastInputString[ cmdMAX_INPUT_SIZE ];
portBASE_TYPE xReturned;

	( void ) pvParameters;

	/* Obtain the address of the output buffer.  Note there is no mutual
	exclusion on this buffer as it is assumed only one command console
	interface will be used at any one time. */
	pcOutputString = FreeRTOS_CLIGetOutputBuffer();

	/* Initialise the virtual com port (CDC) interface. */
	prvSetupUSBDrivers();

	/* Send the welcome message.  This probably won't be seen as the console
	will not have been connected yet. */
	USB_WriteEP( CDC_DEP_IN, ( uint8_t * ) pcWelcomeMessage, strlen( ( const char * ) pcWelcomeMessage ) );

	for( ;; )
	{
		/* No characters received yet for the current input string. */
		cRxedChar = 0;

		/* Only interested in reading one character at a time. */
		cRxedChar = cGetCDCChar();

		if( xSemaphoreTake( xCDCMutex, cmdMAX_MUTEX_WAIT ) == pdPASS )
		{
			/* Echo the character back. */
			USB_WriteEP( CDC_DEP_IN, ( uint8_t * ) &cRxedChar, sizeof( uint8_t ) );

			/* Was it the end of the line? */
			if( cRxedChar == '\n' || cRxedChar == '\r' )
			{
				/* Just to space the output from the input. */
				USB_WriteEP( CDC_DEP_IN, ( uint8_t * ) pcNewLine, strlen( ( const char * ) pcNewLine ) );

				/* See if the command is empty, indicating that the last command is
				to be executed again. */
				if( cInputIndex == 0 )
				{
					/* Copy the last command back into the input string. */
					strcpy( ( char * ) cInputString, ( char * ) cLastInputString );
				}

				/* Pass the received command to the command interpreter.  The
				command interpreter is called repeatedly until it returns pdFALSE
				(indicating there is no more output) as it might generate more than
				one string. */
				do
				{
					/* Get the next output string from the command interpreter. */
					xReturned = FreeRTOS_CLIProcessCommand( cInputString, pcOutputString, configCOMMAND_INT_MAX_OUTPUT_SIZE );

					/* Write the generated string to the CDC. */
					USB_WriteEP( CDC_DEP_IN, ( uint8_t * ) pcOutputString, strlen( ( const char * ) pcOutputString ) );
					vTaskDelay( 1 );

				} while( xReturned != pdFALSE );

				/* All the strings generated by the input command have been sent.
				Clear the input	string ready to receive the next command.  Remember
				the command that was just processed first in case it is to be
				processed again. */
				strcpy( ( char * ) cLastInputString, ( char * ) cInputString );
				cInputIndex = 0;
				memset( cInputString, 0x00, cmdMAX_INPUT_SIZE );

				USB_WriteEP( CDC_DEP_IN, ( uint8_t * ) pcEndOfOutputMessage, strlen( ( const char * ) pcEndOfOutputMessage ) );
			}
			else
			{
				if( cRxedChar == '\r' )
				{
					/* Ignore the character. */
				}
				else if( cRxedChar == '\b' )
				{
					/* Backspace was pressed.  Erase the last character in the
					string - if any. */
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
					if( ( cRxedChar >= ' ' ) && ( cRxedChar <= '~' ) )
					{
						if( cInputIndex < cmdMAX_INPUT_SIZE )
						{
							cInputString[ cInputIndex ] = cRxedChar;
							cInputIndex++;
						}
					}
				}
			}

			/* Must ensure to give the mutex back. */
			xSemaphoreGive( xCDCMutex );
		}
	}
}
/*-----------------------------------------------------------*/

void vOutputString( const uint8_t * const pucMessage )
{
	if( xSemaphoreTake( xCDCMutex, cmdMAX_MUTEX_WAIT ) == pdPASS )
	{
		USB_WriteEP( CDC_DEP_IN, ( uint8_t * ) pucMessage, strlen( ( const char * ) pucMessage ) );
		xSemaphoreGive( xCDCMutex );
	}
}
/*-----------------------------------------------------------*/

int8_t cGetCDCChar( void )
{
int32_t lAvailableBytes, xBytes = 0;
int8_t cInputChar;

	do
	{
		/* Are there any characters already available? */
		CDC_OutBufAvailChar( &lAvailableBytes );
		if( lAvailableBytes > 0 )
		{
			if( xSemaphoreTake( xCDCMutex, cmdMAX_MUTEX_WAIT ) == pdPASS )
			{
				/* Attempt to read one character. */
				xBytes = 1;
				xBytes = CDC_RdOutBuf( ( char * ) &cInputChar, &xBytes );

				xSemaphoreGive( xCDCMutex );
			}
		}

		if( xBytes == 0 )
		{
			/* A character was not available.  Wait until signalled by the
			CDC Rx callback function that new data has arrived. */
			xSemaphoreTake( xNewDataSemaphore, portMAX_DELAY );
		}

	} while( xBytes == 0 );

	return cInputChar;
}
/*-----------------------------------------------------------*/

/* Callback function executed by the USB interrupt when new data arrives. */
void vCDCNewDataNotify( void )
{
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	configASSERT( xNewDataSemaphore );

	/* 'Give' the semaphore that signals the arrival of new data to the command
	console task. */
	xSemaphoreGiveFromISR( xNewDataSemaphore, &xHigherPriorityTaskWoken );
	portEND_SWITCHING_ISR( xHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/

static void prvSetupUSBDrivers( void )
{
LPC_USBDRV_INIT_T xUSBCallback;

	/* Initialise the callback structure. */
	memset( ( void * ) &xUSBCallback, 0, sizeof( LPC_USBDRV_INIT_T ) );
	xUSBCallback.USB_Reset_Event = USB_Reset_Event;
	xUSBCallback.USB_P_EP[ 0 ] = USB_EndPoint0;
	xUSBCallback.USB_P_EP[ 1 ] = USB_EndPoint1;
	xUSBCallback.USB_P_EP[ 2 ] = USB_EndPoint2;
	xUSBCallback.ep0_maxp = USB_MAX_PACKET0;

	/* Initialise then connect the USB. */
	USB_Init( &xUSBCallback );
	USB_Connect( pdTRUE );
}
