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
char cGetCDCChar( void );

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
static const char * const pcWelcomeMessage = "FreeRTOS command server.\r\nType Help to view a list of registered commands.\r\n\r\n>";
static const char * const pcEndOfOutputMessage = "\r\n[Press ENTER to execute the previous command again]\r\n>";
static const char * const pcNewLine = "\r\n";

/*-----------------------------------------------------------*/

void vCDCCommandConsoleStart( uint16_t usStackSize, UBaseType_t uxPriority )
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
char cRxedChar;
uint8_t ucInputIndex = 0;
char *pcOutputString;
static char cInputString[ cmdMAX_INPUT_SIZE ], cLastInputString[ cmdMAX_INPUT_SIZE ];
BaseType_t xReturned;

	( void ) pvParameters;

	/* Obtain the address of the output buffer.  Note there is no mutual
	exclusion on this buffer as it is assumed only one command console
	interface will be used at any one time. */
	pcOutputString = FreeRTOS_CLIGetOutputBuffer();

	/* Initialise the virtual com port (CDC) interface. */
	prvSetupUSBDrivers();

	/* Send the welcome message.  This probably won't be seen as the console
	will not have been connected yet. */
	USB_WriteEP( CDC_DEP_IN, ( uint8_t * ) pcWelcomeMessage, strlen( pcWelcomeMessage ) );

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
				USB_WriteEP( CDC_DEP_IN, ( uint8_t * ) pcNewLine, strlen( pcNewLine ) );

				/* See if the command is empty, indicating that the last command is
				to be executed again. */
				if( ucInputIndex == 0 )
				{
					/* Copy the last command back into the input string. */
					strcpy( cInputString, cLastInputString );
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
					USB_WriteEP( CDC_DEP_IN, ( uint8_t * ) pcOutputString, strlen( pcOutputString ) );
					vTaskDelay( 1 );

				} while( xReturned != pdFALSE );

				/* All the strings generated by the input command have been sent.
				Clear the input	string ready to receive the next command.  Remember
				the command that was just processed first in case it is to be
				processed again. */
				strcpy( cLastInputString, cInputString );
				ucInputIndex = 0;
				memset( cInputString, 0x00, cmdMAX_INPUT_SIZE );

				USB_WriteEP( CDC_DEP_IN, ( uint8_t * ) pcEndOfOutputMessage, strlen( pcEndOfOutputMessage ) );
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
					if( ucInputIndex > 0 )
					{
						ucInputIndex--;
						cInputString[ ucInputIndex ] = '\0';
					}
				}
				else
				{
					/* A character was entered.  Add it to the string
					entered so far.  When a \n is entered the complete
					string will be passed to the command interpreter. */
					if( ( cRxedChar >= ' ' ) && ( cRxedChar <= '~' ) )
					{
						if( ucInputIndex < cmdMAX_INPUT_SIZE )
						{
							cInputString[ ucInputIndex ] = cRxedChar;
							ucInputIndex++;
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

void vOutputString( const char * const pcMessage )
{
	if( xSemaphoreTake( xCDCMutex, cmdMAX_MUTEX_WAIT ) == pdPASS )
	{
		USB_WriteEP( CDC_DEP_IN, ( uint8_t * ) pcMessage, strlen( pcMessage ) );
		xSemaphoreGive( xCDCMutex );
	}
}
/*-----------------------------------------------------------*/

char cGetCDCChar( void )
{
int32_t lAvailableBytes, xBytes = 0;
char cInputChar;

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
				xBytes = CDC_RdOutBuf( &cInputChar, &xBytes );

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
BaseType_t xHigherPriorityTaskWoken = pdFALSE;

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
