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
#include "limits.h"

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* LPCUSB includes. */
#include "USB.h"
#include "Descriptors.h"

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
 * Some USB processing is deferred from LPCUSB interrupt service routines to
 * LPCUSB functions that are called from a FreeRTOS task.
 * prvNotifyTaskofUSBEvent() is used from interrupt event callback functions.
 * It uses a semaphore to unblock the handling task whenever task level
 * processing might be required.
 */
static void prvNotifyTaskOfUSBEvent( void );

/*-----------------------------------------------------------*/

/* 'Given' by the CDC interrupt to unblock the command console task when CDC
events are potentially waiting to be processed. */
static xSemaphoreHandle xCDCEventSemaphore = NULL;

/* Used to guard access to the CDC output, which is used by more than one
task. */
static xSemaphoreHandle xCDCMutex = NULL;

/* Const messages output by the command console. */
static const char * const pcWelcomeMessage = "FreeRTOS command server.\r\nType Help to view a list of registered commands.\r\n\r\n>";
static const char * const pcEndOfOutputMessage = "\r\n[Press ENTER to execute the previous command again]\r\n>";
static const char * const pcNewLine = "\r\n";

/* LPCUSBlib CDC Class driver interface configuration and state information. */
static USB_ClassInfo_CDC_Device_t xVirtualCOMPort = {
	.Config = {
		.ControlInterfaceNumber         = 0,

		.DataINEndpointNumber           = CDC_TX_EPNUM,
		.DataINEndpointSize             = CDC_TXRX_EPSIZE,
		.DataINEndpointDoubleBank       = false,

		.DataOUTEndpointNumber          = CDC_RX_EPNUM,
		.DataOUTEndpointSize            = CDC_TXRX_EPSIZE,
		.DataOUTEndpointDoubleBank      = false,

		.NotificationEndpointNumber     = CDC_NOTIFICATION_EPNUM,
		.NotificationEndpointSize       = CDC_NOTIFICATION_EPSIZE,
		.NotificationEndpointDoubleBank = false,
		.PortNumber             		= 0,
	},
};

/*-----------------------------------------------------------*/

void vCDCCommandConsoleStart( uint16_t usStackSize, unsigned portBASE_TYPE uxPriority )
{
	/* Create the semaphores and mutexes used by the CDC to task interface. */
	xCDCMutex = xSemaphoreCreateMutex();
	xCDCEventSemaphore = xSemaphoreCreateCounting( UINT_MAX, 0 );
	configASSERT( xCDCMutex );
	configASSERT( xCDCEventSemaphore );

	/* Add the semaphore and mutex to the queue registry for viewing in the
	kernel aware state viewer. */
	vQueueAddToRegistry( xCDCMutex, ( signed char * ) "CDCMu" );
	vQueueAddToRegistry( xCDCEventSemaphore, ( signed char * ) "CDCDat" );

	/* Create that task that handles the console itself. */
	xTaskCreate( 	prvCDCCommandConsoleTask,			/* The task that implements the command console. */
					( const int8_t * const ) "CDCCmd",	/* Text name assigned to the task.  This is just to assist debugging.  The kernel does not use this name itself. */
					usStackSize,						/* The size of the stack allocated to the task. */
					NULL,								/* The parameter is not used, so NULL is passed. */
					uxPriority,							/* The priority allocated to the task. */
					NULL );								/* A handle is not required, so just pass NULL. */
}
/*-----------------------------------------------------------*/

static void prvCDCCommandConsoleTask( void *pvParameters )
{
char cRxedChar, *pcOutputString;
static char cInputString[ cmdMAX_INPUT_SIZE ], cLastInputString[ cmdMAX_INPUT_SIZE ];
portBASE_TYPE xReturned, xInputIndex = 0;

	/* Just to avoid warnings about unused parameters. */
	( void ) pvParameters;

	/* Initialise LPCUSB CDC driver. */
	USB_Init( xVirtualCOMPort.Config.PortNumber, USB_MODE_Device );

	/* Obtain the address of the output buffer.  Note there is no mutual
	exclusion on this buffer as it is assumed only one command console
	interface will be used at any one time. */
	pcOutputString = ( char * ) FreeRTOS_CLIGetOutputBuffer();

	/* Send the welcome message.  This probably won't be seen as the console
	will not have been connected yet (the console cannot be connected until the
	virtual COM port has enumerated). */
	CDC_Device_SendData( &xVirtualCOMPort, pcWelcomeMessage, strlen( ( const char * ) pcWelcomeMessage ) );

	for( ;; )
	{
		/* Wait for new events to originate from the LPCUSB interrupts. */
//		xSemaphoreTake( xCDCEventSemaphore, 100 );

		/* LPCUSB function to process events latched by the USB interrupts. */
		CDC_Device_USBTask( &xVirtualCOMPort );
		USB_USBTask( xVirtualCOMPort.Config.PortNumber, USB_MODE_Device );

		/* Ensure no other tasks are using the COM port. */
		if( xSemaphoreTake( xCDCMutex, cmdMAX_MUTEX_WAIT ) == pdPASS )
		{
			/* Have any characters been received? */
			if( CDC_Device_BytesReceived( &xVirtualCOMPort ) != 0 )
			{
				/* Only interested in reading one character at a time. */
				cRxedChar = CDC_Device_ReceiveByte( &xVirtualCOMPort );

				/* Echo the character back. */
				CDC_Device_SendData( &xVirtualCOMPort, &cRxedChar, sizeof( uint8_t ) );

				/* Was it an end of line character? */
				if( cRxedChar == '\n' || cRxedChar == '\r' )
				{
					/* Just to space the output from the input. */
					CDC_Device_SendData( &xVirtualCOMPort, pcNewLine, strlen( ( const char * ) pcNewLine ) );

					/* See if the command is empty, indicating that the last
					command is to be executed again. */
					if( xInputIndex == 0 )
					{
						/* Copy the last command back into the input string. */
						strcpy( ( char * ) cInputString, ( char * ) cLastInputString );
					}

					/* Pass the received command to the command interpreter.
					The	command interpreter is called repeatedly until it
					returns pdFALSE	(indicating there is no more output) as it
					might generate more than one string. */
					do
					{
						/* Get the next output string from the command
						interpreter. */
						xReturned = FreeRTOS_CLIProcessCommand( ( const int8_t * const ) cInputString, ( int8_t * ) pcOutputString, configCOMMAND_INT_MAX_OUTPUT_SIZE );

						/* Write the generated string to the CDC. */
						CDC_Device_SendData( &xVirtualCOMPort, pcOutputString, strlen( ( const char * ) pcOutputString ) );

					} while( xReturned != pdFALSE );

					/* All the strings generated by the input command have been
					sent.  Clear the input string ready to receive the next
					command.  Remember the command that was just processed first
					in case it is to be	processed again. */
					strcpy( ( char * ) cLastInputString, ( char * ) cInputString );
					xInputIndex = 0;
					memset( cInputString, 0x00, cmdMAX_INPUT_SIZE );

					CDC_Device_SendData( &xVirtualCOMPort, pcEndOfOutputMessage, strlen( ( const char * ) pcEndOfOutputMessage ) );
				}
				else
				{
					if( cRxedChar == '\r' )
					{
						/* Ignore the character. */
					}
					else if( cRxedChar == '\b' )
					{
						/* Backspace was pressed.  Erase the last character in
						thestring - if any. */
						if( xInputIndex > 0 )
						{
							xInputIndex--;
							cInputString[ xInputIndex ] = '\0';
						}
					}
					else
					{
						/* A character was entered.  Add it to the string
						entered so far.  When a \n is entered the complete
						string will be passed to the command interpreter. */
						if( ( cRxedChar >= ' ' ) && ( cRxedChar <= '~' ) )
						{
							if( xInputIndex < cmdMAX_INPUT_SIZE )
							{
								cInputString[ xInputIndex ] = cRxedChar;
								xInputIndex++;
							}
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
		CDC_Device_SendData( &xVirtualCOMPort, ( const char * const ) pucMessage, strlen( ( const char * ) pucMessage ) );
		xSemaphoreGive( xCDCMutex );
	}
}
/*-----------------------------------------------------------*/

static void prvNotifyTaskOfUSBEvent( void )
{
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	/* 'Give' the semaphore that signals the arrival of new data to the command
	console task. */
	configASSERT( xCDCEventSemaphore );
	xSemaphoreGiveFromISR( xCDCEventSemaphore, &xHigherPriorityTaskWoken );
	portEND_SWITCHING_ISR( xHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/

/* Standard LPCUSB event handler. */
void EVENT_USB_Device_ConfigurationChanged( void )
{
	CDC_Device_ConfigureEndpoints( &xVirtualCOMPort );
	prvNotifyTaskOfUSBEvent();
}
/*-----------------------------------------------------------*/

/* Standard LPCUSB event handler. */
void EVENT_USB_Device_ControlRequest( void )
{
	CDC_Device_ProcessControlRequest( &xVirtualCOMPort );
	prvNotifyTaskOfUSBEvent();
}
/*-----------------------------------------------------------*/

/* Standard LPCUSB event handler. */
void EVENT_USB_Device_Connect(void)
{
	prvNotifyTaskOfUSBEvent();
}
/*-----------------------------------------------------------*/

/* Standard LPCUSB event handler. */
void EVENT_USB_Device_Disconnect(void)
{
	prvNotifyTaskOfUSBEvent();
}
/*-----------------------------------------------------------*/

/* Standard LPCUSB event handler. */
void EVENT_CDC_Device_LineEncodingChanged(USB_ClassInfo_CDC_Device_t *const CDCInterfaceInfo)
{
	prvNotifyTaskOfUSBEvent();
}
/*-----------------------------------------------------------*/

/* Standard LPCUSB event handler. */
void EVENT_CDC_Device_ControLineStateChanged(USB_ClassInfo_CDC_Device_t *const CDCInterfaceInfo)
{
	prvNotifyTaskOfUSBEvent();
}

