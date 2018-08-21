/*
 * FreeRTOS Kernel V10.1.0
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
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
#include "event_groups.h"

/* Example includes. */
#include "FreeRTOS_CLI.h"

/* Library includes. */
#include "board.h"
#include "chip.h"
#include "USBD.h"
#include "CDCDSerialDriver.h"

/*-----------------------------------------------------------*/

/* Dimensions the buffer into which input characters are placed. */
#define cmdMAX_INPUT_SIZE		50

/* DEL acts as a backspace. */
#define cmdASCII_DEL		( 0x7F )

/* The bits in the event group used to signal USB interrupt events to this
task. */
#define cmdRX_COMPLETE_BIT	( 0x01 )
#define cmdTX_COMPLETE_BIT	( 0x02 )
/*-----------------------------------------------------------*/

/*
 * The task that implements the command console processing.
 */
static void prvCDCCommandConsoleTask( void *pvParameters );

/*
 * Initialise the USB hardware and driver.
 */
static void prvCDCInit( void );

/*
 * Handler installed on the VBUS pin to detect connect() and disconnect()
 * events.
 */
static void prvVBusISRHandler( void );

/*
 * USB handler defined by the driver, installed after the CDC driver has been
 * initialised.
 */
extern void USBD_IrqHandler( void );

/*
 * The function that creates the CLI task.
 */
void vUSBCommandConsoleStart( uint16_t usStackSize, UBaseType_t uxPriority );

/*
 * Send xDataLength bytes from pcData to the CDC port.
 */
static void prvCDCSend( const char *pcData, size_t xDataLenth );

/*
 * Initiate a receive into the Rx buffer from the CDC port, then wait for a
 * period for characters to be received.
 */
static void prvCDCGetChar( void );

/*
 * Configure VBus pins and interrupts, and check for connection.
 */
static void prvConfigureVBus( void );

/*
 * Callback which is invoked when a CDC read completes.  This callback is
 * passed as a parameter to the CDC receive function.
 */
static void prvCDCDataReceivedCallback( uint32_t ulUnused, uint8_t ucStatus, uint32_t ulBytesReceived, uint32_t ulBytesRemaining );

/*
 * Callback which is invoked when a CDC write completes.  This callback is
 * passed as a parameter to the CDC send function.
 */
static void prvCDCDataTransmittedCallback( uint32_t ulUnused, uint8_t ucStatus, uint32_t ulBytesSent, uint32_t ulBytesRemaining );

/*
 * Keep trying to initiate an Rx until it is started successfully
 */
static void prvStartRx( void );

/*-----------------------------------------------------------*/

/* Const messages output by the command console. */
static const char * const pcWelcomeMessage = "FreeRTOS command server.\r\nType Help to view a list of registered commands.\r\n\r\n>";
static const char * const pcEndOfOutputMessage = "\r\n[Press ENTER to execute the previous command again]\r\n>";
static const char * const pcNewLine = "\r\n";

/* Buffer into which received characters are placed. */
static char pcRxBuffer[ cmdMAX_INPUT_SIZE ];

/* The number of bytes in pcRxBuffer that have not yet been read. */
static uint32_t ulBytesAvailable = 0;

/* Used to unblock the task when bytes are received and when bytes have
completed sending. */
static EventGroupHandle_t xCDCEventBits;

/*-----------------------------------------------------------*/

void vUSBCommandConsoleStart( uint16_t usStackSize, UBaseType_t uxPriority )
{
	/* Event group used to indicate that bytes are available in the Rx buffer
	or that bytes have finished sending. */
	xCDCEventBits = xEventGroupCreate();
	configASSERT( xCDCEventBits );

	/* Create the task that handles the console itself. */
	xTaskCreate( 	prvCDCCommandConsoleTask,	/* The task that implements the command console. */
					"CLI",						/* Text name assigned to the task.  This is just to assist debugging.  The kernel does not use this name itself. */
					usStackSize,				/* The size of the stack allocated to the task. */
					NULL,						/* The parameter is not used, so NULL is passed. */
					uxPriority,					/* The priority allocated to the task. */
					NULL );						/* A handle is not required, so just pass NULL. */
}
/*-----------------------------------------------------------*/

static void prvCDCCommandConsoleTask( void *pvParameters )
{
uint8_t ucInputIndex = 0;
char *pcOutputString, cRxedChar;
static char cInputString[ cmdMAX_INPUT_SIZE ], cLastInputString[ cmdMAX_INPUT_SIZE ];
BaseType_t xReturned;
uint32_t ulBufferIndex = 0;

	( void ) pvParameters;

	/* Obtain the address of the output buffer.  Note there is no mutual
	exclusion on this buffer as it is assumed only one command console interface
	will be used at any one time. */
	pcOutputString = FreeRTOS_CLIGetOutputBuffer();

	/* Initialise the CDC driver. */
	prvCDCInit();

	/* Start receiving into the buffer. */
	prvStartRx();

	/* Send the welcome message. */
	prvCDCSend( pcWelcomeMessage, strlen( pcWelcomeMessage ) );

	for( ;; )
	{
		/* Wait for my characters to be available. */
		prvCDCGetChar();

		/* Process the bytes char for char on the assumption that as input comes
		from typing it is unlikely that more than a single byte will be received
		at a time anyway. */
		while( ulBytesAvailable > 0 )
		{
			/* Read next byte from the rx buffer. */
			cRxedChar = pcRxBuffer[ ulBufferIndex ];

			taskENTER_CRITICAL();
			{
				ulBytesAvailable--;
			}
			taskEXIT_CRITICAL();

			/* Echo the character back. */
			prvCDCSend( &cRxedChar, sizeof( cRxedChar ) );

			/* Was it the end of the line? */
			if( cRxedChar == '\n' || cRxedChar == '\r' )
			{
				/* Just to space the output from the input. */
				prvCDCSend( pcNewLine, strlen( pcNewLine ) );

				/* See if the command is empty, indicating that the last command
				is to be executed again. */
				if( ucInputIndex == 0 )
				{
					/* Copy the last command back into the input string. */
					strcpy( cInputString, cLastInputString );
				}

				/* Pass the received command to the command interpreter.  The
				command interpreter is called repeatedly until it returns
				pdFALSE	(indicating there is no more output) as it might
				generate more than one string. */
				do
				{
					/* Get the next output string from the command interpreter. */
					xReturned = FreeRTOS_CLIProcessCommand( cInputString, pcOutputString, configCOMMAND_INT_MAX_OUTPUT_SIZE );

					/* Write the generated string to the UART. */
					prvCDCSend( pcOutputString, strlen( pcOutputString ) );

				} while( xReturned != pdFALSE );

				/* All the strings generated by the input command have been
				sent.  Clear the input string ready to receive the next command.
				Remember the command that was just processed first in case it is
				to be processed again. */
				strcpy( cLastInputString, cInputString );
				ucInputIndex = 0;
				memset( cInputString, 0x00, cmdMAX_INPUT_SIZE );

				prvCDCSend( pcEndOfOutputMessage, strlen( pcEndOfOutputMessage ) );
			}
			else
			{
				if( cRxedChar == '\r' )
				{
					/* Ignore the character. */
				}
				else if( ( cRxedChar == '\b' ) || ( cRxedChar == cmdASCII_DEL ) )
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
					/* A character was entered.  Add it to the string entered so
					far.  When a \n is entered the complete	string will be
					passed to the command interpreter. */
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

			/* Move onto the next byte the next time around. */
			ulBufferIndex++;
			if( ulBufferIndex >= cmdMAX_INPUT_SIZE )
			{
				ulBufferIndex = 0;
			}
		}
	}
}
/*-----------------------------------------------------------*/

static void prvCDCInit( void )
{
extern WEAK const USBDDriverDescriptors cdcdSerialDriverDescriptors;

	/* If they are present, configure Vbus & Wake-up pins */
	PIO_InitializeInterrupts( 0 );

	/* CDC serial driver initialization */
	CDCDSerialDriver_Initialize( &cdcdSerialDriverDescriptors );

	/* Configure VBus pins and interrupts, and check for connection. */
	prvConfigureVBus();
}
/*-----------------------------------------------------------*/

static void prvCDCSend( const char *pcData, size_t xDataLength )
{
const TickType_t xTransferCompleteDelay = pdMS_TO_TICKS( 500UL );

	( void ) pcData;
	( void ) xDataLength;

	if( xDataLength > 0 )
	{
		if( CDCDSerialDriver_Write( ( void * ) pcData, xDataLength, ( TransferCallback ) prvCDCDataTransmittedCallback, 0 ) == USBD_STATUS_SUCCESS )
		{
			/* Wait for the transfer to complete. */
			xEventGroupWaitBits(	xCDCEventBits,
									cmdTX_COMPLETE_BIT, /* The bit to wait for. */
									pdTRUE, /* Clear the bit before exiting the function. */
									pdFALSE, /* Only need to wait for one bit anyway. */
									xTransferCompleteDelay ); /* The maximum time to wait for the event. */
		}
	}
}
/*-----------------------------------------------------------*/

static void prvStartRx( void )
{
const TickType_t xFailedReadDelay = pdMS_TO_TICKS( 150UL );

	while( CDCDSerialDriver_Read( pcRxBuffer, cmdMAX_INPUT_SIZE, ( TransferCallback ) prvCDCDataReceivedCallback, 0 ) != USBD_STATUS_SUCCESS )
	{
		/* Maybe the CDC is not connected. */
		vTaskDelay( xFailedReadDelay );
	}
}
/*-----------------------------------------------------------*/

static void prvCDCGetChar( void )
{
const TickType_t xTransferCompleteDelay = pdMS_TO_TICKS( 750UL );

	if( ulBytesAvailable == 0 )
	{
		/* Wait for a transfer to complete. */
		xEventGroupWaitBits(	xCDCEventBits,
								cmdRX_COMPLETE_BIT, /* The bit to wait for. */
								pdTRUE, /* Clear the bit before exiting the function. */
								pdFALSE, /* Only need to wait for one bit anyway. */
								xTransferCompleteDelay ); /* The maximum time to wait for the event. */
	}
}
/*-----------------------------------------------------------*/

static void prvVBusISRHandler( void )
{
const Pin xVBusPin = PIN_USB_VBUS;

    /* Check current level on VBus to detect a connect/disconnect. */
    if( PIO_Get( &xVBusPin ) != 0 )
    {
        USBD_Connect();
    }
    else
    {
        USBD_Disconnect();
    }
}
/*-----------------------------------------------------------*/

static void prvCDCDataReceivedCallback( uint32_t ulUnused, uint8_t ucStatus, uint32_t ulBytesReceived, uint32_t ulBytesRemaining )
{
BaseType_t xHigherPriorityTaskWoken = pdFALSE;
static uint32_t ulNextRxPosition = 0;

	( void ) ulUnused;
	( void ) ucStatus;
	( void ) ulBytesRemaining;

	/* If bytes were received then store the number of bytes placed into the Rx
	buffer. */
	if( ucStatus == USBD_STATUS_SUCCESS )
	{
		ulBytesAvailable += ulBytesReceived;

		/* Restart the Rx position from a buffer position past the newly
		received data. */
		ulNextRxPosition += ulBytesReceived;

		if( ulNextRxPosition >= cmdMAX_INPUT_SIZE )
		{
			ulNextRxPosition = 0;
		}
		CDCDSerialDriver_Read( pcRxBuffer + ulNextRxPosition, cmdMAX_INPUT_SIZE - ulNextRxPosition, ( TransferCallback ) prvCDCDataReceivedCallback, 0 );

		/* Ensure the task knows new data is available. */
		xEventGroupSetBitsFromISR( xCDCEventBits, cmdRX_COMPLETE_BIT, &xHigherPriorityTaskWoken );
		portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
	}
}
/*-----------------------------------------------------------*/

static void prvCDCDataTransmittedCallback( uint32_t ulUnused, uint8_t ucStatus, uint32_t ulBytesSent, uint32_t ulBytesRemaining )
{
BaseType_t xHigherPriorityTaskWoken = pdFALSE;

	( void ) ulUnused;
	( void ) ucStatus;
	( void ) ulBytesRemaining;
	( void ) ulBytesSent;

	xEventGroupSetBitsFromISR( xCDCEventBits, cmdTX_COMPLETE_BIT, &xHigherPriorityTaskWoken );
	portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/

static void prvConfigureVBus( void )
{
const Pin xVBusPin = PIN_USB_VBUS;
const uint32_t ulPriority = 7; /* Highest. */

	/* Configure PIO to generate an interrupt on status change. */
    PIO_Configure( &xVBusPin, 1 );
    PIO_ConfigureIt( &xVBusPin );

	/* Ensure interrupt is disabled before setting the mode and installing the
	handler.  The priority of the tick interrupt should always be set to the
	lowest possible. */
	AIC->AIC_SSR  = ID_PIOE;
	AIC->AIC_IDCR = AIC_IDCR_INTD;
	AIC->AIC_SMR  = AIC_SMR_SRCTYPE_EXT_POSITIVE_EDGE | ulPriority;
	AIC->AIC_SVR = ( uint32_t ) prvVBusISRHandler;

	/* Start with the interrupt clear. */
	AIC->AIC_ICCR = AIC_ICCR_INTCLR;
	PIO_EnableIt( &xVBusPin );
    AIC_EnableIT( ID_PIOE );

	/* Check current level on VBus */
	if( PIO_Get( &xVBusPin ) != pdFALSE )
	{
		/* If VBUS present, force the connect */
		USBD_Connect();
	}
	else
	{
		USBD_Disconnect();
	}
}
/*-----------------------------------------------------------*/

void USBDCallbacks_Initialized( void )
{
	/* CDC specific re-implementation of weak callback function.  Invoked after
	the USB driver has been initialised. By default, configures the UDP/UDPHS
	interrupt.  The interrupt priority is set to the highest to ensure the
	interrupt nesting tests interfer as little as possible with the USB. */
	AIC_EnableIT( ID_UDPHS );
}
/*-----------------------------------------------------------*/

void USBDDriverCallbacks_ConfigurationChanged( uint8_t ucConfigNumber )
{
	/* CDC specific re-implementation of weak callback function.  Invoked when
	the configuration of the device changes. Parse used endpoints. */
	CDCDSerialDriver_ConfigurationChangedHandler( ucConfigNumber );
}
/*-----------------------------------------------------------*/

void USBDCallbacks_RequestReceived( const USBGenericRequest *pxRequest )
{
	/* CDC specific re-implementation of weak callback function.  Invoked when
	a new SETUP request is received from the host. */
	CDCDSerialDriver_RequestHandler( pxRequest );
}
/*-----------------------------------------------------------*/
