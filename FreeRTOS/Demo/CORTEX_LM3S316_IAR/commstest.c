/*
 * FreeRTOS V202107.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

/*
 * The comms test Rx and Tx task and co-routine.  See the comments at the top
 * of main.c for full information.
 */


/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "croutine.h"

/* Demo application include files. */
#include "partest.h"

/* Library include files. */
#include "DriverLib.h"

/* The LED's toggled by the various tasks. */
#define commsFAIL_LED			( 7 )
#define commsRX_LED			( 6 )
#define commsTX_LED			( 5 )

/* The length of the queue used to pass received characters to the Comms Rx
task. */
#define commsRX_QUEUE_LEN			( 5 )

/* The baud rate used by the UART comms tasks/co-routine. */
#define commsBAUD_RATE				( 57600 )

/* FIFO setting for the UART.  The FIFO is not used to create a better test. */
#define commsFIFO_SET				( 0x10 )

/* The string that is transmitted on the UART contains sequentially the
characters from commsFIRST_TX_CHAR to commsLAST_TX_CHAR. */
#define commsFIRST_TX_CHAR '0'
#define commsLAST_TX_CHAR 'z'

/* Just used to walk through the program memory in order that some random data
can be generated. */
#define commsTOTAL_PROGRAM_MEMORY ( ( unsigned long * ) ( 8 * 1024 ) )
#define commsFIRST_PROGRAM_BYTES ( ( unsigned long * ) 4 )

/* The time between transmissions of the string on UART 0.   This is pseudo
random in order to generate a bit or randomness to when the interrupts occur.*/
#define commsMIN_TX_DELAY			( 40 / portTICK_PERIOD_MS )
#define commsMAX_TX_DELAY			( ( TickType_t ) 0x7f )
#define commsOFFSET_TIME			( ( TickType_t ) 3 )

/* The time the Comms Rx task should wait to receive a character.  This should
be slightly longer than the time between transmissions.  If we do not receive
a character after this time then there must be an error in the transmission or
the timing of the transmission. */
#define commsRX_DELAY			( commsMAX_TX_DELAY + 20 )


static unsigned portBASE_TYPE uxCommsErrorStatus = pdPASS;

/* The queue used to pass characters out of the ISR. */
static QueueHandle_t xCommsQueue;

/* The next character to transmit. */
static char cNextChar;

/*-----------------------------------------------------------*/

void vSerialInit( void )
{
	/* Create the queue used to communicate between the UART ISR and the Comms
	Rx task. */
	xCommsQueue = xQueueCreate( commsRX_QUEUE_LEN, sizeof( char ) );

	/* Enable the UART.  GPIOA has already been initialised. */
	SysCtlPeripheralEnable(SYSCTL_PERIPH_UART0);

	/* Set GPIO A0 and A1 as peripheral function.  They are used to output the
	UART signals. */
	GPIODirModeSet( GPIO_PORTA_BASE, GPIO_PIN_0 | GPIO_PIN_1, GPIO_DIR_MODE_HW );

	/* Configure the UART for 8-N-1 operation. */
	UARTConfigSetExpClk( UART0_BASE, SysCtlClockGet(), commsBAUD_RATE, UART_CONFIG_WLEN_8 | UART_CONFIG_PAR_NONE | UART_CONFIG_STOP_ONE );

	/* We dont want to use the fifo.  This is for test purposes to generate
	as many interrupts as possible. */
	HWREG( UART0_BASE + UART_O_LCR_H ) &= ~commsFIFO_SET;

	/* Enable both Rx and Tx interrupts. */
	HWREG( UART0_BASE + UART_O_IM ) |= ( UART_INT_TX | UART_INT_RX );
	IntPrioritySet( INT_UART0, configKERNEL_INTERRUPT_PRIORITY );
	IntEnable( INT_UART0 );
}
/*-----------------------------------------------------------*/

void vSerialTxCoRoutine( CoRoutineHandle_t xHandle, unsigned portBASE_TYPE uxIndex )
{
TickType_t xDelayPeriod;
static unsigned long *pulRandomBytes = commsFIRST_PROGRAM_BYTES;

	/* Co-routine MUST start with a call to crSTART. */
	crSTART( xHandle );

	for(;;)
    {	
		/* Was the previously transmitted string received correctly? */
		if( uxCommsErrorStatus != pdPASS )
		{
			/* An error was encountered so set the error LED. */
			vParTestSetLED( commsFAIL_LED, pdTRUE );
		}

		/* The next character to Tx is the first in the string. */
		cNextChar = commsFIRST_TX_CHAR;

		UARTIntDisable( UART0_BASE, UART_INT_TX );
		{
			/* Send the first character. */
			if( !( HWREG( UART0_BASE + UART_O_FR ) & UART_FR_TXFF ) )
			{
				HWREG( UART0_BASE + UART_O_DR ) = cNextChar;
			}

			/* Move the variable to the char to Tx on so the ISR transmits
			the next character in the string once this one has completed. */
			cNextChar++;
		}
		UARTIntEnable(UART0_BASE, UART_INT_TX);

		/* Toggle the LED to show a new string is being transmitted. */
        vParTestToggleLED( commsTX_LED );

		/* Delay before we start the string off again.  A pseudo-random delay
		is used as this will provide a better test. */
		xDelayPeriod = xTaskGetTickCount() + ( *pulRandomBytes );

		pulRandomBytes++;
		if( pulRandomBytes > commsTOTAL_PROGRAM_MEMORY )
		{
			pulRandomBytes = commsFIRST_PROGRAM_BYTES;
		}

		/* Make sure we don't wait too long... */
		xDelayPeriod &= commsMAX_TX_DELAY;

		/* ...but we do want to wait. */
		if( xDelayPeriod < commsMIN_TX_DELAY )
		{
			xDelayPeriod = commsMIN_TX_DELAY;
		}

		/* Block for the random(ish) time. */
		crDELAY( xHandle, xDelayPeriod );
    }

	/* Co-routine MUST end with a call to crEND. */
	crEND();
}
/*-----------------------------------------------------------*/

void vUART_ISR( void )
{
unsigned long ulStatus;
char cRxedChar;
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	/* What caused the interrupt. */
	ulStatus = UARTIntStatus( UART0_BASE, pdTRUE );

	/* Clear the interrupt. */
	UARTIntClear( UART0_BASE, ulStatus );

	/* Was an Rx interrupt pending? */
	if( ulStatus & UART_INT_RX )
	{
		if( ( HWREG(UART0_BASE + UART_O_FR ) & UART_FR_RXFF ) )
		{
			/* Get the char from the buffer and post it onto the queue of
			Rxed chars.  Posting the character should wake the task that is
			blocked on the queue waiting for characters. */
			cRxedChar = ( char ) HWREG( UART0_BASE + UART_O_DR );
			xQueueSendFromISR( xCommsQueue, &cRxedChar, &xHigherPriorityTaskWoken );
		}		
	}

	/* Was a Tx interrupt pending? */
	if( ulStatus & UART_INT_TX )
	{
		/* Send the next character in the string.  We are not using the FIFO. */
		if( cNextChar <= commsLAST_TX_CHAR )
		{
			if( !( HWREG( UART0_BASE + UART_O_FR ) & UART_FR_TXFF ) )
			{
				HWREG( UART0_BASE + UART_O_DR ) = cNextChar;
			}
			cNextChar++;
		}
	}
	
	/* If a task was woken by the character being received then we force
	a context switch to occur in case the task is of higher priority than
	the currently executing task (i.e. the task that this interrupt
	interrupted.) */
	portEND_SWITCHING_ISR( xHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/

void vCommsRxTask( void * pvParameters )
{
static char cRxedChar, cExpectedChar;

	/* Set the char we expect to receive to the start of the string. */
	cExpectedChar = commsFIRST_TX_CHAR;

	for( ;; )
	{
		/* Wait for a character to be received. */
		xQueueReceive( xCommsQueue, ( void * ) &cRxedChar, commsRX_DELAY );

		/* Was the character received (if any) the expected character. */
		if( cRxedChar != cExpectedChar )
		{
			/* Got an unexpected character.  This can sometimes occur when
			reseting the system using the debugger leaving characters already
			in the UART registers. */
			uxCommsErrorStatus = pdFAIL;

			/* Resync by waiting for the end of the current string. */
			while( cRxedChar != commsLAST_TX_CHAR )
			{
				while( !xQueueReceive( xCommsQueue, ( void * ) &cRxedChar, portMAX_DELAY ) );
			}

			/* The next expected character is the start of the string again. */
			cExpectedChar = commsFIRST_TX_CHAR;
		}
		else
		{
			if( cExpectedChar == commsLAST_TX_CHAR )
			{
				/* We have reached the end of the string - we now expect to
				receive the first character in the string again.   The LED is
				toggled to indicate that the entire string was received without
				error. */
				vParTestToggleLED( commsRX_LED );
				cExpectedChar = commsFIRST_TX_CHAR;
			}
			else
			{
				/* We got the expected character, we now expect to receive the
				next character in the string. */
				cExpectedChar++;
			}
		}
	}
}
/*-----------------------------------------------------------*/

unsigned portBASE_TYPE uxGetCommsStatus( void )
{
	return uxCommsErrorStatus;
}
