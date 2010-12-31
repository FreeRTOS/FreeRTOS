/*
    FreeRTOS V6.1.0 - Copyright (C) 2010 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS books - available as PDF or paperback  *
    *                                                                         *
    *        "Using the FreeRTOS Real Time Kernel - a Practical Guide"        *
    *                  http://www.FreeRTOS.org/Documentation                  *
    *                                                                         *
    * A pdf reference manual is also available.  Both are usually delivered   *
    * to your inbox within 20 minutes to two hours when purchased between 8am *
    * and 8pm GMT (although please allow up to 24 hours in case of            *
    * exceptional circumstances).  Thank you for your support!                *
    *                                                                         *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    ***NOTE*** The exception to the GPL is included to allow you to distribute
    a combined work that includes FreeRTOS without being obliged to provide the
    source code for proprietary components outside of the FreeRTOS kernel.
    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
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


/* BASIC INTERRUPT DRIVEN SERIAL PORT DRIVER.
 *
 * This file only supports UART A0 in loopback mode, and has not been tested
 * for real UART operation (only loopback mode) so is not guaranteed to have
 * a correct baud rate configuration.
 */

/* Standard includes. */
#include <stdlib.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "queue.h"
#include "task.h"

/* Demo application includes. */
#include "serial.h"

/* HAL includes. */
#include "hal_usb.h"

/* Constants required to setup the hardware. */
#define serTX_AND_RX			( ( unsigned portCHAR ) 0x03 )

/* Misc. constants. */
#define serNO_BLOCK				( ( portTickType ) 0 )

/* The queue used to hold received characters. */
static xQueueHandle xRxedChars;

/* The queue used to hold characters waiting transmission. */
static xQueueHandle xCharsForTx;

/*-----------------------------------------------------------*/

xComPortHandle xSerialPortInitMinimal( unsigned portLONG ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
unsigned portLONG ulBaudRateCount;

	/* Initialise the hardware. */

	/* Generate the baud rate constants for the wanted baud rate. */
	ulBaudRateCount = configCPU_CLOCK_HZ / ulWantedBaud;

	portENTER_CRITICAL();
	{
		/* Create the queues used by the com test task. */
		xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed portCHAR ) );
		xCharsForTx = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed portCHAR ) );

#if 0
		/* Reset UART. */
		UCA0CTL1 |= UCSWRST;

		/* Use SMCLK. */
		UCA0CTL1 = UCSSEL0 | UCSSEL1;
		
		/* Setup baud rate low byte. */
		UCA0BR0 = ( unsigned portCHAR ) ( ulBaudRateCount & ( unsigned portLONG ) 0xff );

		/* Setup baud rate high byte. */
		ulBaudRateCount >>= 8UL;
		UCA0BR1 = ( unsigned portCHAR ) ( ulBaudRateCount & ( unsigned portLONG ) 0xff );

		/* UCLISTEN sets loopback mode! */
		UCA0STAT = UCLISTEN;

		/* Clear interrupts. */
//		UCA0IFG = 0;
		
		/* Enable interrupts. */
		UCA0IE |= UCRXIE;
		
		/* Take out of reset. */
		UCA0CTL1 &= ~UCSWRST;
#else
	USB_PORT_SEL |= USB_PIN_RXD + USB_PIN_TXD;
	USB_PORT_DIR |= USB_PIN_TXD;
	USB_PORT_DIR &= ~USB_PIN_RXD;
	
	UCA1CTL1 |= UCSWRST;                          //Reset State
	UCA1CTL0 = UCMODE_0;
	
	UCA1CTL0 &= ~UC7BIT;                      // 8bit char
	UCA1CTL1 |= UCSSEL_2;
//	UCA1BR0 = 16;                             // 8Mhz/57600=138
//	UCA1BR1 = 1;
		/* Setup baud rate low byte. */
		UCA0BR0 = ( unsigned portCHAR ) ( ulBaudRateCount & ( unsigned portLONG ) 0xff );

		/* Setup baud rate high byte. */
		ulBaudRateCount >>= 8UL;
		UCA0BR1 = ( unsigned portCHAR ) ( ulBaudRateCount & ( unsigned portLONG ) 0xff );

	UCA1MCTL = 0xE;
	UCA1CTL1 &= ~UCSWRST;
	UCA1IE |= UCRXIE;
#endif
	}
	portEXIT_CRITICAL();
	
	/* Unlike other ports, this serial code does not allow for more than one
	com port.  We therefore don't return a pointer to a port structure and can
	instead just return NULL. */
	return NULL;
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, signed portCHAR *pcRxedChar, portTickType xBlockTime )
{
	/* Get the next character from the buffer.  Return false if no characters
	are available, or arrive before xBlockTime expires. */
	if( xQueueReceive( xRxedChars, pcRxedChar, xBlockTime ) )
	{
		return pdTRUE;
	}
	else
	{
		return pdFALSE;
	}
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, signed portCHAR cOutChar, portTickType xBlockTime )
{
signed portBASE_TYPE xReturn;

	xReturn = xQueueSend( xCharsForTx, &cOutChar, xBlockTime );
	UCA0IE |= UCTXIE;

	return xReturn;
}
/*-----------------------------------------------------------*/
char cTxedBytes[ 512 ];
char cRxedBytes[ 512 ];
volatile int xIndex = 0;
volatile int xIndex2 = 0;

#pragma vector=USCI_A0_VECTOR
static __interrupt void prvUSCI_A0_ISR( void )
{
signed portCHAR cChar;
portBASE_TYPE xTaskWoken = pdFALSE;
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	while( UCA0IFG & UCRXIFG )
	{
		/* Get the character from the UART and post it on the queue of Rxed
		characters. */
		cChar = UCA0RXBUF;

if( xIndex2 < 500 )
{
	cRxedBytes[ xIndex2++ ] = cChar;
}

		xQueueSendFromISR( xRxedChars, &cChar, &xHigherPriorityTaskWoken );
	}
	
	if( UCA0IFG & UCTXIFG )
	{
		/* The previous character has been transmitted.  See if there are any
		further characters waiting transmission. */
		if( xQueueReceiveFromISR( xCharsForTx, &cChar, &xTaskWoken ) == pdTRUE )
		{
if( xIndex < 500 )
{
	cTxedBytes[ xIndex++ ] = cChar;
}

			/* There was another character queued - transmit it now. */
			UCA0TXBUF = cChar;
		}
		else
		{
			/* There were no other characters to transmit - disable the Tx
			interrupt. */
			UCA0IE &= ~UCTXIE;
		}
	}

	__bic_SR_register_on_exit( SCG1 + SCG0 + OSCOFF + CPUOFF );	
	portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
}


