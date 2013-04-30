/*
    FreeRTOS V7.4.2 - Copyright (C) 2013 Real Time Engineers Ltd.

    FEATURES AND PORTS ARE ADDED TO FREERTOS ALL THE TIME.  PLEASE VISIT
    http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

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

    >>>>>>NOTE<<<<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
    details. You should have received a copy of the GNU General Public License
    and the FreeRTOS license exception along with FreeRTOS; if not it can be
    viewed here: http://www.freertos.org/a00114.html and also obtained by
    writing to Real Time Engineers Ltd., contact details for whom are available
    on the FreeRTOS WEB site.

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
    including FreeRTOS+Trace - an indispensable productivity tool, and our new
    fully thread aware and reentrant UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High 
    Integrity Systems, who sell the code with commercial support, 
    indemnification and middleware, under the OpenRTOS brand.
    
    http://www.SafeRTOS.com - High Integrity Systems also provide a safety 
    engineered and independently SIL3 certified version for use in safety and 
    mission critical applications that require provable dependability.
*/


/* BASIC INTERRUPT DRIVEN SERIAL PORT DRIVER.   
 * 
 * This file only supports UART 1
 */

/* Standard includes. */
#include <stdlib.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "queue.h"
#include "task.h"

/* Demo application includes. */
#include "serial.h"

/* Constants required to setup the hardware. */
#define serTX_AND_RX			( ( unsigned char ) 0x03 )

/* Misc. constants. */
#define serNO_BLOCK				( ( portTickType ) 0 )

/* Enable the UART Tx interrupt. */
#define vInterruptOn() IFG2 |= UTXIFG1

/* The queue used to hold received characters. */
static xQueueHandle xRxedChars; 

/* The queue used to hold characters waiting transmission. */
static xQueueHandle xCharsForTx; 

static volatile short sTHREEmpty;

/*-----------------------------------------------------------*/

xComPortHandle xSerialPortInitMinimal( unsigned long ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
unsigned long ulBaudRateCount;

	/* Initialise the hardware. */

	/* Generate the baud rate constants for the wanted baud rate. */
	ulBaudRateCount = configCPU_CLOCK_HZ / ulWantedBaud;

	portENTER_CRITICAL();
	{
		/* Create the queues used by the com test task. */
		xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed char ) );
		xCharsForTx = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed char ) );

		/* Reset UART. */
		UCTL1 |= SWRST;

		/* Set pin function. */
		P4SEL |= serTX_AND_RX;

		/* All other bits remain at zero for n, 8, 1 interrupt driven operation. 
		LOOPBACK MODE!*/
		U1CTL |= CHAR + LISTEN;
		U1TCTL |= SSEL1;

		/* Setup baud rate low byte. */
		U1BR0 = ( unsigned char ) ( ulBaudRateCount & ( unsigned long ) 0xff );

		/* Setup baud rate high byte. */
		ulBaudRateCount >>= 8UL;
		U1BR1 = ( unsigned char ) ( ulBaudRateCount & ( unsigned long ) 0xff );

		/* Enable ports. */
		ME2 |= UTXE1 + URXE1;

		/* Set. */
		UCTL1 &= ~SWRST;

		/* Nothing in the buffer yet. */
		sTHREEmpty = pdTRUE;

		/* Enable interrupts. */
		IE2 |= URXIE1 + UTXIE1;
	}
	portEXIT_CRITICAL();
	
	/* Unlike other ports, this serial code does not allow for more than one
	com port.  We therefore don't return a pointer to a port structure and can
	instead just return NULL. */
	return NULL;
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, signed char *pcRxedChar, portTickType xBlockTime )
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

signed portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, signed char cOutChar, portTickType xBlockTime )
{
signed portBASE_TYPE xReturn;

	/* Transmit a character. */

	portENTER_CRITICAL();
	{
		if( sTHREEmpty == pdTRUE )
		{
			/* If sTHREEmpty is true then the UART Tx ISR has indicated that 
			there are no characters queued to be transmitted - so we can
			write the character directly to the shift Tx register. */
			sTHREEmpty = pdFALSE;
			U1TXBUF = cOutChar;
			xReturn = pdPASS;
		}
		else
		{
			/* sTHREEmpty is false, so there are still characters waiting to be
			transmitted.  We have to queue this character so it gets 
			transmitted	in turn. */

			/* Return false if after the block time there is no room on the Tx 
			queue.  It is ok to block inside a critical section as each task
			maintains it's own critical section status. */
			xReturn = xQueueSend( xCharsForTx, &cOutChar, xBlockTime );

			/* Depending on queue sizing and task prioritisation:  While we 
			were blocked waiting to post on the queue interrupts were not 
			disabled.  It is possible that the serial ISR has emptied the 
			Tx queue, in which case we need to start the Tx off again
			writing directly to the Tx register. */
			if( ( sTHREEmpty == pdTRUE ) && ( xReturn == pdPASS ) )
			{
				/* Get back the character we just posted. */
				xQueueReceive( xCharsForTx, &cOutChar, serNO_BLOCK );
				sTHREEmpty = pdFALSE;
				U1TXBUF = cOutChar;
			}
		}
	}
	portEXIT_CRITICAL();

	return pdPASS;
}
/*-----------------------------------------------------------*/

#if configINTERRUPT_EXAMPLE_METHOD == 1

	/*
	 * UART RX interrupt service routine.
	 */
	void vRxISR( void ) __interrupt[ UART1RX_VECTOR ]
	{
	signed char cChar;
	portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;
	
		/* Get the character from the UART and post it on the queue of Rxed 
		characters. */
		cChar = U1RXBUF;
	
		xQueueSendFromISR( xRxedChars, &cChar, &xHigherPriorityTaskWoken );

		if( xHigherPriorityTaskWoken )
		{
			/*If the post causes a task to wake force a context switch 
			as the woken task may have a higher priority than the task we have 
			interrupted. */
			taskYIELD();
		}

        /* Make sure any low power mode bits are clear before leaving the ISR. */
        __bic_SR_register_on_exit( SCG1 + SCG0 + OSCOFF + CPUOFF );
	}
	/*-----------------------------------------------------------*/
	
	/*
	 * UART Tx interrupt service routine.
	 */
	void vTxISR( void ) __interrupt[ UART1TX_VECTOR ]
	{
	signed char cChar;
	portBASE_TYPE xTaskWoken = pdFALSE;
	
		/* The previous character has been transmitted.  See if there are any
		further characters waiting transmission. */
	
		if( xQueueReceiveFromISR( xCharsForTx, &cChar, &xTaskWoken ) == pdTRUE )
		{
			/* There was another character queued - transmit it now. */
			U1TXBUF = cChar;
		}
		else
		{
			/* There were no other characters to transmit. */
			sTHREEmpty = pdTRUE;
		}

        /* Make sure any low power mode bits are clear before leaving the ISR. */
        __bic_SR_register_on_exit( SCG1 + SCG0 + OSCOFF + CPUOFF );
	}
    /*-----------------------------------------------------------*/

#elif configINTERRUPT_EXAMPLE_METHOD == 2

    /* This is a standard C function as an assembly file wrapper is used as an
    interrupt entry point. */
	void vRxISR( void )
	{
	signed char cChar;
	portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;
	
		/* Get the character from the UART and post it on the queue of Rxed 
		characters. */
		cChar = U1RXBUF;
	
		xQueueSendFromISR( xRxedChars, &cChar, &xHigherPriorityTaskWoken );

        /*If the post causes a task to wake force a context switch 
        as the woken task may have a higher priority than the task we have 
        interrupted. */
        portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
	}
	/*-----------------------------------------------------------*/
	
    /* This is a standard C function as an assembly file wrapper is used as an
    interrupt entry point. */
	void vTxISR( void )
	{
	signed char cChar;
	portBASE_TYPE xTaskWoken = pdFALSE;
	
		/* The previous character has been transmitted.  See if there are any
		further characters waiting transmission. */
	
		if( xQueueReceiveFromISR( xCharsForTx, &cChar, &xTaskWoken ) == pdTRUE )
		{
			/* There was another character queued - transmit it now. */
			U1TXBUF = cChar;
		}
		else
		{
			/* There were no other characters to transmit. */
			sTHREEmpty = pdTRUE;
		}
	}

#endif /* configINTERRUPT_EXAMPLE_METHOD */
/*-----------------------------------------------------------*/
