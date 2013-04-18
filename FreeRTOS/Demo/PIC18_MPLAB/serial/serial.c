/*
    FreeRTOS V7.4.1 - Copyright (C) 2013 Real Time Engineers Ltd.

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

/*
Changes from V1.2.5

	+  Clear overrun errors in the Rx ISR.  Overrun errors prevent any further
	   characters being received.

Changes from V2.0.0

	+ Use portTickType in place of unsigned pdLONG for delay periods.
	+ cQueueReieveFromISR() used in place of xQueueReceive() in ISR.
*/

/* BASIC INTERRUPT DRIVEN SERIAL PORT DRIVER. */

/* Scheduler header files. */
#include "FreeRTOS.h"
#include "task.h"
#include "serial.h"
#include "queue.h"

/*
 * Prototypes for ISR's.  The PIC architecture means that these functions
 * have to be called from port.c.  The prototypes are not however included
 * in the header as the header is common to all ports.
 */
void vSerialTxISR( void );
void vSerialRxISR( void );

/* Hardware pin definitions. */
#define serTX_PIN	TRISCbits.TRISC6
#define serRX_PIN	TRISCbits.TRISC7

/* Bit/register definitions. */
#define serINPUT				( 1 )
#define serOUTPUT				( 0 )
#define serTX_ENABLE			( ( unsigned short ) 1 )
#define serRX_ENABLE			( ( unsigned short ) 1 )
#define serHIGH_SPEED			( ( unsigned short ) 1 )
#define serCONTINUOUS_RX		( ( unsigned short ) 1 )
#define serCLEAR_OVERRUN		( ( unsigned short ) 0 )
#define serINTERRUPT_ENABLED 	( ( unsigned short ) 1 )
#define serINTERRUPT_DISABLED 	( ( unsigned short ) 0 )

/* All ISR's use the PIC18 low priority interrupt. */
#define							serLOW_PRIORITY ( 0 )

/*-----------------------------------------------------------*/

/* Queues to interface between comms API and interrupt routines. */
static xQueueHandle xRxedChars; 
static xQueueHandle xCharsForTx;

/*-----------------------------------------------------------*/

xComPortHandle xSerialPortInitMinimal( unsigned long ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
unsigned long ulBaud;

	/* Calculate the baud rate generator constant.
	SPBRG = ( (FOSC / Desired Baud Rate) / 16 ) - 1 */
	ulBaud = configCPU_CLOCK_HZ / ulWantedBaud;
	ulBaud /= ( unsigned long ) 16;
	ulBaud -= ( unsigned long ) 1;

	/* Create the queues used by the ISR's to interface to tasks. */
	xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( char ) );
	xCharsForTx = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( char ) );

	portENTER_CRITICAL();
	{
		/* Start with config registers cleared, so we can just set the wanted
		bits. */
		TXSTA = ( unsigned short ) 0;
		RCSTA = ( unsigned short ) 0;

		/* Set the baud rate generator using the above calculated constant. */
		SPBRG = ( unsigned char ) ulBaud;

		/* Setup the IO pins to enable the USART IO. */
		serTX_PIN = serOUTPUT;
		serRX_PIN = serINPUT;

		/* Set the serial interrupts to use the same priority as the tick. */
		IPR1bits.TXIP = serLOW_PRIORITY;
		IPR1bits.RCIP = serLOW_PRIORITY;

		/* Setup Tx configuration. */
		TXSTAbits.BRGH = serHIGH_SPEED;
		TXSTAbits.TXEN = serTX_ENABLE;

		/* Setup Rx configuration. */
		RCSTAbits.SPEN = serRX_ENABLE;
		RCSTAbits.CREN = serCONTINUOUS_RX;

		/* Enable the Rx interrupt now, the Tx interrupt will get enabled when
		we have data to send. */
		PIE1bits.RCIE = serINTERRUPT_ENABLED;
	}
	portEXIT_CRITICAL();

	/* Unlike other ports, this serial code does not allow for more than one
	com port.  We therefore don't return a pointer to a port structure and 
	can	instead just return NULL. */
	return NULL;
}
/*-----------------------------------------------------------*/

xComPortHandle xSerialPortInit( eCOMPort ePort, eBaud eWantedBaud, eParity eWantedParity, eDataBits eWantedDataBits, eStopBits eWantedStopBits, unsigned portBASE_TYPE uxBufferLength )
{
	/* This is not implemented in this port.
	Use xSerialPortInitMinimal() instead. */
}
/*-----------------------------------------------------------*/

portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, signed char *pcRxedChar, portTickType xBlockTime )
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

portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, signed char cOutChar, portTickType xBlockTime )
{
	/* Return false if after the block time there is no room on the Tx queue. */
	if( xQueueSend( xCharsForTx, ( const void * ) &cOutChar, xBlockTime ) != pdPASS )
	{
		return pdFAIL;
	}

	/* Turn interrupt on - ensure the compiler only generates a single 
	instruction for this. */
	PIE1bits.TXIE = serINTERRUPT_ENABLED;

	return pdPASS;
}
/*-----------------------------------------------------------*/

void vSerialClose( xComPortHandle xPort )
{
	/* Not implemented for this port.
	To implement, turn off the interrupts and delete the memory
	allocated to the queues. */
}
/*-----------------------------------------------------------*/

#pragma interruptlow vSerialRxISR save=PRODH, PRODL, TABLAT, section(".tmpdata")
void vSerialRxISR( void )
{
char cChar;
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	/* Get the character and post it on the queue of Rxed characters.
	If the post causes a task to wake force a context switch as the woken task
	may have a higher priority than the task we have interrupted. */
	cChar = RCREG;

	/* Clear any overrun errors. */
	if( RCSTAbits.OERR )
	{
		RCSTAbits.CREN = serCLEAR_OVERRUN;
		RCSTAbits.CREN = serCONTINUOUS_RX;	
	}

	xQueueSendFromISR( xRxedChars, ( const void * ) &cChar, &xHigherPriorityTaskWoken );

	if( xHigherPriorityTaskWoken )
	{
		taskYIELD();
	}
}
/*-----------------------------------------------------------*/

#pragma interruptlow vSerialTxISR save=PRODH, PRODL, TABLAT, section(".tmpdata")
void vSerialTxISR( void )
{
char cChar, cTaskWoken = pdFALSE;

	if( xQueueReceiveFromISR( xCharsForTx, &cChar, &cTaskWoken ) == pdTRUE )
	{
		/* Send the next character queued for Tx. */
		TXREG = cChar;
	}
	else
	{
		/* Queue empty, nothing to send. */
		PIE1bits.TXIE = serINTERRUPT_DISABLED;
	}
}



