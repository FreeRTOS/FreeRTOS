/*
 * FreeRTOS Kernel V10.2.1
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
Changes from V1.2.5

	+  Clear overrun errors in the Rx ISR.  Overrun errors prevent any further
	   characters being received.

Changes from V2.0.0

	+ Use TickType_t in place of unsigned pdLONG for delay periods.
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
static QueueHandle_t xRxedChars; 
static QueueHandle_t xCharsForTx;

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

portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, signed char *pcRxedChar, TickType_t xBlockTime )
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

portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, signed char cOutChar, TickType_t xBlockTime )
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



