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
Changes from V3.0.0
	+ ISRcode removed. Is now pulled inline to reduce stack-usage.

Changes from V3.0.1
*/

/* BASIC INTERRUPT DRIVEN SERIAL PORT DRIVER. */

/* Scheduler header files. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

#include "serial.h"

/* Hardware pin definitions. */
#define serTX_PIN				bTRC6
#define serRX_PIN				bTRC7

/* Bit/register definitions. */
#define serINPUT				( 1 )
#define serOUTPUT				( 0 )
#define serINTERRUPT_ENABLED 	( 1 )

/* All ISR's use the PIC18 low priority interrupt. */
#define	serLOW_PRIORITY			( 0 )

/*-----------------------------------------------------------*/

/* Queues to interface between comms API and interrupt routines. */
QueueHandle_t xRxedChars; 
QueueHandle_t xCharsForTx;
portBASE_TYPE xHigherPriorityTaskWoken;

/*-----------------------------------------------------------*/

xComPortHandle xSerialPortInitMinimal( unsigned long ulWantedBaud, unsigned char ucQueueLength )
{
	unsigned short usSPBRG;
	
	/* Create the queues used by the ISR's to interface to tasks. */
	xRxedChars = xQueueCreate( ucQueueLength, ( unsigned portBASE_TYPE ) sizeof( char ) );
	xCharsForTx = xQueueCreate( ucQueueLength, ( unsigned portBASE_TYPE ) sizeof( char ) );

	portENTER_CRITICAL();

	/* Setup the IO pins to enable the USART IO. */
	serTX_PIN	= serINPUT;		// YES really! See datasheet
	serRX_PIN	= serINPUT;

	/* Set the TX config register. */
	TXSTA = 0b00100000;
		//	  ||||||||--bit0: TX9D	= n/a
		//	  |||||||---bit1: TRMT	= ReadOnly
		//	  ||||||----bit2: BRGH	= High speed
		//	  |||||-----bit3: SENDB = n/a
		//	  ||||------bit4: SYNC	= Asynchronous mode
		//	  |||-------bit5: TXEN	= Transmit enable
		//	  ||--------bit6: TX9	= 8-bit transmission
		//	  |---------bit7: CSRC	= n/a

	/* Set the Receive config register. */
	RCSTA = 0b10010000;
		//	  ||||||||--bit0: RX9D	= ReadOnly
		//	  |||||||---bit1: OERR	= ReadOnly
		//	  ||||||----bit2: FERR	= ReadOnly
		//	  |||||-----bit3: ADDEN	= n/a
		//	  ||||------bit4: CREN	= Enable receiver
		//	  |||-------bit5: SREN	= n/a
		//	  ||--------bit6: RX9	= 8-bit reception
		//	  |---------bit7: SPEN	= Serial port enabled

	/* Calculate the baud rate generator value.
	   We use low-speed (BRGH=0), the formula is
	   SPBRG = ( ( FOSC / Desired Baud Rate ) / 64 ) - 1 */
	usSPBRG = ( ( APROCFREQ / ulWantedBaud ) / 64 ) - 1;
	if( usSPBRG > 255 )
	{
		SPBRG = 255;
	}
	else
	{
		SPBRG = usSPBRG;
	}

	/* Set the serial interrupts to use the same priority as the tick. */
	bTXIP = serLOW_PRIORITY;
	bRCIP = serLOW_PRIORITY;

	/* Enable the Rx interrupt now, the Tx interrupt will get enabled when
	we have data to send. */
	bRCIE = serINTERRUPT_ENABLED;
	
	portEXIT_CRITICAL();

	/* Unlike other ports, this serial code does not allow for more than one
	com port.  We therefore don't return a pointer to a port structure and 
	can	instead just return NULL. */
	return NULL;
}
/*-----------------------------------------------------------*/

xComPortHandle xSerialPortInit( eCOMPort ePort, eBaud eWantedBaud, eParity eWantedParity, eDataBits eWantedDataBits, eStopBits eWantedStopBits, unsigned char ucBufferLength )
{
	/* This is not implemented in this port.
	Use xSerialPortInitMinimal() instead. */
	return NULL;
}
/*-----------------------------------------------------------*/

portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, char *pcRxedChar, TickType_t xBlockTime )
{
	/* Get the next character from the buffer.  Return false if no characters
	are available, or arrive before xBlockTime expires. */
	if( xQueueReceive( xRxedChars, pcRxedChar, xBlockTime ) )
	{
		return ( char ) pdTRUE;
	}

	return ( char ) pdFALSE;
}
/*-----------------------------------------------------------*/

portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, char cOutChar, TickType_t xBlockTime )
{
	/* Return false if after the block time there is no room on the Tx queue. */
	if( xQueueSend( xCharsForTx, ( const void * ) &cOutChar, xBlockTime ) != ( char ) pdPASS )
	{
		return pdFAIL;
	}

	/* Turn interrupt on - ensure the compiler only generates a single 
	instruction for this. */
	bTXIE = serINTERRUPT_ENABLED;

	return pdPASS;
}
/*-----------------------------------------------------------*/

void vSerialClose( xComPortHandle xPort )
{
	/* Not implemented for this port.
	To implement, turn off the interrupts and delete the memory
	allocated to the queues. */
}
