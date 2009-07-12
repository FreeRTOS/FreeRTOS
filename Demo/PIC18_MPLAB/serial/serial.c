/*
	FreeRTOS V5.4.0 - Copyright (C) 2003-2009 Richard Barry.

	This file is part of the FreeRTOS distribution.

	FreeRTOS is free software; you can redistribute it and/or modify it	under 
	the terms of the GNU General Public License (version 2) as published by the 
	Free Software Foundation and modified by the FreeRTOS exception.
	**NOTE** The exception to the GPL is included to allow you to distribute a
	combined work that includes FreeRTOS without being obliged to provide the 
	source code for proprietary components outside of the FreeRTOS kernel.  
	Alternative commercial license and support terms are also available upon 
	request.  See the licensing section of http://www.FreeRTOS.org for full 
	license details.

	FreeRTOS is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
	more details.

	You should have received a copy of the GNU General Public License along
	with FreeRTOS; if not, write to the Free Software Foundation, Inc., 59
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.


	***************************************************************************
	*                                                                         *
	* Looking for a quick start?  Then check out the FreeRTOS eBook!          *
	* See http://www.FreeRTOS.org/Documentation for details                   *
	*                                                                         *
	***************************************************************************

	1 tab == 4 spaces!

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

	http://www.FreeRTOS.org - Documentation, latest information, license and
	contact details.

	http://www.SafeRTOS.com - A version that is certified for use in safety
	critical systems.

	http://www.OpenRTOS.com - Commercial support, development, porting,
	licensing and training services.
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
#define serTX_ENABLE			( ( unsigned portSHORT ) 1 )
#define serRX_ENABLE			( ( unsigned portSHORT ) 1 )
#define serHIGH_SPEED			( ( unsigned portSHORT ) 1 )
#define serCONTINUOUS_RX		( ( unsigned portSHORT ) 1 )
#define serCLEAR_OVERRUN		( ( unsigned portSHORT ) 0 )
#define serINTERRUPT_ENABLED 	( ( unsigned portSHORT ) 1 )
#define serINTERRUPT_DISABLED 	( ( unsigned portSHORT ) 0 )

/* All ISR's use the PIC18 low priority interrupt. */
#define							serLOW_PRIORITY ( 0 )

/*-----------------------------------------------------------*/

/* Queues to interface between comms API and interrupt routines. */
static xQueueHandle xRxedChars; 
static xQueueHandle xCharsForTx;

/*-----------------------------------------------------------*/

xComPortHandle xSerialPortInitMinimal( unsigned portLONG ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
unsigned portLONG ulBaud;

	/* Calculate the baud rate generator constant.
	SPBRG = ( (FOSC / Desired Baud Rate) / 16 ) - 1 */
	ulBaud = configCPU_CLOCK_HZ / ulWantedBaud;
	ulBaud /= ( unsigned portLONG ) 16;
	ulBaud -= ( unsigned portLONG ) 1;

	/* Create the queues used by the ISR's to interface to tasks. */
	xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( portCHAR ) );
	xCharsForTx = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( portCHAR ) );

	portENTER_CRITICAL();
	{
		/* Start with config registers cleared, so we can just set the wanted
		bits. */
		TXSTA = ( unsigned portSHORT ) 0;
		RCSTA = ( unsigned portSHORT ) 0;

		/* Set the baud rate generator using the above calculated constant. */
		SPBRG = ( unsigned portCHAR ) ulBaud;

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

portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, signed portCHAR *pcRxedChar, portTickType xBlockTime )
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

portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, signed portCHAR cOutChar, portTickType xBlockTime )
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
portCHAR cChar;
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
portCHAR cChar, cTaskWoken = pdFALSE;

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



