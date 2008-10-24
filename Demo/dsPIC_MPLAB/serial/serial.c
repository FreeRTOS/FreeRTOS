/*
	FreeRTOS.org V5.1.0 - Copyright (C) 2003-2008 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation; either version 2 of the License, or
	(at your option) any later version.

	FreeRTOS.org is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with FreeRTOS.org; if not, write to the Free Software
	Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

	A special exception to the GPL can be applied should you wish to distribute
	a combined work that includes FreeRTOS.org, without being obliged to provide
	the source code for any proprietary components.  See the licensing section 
	of http://www.FreeRTOS.org for full details of how and when the exception
	can be applied.

    ***************************************************************************
    ***************************************************************************
    *                                                                         *
    * SAVE TIME AND MONEY!  We can port FreeRTOS.org to your own hardware,    *
    * and even write all or part of your application on your behalf.          *
    * See http://www.OpenRTOS.com for details of the services we provide to   *
    * expedite your project.                                                  *
    *                                                                         *
    ***************************************************************************
    ***************************************************************************

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

	http://www.FreeRTOS.org - Documentation, latest information, license and 
	contact details.

	http://www.SafeRTOS.com - A version that is certified for use in safety 
	critical systems.

	http://www.OpenRTOS.com - Commercial support, development, porting, 
	licensing and training services.
*/


/* BASIC INTERRUPT DRIVEN SERIAL PORT DRIVER. 

NOTE:  This driver is primarily to test the scheduler functionality.  It does
not effectively use the buffers or DMA and is therefore not intended to be
an example of an efficient driver. */

/* Standard include file. */
#include <stdlib.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "queue.h"
#include "task.h"

/* Demo app include files. */
#include "serial.h"

/* Hardware setup. */
#define serOUTPUT						0
#define serINPUT						1
#define serLOW_SPEED					0
#define serONE_STOP_BIT					0
#define serEIGHT_DATA_BITS_NO_PARITY	0
#define serNORMAL_IDLE_STATE			0
#define serAUTO_BAUD_OFF				0
#define serLOOPBACK_OFF					0
#define serWAKE_UP_DISABLE				0
#define serNO_HARDWARE_FLOW_CONTROL		0
#define serSTANDARD_IO					0
#define serNO_IRDA						0
#define serCONTINUE_IN_IDLE_MODE		0
#define serUART_ENABLED					1
#define serINTERRUPT_ON_SINGLE_CHAR		0
#define serTX_ENABLE					1
#define serINTERRUPT_ENABLE				1
#define serINTERRUPT_DISABLE			0
#define serCLEAR_FLAG					0
#define serSET_FLAG						1


/* The queues used to communicate between tasks and ISR's. */
static xQueueHandle xRxedChars; 
static xQueueHandle xCharsForTx; 

static portBASE_TYPE xTxHasEnded;
/*-----------------------------------------------------------*/

xComPortHandle xSerialPortInitMinimal( unsigned portLONG ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
portCHAR cChar;

	/* Create the queues used by the com test task. */
	xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed portCHAR ) );
	xCharsForTx = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed portCHAR ) );

	/* Setup the UART. */
	U2MODEbits.BRGH		= serLOW_SPEED;
	U2MODEbits.STSEL	= serONE_STOP_BIT;
	U2MODEbits.PDSEL	= serEIGHT_DATA_BITS_NO_PARITY;
	U2MODEbits.ABAUD	= serAUTO_BAUD_OFF;
	U2MODEbits.LPBACK	= serLOOPBACK_OFF;
	U2MODEbits.WAKE		= serWAKE_UP_DISABLE;
	U2MODEbits.UEN		= serNO_HARDWARE_FLOW_CONTROL;
	U2MODEbits.IREN		= serNO_IRDA;
	U2MODEbits.USIDL	= serCONTINUE_IN_IDLE_MODE;
	U2MODEbits.UARTEN	= serUART_ENABLED;

	U2BRG = (unsigned portSHORT)(( (float)configCPU_CLOCK_HZ / ( (float)16 * (float)ulWantedBaud ) ) - (float)0.5);

	U2STAbits.URXISEL	= serINTERRUPT_ON_SINGLE_CHAR;
	U2STAbits.UTXEN		= serTX_ENABLE;
	U2STAbits.UTXINV	= serNORMAL_IDLE_STATE;
	U2STAbits.UTXISEL0	= serINTERRUPT_ON_SINGLE_CHAR;
	U2STAbits.UTXISEL1	= serINTERRUPT_ON_SINGLE_CHAR;

	/* It is assumed that this function is called prior to the scheduler being
	started.  Therefore interrupts must not be allowed to occur yet as they
	may attempt to perform a context switch. */
	portDISABLE_INTERRUPTS();

	IFS1bits.U2RXIF = serCLEAR_FLAG;
	IFS1bits.U2TXIF = serCLEAR_FLAG;
	IPC7bits.U2RXIP = configKERNEL_INTERRUPT_PRIORITY;
	IPC7bits.U2TXIP = configKERNEL_INTERRUPT_PRIORITY;
	IEC1bits.U2TXIE = serINTERRUPT_ENABLE;
	IEC1bits.U2RXIE = serINTERRUPT_ENABLE;

	/* Clear the Rx buffer. */
	while( U2STAbits.URXDA == serSET_FLAG )
	{
		cChar = U2RXREG;
	}

	xTxHasEnded = pdTRUE;

	return NULL;
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, signed portCHAR *pcRxedChar, portTickType xBlockTime )
{
	/* Only one port is supported. */
	( void ) pxPort;

	/* Get the next character from the buffer.  Return false if no characters
	are available or arrive before xBlockTime expires. */
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
	/* Only one port is supported. */
	( void ) pxPort;

	/* Return false if after the block time there is no room on the Tx queue. */
	if( xQueueSend( xCharsForTx, &cOutChar, xBlockTime ) != pdPASS )
	{
		return pdFAIL;
	}

	/* A critical section should not be required as xTxHasEnded will not be
	written to by the ISR if it is already 0 (is this correct?). */
	if( xTxHasEnded )
	{
		xTxHasEnded = pdFALSE;
		IFS1bits.U2TXIF = serSET_FLAG;
	}

	return pdPASS;
}
/*-----------------------------------------------------------*/

void vSerialClose( xComPortHandle xPort )
{
}
/*-----------------------------------------------------------*/

void __attribute__((__interrupt__, auto_psv)) _U2RXInterrupt( void )
{
portCHAR cChar;
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	/* Get the character and post it on the queue of Rxed characters.
	If the post causes a task to wake force a context switch as the woken task
	may have a higher priority than the task we have interrupted. */
	IFS1bits.U2RXIF = serCLEAR_FLAG;
	while( U2STAbits.URXDA )
	{
		cChar = U2RXREG;
		xQueueSendFromISR( xRxedChars, &cChar, &xHigherPriorityTaskWoken );
	}

	if( xHigherPriorityTaskWoken != pdFALSE )
	{
		taskYIELD();
	}
}
/*-----------------------------------------------------------*/

void __attribute__((__interrupt__, auto_psv)) _U2TXInterrupt( void )
{
signed portCHAR cChar;
portBASE_TYPE xTaskWoken = pdFALSE;

	/* If the transmit buffer is full we cannot get the next character.
	Another interrupt will occur the next time there is space so this does
	not matter. */
	IFS1bits.U2TXIF = serCLEAR_FLAG;
	while( !( U2STAbits.UTXBF ) )
	{
		if( xQueueReceiveFromISR( xCharsForTx, &cChar, &xTaskWoken ) == pdTRUE )
		{
			/* Send the next character queued for Tx. */
			U2TXREG = cChar;
		}
		else
		{
			/* Queue empty, nothing to send. */
			xTxHasEnded = pdTRUE;
			break;
		}
	}

	if( xTaskWoken != pdFALSE )
	{
		taskYIELD();
	}
}


