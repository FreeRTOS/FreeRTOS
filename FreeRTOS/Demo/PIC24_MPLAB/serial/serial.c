/*
    FreeRTOS V8.2.3 - Copyright (C) 2015 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>>> AND MODIFIED BY <<<< the FreeRTOS exception.

    ***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
    ***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that is more than just the market leader, it     *
     *    is the industry's de facto standard.                               *
     *                                                                       *
     *    Help yourself get started quickly while simultaneously helping     *
     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
     *    tutorial book, reference manual, or both:                          *
     *    http://www.FreeRTOS.org/Documentation                              *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
    the FAQ page "My application does not run, what could be wrong?".  Have you
    defined configASSERT()?

    http://www.FreeRTOS.org/support - In return for receiving this top quality
    embedded software for free we request you assist our global community by
    participating in the support forum.

    http://www.FreeRTOS.org/training - Investing in training allows your team to
    be as productive as possible as early as possible.  Now you can receive
    FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
    Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
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
static QueueHandle_t xRxedChars; 
static QueueHandle_t xCharsForTx; 

static portBASE_TYPE xTxHasEnded;
/*-----------------------------------------------------------*/

xComPortHandle xSerialPortInitMinimal( unsigned long ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
char cChar;

	/* Create the queues used by the com test task. */
	xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed char ) );
	xCharsForTx = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed char ) );

	/* Setup the UART. */
	U2MODEbits.BRGH		= serLOW_SPEED;
	U2MODEbits.STSEL	= serONE_STOP_BIT;
	U2MODEbits.PDSEL	= serEIGHT_DATA_BITS_NO_PARITY;
	U2MODEbits.RXINV	= serNORMAL_IDLE_STATE;
	U2MODEbits.ABAUD	= serAUTO_BAUD_OFF;
	U2MODEbits.LPBACK	= serLOOPBACK_OFF;
	U2MODEbits.WAKE		= serWAKE_UP_DISABLE;
	U2MODEbits.UEN		= serNO_HARDWARE_FLOW_CONTROL;
	U2MODEbits.IREN		= serNO_IRDA;
	U2MODEbits.USIDL	= serCONTINUE_IN_IDLE_MODE;
	U2MODEbits.UARTEN	= serUART_ENABLED;

	U2BRG = (unsigned short)(( (float)configCPU_CLOCK_HZ / ( (float)16 * (float)ulWantedBaud ) ) - (float)0.5);

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

signed portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, signed char *pcRxedChar, TickType_t xBlockTime )
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

signed portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, signed char cOutChar, TickType_t xBlockTime )
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
	/* Note implemented. */
	( void ) xPort;
}
/*-----------------------------------------------------------*/

void __attribute__((__interrupt__, auto_psv)) _U2RXInterrupt( void )
{
char cChar;
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
signed char cChar;
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	/* If the transmit buffer is full we cannot get the next character.
	Another interrupt will occur the next time there is space so this does
	not matter. */
	IFS1bits.U2TXIF = serCLEAR_FLAG;
	while( !( U2STAbits.UTXBF ) )
	{
		if( xQueueReceiveFromISR( xCharsForTx, &cChar, &xHigherPriorityTaskWoken ) == pdTRUE )
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

	if( xHigherPriorityTaskWoken != pdFALSE )
	{
		taskYIELD();
	}
}


