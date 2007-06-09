/*
	FreeRTOS.org V4.3.1 - Copyright (C) 2003-2007 Richard Barry.

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
	See http://www.FreeRTOS.org for documentation, latest information, license 
	and contact details.  Please ensure to read the configuration and relevant 
	port sections of the online documentation.

	Also see http://www.SafeRTOS.com for an IEC 61508 compliant version along
	with commercial development and support options.
	***************************************************************************
*/

/* 
	BASIC INTERRUPT DRIVEN SERIAL PORT DRIVER FOR USART0. 

	This file contains all the serial port components that can be compiled to
	either ARM or THUMB mode.  Components that must be compiled to ARM mode are
	contained in serialISR.c.
*/

/* Standard includes. */
#include <stdlib.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "queue.h"
#include "task.h"

/* Demo application includes. */
#include "serial.h"
#include "AT91R40008.h"
#include "usart.h"
#include "pio.h"
#include "aic.h"

/*-----------------------------------------------------------*/

/* Constants to setup and access the UART. */
#define portUSART0_AIC_CHANNEL	( ( unsigned portLONG ) 2 )

#define serINVALID_QUEUE		( ( xQueueHandle ) 0 )
#define serHANDLE				( ( xComPortHandle ) 1 )
#define serNO_BLOCK				( ( portTickType ) 0 )

/*-----------------------------------------------------------*/

/* Queues used to hold received characters, and characters waiting to be
transmitted. */
static xQueueHandle xRxedChars; 
static xQueueHandle xCharsForTx; 

/*-----------------------------------------------------------*/

/* 
 * The queues are created in serialISR.c as they are used from the ISR.
 * Obtain references to the queues and THRE Empty flag. 
 */
extern void vSerialISRCreateQueues(  unsigned portBASE_TYPE uxQueueLength, xQueueHandle *pxRxedChars, xQueueHandle *pxCharsForTx );

/*-----------------------------------------------------------*/

xComPortHandle xSerialPortInitMinimal( unsigned portLONG ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
unsigned portLONG ulSpeed;
unsigned portLONG ulCD;
xComPortHandle xReturn = serHANDLE;
extern void ( vUART_ISR )( void );

	/* The queues are used in the serial ISR routine, so are created from
	serialISR.c (which is always compiled to ARM mode. */
	vSerialISRCreateQueues( uxQueueLength, &xRxedChars, &xCharsForTx );

	if( 
		( xRxedChars != serINVALID_QUEUE ) && 
		( xCharsForTx != serINVALID_QUEUE ) && 
		( ulWantedBaud != ( unsigned portLONG ) 0 ) 
	  )
	{
		portENTER_CRITICAL();
		{
			/* Enable clock to USART0... */
			AT91C_BASE_PS->PS_PCER = AT91C_PS_US0;

			/* Disable all USART0 interrupt sources to begin... */
			AT91C_BASE_US0->US_IDR = 0xFFFFFFFF;

			/* Reset various status bits (just in case)... */
			AT91C_BASE_US0->US_CR = US_RSTSTA;

			AT91C_BASE_PIO->PIO_PDR = TXD0 | RXD0;  /* Enable RXD and TXD pins */
			AT91C_BASE_US0->US_CR = US_RSTRX | US_RSTTX | US_RXDIS | US_TXDIS;

			/* Clear Transmit and Receive Counters */
			AT91C_BASE_US0->US_RCR = 0;
			AT91C_BASE_US0->US_TCR = 0;

			/* Input clock to baud rate generator is MCK */
			ulSpeed = configCPU_CLOCK_HZ * 10;  
			ulSpeed = ulSpeed / 16;
			ulSpeed = ulSpeed / ulWantedBaud;
			
			/* compute the error */
			ulCD  = ulSpeed / 10;
			if ((ulSpeed - (ulCD * 10)) >= 5)
			ulCD++;

			/* Define the baud rate divisor register */
			AT91C_BASE_US0->US_BRGR = ulCD;

			/* Define the USART mode */
			AT91C_BASE_US0->US_MR = US_CLKS_MCK | US_CHRL_8 | US_PAR_NO | US_NBSTOP_1 | US_CHMODE_NORMAL;

			/* Write the Timeguard Register */
			AT91C_BASE_US0->US_TTGR = 0;

			/* Setup the interrupt for USART0.

			Store interrupt handler function address in USART0 vector register... */
			AT91C_BASE_AIC->AIC_SVR[ portUSART0_AIC_CHANNEL ] = (unsigned long)vUART_ISR;
			
			/* USART0 interrupt level-sensitive, priority 1... */
			AT91C_BASE_AIC->AIC_SMR[ portUSART0_AIC_CHANNEL ] = AIC_SRCTYPE_INT_LEVEL_SENSITIVE | 1;
			
			/* Clear some pending USART0 interrupts (just in case)... */
			AT91C_BASE_US0->US_CR = US_RSTSTA;

			/* Enable USART0 interrupt sources (but not Tx for now)... */
			AT91C_BASE_US0->US_IER = US_RXRDY;

			/* Enable USART0 interrupts in the AIC... */
			AT91C_BASE_AIC->AIC_IECR = ( 1 << portUSART0_AIC_CHANNEL );

			/* Enable receiver and transmitter... */
			AT91C_BASE_US0->US_CR = US_RXEN | US_TXEN;
		}
		portEXIT_CRITICAL();
	}
	else
	{
		xReturn = ( xComPortHandle ) 0;
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, signed portCHAR *pcRxedChar, portTickType xBlockTime )
{
	/* The port handle is not required as this driver only supports UART0. */
	( void ) pxPort;

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

void vSerialPutString( xComPortHandle pxPort, const signed portCHAR * const pcString, unsigned portSHORT usStringLength )
{
signed portCHAR *pxNext;

	/* NOTE: This implementation does not handle the queue being full as no
	block time is used! */

	/* The port handle is not required as this driver only supports UART0. */
	( void ) pxPort;

	/* Send each character in the string, one at a time. */
	pxNext = ( signed portCHAR * ) pcString;
	while( *pxNext )
	{
		xSerialPutChar( pxPort, *pxNext, serNO_BLOCK );
		pxNext++;
	}
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, signed portCHAR cOutChar, portTickType xBlockTime )
{
	/* Place the character in the queue of characters to be transmitted. */
	if( xQueueSend( xCharsForTx, &cOutChar, xBlockTime ) != pdPASS )
	{
		return pdFAIL;
	}

	/* Turn on the Tx interrupt so the ISR will remove the character from the
	queue and send it.   This does not need to be in a critical section as
	if the interrupt has already removed the character the next interrupt
	will simply turn off the Tx interrupt again. */
	AT91C_BASE_US0->US_IER = US_TXRDY;

	return pdPASS;
}
/*-----------------------------------------------------------*/

void vSerialClose( xComPortHandle xPort )
{
	/* Not supported as not required by the demo application. */
}
/*-----------------------------------------------------------*/

