/*
	FreeRTOS.org V5.3.1 - Copyright (C) 2003-2009 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify it
	under the terms of the GNU General Public License (version 2) as published
	by the Free Software Foundation and modified by the FreeRTOS exception.
	**NOTE** The exception to the GPL is included to allow you to distribute a
	combined work that includes FreeRTOS.org without being obliged to provide
	the source code for any proprietary components.  Alternative commercial
	license and support terms are also available upon request.  See the 
	licensing section of http://www.FreeRTOS.org for full details.

	FreeRTOS.org is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
	more details.

	You should have received a copy of the GNU General Public License along
	with FreeRTOS.org; if not, write to the Free Software Foundation, Inc., 59
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.


	***************************************************************************
	*                                                                         *
	* Get the FreeRTOS eBook!  See http://www.FreeRTOS.org/Documentation      *
	*                                                                         *
	* This is a concise, step by step, 'hands on' guide that describes both   *
	* general multitasking concepts and FreeRTOS specifics. It presents and   *
	* explains numerous examples that are written using the FreeRTOS API.     *
	* Full source code for all the examples is provided in an accompanying    *
	* .zip file.                                                              *
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
	BASIC INTERRUPT DRIVEN SERIAL PORT DRIVER FOR UART0. 
*/

/* Standard includes. */ 
#include <stdlib.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* Demo application includes. */
#include "serial.h"

/*-----------------------------------------------------------*/

/* Location of the COM0 registers. */
#define serCOM0							( ( AT91PS_USART ) AT91C_BASE_US0 )

/* Interrupt control macros. */
#define serINTERRUPT_LEVEL				( 5 )
#define vInterruptOn()					AT91F_US_EnableIt( serCOM0, AT91C_US_TXRDY | AT91C_US_RXRDY )
#define vInterruptOff()					AT91F_US_DisableIt( serCOM0, AT91C_US_TXRDY )

/* Misc constants. */
#define serINVALID_QUEUE				( ( xQueueHandle ) 0 )
#define serHANDLE						( ( xComPortHandle ) 1 )
#define serNO_BLOCK						( ( portTickType ) 0 )
#define serNO_TIMEGUARD					( ( unsigned portLONG ) 0 )
#define serNO_PERIPHERAL_B_SETUP		( ( unsigned portLONG ) 0 )


/* Queues used to hold received characters, and characters waiting to be
transmitted. */
static xQueueHandle xRxedChars; 
static xQueueHandle xCharsForTx; 

/*-----------------------------------------------------------*/

/* Interrupt entry point written in the assembler file serialISR.s79. */
extern void vSerialISREntry( void );

/* The interrupt service routine - called from the assembly entry point. */
__arm void vSerialISR( void );

/*-----------------------------------------------------------*/

/*
 * See the serial2.h header file.
 */
xComPortHandle xSerialPortInitMinimal( unsigned portLONG ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
xComPortHandle xReturn = serHANDLE;
extern void ( vUART_ISR )( void );

	/* Create the queues used to hold Rx and Tx characters. */
	xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed portCHAR ) );
	xCharsForTx = xQueueCreate( uxQueueLength + 1, ( unsigned portBASE_TYPE ) sizeof( signed portCHAR ) );

	/* If the queues were created correctly then setup the serial port 
	hardware. */
	if( ( xRxedChars != serINVALID_QUEUE ) && ( xCharsForTx != serINVALID_QUEUE ) )
	{
		portENTER_CRITICAL();
		{
			/* Enable the USART clock. */
   			AT91F_PMC_EnablePeriphClock( AT91C_BASE_PMC, 1 << AT91C_ID_US0 );

			AT91F_PIO_CfgPeriph( AT91C_BASE_PIOA, ( ( unsigned portLONG ) AT91C_PA5_RXD0 ) | ( ( unsigned portLONG ) AT91C_PA6_TXD0 ), serNO_PERIPHERAL_B_SETUP );

			/* Set the required protocol. */
			AT91F_US_Configure( serCOM0, configCPU_CLOCK_HZ, AT91C_US_ASYNC_MODE, ulWantedBaud, serNO_TIMEGUARD );

			/* Enable Rx and Tx. */
			serCOM0->US_CR = AT91C_US_RXEN | AT91C_US_TXEN;

			/* Enable the Rx interrupts.  The Tx interrupts are not enabled
			until there are characters to be transmitted. */
    		AT91F_US_EnableIt( serCOM0, AT91C_US_RXRDY );

			/* Enable the interrupts in the AIC. */
			AT91F_AIC_ConfigureIt( AT91C_BASE_AIC, AT91C_ID_US0, serINTERRUPT_LEVEL, AT91C_AIC_SRCTYPE_INT_LEVEL_SENSITIVE, ( void (*)( void ) ) vSerialISREntry );
			AT91F_AIC_EnableIt( AT91C_BASE_AIC, AT91C_ID_US0 );
		}
		portEXIT_CRITICAL();
	}
	else
	{
		xReturn = ( xComPortHandle ) 0;
	}

	/* This demo file only supports a single port but we have to return 
	something to comply with the standard demo header file. */
	return xReturn;
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, signed portCHAR *pcRxedChar, portTickType xBlockTime )
{
	/* The port handle is not required as this driver only supports one port. */
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

	/* A couple of parameters that this port does not use. */
	( void ) usStringLength;
	( void ) pxPort;

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
	vInterruptOn();

	return pdPASS;
}
/*-----------------------------------------------------------*/

void vSerialClose( xComPortHandle xPort )
{
	/* Not supported as not required by the demo application. */
}
/*-----------------------------------------------------------*/

/* Serial port ISR.  This can cause a context switch so is not defined as a
standard ISR using the __irq keyword.  Instead a wrapper function is defined
within serialISR.s79 which in turn calls this function.  See the port
documentation on the FreeRTOS.org website for more information. */
__arm void vSerialISR( void )
{
unsigned portLONG ulStatus;
signed portCHAR cChar;
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	/* What caused the interrupt? */
	ulStatus = serCOM0->US_CSR &= serCOM0->US_IMR;

	if( ulStatus & AT91C_US_TXRDY )
	{
		/* The interrupt was caused by the THR becoming empty.  Are there any
		more characters to transmit? */
		if( xQueueReceiveFromISR( xCharsForTx, &cChar, &xHigherPriorityTaskWoken ) == pdTRUE )
		{
			/* A character was retrieved from the queue so can be sent to the
			THR now. */
			serCOM0->US_THR = cChar;
		}
		else
		{
			/* Queue empty, nothing to send so turn off the Tx interrupt. */
			vInterruptOff();
		}		
	}

	if( ulStatus & AT91C_US_RXRDY )
	{
		/* The interrupt was caused by a character being received.  Grab the
		character from the RHR and place it in the queue or received 
		characters. */
		cChar = serCOM0->US_RHR;
		xQueueSendFromISR( xRxedChars, &cChar, &xHigherPriorityTaskWoken );
	}

	/* If a task was woken by either a character being received or a character 
	being transmitted then we may need to switch to another task. */
	portEND_SWITCHING_ISR( xHigherPriorityTaskWoken );

	/* End the interrupt in the AIC. */
	AT91C_BASE_AIC->AIC_EOICR = 0;
}




	
