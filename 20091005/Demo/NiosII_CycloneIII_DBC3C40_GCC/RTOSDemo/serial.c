/*
    FreeRTOS V5.4.2 - Copyright (C) 2009 Real Time Engineers Ltd.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under 
    the terms of the GNU General Public License (version 2) as published by the 
    Free Software Foundation and modified by the FreeRTOS exception.
    **NOTE** The exception to the GPL is included to allow you to distribute a
    combined work that includes FreeRTOS without being obliged to provide the 
    source code for proprietary components outside of the FreeRTOS kernel.  
    Alternative commercial license and support terms are also available upon 
    request.  See the licensing section of http://www.FreeRTOS.org for full 
    license details.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT
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

/* NOTE:  This is just a test file and not intended to be a generic 
COM driver. */

#include "altera_avalon_uart.h"
#include "altera_avalon_uart_regs.h"
#include "sys/alt_irq.h"

#include "FreeRTOS.h"
#include "queue.h"
#include "system.h"
#include "Serial.h"
/*---------------------------------------------------------------------------*/

#define serINVALID_QUEUE				( ( xQueueHandle ) 0 )
#define serNO_BLOCK						( ( portTickType ) 0 )
/*---------------------------------------------------------------------------*/

static xQueueHandle xRxedChars; 
static xQueueHandle xCharsForTx; 

alt_u32 uartControl;
/*---------------------------------------------------------------------------*/

static void vUARTInterruptHandler( void* context, alt_u32 id );
static void vUARTReceiveHandler( alt_u32 status );
static void vUARTTransmitHandler( alt_u32 status );
/*---------------------------------------------------------------------------*/

xComPortHandle xSerialPortInitMinimal( unsigned portLONG ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
	/* Create the queues used to hold Rx and Tx characters. */
	xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed portCHAR ) );
	xCharsForTx = xQueueCreate( uxQueueLength + 1, ( unsigned portBASE_TYPE ) sizeof( signed portCHAR ) );

	/* If the queues were created correctly then setup the serial port hardware. */
	if( ( xRxedChars != serINVALID_QUEUE ) && ( xCharsForTx != serINVALID_QUEUE ) )
	{
		portENTER_CRITICAL();
		{
			uartControl = ALTERA_AVALON_UART_CONTROL_RTS_MSK | ALTERA_AVALON_UART_CONTROL_RRDY_MSK | ALTERA_AVALON_UART_CONTROL_DCTS_MSK;
			IOWR_ALTERA_AVALON_UART_CONTROL( UART_BASE, uartControl ); 
		  
		    /* register the interrupt handler */
			alt_irq_register ( UART_IRQ, NULL, vUARTInterruptHandler );
		}
		portEXIT_CRITICAL();
	}
	else
	{
		return ( xComPortHandle ) 0;
	}
    return ( xComPortHandle ) 1;
}
/*---------------------------------------------------------------------------*/

void vSerialClose( xComPortHandle xPort )
{
    /* Never used. */
}
/*---------------------------------------------------------------------------*/

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
		uartControl |= ALTERA_AVALON_UART_CONTROL_RRDY_MSK;
		IOWR_ALTERA_AVALON_UART_CONTROL( UART_BASE, uartControl );
		return pdFALSE;
	}
}
/*---------------------------------------------------------------------------*/

signed portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, signed portCHAR cOutChar, portTickType xBlockTime )
{
signed portBASE_TYPE lReturn = pdPASS;

	/* Place the character in the queue of characters to be transmitted. */
	if( xQueueSend( xCharsForTx, &cOutChar, xBlockTime ) == pdPASS )
	{
        /*Triggers an interrupt on every character or (down) when queue is full. */
        uartControl |= ALTERA_AVALON_UART_CONTROL_TRDY_MSK; 
        IOWR_ALTERA_AVALON_UART_CONTROL( UART_BASE, uartControl );
        lReturn = pdPASS;
    }
    else
    {	
		lReturn = pdFAIL;
	}
	return lReturn;
}
/*---------------------------------------------------------------------------*/

void vSerialPutString( xComPortHandle pxPort, const signed portCHAR * const pcString, unsigned portSHORT usStringLength )
{
signed portCHAR *pxNext;

	/* A couple of parameters that this port does not use. */
	( void ) usStringLength;
	( void ) pxPort;

	/* NOTE: This implementation does not handle the queue being full as no block time is used! */

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

static void vUARTInterruptHandler( void* context, alt_u32 id )
{
	alt_u32 status;

	/* Read the status register in order to determine the cause of the 
    interrupt. */
	status = IORD_ALTERA_AVALON_UART_STATUS( UART_BASE );
	
	/* Clear any error flags set at the device */
	IOWR_ALTERA_AVALON_UART_STATUS( UART_BASE, 0 );
	
	/* process a read irq */
	if ( status & ALTERA_AVALON_UART_STATUS_RRDY_MSK )
	{
		vUARTReceiveHandler( status );
	}
	
	/* process a write irq */
	if ( status & ( ALTERA_AVALON_UART_STATUS_TRDY_MSK  ) )
	{
		vUARTTransmitHandler( status );
	}
}
/*---------------------------------------------------------------------------*/

static void vUARTReceiveHandler( alt_u32 status )
{
signed portCHAR cChar;
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	/* If there was an error, discard the data */
	if ( status & ( ALTERA_AVALON_UART_STATUS_PE_MSK | ALTERA_AVALON_UART_STATUS_FE_MSK ) )
	{
        asm("break");
		return;
	}

	/* Transfer data from the device to the circular buffer */
	cChar = IORD_ALTERA_AVALON_UART_RXDATA( UART_BASE );
	if ( pdTRUE != xQueueSendFromISR( xRxedChars, &cChar, &xHigherPriorityTaskWoken ) )
	{
		/* If the circular buffer was full, disable interrupts. Interrupts will 
        be re-enabled when data is removed from the buffer. */
		uartControl &= ~ALTERA_AVALON_UART_CONTROL_RRDY_MSK;
		IOWR_ALTERA_AVALON_UART_CONTROL( UART_BASE, uartControl );
	}
    
	portEND_SWITCHING_ISR( xHigherPriorityTaskWoken );
}
/*---------------------------------------------------------------------------*/

static void vUARTTransmitHandler( alt_u32 status )
{
signed portCHAR cChar;
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;
	/* Transfer data if there is some ready to be transferred */
	if( xQueueReceiveFromISR( xCharsForTx, &cChar, &xHigherPriorityTaskWoken ) == pdTRUE )
	{
		IOWR_ALTERA_AVALON_UART_TXDATA( UART_BASE, cChar );
    }
    else
    {
		uartControl &= ~ALTERA_AVALON_UART_CONTROL_TRDY_MSK;
    }
	
	IOWR_ALTERA_AVALON_UART_CONTROL( UART_BASE, uartControl );
    portEND_SWITCHING_ISR( xHigherPriorityTaskWoken );    
}    
/*---------------------------------------------------------------------------*/
