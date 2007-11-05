/*
	FreeRTOS.org V4.6.1 - Copyright (C) 2003-2007 Richard Barry.

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

	Also see http://www.SafeRTOS.com a version that has been certified for use
	in safety critical systems, plus commercial licensing, development and
	support options.
	***************************************************************************
*/

/*
	BASIC INTERRUPT DRIVEN SERIAL PORT DRIVER FOR UART0.
*/


/*-----------------------------------------------------------
 * Components that can be compiled to either ARM or THUMB mode are
 * contained in this file.c  The ISR routines, which can only be compiled
 * to ARM mode, are contained in serialISR.c.
 *----------------------------------------------------------*/



/* Library includes. */
#include "75x_uart.h"
#include "75x_gpio.h"
#include "75x_eic.h"
#include "75x_mrcc.h"

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* Demo application includes. */
#include "serial.h"

#define serINVALID_QUEUE				( ( xQueueHandle ) 0 )
#define serNO_BLOCK						( ( portTickType ) 0 )

/*-----------------------------------------------------------*/

/* Queues used to hold received characters, and characters waiting to be
transmitted. */
static xQueueHandle xRxedChars;
static xQueueHandle xCharsForTx;

static volatile portBASE_TYPE xQueueEmpty = pdTRUE;

/*-----------------------------------------------------------*/

/* The interrupt service routine - called from the assembly entry point. */
void vSerialISR( void );
void vConfigureQueues( xQueueHandle xQForRx, xQueueHandle xQForTx, volatile portBASE_TYPE *pxEmptyFlag );

/*-----------------------------------------------------------*/

/*
 * See the serial2.h header file.
 */
xComPortHandle xSerialPortInitMinimal( unsigned portLONG ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
xComPortHandle xReturn;
UART_InitTypeDef UART_InitStructure;
GPIO_InitTypeDef GPIO_InitStructure;
EIC_IRQInitTypeDef  EIC_IRQInitStructure;	

	/* Create the queues used to hold Rx and Tx characters. */
	xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed portCHAR ) );
	xCharsForTx = xQueueCreate( uxQueueLength + 1, ( unsigned portBASE_TYPE ) sizeof( signed portCHAR ) );

	/* If the queues were created correctly then setup the serial port
	hardware. */
	if( ( xRxedChars != serINVALID_QUEUE ) && ( xCharsForTx != serINVALID_QUEUE ) )
	{
	
		vConfigureQueues( xRxedChars, xCharsForTx, &xQueueEmpty );
	
		portENTER_CRITICAL();
		{
			/* Enable the UART0 Clock. */
			MRCC_PeripheralClockConfig( MRCC_Peripheral_UART0, ENABLE );
			
			/* Configure the UART0_Tx as alternate function */
			GPIO_InitStructure.GPIO_Mode = GPIO_Mode_AF_PP;
			GPIO_InitStructure.GPIO_Pin =  GPIO_Pin_11;
			GPIO_Init(GPIO0, &GPIO_InitStructure);
			
			/* Configure the UART0_Rx as input floating */
			GPIO_InitStructure.GPIO_Mode = GPIO_Mode_IN_FLOATING;
			GPIO_InitStructure.GPIO_Pin = GPIO_Pin_10;
			GPIO_Init(GPIO0, &GPIO_InitStructure);
			
			/* Configure UART0. */
			UART_InitStructure.UART_WordLength = UART_WordLength_8D;
			UART_InitStructure.UART_StopBits = UART_StopBits_1;
			UART_InitStructure.UART_Parity = UART_Parity_No;
			UART_InitStructure.UART_BaudRate = ulWantedBaud;
			UART_InitStructure.UART_HardwareFlowControl = UART_HardwareFlowControl_None;
			UART_InitStructure.UART_Mode = UART_Mode_Tx_Rx;
			UART_InitStructure.UART_TxFIFOLevel = UART_FIFOLevel_1_2; /* FIFO size 16 bytes, FIFO level 8 bytes */
			UART_InitStructure.UART_RxFIFOLevel = UART_FIFOLevel_1_2; /* FIFO size 16 bytes, FIFO level 8 bytes */
			UART_Init(UART0, &UART_InitStructure);

			/* Enable the UART0 */
			UART_Cmd(UART0, ENABLE);

			/* Configure the IEC for the UART interrupts. */			
			EIC_IRQInitStructure.EIC_IRQChannelCmd = ENABLE;
			EIC_IRQInitStructure.EIC_IRQChannel = UART0_IRQChannel;
			EIC_IRQInitStructure.EIC_IRQChannelPriority = 1;
			EIC_IRQInit(&EIC_IRQInitStructure);
			
			xQueueEmpty = pdTRUE;
			UART_ITConfig( UART0, UART_IT_Transmit | UART_IT_Receive, ENABLE );
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
portBASE_TYPE xReturn;

	/* Place the character in the queue of characters to be transmitted. */
	portENTER_CRITICAL();
	{
		if( xQueueEmpty == pdTRUE )
		{
			UART0->DR = cOutChar;
			xReturn = pdPASS;
		}
		else
		{
			if( xQueueSend( xCharsForTx, &cOutChar, xBlockTime ) != pdPASS )
			{
				xReturn = pdFAIL;
			}			
			else
			{
				xReturn = pdPASS;				
			}
		}
		
		xQueueEmpty = pdFALSE;
	}
	portEXIT_CRITICAL();

	return xReturn;
}
/*-----------------------------------------------------------*/

void vSerialClose( xComPortHandle xPort )
{
	/* Not supported as not required by the demo application. */
}
/*-----------------------------------------------------------*/





	
