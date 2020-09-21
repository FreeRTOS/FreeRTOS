/*
 * FreeRTOS Kernel V10.3.0
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

#define serINVALID_QUEUE				( ( QueueHandle_t ) 0 )
#define serNO_BLOCK						( ( TickType_t ) 0 )

/*-----------------------------------------------------------*/

/* Queues used to hold received characters, and characters waiting to be
transmitted. */
static QueueHandle_t xRxedChars;
static QueueHandle_t xCharsForTx;

static volatile portBASE_TYPE xQueueEmpty = pdTRUE;

/*-----------------------------------------------------------*/

/* The interrupt service routine - called from the assembly entry point. */
void vSerialISR( void );
void vConfigureQueues( QueueHandle_t xQForRx, QueueHandle_t xQForTx, volatile portBASE_TYPE *pxEmptyFlag );

/*-----------------------------------------------------------*/

/*
 * See the serial2.h header file.
 */
xComPortHandle xSerialPortInitMinimal( unsigned long ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
xComPortHandle xReturn;
UART_InitTypeDef UART_InitStructure;
GPIO_InitTypeDef GPIO_InitStructure;
EIC_IRQInitTypeDef  EIC_IRQInitStructure;	

	/* Create the queues used to hold Rx and Tx characters. */
	xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed char ) );
	xCharsForTx = xQueueCreate( uxQueueLength + 1, ( unsigned portBASE_TYPE ) sizeof( signed char ) );

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

signed portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, signed char *pcRxedChar, TickType_t xBlockTime )
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

void vSerialPutString( xComPortHandle pxPort, const signed char * const pcString, unsigned short usStringLength )
{
signed char *pxNext;

	/* A couple of parameters that this port does not use. */
	( void ) usStringLength;
	( void ) pxPort;

	/* NOTE: This implementation does not handle the queue being full as no
	block time is used! */

	/* The port handle is not required as this driver only supports UART0. */
	( void ) pxPort;

	/* Send each character in the string, one at a time. */
	pxNext = ( signed char * ) pcString;
	while( *pxNext )
	{
		xSerialPutChar( pxPort, *pxNext, serNO_BLOCK );
		pxNext++;
	}
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, signed char cOutChar, TickType_t xBlockTime )
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





	
