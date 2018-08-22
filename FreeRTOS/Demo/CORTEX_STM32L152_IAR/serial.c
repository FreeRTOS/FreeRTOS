/*
 * FreeRTOS Kernel V10.1.0
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
	
	***Note*** This example uses queues to send each character into an interrupt
	service routine and out of an interrupt service routine individually.  This
	is done to demonstrate queues being used in an interrupt, and to deliberately
	load the system to test the FreeRTOS port.  It is *NOT* meant to be an 
	example of an efficient implementation.  An efficient implementation should
	use FIFO's or DMA if available, and only use FreeRTOS API functions when 
	enough has been received to warrant a task being unblocked to process the
	data.
*/

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "queue.h"
#include "semphr.h"
#include "comtest2.h"

/* Library includes. */
#include "stm32l152_eval.h"

/* Demo application includes. */
#include "serial.h"
/*-----------------------------------------------------------*/

/* Misc defines. */
#define serINVALID_QUEUE				( ( QueueHandle_t ) 0 )
#define serNO_BLOCK						( ( TickType_t ) 0 )

/*-----------------------------------------------------------*/

/* The queue used to hold received characters. */
static QueueHandle_t xRxedChars;
static QueueHandle_t xCharsForTx;

/*-----------------------------------------------------------*/

/*
 * See the serial2.h header file.
 */
xComPortHandle xSerialPortInitMinimal( unsigned long ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
USART_InitTypeDef USART_InitStructure;
xComPortHandle xReturn;
NVIC_InitTypeDef NVIC_InitStructure;

	/* Create the queues used to hold Rx/Tx characters. */
	xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed char ) );
	xCharsForTx = xQueueCreate( uxQueueLength + 1, ( unsigned portBASE_TYPE ) sizeof( signed char ) );
	
	/* If the queues were created correctly then setup the serial port
	hardware. */
	if( ( xRxedChars != serINVALID_QUEUE ) && ( xCharsForTx != serINVALID_QUEUE ) )
	{
		USART_InitStructure.USART_BaudRate = ulWantedBaud;
		USART_InitStructure.USART_WordLength = USART_WordLength_8b;
		USART_InitStructure.USART_StopBits = USART_StopBits_1;
		USART_InitStructure.USART_Parity = USART_Parity_No;
		USART_InitStructure.USART_HardwareFlowControl = USART_HardwareFlowControl_None;
		USART_InitStructure.USART_Mode = USART_Mode_Rx | USART_Mode_Tx;
		
		/* The Eval board COM2 is being used, which in reality is the STM32
		USART3. */
		STM_EVAL_COMInit( COM2, &USART_InitStructure );
		
		NVIC_InitStructure.NVIC_IRQChannel = USART3_IRQn;
		NVIC_InitStructure.NVIC_IRQChannelPreemptionPriority = configLIBRARY_MAX_SYSCALL_INTERRUPT_PRIORITY;
		NVIC_InitStructure.NVIC_IRQChannelSubPriority = 0; /* Not used as 4 bits are used for the pre-emption priority. */;
		NVIC_InitStructure.NVIC_IRQChannelCmd = ENABLE;
		NVIC_Init( &NVIC_InitStructure );
		USART_ITConfig( USART3, USART_IT_RXNE, ENABLE );
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

	/* The port handle is not required as this driver only supports UART1. */
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
signed portBASE_TYPE xReturn;

	if( xQueueSend( xCharsForTx, &cOutChar, xBlockTime ) == pdPASS )
	{
		xReturn = pdPASS;
		USART_ITConfig( USART3, USART_IT_TXE, ENABLE );
	}
	else
	{
		xReturn = pdFAIL;
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

void vSerialClose( xComPortHandle xPort )
{
	/* Not supported as not required by the demo application. */
}
/*-----------------------------------------------------------*/

void USART3_IRQHandler( void )
{
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;
char cChar;

	if( USART_GetITStatus( USART3, USART_IT_TXE ) == SET )
	{
		/* The interrupt was caused by the TX register becoming empty.  Are 
		there any more characters to transmit? */
		if( xQueueReceiveFromISR( xCharsForTx, &cChar, &xHigherPriorityTaskWoken ) == pdTRUE )
		{
			/* A character was retrieved from the queue so can be sent to the
			USART now. */
			USART_SendData( USART3, cChar );
		}
		else
		{
			USART_ITConfig( USART3, USART_IT_TXE, DISABLE );		
		}		
	}
	
	if( USART_GetITStatus( USART3, USART_IT_RXNE ) == SET )
	{
		/* A character has been received on the USART, send it to the Rx
		handler task. */
		cChar = USART_ReceiveData( USART3 );
		xQueueSendFromISR( xRxedChars, &cChar, &xHigherPriorityTaskWoken );
	}	

	/* If sending or receiving from a queue has caused a task to unblock, and
	the unblocked task has a priority equal to or higher than the currently 
	running task (the task this ISR interrupted), then xHigherPriorityTaskWoken 
	will have automatically been set to pdTRUE within the queue send or receive 
	function.  portEND_SWITCHING_ISR() will then ensure that this ISR returns 
	directly to the higher priority unblocked task. */
	portEND_SWITCHING_ISR( xHigherPriorityTaskWoken );
}





	
