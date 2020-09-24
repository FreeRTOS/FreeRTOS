/*
 * FreeRTOS Kernel V10.4.1
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
	BASIC INTERRUPT DRIVEN SERIAL PORT DRIVER FOR UART1.
*/

/* Library includes. */
#include "91x_lib.h"

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "queue.h"
#include "semphr.h"

/* Demo application includes. */
#include "serial.h"
/*-----------------------------------------------------------*/

/* Misc defines. */
#define serINVALID_QUEUE				( ( QueueHandle_t ) 0 )
#define serNO_BLOCK						( ( TickType_t ) 0 )
#define serTX_BLOCK_TIME				( 40 / portTICK_PERIOD_MS )

/* Interrupt and status bit definitions. */
#define mainTXRIS 0x20	
#define mainRXRIS 0x50
#define serTX_FIFO_FULL 0x20
#define serCLEAR_ALL_INTERRUPTS 0x3ff
/*-----------------------------------------------------------*/

/* The queue used to hold received characters. */
static QueueHandle_t xRxedChars;

/* The semaphore used to wake a task waiting for space to become available
in the FIFO. */
static SemaphoreHandle_t xTxFIFOSemaphore;

/*-----------------------------------------------------------*/

/* UART interrupt handler. */
void UART1_IRQHandler( void );

/* The interrupt service routine - called from the assembly entry point. */
__arm void UART1_IRQHandler( void );

/*-----------------------------------------------------------*/

/* Flag to indicate whether or not a task is blocked waiting for space on
the FIFO. */
static long lTaskWaiting = pdFALSE;

/*
 * See the serial2.h header file.
 */
xComPortHandle xSerialPortInitMinimal( unsigned long ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
xComPortHandle xReturn;
UART_InitTypeDef xUART1_Init;
GPIO_InitTypeDef GPIO_InitStructure;
	
	/* Create the queues used to hold Rx characters. */
	xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed char ) );
	
	/* Create the semaphore used to wake a task waiting for space to become
	available in the FIFO. */
	vSemaphoreCreateBinary( xTxFIFOSemaphore );

	/* If the queue/semaphore was created correctly then setup the serial port
	hardware. */
	if( ( xRxedChars != serINVALID_QUEUE ) && ( xTxFIFOSemaphore != serINVALID_QUEUE ) )
	{
		/* Pre take the semaphore so a task will block if it tries to access
		it. */
		xSemaphoreTake( xTxFIFOSemaphore, 0 );
		
		/* Configure the UART. */
		xUART1_Init.UART_WordLength = UART_WordLength_8D;
		xUART1_Init.UART_StopBits = UART_StopBits_1;
		xUART1_Init.UART_Parity = UART_Parity_No;
		xUART1_Init.UART_BaudRate = ulWantedBaud;
		xUART1_Init.UART_HardwareFlowControl = UART_HardwareFlowControl_None;
		xUART1_Init.UART_Mode = UART_Mode_Tx_Rx;
		xUART1_Init.UART_FIFO = UART_FIFO_Enable;

		/* Enable the UART1 Clock */
		SCU_APBPeriphClockConfig( __UART1, ENABLE );
		
		/* Enable the GPIO3 Clock */
		SCU_APBPeriphClockConfig( __GPIO3, ENABLE );
		
		/* Configure UART1_Rx pin GPIO3.2 */
		GPIO_InitStructure.GPIO_Direction = GPIO_PinInput;
		GPIO_InitStructure.GPIO_Pin = GPIO_Pin_2;
		GPIO_InitStructure.GPIO_Type = GPIO_Type_PushPull ;
		GPIO_InitStructure.GPIO_IPConnected = GPIO_IPConnected_Enable;
		GPIO_InitStructure.GPIO_Alternate = GPIO_InputAlt1 ;
		GPIO_Init( GPIO3, &GPIO_InitStructure );
		
		/* Configure UART1_Tx pin GPIO3.3 */
		GPIO_InitStructure.GPIO_Direction = GPIO_PinOutput;
		GPIO_InitStructure.GPIO_Pin = GPIO_Pin_3;
		GPIO_InitStructure.GPIO_Type = GPIO_Type_PushPull ;
		GPIO_InitStructure.GPIO_IPConnected = GPIO_IPConnected_Enable;
		GPIO_InitStructure.GPIO_Alternate = GPIO_OutputAlt2 ;
		GPIO_Init( GPIO3, &GPIO_InitStructure );
		
		
		portENTER_CRITICAL();
		{		
			/* Configure the UART itself. */
			UART_DeInit( UART1 );		
			UART_Init( UART1, &xUART1_Init );
			UART_ITConfig( UART1, UART_IT_Receive | UART_IT_Transmit, ENABLE );
			UART1->ICR = serCLEAR_ALL_INTERRUPTS;
			UART_LoopBackConfig( UART1, DISABLE );
			UART_IrDACmd( IrDA1, DISABLE );

			/* Configure the VIC for the UART interrupts. */			
			VIC_Config( UART1_ITLine, VIC_IRQ, 9 );
			VIC_ITCmd( UART1_ITLine, ENABLE );

			UART_Cmd( UART1, ENABLE );			
			lTaskWaiting = pdFALSE;
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
portBASE_TYPE xReturn;

	portENTER_CRITICAL();
	{
		/* Can we write to the FIFO? */
		if( UART1->FR & serTX_FIFO_FULL )
		{
			/* Wait for the interrupt letting us know there is space on the
			FIFO.  It is ok to block in a critical section, interrupts will be
			enabled	for other tasks once we force a switch. */
			lTaskWaiting = pdTRUE;
			
			/* Just to be a bit different this driver uses a semaphore to
			block the sending task when the FIFO is full.  The standard COMTest
			task assumes a queue of adequate length exists so does not use
			a block time.  For this demo the block time is therefore hard
			coded. */
			xReturn = xSemaphoreTake( xTxFIFOSemaphore, serTX_BLOCK_TIME );
			if( xReturn )
			{
				UART1->DR = cOutChar;
			}
		}
		else
		{
			UART1->DR = cOutChar;
			xReturn = pdPASS;
		}
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

void UART1_IRQHandler( void )
{
signed char cChar;
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	while( UART1->RIS &	mainRXRIS )
	{
		/* The interrupt was caused by a character being received.  Grab the
		character from the DR and place it in the queue of received
		characters. */
		cChar = UART1->DR;
		xQueueSendFromISR( xRxedChars, &cChar, &xHigherPriorityTaskWoken );
	}	
	
	if( UART1->RIS & mainTXRIS )
	{
		if( lTaskWaiting == pdTRUE )
		{
			/* This interrupt was caused by space becoming available on the Tx
			FIFO, wake any task that is waiting to post (if any). */
			xSemaphoreGiveFromISR( xTxFIFOSemaphore, &xHigherPriorityTaskWoken );
			lTaskWaiting = pdFALSE;
		}
		
		UART1->ICR = mainTXRIS;
	}

	/* If a task was woken by either a character being received or a character
	being transmitted then we may need to switch to another task. */
	portEND_SWITCHING_ISR( xHigherPriorityTaskWoken );
}





	
