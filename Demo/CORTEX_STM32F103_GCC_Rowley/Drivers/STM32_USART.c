/*
    FreeRTOS V6.0.5 - Copyright (C) 2010 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS eBook                                  *
    *                                                                         *
    *        "Using the FreeRTOS Real Time Kernel - a Practical Guide"        *
    *                  http://www.FreeRTOS.org/Documentation                  *
    *                                                                         *
    * A pdf reference manual is also available.  Both are usually delivered   *
    * to your inbox within 20 minutes to two hours when purchased between 8am *
    * and 8pm GMT (although please allow up to 24 hours in case of            *
    * exceptional circumstances).  Thank you for your support!                *
    *                                                                         *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    ***NOTE*** The exception to the GPL is included to allow you to distribute
    a combined work that includes FreeRTOS without being obliged to provide the
    source code for proprietary components outside of the FreeRTOS kernel.
    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public 
    License and the FreeRTOS license exception along with FreeRTOS; if not it 
    can be viewed here: http://www.freertos.org/a00114.html and also obtained 
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!

    http://www.FreeRTOS.org - Documentation, latest information, license and
    contact details.

    http://www.SafeRTOS.com - A version that is certified for use in safety
    critical systems.

    http://www.OpenRTOS.com - Commercial support, development, porting,
    licensing and training services.
*/

/*
	INTERRUPT DRIVEN SERIAL PORT DRIVER.
*/


/******************************************************************************
*** NOTE:  COM0 == USART1, COM1 == USART2
******************************************************************************/


/* Scheduler includes. */
#include "FreeRTOS.h"
#include "queue.h"
#include "semphr.h"

/* Driver includes. */
#include "CircularBuffer.h"

/* Library includes. */
#include "stm32f10x_lib.h"
#include "stm32f10x_rcc.h"

/* Driver includes. */
#include "STM32_USART.h"
/*-----------------------------------------------------------*/

/* The number of COM ports that can be controlled at the same time. */
#define serNUM_COM_PORTS				( 2 )

/* Indexes into the xCOMBufferDefinitions array for the Rx and Tx buffers. */
#define serRX_BUFFER_INDEX				( 0 )
#define serTX_BUFFER_INDEX				( 1 )

/* A counting semaphore is used to allows tasks to block to wait for characters
to be received.  This constant defines the max count.  Making this value higher
does not change the amount of RAM used by the semaphore, so its worth making it
quite high. */
#define serSEMAPHORE_MAX_COUNT			( 100 )

/*-----------------------------------------------------------*/

/* An Rx and a Tx buffer structure for each COM port. */
static xCircularBuffer xCOMBufferDefinitions[ serNUM_COM_PORTS ][ 2 ];

/* The buffers themselves. */
static unsigned char ucCOM0_Rx_Buffer[ configCOM0_RX_BUFFER_LENGTH ];
static unsigned char ucCOM0_Tx_Buffer[ configCOM0_TX_BUFFER_LENGTH ];
static unsigned char ucCOM1_Rx_Buffer[ configCOM1_RX_BUFFER_LENGTH ];
static unsigned char ucCOM1_Tx_Buffer[ configCOM1_TX_BUFFER_LENGTH ];

/* Semaphores used to block tasks that are waiting for characters to be
received. */
static xSemaphoreHandle xCOM0RxSemaphore, xCOM1RxSemaphore;

/*-----------------------------------------------------------*/

/* UART interrupt handler. */
void vUARTInterruptHandler( void );

/*-----------------------------------------------------------*/

/*
 * See serial.h in this project for parameter descriptions.
 */
long lCOMPortInit( unsigned long ulPort, unsigned long ulWantedBaud )
{
long lReturn = pdFAIL;
USART_InitTypeDef USART_InitStructure;
NVIC_InitTypeDef NVIC_InitStructure;
GPIO_InitTypeDef GPIO_InitStructure;

	if( ulPort < serNUM_COM_PORTS )
	{
		/* The common (not port dependent) part of the initialisation. */
		USART_InitStructure.USART_BaudRate = ulWantedBaud;
		USART_InitStructure.USART_WordLength = USART_WordLength_8b;
		USART_InitStructure.USART_StopBits = USART_StopBits_1;
		USART_InitStructure.USART_Parity = USART_Parity_No;
		USART_InitStructure.USART_HardwareFlowControl = USART_HardwareFlowControl_None;
		USART_InitStructure.USART_Mode = USART_Mode_Rx | USART_Mode_Tx;
		NVIC_InitStructure.NVIC_IRQChannelPreemptionPriority = configLIBRARY_KERNEL_INTERRUPT_PRIORITY;
		NVIC_InitStructure.NVIC_IRQChannelSubPriority = 0;
		NVIC_InitStructure.NVIC_IRQChannelCmd = ENABLE;


		/* Init the buffer structures with the buffer for the COM port being
		initialised, and perform any non-common initialisation necessary.  This
		does not check to see if the COM port has already been initialised. */
		if( ulPort == 0 )
		{
			/* Create the semaphore used to enable tasks to block to wait for
			characters to be received. */
            xCOM0RxSemaphore = xSemaphoreCreateCounting( serSEMAPHORE_MAX_COUNT, 0 );

			vInitialiseCircularBuffer(	&( xCOMBufferDefinitions[ ulPort ][ serRX_BUFFER_INDEX ] ),
										ucCOM0_Rx_Buffer,
										configCOM0_RX_BUFFER_LENGTH,
										sizeof( unsigned char ),
										NULL
									);

			vInitialiseCircularBuffer(	&( xCOMBufferDefinitions[ ulPort ][ serTX_BUFFER_INDEX ] ),
										ucCOM0_Tx_Buffer,
										configCOM0_TX_BUFFER_LENGTH,
										sizeof( unsigned char ),
										NULL
									);

			/* Enable COM1 clock - the ST libraries start numbering from UART1, 
			making this UART 2. */
			RCC_APB2PeriphClockCmd( RCC_APB2Periph_USART1 | RCC_APB2Periph_GPIOA, ENABLE );	

			/* Configure USART1 Rx (PA10) as input floating */
			GPIO_InitStructure.GPIO_Pin = GPIO_Pin_10;
			GPIO_InitStructure.GPIO_Mode = GPIO_Mode_IN_FLOATING;
			GPIO_Init( GPIOA, &GPIO_InitStructure );
			
			/* Configure USART1 Tx (PA9) as alternate function push-pull */
			GPIO_InitStructure.GPIO_Pin = GPIO_Pin_9;
			GPIO_InitStructure.GPIO_Speed = GPIO_Speed_50MHz;
			GPIO_InitStructure.GPIO_Mode = GPIO_Mode_AF_PP;
			GPIO_Init( GPIOA, &GPIO_InitStructure );

			USART_Init( USART1, &USART_InitStructure );		
			USART_ITConfig( USART1, USART_IT_RXNE, ENABLE );
			
			NVIC_InitStructure.NVIC_IRQChannel = USART1_IRQChannel;
			NVIC_Init( &NVIC_InitStructure );
			
            USART_DMACmd( USART1, ( USART_DMAReq_Tx | USART_DMAReq_Rx ), ENABLE );
			USART_Cmd( USART1, ENABLE );	
		}
		else
		{
			/* Create the semaphore used to enable tasks to block to wait for
			characters to be received. */
            xCOM1RxSemaphore = xSemaphoreCreateCounting( serSEMAPHORE_MAX_COUNT, 0 );

			vInitialiseCircularBuffer(	&( xCOMBufferDefinitions[ ulPort ][ serRX_BUFFER_INDEX ] ),
										ucCOM1_Rx_Buffer,
										configCOM1_RX_BUFFER_LENGTH,
										sizeof( unsigned char ),
										NULL
									);

			vInitialiseCircularBuffer(	&( xCOMBufferDefinitions[ ulPort ][ serTX_BUFFER_INDEX ] ),
										ucCOM1_Tx_Buffer,
										configCOM1_TX_BUFFER_LENGTH,
										sizeof( unsigned char ),
										NULL
									);

			/* Enable COM0 clock - the ST libraries start numbering from 1. */
			RCC_APB2PeriphClockCmd( RCC_APB1Periph_USART2 | RCC_APB2Periph_GPIOA, ENABLE );	

			/* Configure USART2 Rx (PA3) as input floating */
			GPIO_InitStructure.GPIO_Pin = GPIO_Pin_3;
			GPIO_InitStructure.GPIO_Mode = GPIO_Mode_IN_FLOATING;
			GPIO_Init( GPIOA, &GPIO_InitStructure );
			
			/* Configure USART2 Tx (PA2) as alternate function push-pull */
			GPIO_InitStructure.GPIO_Pin = GPIO_Pin_2;
			GPIO_InitStructure.GPIO_Speed = GPIO_Speed_50MHz;
			GPIO_InitStructure.GPIO_Mode = GPIO_Mode_AF_PP;
			GPIO_Init( GPIOA, &GPIO_InitStructure );

			USART_Init( USART2, &USART_InitStructure );		
			USART_ITConfig( USART2, USART_IT_RXNE, ENABLE );
			
			NVIC_InitStructure.NVIC_IRQChannel = USART2_IRQChannel;
			NVIC_Init( &NVIC_InitStructure );
			
            USART_DMACmd( USART2, ( USART_DMAReq_Tx | USART_DMAReq_Rx ), ENABLE );
			USART_Cmd( USART2, ENABLE );	
		}	
			
		/* Everything is ok. */
		lReturn = pdPASS;
	}
	
	return lReturn;
}
/*-----------------------------------------------------------*/

signed long xUSARTGetChar( long lPort, signed char *pcRxedChar, portTickType xBlockTime )
{
	return pdFALSE;
}
/*-----------------------------------------------------------*/

void vSerialPutString( long lPort, const signed char * const pcString, unsigned portSHORT usStringLength )
{
}
/*-----------------------------------------------------------*/

signed long xSerialPutChar( long lPort, signed char cOutChar, portTickType xBlockTime )
{
	return pdFALSE;
}
/*-----------------------------------------------------------*/

void vUARTInterruptHandler( void )
{
long xHigherPriorityTaskWoken = pdFALSE;
char cChar;

	if( USART_GetITStatus( USART1, USART_IT_TXE ) == SET )
	{
		/* The interrupt was caused by the THR becoming empty.  Are there any
		more characters to transmit? */
if( 0 )//		if( xQueueReceiveFromISR( xCharsForTx, &cChar, &xHigherPriorityTaskWoken ) == pdTRUE )
		{
			/* A character was retrieved from the queue so can be sent to the
			THR now. */
			USART_SendData( USART1, cChar );
		}
		else
		{
			USART_ITConfig( USART1, USART_IT_TXE, DISABLE );		
		}		
	}
	
	if( USART_GetITStatus( USART1, USART_IT_RXNE ) == SET )
	{
		cChar = USART_ReceiveData( USART1 );
//		xQueueSendFromISR( xRxedChars, &cChar, &xHigherPriorityTaskWoken );
	}	
	
	portEND_SWITCHING_ISR( xHigherPriorityTaskWoken );
}





	
