/*
    FreeRTOS V7.5.0 - Copyright (C) 2013 Real Time Engineers Ltd.

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that has become a de facto standard.             *
     *                                                                       *
     *    Help yourself get started quickly and support the FreeRTOS         *
     *    project by purchasing a FreeRTOS tutorial book, reference          *
     *    manual, or both from: http://www.FreeRTOS.org/Documentation        *
     *                                                                       *
     *    Thank you!                                                         *
     *                                                                       *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    >>! NOTE: The modification to the GPL is included to allow you to distribute
    >>! a combined work that includes FreeRTOS without being obliged to provide
    >>! the source code for proprietary components outside of the FreeRTOS
    >>! kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available from the following
    link: http://www.freertos.org/a00114.html

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org - Documentation, books, training, latest versions,
    license and Real Time Engineers Ltd. contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

/*
	INTERRUPT DRIVEN SERIAL PORT DRIVER.
*/


/******************************************************************************
*** NOTE:  COM0 == USART1, COM1 == USART2
******************************************************************************/


/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* Library includes. */
#include "stm32f10x_lib.h"

/* Driver includes. */
#include "STM32_USART.h"
/*-----------------------------------------------------------*/

/* The number of COM ports that can be controlled at the same time. */
#define serNUM_COM_PORTS				( 2 )

/* Queues are used to hold characters that are waiting to be transmitted.  This
constant sets the maximum number of characters that can be contained in such a
queue at any one time. */
#define serTX_QUEUE_LEN					( 100 )

/* Queues are used to hold characters that have been received but not yet 
processed.  This constant sets the maximum number of characters that can be 
contained in such a queue. */
#define serRX_QUEUE_LEN					( 100 )

/* The maximum amount of time that calls to lSerialPutString() should wait for
there to be space to post each character to the queue of characters waiting
transmission.  NOTE!  This is the time to wait per character - not the time to
wait for the entire string. */
#define serPUT_STRING_CHAR_DELAY		( 5 / portTICK_RATE_MS )

/*-----------------------------------------------------------*/

/* References to the USART peripheral addresses themselves. */
static USART_TypeDef * const xUARTS[ serNUM_COM_PORTS ] = { ( ( USART_TypeDef * ) USART1_BASE ), ( ( USART_TypeDef * ) USART2_BASE ) };

/* Queues used to hold characters waiting to be transmitted - one queue per port. */
static xQueueHandle xCharsForTx[ serNUM_COM_PORTS ] = { 0 };

/* Queues holding received characters - one queue per port. */
static xQueueHandle xRxedChars[ serNUM_COM_PORTS ] = { 0 };

/*-----------------------------------------------------------*/

/* UART interrupt handlers, as named in the vector table. */
void USART1_IRQHandler( void );
void USART2_IRQHandler( void );

/*-----------------------------------------------------------*/

/*
 * See header file for parameter descriptions.
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
			/* Create the queue of chars that are waiting to be sent to COM0. */
			xCharsForTx[ 0 ] = xQueueCreate( serTX_QUEUE_LEN, sizeof( char ) );

			/* Create the queue used to hold characters received from COM0. */
			xRxedChars[ 0 ] = xQueueCreate( serRX_QUEUE_LEN, sizeof( char ) );

			/* Enable COM0 clock - the ST libraries start numbering from UART1. */
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

			/* Everything is ok. */
			lReturn = pdPASS;
		}
		else if( ulPort == 1 )
		{
			/* Create the queue of chars that are waiting to be sent to COM1. */
			xCharsForTx[ 1 ] = xQueueCreate( serTX_QUEUE_LEN, sizeof( char ) );

			/* Create the queue used to hold characters received from COM0. */
			xRxedChars[ 1 ] = xQueueCreate( serRX_QUEUE_LEN, sizeof( char ) );

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

			/* Everything is ok. */
			lReturn = pdPASS;
		}	
		else
		{
			/* Nothing to do unless more than two ports are supported. */
		}
	}
	
	return lReturn;
}
/*-----------------------------------------------------------*/

signed long xSerialGetChar( long lPort, signed char *pcRxedChar, portTickType xBlockTime )
{
long lReturn = pdFAIL;

	if( lPort < serNUM_COM_PORTS ) 
	{
		if( xQueueReceive( xRxedChars[ lPort ], pcRxedChar, xBlockTime ) == pdPASS )
		{
			lReturn = pdPASS;
		}
	}

	return lReturn;
}
/*-----------------------------------------------------------*/

long lSerialPutString( long lPort, const char * const pcString, unsigned long ulStringLength )
{
long lReturn;
unsigned long ul;

	if( lPort < serNUM_COM_PORTS )
	{
		lReturn = pdPASS;

		for( ul = 0; ul < ulStringLength; ul++ )
		{
			if( xQueueSend( xCharsForTx[ lPort ], &( pcString[ ul ] ), serPUT_STRING_CHAR_DELAY ) != pdPASS )
			{
				/* Cannot fit any more in the queue.  Try turning the Tx on to 
				clear some space. */
				USART_ITConfig( xUARTS[ lPort ], USART_IT_TXE, ENABLE );
				vTaskDelay( serPUT_STRING_CHAR_DELAY );

				/* Go back and try again. */
				continue;
			}
		}

        USART_ITConfig( xUARTS[ lPort ], USART_IT_TXE, ENABLE );
	}
	else
	{
		lReturn = pdFAIL;
	}

	return lReturn;
}
/*-----------------------------------------------------------*/

signed long xSerialPutChar( long lPort, signed char cOutChar, portTickType xBlockTime )
{
long lReturn;

	if( xQueueSend( xCharsForTx[ lPort ], &cOutChar, xBlockTime ) == pdPASS )
	{
		lReturn = pdPASS;
		USART_ITConfig( xUARTS[ lPort ], USART_IT_TXE, ENABLE );
	}
	else
	{
		lReturn = pdFAIL;
	}

	return lReturn;
}
/*-----------------------------------------------------------*/

void USART1_IRQHandler( void )
{
long xHigherPriorityTaskWoken = pdFALSE;
char cChar;

	if( USART_GetITStatus( USART1, USART_IT_TXE ) == SET )
	{
		/* The interrupt was caused by the THR becoming empty.  Are there any
		more characters to transmit? */
		if( xQueueReceiveFromISR( xCharsForTx[ 0 ], &cChar, &xHigherPriorityTaskWoken ) )
		{
			/* A character was retrieved from the buffer so can be sent to the
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
		xQueueSendFromISR( xRxedChars[ 0 ], &cChar, &xHigherPriorityTaskWoken );
	}	
	
	portEND_SWITCHING_ISR( xHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/

void USART2_IRQHandler( void )
{
}




	
