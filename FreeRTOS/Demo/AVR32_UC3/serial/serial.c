/*This file has been prepared for Doxygen automatic documentation generation.*/
/*! \file *********************************************************************
 *
 * \brief FreeRTOS Serial Port management example for AVR32 UC3.
 *
 * - Compiler:           IAR EWAVR32 and GNU GCC for AVR32
 * - Supported devices:  All AVR32 devices can be used.
 * - AppNote:
 *
 * \author               Atmel Corporation: http://www.atmel.com \n
 *                       Support and FAQ: http://support.atmel.no/
 *
 *****************************************************************************/

/* Copyright (c) 2007, Atmel Corporation All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 *
 * 3. The name of ATMEL may not be used to endorse or promote products derived
 * from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY ATMEL ``AS IS'' AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE EXPRESSLY AND
 * SPECIFICALLY DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */


/*
  BASIC INTERRUPT DRIVEN SERIAL PORT DRIVER FOR USART.
*/

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "queue.h"
#include "task.h"

/* Demo application includes. */
#include "serial.h"
#include <avr32/io.h>
#include "board.h"
#include "gpio.h"

/*-----------------------------------------------------------*/

/* Constants to setup and access the USART. */
#define serINVALID_COMPORT_HANDLER        ( ( xComPortHandle ) 0 )
#define serINVALID_QUEUE                  ( ( QueueHandle_t ) 0 )
#define serHANDLE                         ( ( xComPortHandle ) 1 )
#define serNO_BLOCK                       ( ( TickType_t ) 0 )

/*-----------------------------------------------------------*/

/* Queues used to hold received characters, and characters waiting to be
transmitted. */
static QueueHandle_t xRxedChars;
static QueueHandle_t xCharsForTx;

/*-----------------------------------------------------------*/

/* Forward declaration. */
static void vprvSerialCreateQueues( unsigned portBASE_TYPE uxQueueLength,
									QueueHandle_t *pxRxedChars,
									QueueHandle_t *pxCharsForTx );

/*-----------------------------------------------------------*/

#if __GNUC__
	__attribute__((__noinline__))
#elif __ICCAVR32__
	#pragma optimize = no_inline
#endif

static portBASE_TYPE prvUSART_ISR_NonNakedBehaviour( void )
{
	/* Now we can declare the local variables. */
	signed char     cChar;
	portBASE_TYPE     xHigherPriorityTaskWoken = pdFALSE;
	unsigned long     ulStatus;
	volatile avr32_usart_t  *usart = serialPORT_USART;
	portBASE_TYPE retstatus;

	/* What caused the interrupt? */
	ulStatus = usart->csr & usart->imr;

	if (ulStatus & AVR32_USART_CSR_TXRDY_MASK)
	{
		/* The interrupt was caused by the THR becoming empty.  Are there any
		more characters to transmit?
		Because FreeRTOS is not supposed to run with nested interrupts, put all OS
		calls in a critical section . */
		portENTER_CRITICAL();
			retstatus = xQueueReceiveFromISR( xCharsForTx, &cChar, &xHigherPriorityTaskWoken );
		portEXIT_CRITICAL();

		if (retstatus == pdTRUE)
		{
			/* A character was retrieved from the queue so can be sent to the
			 THR now. */
			usart->thr = cChar;
		}
		else
		{
			/* Queue empty, nothing to send so turn off the Tx interrupt. */
			usart->idr = AVR32_USART_IDR_TXRDY_MASK;
		}
	}

	if (ulStatus & AVR32_USART_CSR_RXRDY_MASK)
	{
		/* The interrupt was caused by the receiver getting data. */
		cChar = usart->rhr; //TODO

		/* Because FreeRTOS is not supposed to run with nested interrupts, put all OS
		calls in a critical section . */
		portENTER_CRITICAL();
			xQueueSendFromISR(xRxedChars, &cChar, &xHigherPriorityTaskWoken);
		portEXIT_CRITICAL();
	}

	/* The return value will be used by portEXIT_SWITCHING_ISR() to know if it
	should perform a vTaskSwitchContext(). */
	return ( xHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/

/*
 * USART interrupt service routine.
 */
#if __GNUC__
	__attribute__((__naked__))
#elif __ICCAVR32__
	#pragma shadow_registers = full   // Naked.
#endif

static void vUSART_ISR( void )
{
	/* This ISR can cause a context switch, so the first statement must be a
	call to the portENTER_SWITCHING_ISR() macro.  This must be BEFORE any
	variable declarations. */
	portENTER_SWITCHING_ISR();

	prvUSART_ISR_NonNakedBehaviour();

	/* Exit the ISR.  If a task was woken by either a character being received
	or transmitted then a context switch will occur. */
	portEXIT_SWITCHING_ISR();
}
/*-----------------------------------------------------------*/


/*
 * Init the serial port for the Minimal implementation.
 */
xComPortHandle xSerialPortInitMinimal( unsigned long ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
static const gpio_map_t USART_GPIO_MAP =
{
	{ serialPORT_USART_RX_PIN, serialPORT_USART_RX_FUNCTION },
	{ serialPORT_USART_TX_PIN, serialPORT_USART_TX_FUNCTION }
};

xComPortHandle    xReturn = serHANDLE;
volatile avr32_usart_t  *usart = serialPORT_USART;
int cd; /* USART Clock Divider. */

	/* Create the rx and tx queues. */
	vprvSerialCreateQueues( uxQueueLength, &xRxedChars, &xCharsForTx );

	/* Configure USART. */
	if( ( xRxedChars != serINVALID_QUEUE ) &&
	  ( xCharsForTx != serINVALID_QUEUE ) &&
	  ( ulWantedBaud != ( unsigned long ) 0 ) )
	{
		portENTER_CRITICAL();
		{
			/**
			** Reset USART.
			**/
			/* Disable all USART interrupt sources to begin... */
			usart->idr = 0xFFFFFFFF;

			/* Reset mode and other registers that could cause unpredictable
			 behaviour after reset */
			usart->mr = 0; /* Reset Mode register. */
			usart->rtor = 0; /* Reset Receiver Time-out register. */
			usart->ttgr = 0; /* Reset Transmitter Timeguard register. */

			/* Shutdown RX and TX, reset status bits, reset iterations in CSR, reset NACK
			 and turn off DTR and RTS */
			usart->cr = AVR32_USART_CR_RSTRX_MASK   |
					   AVR32_USART_CR_RSTTX_MASK   |
					   AVR32_USART_CR_RXDIS_MASK   |
					   AVR32_USART_CR_TXDIS_MASK   |
					   AVR32_USART_CR_RSTSTA_MASK  |
					   AVR32_USART_CR_RSTIT_MASK   |
					   AVR32_USART_CR_RSTNACK_MASK |
					   AVR32_USART_CR_DTRDIS_MASK  |
					   AVR32_USART_CR_RTSDIS_MASK;

			/**
			** Configure USART.
			**/
			/* Enable USART RXD & TXD pins. */
			gpio_enable_module( USART_GPIO_MAP, sizeof( USART_GPIO_MAP ) / sizeof( USART_GPIO_MAP[0] ) );

			/* Set the USART baudrate to be as close as possible to the wanted baudrate. */
			/*
			*             ** BAUDRATE CALCULATION **
			*
			*                 Selected Clock                       Selected Clock
			*     baudrate = ----------------   or     baudrate = ----------------
			*                    16 x CD                              8 x CD
			*
			*       (with 16x oversampling)              (with 8x oversampling)
			*/

			if( ulWantedBaud < ( configCPU_CLOCK_HZ / 16 ) )
			{
				/* Use 8x oversampling */
				usart->mr |= (1<<AVR32_USART_MR_OVER_OFFSET);
				cd = configCPU_CLOCK_HZ / (8*ulWantedBaud);

				if( cd < 2 )
				{
					return serINVALID_COMPORT_HANDLER;
				}

				usart->brgr = (cd << AVR32_USART_BRGR_CD_OFFSET);
			}
			else
			{
				/* Use 16x oversampling */
				usart->mr &= ~(1<<AVR32_USART_MR_OVER_OFFSET);
				cd = configCPU_CLOCK_HZ / (16*ulWantedBaud);

				if( cd > 65535 )
				{
					/* Baudrate is too low */
					return serINVALID_COMPORT_HANDLER;
				}
			}

			usart->brgr = (cd << AVR32_USART_BRGR_CD_OFFSET);

			/* Set the USART Mode register: Mode=Normal(0), Clk selection=MCK(0),
			CHRL=8,  SYNC=0(asynchronous), PAR=None, NBSTOP=1, CHMODE=0, MSBF=0,
			MODE9=0, CKLO=0, OVER(previously done when setting the baudrate),
			other fields not used in this mode. */
			usart->mr |= ((8-5) << AVR32_USART_MR_CHRL_OFFSET  ) |
					(   4  << AVR32_USART_MR_PAR_OFFSET   ) |
					(   1  << AVR32_USART_MR_NBSTOP_OFFSET);

			/* Write the Transmit Timeguard Register */
			usart->ttgr = 0;


			/* Register the USART interrupt handler to the interrupt controller and
			 enable the USART interrupt. */
			INTC_register_interrupt((__int_handler)&vUSART_ISR, serialPORT_USART_IRQ, INT1);

			/* Enable USART interrupt sources (but not Tx for now)... */
			usart->ier = AVR32_USART_IER_RXRDY_MASK;

			/* Enable receiver and transmitter... */
			usart->cr |= AVR32_USART_CR_TXEN_MASK | AVR32_USART_CR_RXEN_MASK;
		}
		portEXIT_CRITICAL();
	}
	else
	{
		xReturn = serINVALID_COMPORT_HANDLER;
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, signed char *pcRxedChar, TickType_t xBlockTime )
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

void vSerialPutString( xComPortHandle pxPort, const signed char * const pcString, unsigned short usStringLength )
{
signed char *pxNext;

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
volatile avr32_usart_t  *usart = serialPORT_USART;

	/* Place the character in the queue of characters to be transmitted. */
	if( xQueueSend( xCharsForTx, &cOutChar, xBlockTime ) != pdPASS )
	{
		return pdFAIL;
	}

	/* Turn on the Tx interrupt so the ISR will remove the character from the
	queue and send it.   This does not need to be in a critical section as
	if the interrupt has already removed the character the next interrupt
	will simply turn off the Tx interrupt again. */
	usart->ier = (1 << AVR32_USART_IER_TXRDY_OFFSET);

	return pdPASS;
}
/*-----------------------------------------------------------*/

void vSerialClose( xComPortHandle xPort )
{
  /* Not supported as not required by the demo application. */
}
/*-----------------------------------------------------------*/

/*###########################################################*/

/*
 * Create the rx and tx queues.
 */
static void vprvSerialCreateQueues(  unsigned portBASE_TYPE uxQueueLength, QueueHandle_t *pxRxedChars, QueueHandle_t *pxCharsForTx )
{
	/* Create the queues used to hold Rx and Tx characters. */
	xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed char ) );
	xCharsForTx = xQueueCreate( uxQueueLength + 1, ( unsigned portBASE_TYPE ) sizeof( signed char ) );

	/* Pass back a reference to the queues so the serial API file can
	post/receive characters. */
	*pxRxedChars = xRxedChars;
	*pxCharsForTx = xCharsForTx;
}
/*-----------------------------------------------------------*/
