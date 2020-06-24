/*
 * FreeRTOS Kernel V10.3.1
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
	
	***NOTE*** 
	The implementation provided in this file is intended to demonstrate using
	queues to pass data into and out of interrupts, and to demonstrate context 
	switching from inside an interrupt service routine.  It is *not* intended to 
	represent an efficient implementation.  Real implementations should not pass 
	individual characters on queues, but instead use RAM buffers, DMA and/or 
	FIFO features as appropriate.  Semaphores can be used to signal a task that 
	data is	available to be processed.
*/

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "queue.h"
#include "semphr.h"

/* Demo application includes. */
#include "serial.h"

/*-----------------------------------------------------------*/

/* Registers required to configure the SCI. */
#define serialSCI_GCR0_REG  		( * ( ( volatile unsigned long * ) 0xFFF7E400 ) )
#define serialSCI_GCR1_REG    		( * ( ( volatile unsigned long * ) 0xFFF7E404 ) )
#define serialSCI_GCR2_REG    		( * ( ( volatile unsigned long * ) 0xFFF7E408 ) )
#define serialSCI_SETINT_REG  		( * ( ( volatile unsigned long * ) 0xFFF7E40C ) )
#define serialSCI_CLRINT_REG  		( * ( ( volatile unsigned long * ) 0xFFF7E410 ) )
#define serialSCI_SETINTLVL_REG  	( * ( ( volatile unsigned long * ) 0xFFF7E414 ) )
#define serialSCI_CLRINTLVL_REG		( * ( ( volatile unsigned long * ) 0xFFF7E418 ) )
#define serialSCI_FLR_REG	    	( * ( ( volatile unsigned long * ) 0xFFF7E41C ) )
#define serialSCI_INTVEC0_REG	   	( * ( ( volatile unsigned long * ) 0xFFF7E420 ) )
#define serialSCI_INTVEC1_REG	   	( * ( ( volatile unsigned long * ) 0xFFF7E424 ) )
#define serialSCI_LENGTH_REG	   	( * ( ( volatile unsigned long * ) 0xFFF7E428 ) )
#define serialSCI_BAUD_REG	    	( * ( ( volatile unsigned long * ) 0xFFF7E42C ) )
#define serialSCI_RD_REG	    	( * ( ( volatile unsigned long * ) 0xFFF7E434 ) )
#define serialSCI_TD_REG	    	( * ( ( volatile unsigned long * ) 0xFFF7E438 ) )
#define serialSCI_FUN_REG	    	( * ( ( volatile unsigned long * ) 0xFFF7E43C ) )
#define serialSCI_DIR_REG	    	( * ( ( volatile unsigned long * ) 0xFFF7E440 ) )
#define serialSCI_DIN_REG	    	( * ( ( volatile unsigned long * ) 0xFFF7E444 ) )
#define serialSCI_DOUT_REG	    	( * ( ( volatile unsigned long * ) 0xFFF7E448 ) )
#define serialSCI_DSET_REG	    	( * ( ( volatile unsigned long * ) 0xFFF7E44C ) )
#define serialSCI_DCLR_REG	    	( * ( ( volatile unsigned long * ) 0xFFF7E450 ) )

/* SCI constants */
#define serialSCI_FE_INT    ( 0x04000000 )  /* framming error */
#define serialSCI_OE_INT    ( 0x02000000 )  /* overrun error */
#define serialSCI_PE_INT    ( 0x01000000 )  /* parity error */
#define serialSCI_RX_INT    ( 0x00000200 )  /* receive buffer ready */
#define serialSCI_TX_INT    ( 0x00000100 )  /* transmit buffer ready */
#define serialSCI_WAKE_INT  ( 0x00000002 )  /* wakeup */
#define serialSCI_BREAK_INT ( 0x00000001 )  /* break detect */
#define serialSCI_IDLE_FLG  ( 0x00000004 )  /* IDLE flasg */

/* Registers required to configure the VIM. */
#define serialVIM_REQMASKSET0_REG	( * ( ( volatile unsigned long * ) 0xFFFFFE30 ) )
#define serialVIM_SCIHINT_RAM       ( * ( ( void (**)(void) ) 0xFFF82038 ) )

/* Baudrate */
#define serialBAURATE     	19200.0			/* Baudrate in Hz */

/*-----------------------------------------------------------*/

/* Misc defines. */
#define serINVALID_QUEUE				( ( QueueHandle_t ) 0 )
#define serNO_BLOCK						( ( TickType_t ) 0 )
#define serTX_BLOCK_TIME				( 40 / portTICK_PERIOD_MS )

/*-----------------------------------------------------------*/

/* The queue used to hold received characters. */
static QueueHandle_t xRxedChars = NULL;
static QueueHandle_t xCharsForTx = NULL;

/*-----------------------------------------------------------*/

/* UART interrupt handler. */
__interrupt void vSCIInterruptHandler( void );

/*-----------------------------------------------------------*/

/*
 * See the serial2.h header file.
 */
xComPortHandle xSerialPortInitMinimal( unsigned long ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
xComPortHandle xReturn = ( xComPortHandle ) 0;

	/* unused parameters, demo has a fixed baud rate (19200) */
	( void ) ulWantedBaud;

	/* Create the queues used to hold Rx/Tx characters. */
	xRxedChars  = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed char ) );
	xCharsForTx = xQueueCreate( uxQueueLength + 1, ( unsigned portBASE_TYPE ) sizeof( signed char ) );
	
	/* If the queue/semaphore was created correctly then setup the serial port
	hardware. */
	if( ( xRxedChars != serINVALID_QUEUE ) && ( xCharsForTx != serINVALID_QUEUE ) )
	{
		/* Initalise SCI1 */
	    /* Bring SCI out of reset */
		serialSCI_GCR0_REG = 0x00000001UL;
	    /* Disable all interrupts */
		serialSCI_CLRINT_REG = 0xFFFFFFFFUL;
		/* All Interrupt to SCI High Level */
		serialSCI_CLRINTLVL_REG = 0xFFFFFFFFUL;
	    /* Global control 1 */
		serialSCI_GCR1_REG = 0x03010032UL;
	    /* Baudrate */
		serialSCI_BAUD_REG = ((unsigned long)((configCPU_CLOCK_HZ / (16.0 * serialBAURATE) + 0.5)) - 1) & 0x00FFFFFF;
	    /* Transmission length (8-bit) */
		serialSCI_LENGTH_REG = 8 - 1;
	    /* Set SCI pins functional mode */
		serialSCI_FUN_REG = 0x00000006UL;
	    /* Enable RX interrupt */
	    serialSCI_SETINT_REG = 0x00000200UL;
	    /* Finally start SCI1 */
	    serialSCI_GCR1_REG |= 0x00000080UL;

		/* Setup interrupt routine address in VIM table */
	    serialVIM_SCIHINT_RAM = &vSCIInterruptHandler;
		/* Enable SCI interrupt in VIM */
	    serialVIM_REQMASKSET0_REG = 0x00002000UL;
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

	/* NOTE: This implementation does not handle the queue being full as no
	block time is used! */

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

	/* check if we are already transmitting */
	if ( (serialSCI_SETINT_REG & serialSCI_TX_INT) == 0)
	{
		/* First byte */

		/* Wait until IDLE idle period is finished */
		while ( (serialSCI_FLR_REG & serialSCI_IDLE_FLG) != 0 ) 
		{ 
			/* wait */ 
		};
		
		/* Need to send first byte before interrupts flags are set. */
		serialSCI_TD_REG = cOutChar;
		
		/* Enable the TX interrupt. */
		serialSCI_SETINT_REG = serialSCI_TX_INT;

		xReturn = pdPASS;
	}
	else if( xQueueSend( xCharsForTx, &cOutChar, xBlockTime ) == pdPASS )
	{
		xReturn = pdPASS;
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

__interrupt void vSCIInterruptHandler( void )
{
/* xHigherPriorityTaskWoken must be initialised to pdFALSE. */
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;
char cChar;
portBASE_TYPE xVectorValue = serialSCI_INTVEC0_REG;

	switch( xVectorValue )
	{
		case 11:
			/* Receive buffer full interrupt, send received char to queue */
			cChar = serialSCI_RD_REG;
			xQueueSendFromISR( xRxedChars, &cChar, &xHigherPriorityTaskWoken );
			break;

		case 12:
			/* Transmit buffer empty interrupt received */
			/* Are there any more characters to transmit? */
			if( xQueueReceiveFromISR( xCharsForTx, &cChar, &xHigherPriorityTaskWoken ) == pdTRUE )
			{
				/* A character was retrieved from the queue so can be sent to
				the TD now. */
				serialSCI_TD_REG = cChar;
			}
			else
			{
				/* no more bytes, clear the TX interrupt */
				serialSCI_CLRINT_REG = serialSCI_TX_INT;
			}
			break;

		default:
			/* unused interrupt, clear flags */
			serialSCI_FLR_REG = 0x07000003;
	}

	/* If calling xQueueSendFromISR() above caused a task to leave the blocked
	state, and the task that left the blocked state has a priority above the
	task that this interrupt interrupted, then xHighPriorityTaskWoken will have
	been set to pdTRUE.  If xHigherPriorityTaskWoken equals true then calling
	portYIELD_FROM_ISR() will result in this interrupt returning directly to the
	unblocked task. */
	portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
}





	
