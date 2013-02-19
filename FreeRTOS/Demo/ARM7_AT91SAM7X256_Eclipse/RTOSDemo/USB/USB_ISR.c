/*
    FreeRTOS V7.4.0 - Copyright (C) 2013 Real Time Engineers Ltd.

    FEATURES AND PORTS ARE ADDED TO FREERTOS ALL THE TIME.  PLEASE VISIT
    http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS tutorial books are available in pdf and paperback.        *
     *    Complete, revised, and edited pdf reference manuals are also       *
     *    available.                                                         *
     *                                                                       *
     *    Purchasing FreeRTOS documentation will not only help you, by       *
     *    ensuring you get running as quickly as possible and with an        *
     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
     *    the FreeRTOS project to continue with its mission of providing     *
     *    professional grade, cross platform, de facto standard solutions    *
     *    for microcontrollers - completely free of charge!                  *
     *                                                                       *
     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
     *                                                                       *
     *    Thank you for using FreeRTOS, and thank you for your support!      *
     *                                                                       *
    ***************************************************************************


    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.

    >>>>>>NOTE<<<<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
    details. You should have received a copy of the GNU General Public License
    and the FreeRTOS license exception along with FreeRTOS; if not itcan be
    viewed here: http://www.freertos.org/a00114.html and also obtained by
    writing to Real Time Engineers Ltd., contact details for whom are available
    on the FreeRTOS WEB site.

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
    including FreeRTOS+Trace - an indispensable productivity tool, and our new
    fully thread aware and reentrant UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High 
    Integrity Systems, who sell the code with commercial support, 
    indemnification and middleware, under the OpenRTOS brand.
    
    http://www.SafeRTOS.com - High Integrity Systems also provide a safety 
    engineered and independently SIL3 certified version for use in safety and 
    mission critical applications that require provable dependability.
*/

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/* Demo app includes. */
#include "USBSample.h"

#define usbINT_CLEAR_MASK	(AT91C_UDP_TXCOMP | AT91C_UDP_STALLSENT | AT91C_UDP_RXSETUP | AT91C_UDP_RX_DATA_BK0 | AT91C_UDP_RX_DATA_BK1 )

#define usbCSR_CLEAR_BIT( pulValueNow, ulBit )											\
{																						\
	/* Set TXCOMP, RX_DATA_BK0, RXSETUP, */												\
	/* STALLSENT and RX_DATA_BK1 to 1 so the */											\
	/* write has no effect. */															\
	( * ( ( unsigned long * ) pulValueNow ) ) |= ( unsigned long ) 0x4f;		\
																						\
	/* Clear the FORCE_STALL and TXPKTRDY bits */										\
	/* so the write has no effect. */													\
	( * ( ( unsigned long * ) pulValueNow ) ) &= ( unsigned long ) 0xffffffcf;	\
																						\
	/* Clear whichever bit we want clear. */											\
	( * ( ( unsigned long * ) pulValueNow ) ) &= ( ~ulBit );						\
}


/*-----------------------------------------------------------*/

/*
 * ISR entry point.
 */

void vUSB_ISR_Wrapper( void ) __attribute__((naked));

/*
 * Actual ISR handler.  This must be separate from the entry point as the stack
 * is used.
 */
void vUSB_ISR_Handler( void ) __attribute__((noinline));

/*-----------------------------------------------------------*/

/* Array in which the USB interrupt status is passed between the ISR and task. */
static xISRStatus xISRMessages[ usbQUEUE_LENGTH + 1 ];

/* Queue used to pass messages between the ISR and the task. */
extern xQueueHandle xUSBInterruptQueue; 

/*-----------------------------------------------------------*/

void vUSB_ISR_Handler( void )
{
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE; 
static volatile unsigned long ulNextMessage = 0;
xISRStatus *pxMessage;
unsigned long ulTemp, ulRxBytes;

	/* To reduce the amount of time spent in this interrupt it would be 
	possible to defer the majority of this processing to an 'interrupt task',
	that is a task that runs at a higher priority than any of the application
	tasks. */

	/* Take the next message from the queue.  Note that usbQUEUE_LENGTH *must*
	be all 1's, as in 0x01, 0x03, 0x07, etc. */
	pxMessage = &( xISRMessages[ ( ulNextMessage & usbQUEUE_LENGTH ) ] );
	ulNextMessage++;

	/* Take a snapshot of the current USB state for processing at the task
	level. */
	pxMessage->ulISR = AT91C_BASE_UDP->UDP_ISR;
	pxMessage->ulCSR0 = AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_0 ];

	/* Clear the interrupts from the ICR register.  The bus end interrupt is
	cleared separately as it does not appear in the mask register. */
	AT91C_BASE_UDP->UDP_ICR = AT91C_BASE_UDP->UDP_IMR | AT91C_UDP_ENDBUSRES;
	
	/* If there are bytes in the FIFO then we have to retrieve them here.  
	Ideally this would be done at the task level.  However we need to clear the
	RXSETUP interrupt before leaving the ISR, and this may cause the data in
	the FIFO to be overwritten.  Also the DIR bit has to be changed before the
	RXSETUP bit is cleared (as per the SAM7 manual). */
	ulTemp = pxMessage->ulCSR0;
	
	/* Are there any bytes in the FIFO? */
	ulRxBytes = ulTemp >> 16;
	ulRxBytes &= usbRX_COUNT_MASK;
	
	/* With this minimal implementation we are only interested in receiving 
	setup bytes on the control end point. */
	if( ( ulRxBytes > 0 ) && ( ulTemp & AT91C_UDP_RXSETUP ) )
	{
		/* Take off 1 for a zero based index. */
		while( ulRxBytes > 0 )
		{
			ulRxBytes--;
			pxMessage->ucFifoData[ ulRxBytes ] = AT91C_BASE_UDP->UDP_FDR[ usbEND_POINT_0 ];			
		}
		
		/* The direction must be changed first. */
		usbCSR_SET_BIT( &ulTemp, ( AT91C_UDP_DIR ) );
		AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_0 ] = ulTemp;
	}
	
	/* Must write zero's to TXCOMP, STALLSENT, RXSETUP, and the RX DATA
	registers to clear the interrupts in the CSR register. */
	usbCSR_CLEAR_BIT( &ulTemp, usbINT_CLEAR_MASK );
	AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_0 ] = ulTemp;

	/* Also clear the interrupts in the CSR1 register. */
	ulTemp = AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_1 ];
	usbCSR_CLEAR_BIT( &ulTemp, usbINT_CLEAR_MASK );	
	AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_1 ] = ulTemp;

	/* The message now contains the entire state and optional data from
	the USB interrupt.  This can now be posted on the Rx queue ready for
	processing at the task level. */
	xQueueSendFromISR( xUSBInterruptQueue, &pxMessage, &xHigherPriorityTaskWoken );

	/* We may want to switch to the USB task, if this message has made
	it the highest priority task that is ready to execute. */
	if( xHigherPriorityTaskWoken )
	{
		portYIELD_FROM_ISR();
	}

	/* Clear the AIC ready for the next interrupt. */		
	AT91C_BASE_AIC->AIC_EOICR = 0;
}
/*-----------------------------------------------------------*/

void vUSB_ISR_Wrapper( void )
{
	/* Save the context of the interrupted task. */
	portSAVE_CONTEXT();

	/* Call the handler itself.  This must be a separate function as it uses
	the stack. */
	__asm volatile ("bl vUSB_ISR_Handler");

	/* Restore the context of the task that is going to 
	execute next. This might not be the same as the originally 
	interrupted task.*/
	portRESTORE_CONTEXT();
}
