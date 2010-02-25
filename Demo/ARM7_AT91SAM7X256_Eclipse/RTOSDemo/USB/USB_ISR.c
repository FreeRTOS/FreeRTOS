/*
    FreeRTOS V6.0.3 - Copyright (C) 2010 Real Time Engineers Ltd.

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
