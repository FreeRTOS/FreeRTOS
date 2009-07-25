/*
	FreeRTOS V5.4.1 - Copyright (C) 2009 Real Time Engineers Ltd.

	This file is part of the FreeRTOS distribution.

	FreeRTOS is free software; you can redistribute it and/or modify it	under 
	the terms of the GNU General Public License (version 2) as published by the 
	Free Software Foundation and modified by the FreeRTOS exception.
	**NOTE** The exception to the GPL is included to allow you to distribute a
	combined work that includes FreeRTOS without being obliged to provide the 
	source code for proprietary components outside of the FreeRTOS kernel.  
	Alternative commercial license and support terms are also available upon 
	request.  See the licensing section of http://www.FreeRTOS.org for full 
	license details.

	FreeRTOS is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
	more details.

	You should have received a copy of the GNU General Public License along
	with FreeRTOS; if not, write to the Free Software Foundation, Inc., 59
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.


	***************************************************************************
	*                                                                         *
	* Looking for a quick start?  Then check out the FreeRTOS eBook!          *
	* See http://www.FreeRTOS.org/Documentation for details                   *
	*                                                                         *
	***************************************************************************

	1 tab == 4 spaces!

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

	http://www.FreeRTOS.org - Documentation, latest information, license and
	contact details.

	http://www.SafeRTOS.com - A version that is certified for use in safety
	critical systems.

	http://www.OpenRTOS.com - Commercial support, development, porting,
	licensing and training services.
*/


/* 
  BASIC INTERRUPT DRIVEN DRIVER FOR USB. 

  This file contains all the usb components that must be compiled
  to ARM mode.  The components that can be compiled to either ARM or THUMB
  mode are contained in USB-CDC.c.

*/

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/* Demo application includes. */
#include "Board.h"
#include "usb.h"
#include "USB-CDC.h"

#define usbINT_CLEAR_MASK	(AT91C_UDP_TXCOMP | AT91C_UDP_STALLSENT | AT91C_UDP_RXSETUP | AT91C_UDP_RX_DATA_BK0 | AT91C_UDP_RX_DATA_BK1 )
/*-----------------------------------------------------------*/

/* Messages and queue used to communicate between the ISR and the USB task. */
static xISRStatus xISRMessages[ usbQUEUE_LENGTH + 1 ];
extern xQueueHandle xUSBInterruptQueue;
/*-----------------------------------------------------------*/

/* The ISR can cause a context switch so is declared naked. */
void vUSB_ISR_Wrapper( void ) __attribute__ ((naked));

/* The function that actually performs the ISR work.  This must be separate
from the wrapper function to ensure the correct stack frame gets set up. */
void vUSB_ISR_Handler( void );
/*-----------------------------------------------------------*/

void vUSB_ISR_Handler( void )
{
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;
static volatile unsigned portLONG ulNextMessage = 0;
xISRStatus *pxMessage;
unsigned portLONG ulRxBytes;
unsigned portCHAR ucFifoIndex;

    /* Use the next message from the array. */
	pxMessage = &( xISRMessages[ ( ulNextMessage & usbQUEUE_LENGTH ) ] );
	ulNextMessage++;

    /* Save UDP ISR state for task-level processing. */
	pxMessage->ulISR = AT91C_BASE_UDP->UDP_ISR;
	pxMessage->ulCSR0 = AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_0 ];

    /* Clear interrupts from ICR. */
	AT91C_BASE_UDP->UDP_ICR = AT91C_BASE_UDP->UDP_IMR | AT91C_UDP_ENDBUSRES;
	
    
	/* Process incoming FIFO data.  Must set DIR (if needed) and clear RXSETUP 
	before exit. */

    /* Read CSR and get incoming byte count. */
	ulRxBytes = ( pxMessage->ulCSR0 >> 16 ) & usbRX_COUNT_MASK;
	
	/* Receive control transfers on endpoint 0. */
	if( pxMessage->ulCSR0 & ( AT91C_UDP_RXSETUP | AT91C_UDP_RX_DATA_BK0 ) )
	{
		/* Save FIFO data buffer for either a SETUP or DATA stage */
		for( ucFifoIndex = 0; ucFifoIndex < ulRxBytes; ucFifoIndex++ )
		{
			pxMessage->ucFifoData[ ucFifoIndex ] = AT91C_BASE_UDP->UDP_FDR[ usbEND_POINT_0 ];
		}

		/* Set direction for data stage.  Must be done before RXSETUP is 
		cleared. */
		if( ( AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_0 ] & AT91C_UDP_RXSETUP ) )
		{
			if( ulRxBytes && ( pxMessage->ucFifoData[ usbREQUEST_TYPE_INDEX ] & 0x80 ) )
			{
				AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_0 ] |= AT91C_UDP_DIR;

				/* Might not be wise in an ISR! */
				while( !(AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_0 ] & AT91C_UDP_DIR) );
			}

			/* Clear RXSETUP */
			AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_0 ] &= ~AT91C_UDP_RXSETUP;

			/* Might not be wise in an ISR! */
			while ( AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_0 ] & AT91C_UDP_RXSETUP );
		}
		else
		{
		   /* Clear RX_DATA_BK0 */
		   AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_0 ] &= ~AT91C_UDP_RX_DATA_BK0;

		   /* Might not be wise in an ISR! */
		   while ( AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_0 ] & AT91C_UDP_RX_DATA_BK0 );
		}
	}
	
	/* If we received data on endpoint 1, disable its interrupts until it is 
	processed in the main loop */
	if( AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_1 ] & ( AT91C_UDP_RX_DATA_BK0 | AT91C_UDP_RX_DATA_BK1 ) )
	{
		AT91C_BASE_UDP->UDP_IDR = AT91C_UDP_EPINT1;
	}
	
	AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_0 ] &= ~( AT91C_UDP_TXCOMP | AT91C_UDP_STALLSENT );
     
	/* Clear interrupts for the other endpoints, retain data flags for endpoint 
	1. */
	AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_1 ] &= ~( AT91C_UDP_TXCOMP | AT91C_UDP_STALLSENT | AT91C_UDP_RXSETUP );
	AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_2 ] &= ~usbINT_CLEAR_MASK;
	AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_3 ] &= ~usbINT_CLEAR_MASK;

	/* Post ISR data to queue for task-level processing */
	xQueueSendFromISR( xUSBInterruptQueue, &pxMessage, &xHigherPriorityTaskWoken );

	/* Clear AIC to complete ISR processing */
	AT91C_BASE_AIC->AIC_EOICR = 0;

	/* Do a task switch if needed */
	if( xHigherPriorityTaskWoken )
	{
		/* This call will ensure that the unblocked task will be executed
		immediately upon completion of the ISR if it has a priority higher
		than the interrupted task. */
		portYIELD_FROM_ISR();
	}
}
/*-----------------------------------------------------------*/

void vUSB_ISR_Wrapper( void )
{
	/* Save the context of the interrupted task. */
	portSAVE_CONTEXT();

	/* Call the handler to do the work.  This must be a separate
	function to ensure the stack frame is set up correctly. */
	vUSB_ISR_Handler();

	/* Restore the context of whichever task will execute next. */
	portRESTORE_CONTEXT();
}


