/*
    FreeRTOS V7.0.2 - Copyright (C) 2011 Real Time Engineers Ltd.
	

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
    >>>NOTE<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.  FreeRTOS is distributed in the hope that it will be useful, but
    WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
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

#include "FreeRTOS.h"
#include "semphr.h"
#include "task.h"

/* Wrapper for the EMAC interrupt. */
void vEMACISR_Wrapper( void ) __attribute__((naked));

/* Handler called by the ISR wrapper.  This must be kept a separate
function to ensure the stack frame is correctly set up. */
void vEMACISR_Handler( void ) __attribute__((noinline));

static xSemaphoreHandle xEMACSemaphore;

/*-----------------------------------------------------------*/

void vPassEMACSemaphore( xSemaphoreHandle xSemaphore )
{
	xEMACSemaphore = xSemaphore;
}
/*-----------------------------------------------------------*/

void vEMACISR_Handler( void )
{
volatile unsigned long ulIntStatus, ulRxStatus;
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	ulIntStatus = AT91C_BASE_EMAC->EMAC_ISR;
	ulRxStatus = AT91C_BASE_EMAC->EMAC_RSR;

	if( ( ulIntStatus & AT91C_EMAC_RCOMP ) || ( ulRxStatus & AT91C_EMAC_REC ) )
	{
		/* A frame has been received, signal the uIP task so it can process
		the Rx descriptors. */
		xSemaphoreGiveFromISR( xEMACSemaphore, &xHigherPriorityTaskWoken );
		AT91C_BASE_EMAC->EMAC_RSR = AT91C_EMAC_REC;
	}

	/* Clear the interrupt. */
	AT91C_BASE_AIC->AIC_EOICR = 0;
	
    /* Switch to the uIP task. */
    if( xHigherPriorityTaskWoken )
    {
    	/* If a task of higher priority than the interrupted task was
    	unblocked by the ISR then this call will ensure that the 
    	unblocked task is the task the ISR returns to. */
    	portYIELD_FROM_ISR();
    }
}
/*-----------------------------------------------------------*/

void vEMACISR_Wrapper( void )
{
	/* Save the context of the interrupted task. */
	portSAVE_CONTEXT();
	
	/* Call the handler task to do the actual work.  This must be a separate
	function to ensure the stack frame is correctly set up. */
	__asm volatile ("bl vEMACISR_Handler");
	
	/* Restore the context of whichever task is the next to run. */
	portRESTORE_CONTEXT();
}


