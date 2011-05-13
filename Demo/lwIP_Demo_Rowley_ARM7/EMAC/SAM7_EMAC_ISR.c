/*
    FreeRTOS V7.0.1 - Copyright (C) 2011 Real Time Engineers Ltd.
	

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
#include "task.h"
#include "semphr.h"
#include "SAM7_EMAC.h"
#include "AT91SAM7X256.h"

/*-----------------------------------------------------------*/

/* The semaphore used to signal the arrival of new data to the interface
task. */
static xSemaphoreHandle xSemaphore = NULL;

/* The interrupt entry point is naked so we can control the context saving. */
void vEMACISR_Wrapper( void ) __attribute__((naked));

/* The interrupt handler function must be separate from the entry function
to ensure the correct stack frame is set up. */
void vEMACISR_Handler( void );

/*-----------------------------------------------------------*/
/*
 * The EMAC ISR.  Handles both Tx and Rx complete interrupts.
 */
void vEMACISR_Handler( void )
{
volatile unsigned long ulIntStatus, ulEventStatus;
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;
extern void vClearEMACTxBuffer( void );

	/* Find the cause of the interrupt. */
	ulIntStatus = AT91C_BASE_EMAC->EMAC_ISR;
	ulEventStatus = AT91C_BASE_EMAC->EMAC_RSR;

	if( ( ulIntStatus & AT91C_EMAC_RCOMP ) || ( ulEventStatus & AT91C_EMAC_REC ) )
	{
		/* A frame has been received, signal the lwIP task so it can process
		the Rx descriptors. */
		xSemaphoreGiveFromISR( xSemaphore, &xHigherPriorityTaskWoken );
		AT91C_BASE_EMAC->EMAC_RSR = AT91C_EMAC_REC;
	}

	if( ulIntStatus & AT91C_EMAC_TCOMP )
	{
		/* A frame has been transmitted.  Mark all the buffers used by the
		frame just transmitted as free again. */
		vClearEMACTxBuffer();
		AT91C_BASE_EMAC->EMAC_TSR = AT91C_EMAC_COMP;
	}

	/* Clear the interrupt. */
	AT91C_BASE_AIC->AIC_EOICR = 0;

	/* If a task was woken by either a frame being received then we may need to 
	switch to another task.  If the unblocked task was of higher priority then
	the interrupted task it will then execute immediately that the ISR
	completes. */
	if( xHigherPriorityTaskWoken )
	{
		portYIELD_FROM_ISR();
	}
}
/*-----------------------------------------------------------*/

void  vEMACISR_Wrapper( void )
{
	/* Save the context of the interrupted task. */
	portSAVE_CONTEXT();

	/* Call the handler to do the work.  This must be a separate
	function to ensure the stack frame is set up correctly. */
	vEMACISR_Handler();

	/* Restore the context of whichever task will execute next. */
	portRESTORE_CONTEXT();
}
/*-----------------------------------------------------------*/

void vPassEMACSemaphore( xSemaphoreHandle xCreatedSemaphore )
{
	/* Simply store the semaphore that should be used by the ISR. */
	xSemaphore = xCreatedSemaphore;
}

