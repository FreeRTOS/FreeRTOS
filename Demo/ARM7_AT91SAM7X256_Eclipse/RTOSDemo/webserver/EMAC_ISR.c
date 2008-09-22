/*
	FreeRTOS.org V5.0.4 - Copyright (C) 2003-2008 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation; either version 2 of the License, or
	(at your option) any later version.

	FreeRTOS.org is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with FreeRTOS.org; if not, write to the Free Software
	Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

	A special exception to the GPL can be applied should you wish to distribute
	a combined work that includes FreeRTOS.org, without being obliged to provide
	the source code for any proprietary components.  See the licensing section 
	of http://www.FreeRTOS.org for full details of how and when the exception
	can be applied.

    ***************************************************************************
    ***************************************************************************
    *                                                                         *
    * SAVE TIME AND MONEY!  We can port FreeRTOS.org to your own hardware,    *
    * and even write all or part of your application on your behalf.          *
    * See http://www.OpenRTOS.com for details of the services we provide to   *
    * expedite your project.                                                  *
    *                                                                         *
    ***************************************************************************
    ***************************************************************************

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

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
void vEMACISR_Handler( void );

static xSemaphoreHandle xEMACSemaphore;

/*-----------------------------------------------------------*/

void vPassEMACSemaphore( xSemaphoreHandle xSemaphore )
{
	xEMACSemaphore = xSemaphore;
}
/*-----------------------------------------------------------*/

void vEMACISR_Handler( void )
{
volatile unsigned portLONG ulIntStatus, ulRxStatus;
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
	vEMACISR_Handler();
	
	/* Restore the context of whichever task is the next to run. */
	portRESTORE_CONTEXT();
}


