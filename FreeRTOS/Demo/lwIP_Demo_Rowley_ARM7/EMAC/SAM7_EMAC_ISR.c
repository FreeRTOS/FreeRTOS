/*
 * FreeRTOS Kernel V10.0.0
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. If you wish to use our Amazon
 * FreeRTOS name, please do so in a fair use way that does not cause confusion.
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


#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"
#include "SAM7_EMAC.h"
#include "AT91SAM7X256.h"

/*-----------------------------------------------------------*/

/* The semaphore used to signal the arrival of new data to the interface
task. */
static SemaphoreHandle_t xSemaphore = NULL;

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

void vPassEMACSemaphore( SemaphoreHandle_t xCreatedSemaphore )
{
	/* Simply store the semaphore that should be used by the ISR. */
	xSemaphore = xCreatedSemaphore;
}

