/*
	FreeRTOS.org V5.4.0 - Copyright (C) 2003-2009 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify it
	under the terms of the GNU General Public License (version 2) as published
	by the Free Software Foundation and modified by the FreeRTOS exception.
	**NOTE** The exception to the GPL is included to allow you to distribute a
	combined work that includes FreeRTOS.org without being obliged to provide
	the source code for any proprietary components.  Alternative commercial
	license and support terms are also available upon request.  See the 
	licensing section of http://www.FreeRTOS.org for full details.

	FreeRTOS.org is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
	more details.

	You should have received a copy of the GNU General Public License along
	with FreeRTOS.org; if not, write to the Free Software Foundation, Inc., 59
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.


	***************************************************************************
	*                                                                         *
	* Get the FreeRTOS eBook!  See http://www.FreeRTOS.org/Documentation      *
	*                                                                         *
	* This is a concise, step by step, 'hands on' guide that describes both   *
	* general multitasking concepts and FreeRTOS specifics. It presents and   *
	* explains numerous examples that are written using the FreeRTOS API.     *
	* Full source code for all the examples is provided in an accompanying    *
	* .zip file.                                                              *
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
 * This file defines the button push task and ISR as described at the top of
 * main.c.  The ISR is called from a wrapper function defined in ButtonISR.s26.
 */

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* The LED output used by the button push task. */
#define butLED1   P7_bit.no7

/* A short delay used for button debouncing. */
#define butDEBOUNCE_DELAY	( 200 / portTICK_RATE_MS )

/* The semaphore used to synchronise the button push task with the interrupt. */
static xSemaphoreHandle xButtonSemaphore;

/*
 * The definition of the button task itself.  See the comments at the top of
 * main.c.
 */
void vButtonTask( void *pvParameters )
{
	/* Ensure the semaphore is created before it gets used. */
	vSemaphoreCreateBinary( xButtonSemaphore );

	for( ;; )
	{
		/* Block on the semaphore to wait for an interrupt event.  The semaphore
		is 'given' from vButtonISRHandler() below.  Using portMAX_DELAY as the
		block time will cause the task to block indefinitely provided
		INCLUDE_vTaskSuspend is set to 1 in FreeRTOSConfig.h. */
		xSemaphoreTake( xButtonSemaphore, portMAX_DELAY );

		/* The button must have been pushed for this line to be executed.
		Simply toggle the LED. */
		butLED1 = !butLED1;
		
		/* Wait a short time then clear any pending button pushes as a crude
		method of debouncing the switch.  xSemaphoreTake() uses a block time of
		zero this time so it returns immediately rather than waiting for the
		interrupt to occur. */
		vTaskDelay( butDEBOUNCE_DELAY );
		xSemaphoreTake( xButtonSemaphore, 0 );
	}
}
/*-----------------------------------------------------------*/

/*
 * The C portion of the interrupt handler.  Interrupts are triggered by pushing
 * the button on the target board.  This interrupt can cause a context switch
 * so has an assembly file wrapper defined within ButtonISR.s26.
 */
void vButtonISRHandler( void )
{
short sHigherPriorityTaskWoken = pdFALSE;

	/* 'Give' the semaphore to unblock the button task. */
	xSemaphoreGiveFromISR( xButtonSemaphore, &sHigherPriorityTaskWoken );
	
	/* If giving the semaphore unblocked a task, and the unblocked task has a
	priority that is higher than the currently running task, then
	sHigherPriorityTaskWoken will have been set to pdTRUE.  Passing a pdTRUE
	value to portYIELD_FROM_ISR() will cause this interrupt to return directly
	to the higher priority unblocked task. */
	portYIELD_FROM_ISR( sHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/
