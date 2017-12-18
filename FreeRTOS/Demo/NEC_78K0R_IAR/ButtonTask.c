/*
 * FreeRTOS Kernel V10.0.1
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
#define butDEBOUNCE_DELAY	( 200 / portTICK_PERIOD_MS )

/* The semaphore used to synchronise the button push task with the interrupt. */
static SemaphoreHandle_t xButtonSemaphore;

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
