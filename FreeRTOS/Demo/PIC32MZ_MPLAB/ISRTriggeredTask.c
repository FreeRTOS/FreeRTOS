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

/*
 * Interrupt service routines that cannot nest have no special requirements and
 * can be written as per the compiler documentation. However interrupts written
 * in this manner will utilise the stack of whichever task was interrupts,
 * rather than the system stack, necessitating that adequate stack space be
 * allocated to each created task. It is therefore not recommended to write
 * interrupt service routines in this manner.
 *
 * Interrupts service routines that can nest require a simple assembly wrapper.
 * This file is provided as a example of how this is done.
 *
 * The example in this file creates a single task.  The task blocks on a
 * semaphore which is periodically 'given' from a timer interrupt.  The assembly
 * wrapper for the interrupt is implemented in ISRTriggeredTask_isr.S.  The
 * C function called by the assembly wrapper is implemented in this file.
 *
 * The task toggle LED mainISR_TRIGGERED_LED each time it is unblocked by the
 * interrupt.
 */


/* Standard includes. */
#include <stdio.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* Standard demo includes. */
#include "ParTest.h"

/*-----------------------------------------------------------*/

/* The LED controlled by the ISR triggered task. */
#define mainISR_TRIGGERED_LED				( 1 )

/* Constants used to configure T5. */
#define mainT5PRESCALAR						( 6 )
#define mainT5_SEMAPHORE_RATE				( 31250 )

/*-----------------------------------------------------------*/

/*
 * The task that is periodically triggered by an interrupt, as described at the
 * top of this file.
 */
static void prvISRTriggeredTask( void* pvParameters );

/*
 * Configures the T5 timer peripheral to generate the interrupts that unblock
 * the task implemented by the prvISRTriggeredTask() function.
 */
static void prvSetupT5( void );

/* The timer 5 interrupt handler.  As this interrupt uses the FreeRTOS assembly
entry point the IPL setting in the following function prototype has no effect. */
void __attribute__( (interrupt(IPL3AUTO), vector(_TIMER_5_VECTOR))) vT5InterruptWrapper( void );

/*-----------------------------------------------------------*/

/* The semaphore given by the T5 interrupt to unblock the task implemented by
 the prvISRTriggeredTask() function. */
static SemaphoreHandle_t xBlockSemaphore = NULL;
/*-----------------------------------------------------------*/

void vStartISRTriggeredTask( void )
{
	/* Create the task described at the top of this file.  The timer is
	configured by the task itself. */
	xTaskCreate( prvISRTriggeredTask, 		/* The function that implements the task. */
				"ISRt", 					/* Text name to help debugging - not used by the kernel. */
				configMINIMAL_STACK_SIZE, 	/* The size of the stack to allocate to the task - defined in words, not bytes. */
				NULL, 						/* The parameter to pass into the task.  Not used in this case. */
				configMAX_PRIORITIES - 1, 	/* The priority at which the task is created. */
				NULL );						/* Used to pass a handle to the created task out of the function.  Not used in this case. */
}
/*-----------------------------------------------------------*/

void vT5InterruptHandler( void )
{
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	/* This function is the handler for the peripheral timer interrupt.
	The interrupt is initially signalled in a separate assembly file
	which switches to the system stack and then calls this function.
	It gives a semaphore which signals the prvISRBlockTask */

	/* Give the semaphore.  If giving the semaphore causes the task to leave the
	Blocked state, and the priority of the task is higher than the priority of
	the interrupted task, then xHigherPriorityTaskWoken will be set to pdTRUE
	inside the xSemaphoreGiveFromISR() function.  xHigherPriorityTaskWoken is
	later passed into portEND_SWITCHING_ISR(), where a context switch is
	requested if it is pdTRUE.  The context switch ensures the interrupt returns
	directly to the unblocked task. */
	xSemaphoreGiveFromISR( xBlockSemaphore, &xHigherPriorityTaskWoken );

	/* Clear the interrupt */
	IFS0CLR = _IFS0_T5IF_MASK;

	/* See comment above the call to xSemaphoreGiveFromISR(). */
	portEND_SWITCHING_ISR( xHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/

static void prvISRTriggeredTask( void* pvParameters )
{
	/* Avoid compiler warnings. */
	( void ) pvParameters;

	/* Create the semaphore used to signal this task */
	xBlockSemaphore = xSemaphoreCreateBinary();

	/* Configure the timer to generate the interrupts. */
	prvSetupT5();

	for( ;; )
	{
		/* Block on the binary semaphore given by the T5 interrupt. */
		xSemaphoreTake( xBlockSemaphore, portMAX_DELAY );

		/* Toggle the LED. */
		vParTestToggleLED( mainISR_TRIGGERED_LED );
	}
}
/*-----------------------------------------------------------*/

static void prvSetupT5( void )
{
	/* Set up timer 5 to generate an interrupt every 50 ms */
	T5CON = 0;
	TMR5 = 0;
	T5CONbits.TCKPS = mainT5PRESCALAR;
	PR5 = mainT5_SEMAPHORE_RATE;

	/* Setup timer 5 interrupt priority to be the maximum from which interrupt
	safe FreeRTOS API functions can be called.  Interrupt safe FreeRTOS API
	functions are those that end "FromISR". */
	IPC6bits.T5IP = configMAX_SYSCALL_INTERRUPT_PRIORITY;

	/* Clear the interrupt as a starting condition. */
	IFS0bits.T5IF = 0;

	/* Enable the interrupt. */
	IEC0bits.T5IE = 1;

	/* Start the timer. */
	T5CONbits.TON = 1;
}
