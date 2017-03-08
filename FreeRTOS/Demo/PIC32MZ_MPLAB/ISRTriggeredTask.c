/*
    FreeRTOS V9.0.1 - Copyright (C) 2017 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>>> AND MODIFIED BY <<<< the FreeRTOS exception.

    ***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
    ***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that is more than just the market leader, it     *
     *    is the industry's de facto standard.                               *
     *                                                                       *
     *    Help yourself get started quickly while simultaneously helping     *
     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
     *    tutorial book, reference manual, or both:                          *
     *    http://www.FreeRTOS.org/Documentation                              *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
    the FAQ page "My application does not run, what could be wrong?".  Have you
    defined configASSERT()?

    http://www.FreeRTOS.org/support - In return for receiving this top quality
    embedded software for free we request you assist our global community by
    participating in the support forum.

    http://www.FreeRTOS.org/training - Investing in training allows your team to
    be as productive as possible as early as possible.  Now you can receive
    FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
    Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
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
