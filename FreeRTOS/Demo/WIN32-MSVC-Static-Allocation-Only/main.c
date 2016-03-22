/*
    FreeRTOS V9.0.0rc1 - Copyright (C) 2016 Real Time Engineers Ltd.
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

/******************************************************************************
 *
 * This project is provided as an example of how to create a FreeRTOS project
 * that does not need a heap.  configSUPPORT_STATIC_ALLOCATION is set to 1 to
 * allow RTOS objects to be created using statically allocated RAM, and
 * configSUPPORT_DYNAMIC_ALLOCATION is set to 0 to remove any build dependency
 * on the FreeRTOS heap.  When configSUPPORT_DYNAMIC_ALLOCATION is set to 0
 * pvPortMalloc() just equates to NULL, and calls to vPortFree() have no
 * effect.  See:
 *
 * http://www.freertos.org/a00111.html and
 * http://www.freertos.org/Static_Vs_Dynamic_Memory_Allocation.html
 *
 *******************************************************************************
 */

/* Standard includes. */
#include <stdio.h>
#include <stdlib.h>
#include <conio.h>

/* FreeRTOS kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Standard demo includes. */
#include "StaticAllocation.h"


/*-----------------------------------------------------------*/

/*
 * Prototypes for the standard FreeRTOS stack overflow hook (callback)
 * function.  http://www.freertos.org/Stacks-and-stack-overflow-checking.html
 */
void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName );

/*
 * This demo has configSUPPORT_STATIC_ALLOCATION set to 1 so the following
 * application callback function must be provided to supply the RAM that will
 * get used for the Idle task data structures and stack.
 */
void vApplicationGetIdleTaskMemory( StaticTask_t **ppxIdleTaskTCBBuffer, StackType_t **ppxIdleTaskStackBuffer, uint16_t *pusIdleTaskStackSize );

/*
* This demo has configSUPPORT_STATIC_ALLOCATION set to 1 and configUSE_TIMERS
* set to 1 so the following application callback function must be provided to
* supply the RAM that will get used for the Timer task data structures and
* stack.
*/
void vApplicationGetTimerTaskMemory( StaticTask_t **ppxTimerTaskTCBBuffer, StackType_t **ppxTimerTaskStackBuffer, uint16_t *pusTimerTaskStackSize );

/* This demo only uses the standard demo tasks that use statically allocated
RAM.  A 'check' task is also created to periodically inspect the demo tasks to
ensure they are still running, and that no errors have been detected. */
static void prvStartCheckTask( void );
static void prvCheckTask( void *pvParameters );

/*-----------------------------------------------------------*/

int main( void )
{
	/* This demo has configSUPPORT_STATIC_ALLOCATION set to 1 and
	configSUPPORT_DYNAMIC_ALLOCATION set to 0, so the only standard temo tasks
	created are the ones that only use static allocation.  This allow the
	application to be built without including a FreeRTOS heap file (without one
	of the heap files described on http://www.freertos.org/a00111.html */
	vStartStaticallyAllocatedTasks();

	/* Start a task that periodically inspects the tasks created by
	vStartStaticallyAllocatedTasks() to ensure they are still running, and not
	reporting any errors. */
	prvStartCheckTask();

	/* Start the scheduler so the demo tasks start to execute. */
	vTaskStartScheduler();

	/* vTaskStartScheduler() would only return if RAM required by the Idle and
	Timer tasks could not be allocated.  As this demo uses statically allocated
	RAM only, there are no allocations that could fail, and
	vTaskStartScheduler() cannot return - so there is no need to put the normal
	infinite loop after the call to vTaskStartScheduler(). */

	return 0;
}
/*-----------------------------------------------------------*/

static void prvStartCheckTask( void )
{
/* Allocate the data structure that will hold the task's TCB.  NOTE:  This is
declared static so it still exists after this function has returned. */
static StaticTask_t xCheckTask;

/* Allocate the stack that will be used by the task.  NOTE:  This is declared
static so it still exists after this function has returned. */
static StackType_t ucTaskStack[ configMINIMAL_STACK_SIZE * sizeof( StackType_t ) ];

	/* Create the task, which will use the RAM allocated by the linker to the
	variables declared in this function. */
	xTaskCreateStatic( prvCheckTask, "Check", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, NULL, ucTaskStack, &xCheckTask );
}
/*-----------------------------------------------------------*/

static void prvCheckTask( void *pvParameters )
{
const TickType_t xCycleFrequency = pdMS_TO_TICKS( 2500UL );
static char *pcStatusMessage = "No errors";

	/* Just to remove compiler warning. */
	( void ) pvParameters;

	for( ;; )
	{
		/* Place this task in the blocked state until it is time to run again. */
		vTaskDelay( xCycleFrequency );

		/* Check the tasks that use static allocation are still executing. */
		if( xAreStaticAllocationTasksStillRunning() != pdPASS )
		{
			pcStatusMessage = "Error: Static allocation";
		}

		/* This is the only task that uses stdout so its ok to call printf()
		directly. */
		printf( "%s - tick count %d - number of tasks executing %d\r\n",
													pcStatusMessage,
													xTaskGetTickCount(),
													uxTaskGetNumberOfTasks() );
	}
}

/*-----------------------------------------------------------*/
void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName )
{
	( void ) pcTaskName;
	( void ) pxTask;

	/* Run time stack overflow checking is performed if
	configCHECK_FOR_STACK_OVERFLOW is defined to 1 or 2.  This hook
	function is called if a stack overflow is detected.  This function is
	provided as an example only as stack overflow checking does not function
	when running the FreeRTOS Windows port. */
	vAssertCalled( __LINE__, __FILE__ );
}
/*-----------------------------------------------------------*/

void vAssertCalled( unsigned long ulLine, const char * const pcFileName )
{
volatile uint32_t ulSetToNonZeroInDebuggerToContinue = 0;

	/* Called if an assertion passed to configASSERT() fails.  See
	http://www.freertos.org/a00110.html#configASSERT for more information. */

	/* Parameters are not used. */
	( void ) ulLine;
	( void ) pcFileName;

	printf( "ASSERT! Line %d, file %s\r\n", ulLine, pcFileName );

 	taskENTER_CRITICAL();
	{
		/* You can step out of this function to debug the assertion by using
		the debugger to set ulSetToNonZeroInDebuggerToContinue to a non-zero
		value. */
		while( ulSetToNonZeroInDebuggerToContinue == 0 )
		{
			__asm{ NOP };
			__asm{ NOP };
		}
	}
	taskEXIT_CRITICAL();
}
/*-----------------------------------------------------------*/

void vApplicationGetIdleTaskMemory( StaticTask_t **ppxIdleTaskTCBBuffer, StackType_t **ppxIdleTaskStackBuffer, uint16_t *pusIdleTaskStackSize )
{
/* The buffers used by the idle task must be static so they are persistent, and
so exist after this function returns. */
static StaticTask_t xIdleTaskTCB;
static StackType_t uxIdleTaskStack[ configMINIMAL_STACK_SIZE ];

	/* configSUPORT_STATIC_ALLOCATION is set to 1 and
	configSUPPORT_DYNAMIC_ALLOCATION is 0, so the application must supply the
	buffers that will be used to hold the Idle task data structure and stack. */
	*ppxIdleTaskTCBBuffer = &xIdleTaskTCB;
	*ppxIdleTaskStackBuffer = uxIdleTaskStack;
	*pusIdleTaskStackSize = configMINIMAL_STACK_SIZE; /* In words.  NOT in bytes! */
}
/*-----------------------------------------------------------*/

void vApplicationGetTimerTaskMemory( StaticTask_t **ppxTimerTaskTCBBuffer, StackType_t **ppxTimerTaskStackBuffer, uint16_t *pusTimerTaskStackSize )
{
/* The buffers used by the Timer/Daemon task must be static so they are
persistent, and so exist after this function returns. */
static StaticTask_t xTimerTaskTCB;
static StackType_t uxTimerTaskStack[ configTIMER_TASK_STACK_DEPTH ];

	/* configSUPPORT_STATIC_ALLOCATION is set to 1,
	configSUPPORT_DYNAMIC_ALLOCATION is set to 1, and configUSE_TIMERS is set
	to 1, so the application must supply the buffers that will be used to hold
	the Timer task data structure and stack. */
	*ppxTimerTaskTCBBuffer = &xTimerTaskTCB;
	*ppxTimerTaskStackBuffer = uxTimerTaskStack;
	*pusTimerTaskStackSize = configTIMER_TASK_STACK_DEPTH; /* In words.  NOT in bytes! */
}

