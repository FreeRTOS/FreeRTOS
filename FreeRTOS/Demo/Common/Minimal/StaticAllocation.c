/*
    FreeRTOS V8.2.3 - Copyright (C) 2015 Real Time Engineers Ltd.
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
 * Demonstrates how to create FreeRTOS objects using pre-allocated memory,
 * rather than the normal dynamically allocated memory.  Currently only tasks
 * are being allocated statically.
 *
 * Two buffers are required by a task - one that is used by the task as its
 * stack, and one that holds the task's control block (TCB).
 * prvStaticallyAllocatedTaskCreator() creates and deletes tasks with all
 * possible combinations of statically allocated and dynamically allocated
 * stacks and TCBs.
 */

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo program include files. */
#include "StaticAllocation.h"

#define staticTASK_PRIORITY		( tskIDLE_PRIORITY + 2 )

/*
 * A task that is created multiple times, using both statically and dynamically
 * allocated stack and TCB.
 */
static void prvStaticallyAllocatedTask( void *pvParameters );

/*
 * The task that creates and deletes the prvStaticallyAllocatedTask() task,
 * using various priorities, and sometimes with statically and sometimes
 * dynamically allocated stack and TCB.
 */
static void prvStaticallyAllocatedTaskCreator( void *pvParameters );

/*
 * Utility function to create pseudo random numbers.
 */
static UBaseType_t prvRand( void );

/*
 * The task that creates and deletes other tasks has to delay occasionally to
 * ensure lower priority tasks are not starved of processing time.  A pseudo
 * random delay time is used just to add a little bit of randomisation into the
 * execution pattern.  prvGetNextDelayTime() generates the pseudo random delay.
 */
static TickType_t prvGetNextDelayTime( void );

/*-----------------------------------------------------------*/

/* DummyTCB_t is a publicly accessible structure that has the same size and
alignment requirements as the real TCB structure.  It is provided as a mechanism
for applications to know the size of the TCB (which is dependent on the
architecture and configuration file settings) without breaking the strict data
hiding policy by exposing the real TCB.  This DummyTCB_t variable is passed into
the xTaskCreateStatic() function, and will hold the task's TCB. */
static DummyTCB_t xTCBBuffer;

/* This is the stack that will be used by the task.  The alignment requirements
for the stack depend on the architecture, and the method of forcing an alignment
is dependent on the compiler, but any bad alignment is corrected inside the
FreeRTOS code. */
static StackType_t uxStackBuffer[ configMINIMAL_STACK_SIZE ];

/* Used by the pseudo random number generating function. */
static uint32_t ulNextRand = 0;

/* Used so a check task can ensure this test is still executing, and not
stalled. */
static volatile UBaseType_t uxCycleCounter = 0;

/*-----------------------------------------------------------*/

void vStartStaticallyAllocatedTasks( void  )
{
	/* Create a single task, which then repeatedly creates and deletes the
	task implemented by prvStaticallyAllocatedTask() at various different
	priorities, and both with and without statically allocated TCB and stack. */
	xTaskCreate( prvStaticallyAllocatedTaskCreator, "StatCreate", configMINIMAL_STACK_SIZE, NULL, staticTASK_PRIORITY, NULL );

	/* Pseudo seed the random number generator. */
	ulNextRand = ( uint32_t ) prvRand;
}
/*-----------------------------------------------------------*/

static void prvStaticallyAllocatedTaskCreator( void *pvParameters )
{
TaskHandle_t xCreatedTask;
BaseType_t xReturned;

	/* Avoid compiler warnings. */
	( void ) pvParameters;

	for( ;; )
	{
		/* Create the task.  xTaskCreateStatic() has two more parameters than
		the usual xTaskCreate() function.  The first new parameter is a pointer to
		the pre-allocated stack.  The second new parameter is a pointer to the
		DummyTCB_t structure that will hold the task's TCB.  If either pointer is
		passed as NULL then the respective object will be allocated dynamically as
		if xTaskCreate() had been called. */
		xReturned = xTaskCreateStatic(
							prvStaticallyAllocatedTask, /* Function that implements the task. */
							"Static",					/* Human readable name for the task. */
							configMINIMAL_STACK_SIZE,	/* Task's stack size, in words (not bytes!). */
							NULL,						/* Parameter to pass into the task. */
							tskIDLE_PRIORITY,			/* The priority of the task. */
							&xCreatedTask,				/* Handle of the task being created. */
							&( uxStackBuffer[ 0 ] ),	/* The buffer to use as the task's stack. */
							&xTCBBuffer );				/* The variable that will hold that task's TCB. */

		/* Check the task was created correctly, then delete the task. */
		configASSERT( xReturned == pdPASS );
		( void ) xReturned; /* In case configASSERT() is not defined. */
		vTaskDelete( xCreatedTask );

		/* Ensure lower priority tasks get CPU time. */
		vTaskDelay( prvGetNextDelayTime() );

		/* Create and delete the task a few times again - testing both static and
		dynamic allocation for the stack and TCB. */
		xReturned = xTaskCreateStatic(
							prvStaticallyAllocatedTask, /* Function that implements the task. */
							"Static",					/* Human readable name for the task. */
							configMINIMAL_STACK_SIZE,	/* Task's stack size, in words (not bytes!). */
							NULL,						/* Parameter to pass into the task. */
							staticTASK_PRIORITY + 1,	/* The priority of the task. */
							&xCreatedTask,				/* Handle of the task being created. */
							NULL,						/* This time, dynamically allocate the stack. */
							&xTCBBuffer );				/* The variable that will hold that task's TCB. */

		configASSERT( xReturned == pdPASS );
		( void ) xReturned; /* In case configASSERT() is not defined. */
		vTaskDelete( xCreatedTask );

		/* Just to show the check task that this task is still executing. */
		uxCycleCounter++;

		/* Ensure lower priority tasks get CPU time. */
		vTaskDelay( prvGetNextDelayTime() );

		xReturned = xTaskCreateStatic(
							prvStaticallyAllocatedTask, /* Function that implements the task. */
							"Static",					/* Human readable name for the task. */
							configMINIMAL_STACK_SIZE,	/* Task's stack size, in words (not bytes!). */
							NULL,						/* Parameter to pass into the task. */
							staticTASK_PRIORITY - 1,	/* The priority of the task. */
							&xCreatedTask,				/* Handle of the task being created. */
							&( uxStackBuffer[ 0 ] ),	/* The buffer to use as the task's stack. */
							NULL );						/* This time dynamically allocate the TCB. */

		configASSERT( xReturned == pdPASS );
		( void ) xReturned; /* In case configASSERT() is not defined. */
		vTaskDelete( xCreatedTask );

		/* Ensure lower priority tasks get CPU time. */
		vTaskDelay( prvGetNextDelayTime() );

		xReturned = xTaskCreateStatic(
							prvStaticallyAllocatedTask, /* Function that implements the task. */
							"Static",					/* Human readable name for the task. */
							configMINIMAL_STACK_SIZE,	/* Task's stack size, in words (not bytes!). */
							NULL,						/* Parameter to pass into the task. */
							staticTASK_PRIORITY,		/* The priority of the task. */
							&xCreatedTask,				/* Handle of the task being created. */
							NULL,						/* This time dynamically allocate the stack and TCB. */
							NULL );						/* This time dynamically allocate the stack and TCB. */

		configASSERT( xReturned == pdPASS );
		( void ) xReturned; /* In case configASSERT() is not defined. */
		vTaskDelete( xCreatedTask );

		/* Ensure lower priority tasks get CPU time. */
		vTaskDelay( prvGetNextDelayTime() );

		/* Just to show the check task that this task is still executing. */
		uxCycleCounter++;
	}
}
/*-----------------------------------------------------------*/

static void prvStaticallyAllocatedTask( void *pvParameters )
{
	( void ) pvParameters;

	/* The created task doesn't do anything - just waits to get deleted. */
	vTaskSuspend( NULL );
}
/*-----------------------------------------------------------*/

static UBaseType_t prvRand( void )
{
const uint32_t ulMultiplier = 0x015a4e35UL, ulIncrement = 1UL;

	/* Utility function to generate a pseudo random number. */
	ulNextRand = ( ulMultiplier * ulNextRand ) + ulIncrement;
	return( ( ulNextRand >> 16UL ) & 0x7fffUL );
}
/*-----------------------------------------------------------*/

static TickType_t prvGetNextDelayTime( void )
{
TickType_t xNextDelay;
const TickType_t xMaxDelay = pdMS_TO_TICKS( ( TickType_t ) 150 );
const TickType_t xMinDelay = pdMS_TO_TICKS( ( TickType_t ) 75 );
const TickType_t xTinyDelay = pdMS_TO_TICKS( ( TickType_t ) 2 );

	/* Generate the next delay time.  This is kept within a narrow band so as
	not to disturb the timing of other tests - but does add in some pseudo
	randomisation into the tests. */
	do
	{
		xNextDelay = prvRand() % xMaxDelay;

		/* Just in case this loop is executed lots of times. */
		vTaskDelay( xTinyDelay );

	} while ( xNextDelay < xMinDelay );

	return xNextDelay;
}
/*-----------------------------------------------------------*/

BaseType_t xAreStaticAllocationTasksStillRunning( void )
{
static UBaseType_t uxLastCycleCounter = 0;
BaseType_t xReturn;

	if( uxCycleCounter == uxLastCycleCounter )
	{
		xReturn = pdFAIL;
	}
	else
	{
		xReturn = pdPASS;
		uxLastCycleCounter = uxCycleCounter;
	}

	return xReturn;
}

