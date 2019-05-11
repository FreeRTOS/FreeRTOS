/*
 * FreeRTOS Kernel V10.2.1
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/**
 * Create a single persistent task which periodically dynamically creates another
 * two tasks.  The original task is called the creator task, the two tasks it
 * creates are called suicidal tasks.
 *
 * One of the created suicidal tasks kill one other suicidal task before killing
 * itself - leaving just the original task remaining.
 *
 * The creator task must be spawned after all of the other demo application tasks
 * as it keeps a check on the number of tasks under the scheduler control.  The
 * number of tasks it expects to see running should never be greater than the
 * number of tasks that were in existence when the creator task was spawned, plus
 * one set of four suicidal tasks.  If this number is exceeded an error is flagged.
 *
 * \page DeathC death.c
 * \ingroup DemoFiles
 * <HR>
 */


#include <stdlib.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo program include files. */
#include "death.h"

#define deathSTACK_SIZE		( configMINIMAL_STACK_SIZE + 60 )

/* The task originally created which is responsible for periodically dynamically
creating another four tasks. */
static portTASK_FUNCTION_PROTO( vCreateTasks, pvParameters );

/* The task function of the dynamically created tasks. */
static portTASK_FUNCTION_PROTO( vSuicidalTask, pvParameters );

/* A variable which is incremented every time the dynamic tasks are created.  This
is used to check that the task is still running. */
static volatile uint16_t usCreationCount = 0;

/* Used to store the number of tasks that were originally running so the creator
task can tell if any of the suicidal tasks have failed to die.
*/
static volatile UBaseType_t uxTasksRunningAtStart = 0;

/* When a task deletes itself, it stack and TCB are cleaned up by the Idle task.
Under heavy load the idle task might not get much processing time, so it would
be legitimate for several tasks to remain undeleted for a short period.  There
may also be a few other unexpected tasks if, for example, the tasks that test
static allocation are also being used. */
static const UBaseType_t uxMaxNumberOfExtraTasksRunning = 3;

/* Used to store a handle to the task that should be killed by a suicidal task,
before it kills itself. */
TaskHandle_t xCreatedTask;

/*-----------------------------------------------------------*/

void vCreateSuicidalTasks( UBaseType_t uxPriority )
{
	xTaskCreate( vCreateTasks, "CREATOR", deathSTACK_SIZE, ( void * ) NULL, uxPriority, NULL );
}
/*-----------------------------------------------------------*/

static portTASK_FUNCTION( vSuicidalTask, pvParameters )
{
volatile long l1, l2;
TaskHandle_t xTaskToKill;
const TickType_t xDelay = pdMS_TO_TICKS( ( TickType_t ) 200 );

	/* Test deletion of a task's secure context, if any. */
	portALLOCATE_SECURE_CONTEXT( configMINIMAL_SECURE_STACK_SIZE );

	if( pvParameters != NULL )
	{
		/* This task is periodically created four times.  Two created tasks are
		passed a handle to the other task so it can kill it before killing itself.
		The other task is passed in null. */
		xTaskToKill = *( TaskHandle_t* )pvParameters;
	}
	else
	{
		xTaskToKill = NULL;
	}

	for( ;; )
	{
		/* Do something random just to use some stack and registers. */
		l1 = 2;
		l2 = 89;
		l2 *= l1;
		vTaskDelay( xDelay );

		if( xTaskToKill != NULL )
		{
			/* Make sure the other task has a go before we delete it. */
			vTaskDelay( ( TickType_t ) 0 );

			/* Kill the other task that was created by vCreateTasks(). */
			vTaskDelete( xTaskToKill );

			/* Kill ourselves. */
			vTaskDelete( NULL );
		}
	}
}/*lint !e818 !e550 Function prototype must be as per standard for task functions. */
/*-----------------------------------------------------------*/

static portTASK_FUNCTION( vCreateTasks, pvParameters )
{
const TickType_t xDelay = pdMS_TO_TICKS( ( TickType_t ) 1000 );
UBaseType_t uxPriority;

	/* Remove compiler warning about unused parameter. */
	( void ) pvParameters;

	/* Delay at the start to ensure tasks created by other demos have been
	created before storing the current number of tasks. */
	vTaskDelay( xDelay );
	uxTasksRunningAtStart = ( UBaseType_t ) uxTaskGetNumberOfTasks();

	uxPriority = uxTaskPriorityGet( NULL );

	for( ;; )
	{
		/* Just loop round, delaying then creating the four suicidal tasks. */
		vTaskDelay( xDelay );

		xCreatedTask = NULL;

		xTaskCreate( vSuicidalTask, "SUICID1", configMINIMAL_STACK_SIZE, NULL, uxPriority, &xCreatedTask );
		xTaskCreate( vSuicidalTask, "SUICID2", configMINIMAL_STACK_SIZE, &xCreatedTask, uxPriority, NULL );

		++usCreationCount;
	}
}
/*-----------------------------------------------------------*/

/* This is called to check that the creator task is still running and that there
are not any more than four extra tasks. */
BaseType_t xIsCreateTaskStillRunning( void )
{
static uint16_t usLastCreationCount = 0xfff;
BaseType_t xReturn = pdTRUE;
static UBaseType_t uxTasksRunningNow;

	if( usLastCreationCount == usCreationCount )
	{
		xReturn = pdFALSE;
	}
	else
	{
		usLastCreationCount = usCreationCount;
	}

	uxTasksRunningNow = ( UBaseType_t ) uxTaskGetNumberOfTasks();

	if( uxTasksRunningNow < uxTasksRunningAtStart )
	{
		xReturn = pdFALSE;
	}
	else if( ( uxTasksRunningNow - uxTasksRunningAtStart ) > uxMaxNumberOfExtraTasksRunning )
	{
		xReturn = pdFALSE;
	}
	else
	{
		/* Everything is okay. */
	}

	return xReturn;
}


