/*
	FreeRTOS V5.4.2 - Copyright (C) 2009 Real Time Engineers Ltd.

	This file is part of the FreeRTOS distribution.

	FreeRTOS is free software; you can redistribute it and/or modify it	under 
	the terms of the GNU General Public License (version 2) as published by the 
	Free Software Foundation and modified by the FreeRTOS exception.
	**NOTE** The exception to the GPL is included to allow you to distribute a
	combined work that includes FreeRTOS without being obliged to provide the 
	source code for proprietary components outside of the FreeRTOS kernel.  
	Alternative commercial license and support terms are also available upon 
	request.  See the licensing section of http://www.FreeRTOS.org for full 
	license details.

	FreeRTOS is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
	more details.

	You should have received a copy of the GNU General Public License along
	with FreeRTOS; if not, write to the Free Software Foundation, Inc., 59
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.


	***************************************************************************
	*                                                                         *
	* Looking for a quick start?  Then check out the FreeRTOS eBook!          *
	* See http://www.FreeRTOS.org/Documentation for details                   *
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

/*
Changes from V3.0.0
	+ CreationCount sizes changed from unsigned portBASE_TYPE to
	  unsigned portSHORT to minimize the risk of overflowing.
	
	+ Reset of usLastCreationCount added
	
Changes from V3.1.0
	+ Changed the dummy calculation to use variables of type long, rather than
	  float.  This allows the file to be used with ports that do not support
	  floating point.

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
static volatile unsigned portSHORT usCreationCount = 0;

/* Used to store the number of tasks that were originally running so the creator
task can tell if any of the suicidal tasks have failed to die.
*/
static volatile unsigned portBASE_TYPE uxTasksRunningAtStart = 0;

/* Tasks are deleted by the idle task.  Under heavy load the idle task might
not get much processing time, so it would be legitimate for several tasks to
remain undeleted for a short period. */
static const unsigned portBASE_TYPE uxMaxNumberOfExtraTasksRunning = 2;

/* Used to store a handle to the task that should be killed by a suicidal task,
before it kills itself. */
xTaskHandle xCreatedTask;

/*-----------------------------------------------------------*/

void vCreateSuicidalTasks( unsigned portBASE_TYPE uxPriority )
{
unsigned portBASE_TYPE *puxPriority;

	/* Create the Creator tasks - passing in as a parameter the priority at which
	the suicidal tasks should be created. */
	puxPriority = ( unsigned portBASE_TYPE * ) pvPortMalloc( sizeof( unsigned portBASE_TYPE ) );
	*puxPriority = uxPriority;

	xTaskCreate( vCreateTasks, ( signed portCHAR * ) "CREATOR", deathSTACK_SIZE, ( void * ) puxPriority, uxPriority, NULL );

	/* Record the number of tasks that are running now so we know if any of the
	suicidal tasks have failed to be killed. */
	uxTasksRunningAtStart = ( unsigned portBASE_TYPE ) uxTaskGetNumberOfTasks();
	
	/* FreeRTOS.org versions before V3.0 started the idle-task as the very
	first task. The idle task was then already included in uxTasksRunningAtStart.
	From FreeRTOS V3.0 on, the idle task is started when the scheduler is
	started. Therefore the idle task is not yet accounted for. We correct
	this by increasing uxTasksRunningAtStart by 1. */
	uxTasksRunningAtStart++;
}
/*-----------------------------------------------------------*/
					
static portTASK_FUNCTION( vSuicidalTask, pvParameters )
{
volatile portLONG l1, l2;
xTaskHandle xTaskToKill;
const portTickType xDelay = ( portTickType ) 200 / portTICK_RATE_MS;

	if( pvParameters != NULL )
	{
		/* This task is periodically created four times.  Two created tasks are
		passed a handle to the other task so it can kill it before killing itself.
		The other task is passed in null. */
		xTaskToKill = *( xTaskHandle* )pvParameters;
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
			vTaskDelay( ( portTickType ) 0 );

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
const portTickType xDelay = ( portTickType ) 1000 / portTICK_RATE_MS;
unsigned portBASE_TYPE uxPriority;

	uxPriority = *( unsigned portBASE_TYPE * ) pvParameters;
	vPortFree( pvParameters );

	for( ;; )
	{
		/* Just loop round, delaying then creating the four suicidal tasks. */
		vTaskDelay( xDelay );

		xCreatedTask = NULL;

		xTaskCreate( vSuicidalTask, ( signed portCHAR * ) "SUICID1", configMINIMAL_STACK_SIZE, NULL, uxPriority, &xCreatedTask );
		xTaskCreate( vSuicidalTask, ( signed portCHAR * ) "SUICID2", configMINIMAL_STACK_SIZE, &xCreatedTask, uxPriority, NULL );

		++usCreationCount;
	}
}
/*-----------------------------------------------------------*/

/* This is called to check that the creator task is still running and that there
are not any more than four extra tasks. */
portBASE_TYPE xIsCreateTaskStillRunning( void )
{
static unsigned portSHORT usLastCreationCount = 0xfff;
portBASE_TYPE xReturn = pdTRUE;
static unsigned portBASE_TYPE uxTasksRunningNow;

	if( usLastCreationCount == usCreationCount )
	{
		xReturn = pdFALSE;
	}
	else
	{
		usLastCreationCount = usCreationCount;
	}
	
	uxTasksRunningNow = ( unsigned portBASE_TYPE ) uxTaskGetNumberOfTasks();

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


