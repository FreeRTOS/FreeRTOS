/*
 * FreeRTOS Kernel V10.2.1
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

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* IoT SDK includes. */
#include "iot_taskpool.h"

/*
 * Prototypes for the functions that demonstrate the task pool API.
 */
static void prvExample_BasicSingleJob( void );
static void prvExample_BasicRecyclableJob( void );

/* Prototypes of the callback functions used in the examples. */
static void prvSimpleTaskNotifyCallback( IotTaskPool_t pTaskPool, IotTaskPoolJob_t pJob, void *pUserContext );

/*
 * Prototypes for the standard FreeRTOS application hook (callback) functions
 * implemented within this file.  See http://www.freertos.org/a00016.html .
 */
void vApplicationMallocFailedHook( void );
void vApplicationIdleHook( void );
void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName );
void vApplicationTickHook( void );
void vApplicationGetIdleTaskMemory( StaticTask_t **ppxIdleTaskTCBBuffer, StackType_t **ppxIdleTaskStackBuffer, uint32_t *pulIdleTaskStackSize );
void vApplicationGetTimerTaskMemory( StaticTask_t **ppxTimerTaskTCBBuffer, StackType_t **ppxTimerTaskStackBuffer, uint32_t *pulTimerTaskStackSize );

/*
 * The task used to demonstrate the task pool API.
 */
static void prvTaskPoolDemoTask( void *pvParameters );

static const IotTaskPoolInfo_t xTaskPoolParameters = {
														/* Minimum number of threads in a task pool. */
														2,
														/* Maximum number of threads in a task pool. */
														2,
														/* Stack size for every task pool thread - in words, not bytes. */
														configMINIMAL_STACK_SIZE,
														/* Priority for every task pool thread. */
														tskIDLE_PRIORITY,
													 };

/*-----------------------------------------------------------*/

int main( void )
{
	/* This example uses a single application task, which in turn is used to
	create and send jobs to task pool tasks. */
	xTaskCreate( prvTaskPoolDemoTask,
				 "PoolDemo",
				 configMINIMAL_STACK_SIZE,
				 NULL,
				 tskIDLE_PRIORITY,
				 NULL );

	vTaskStartScheduler();

	/* Should not reach here as vTaskStartScheduler() will only return if there
	was insufficient FreeRTOS heap memory to create the Idle or Timer
	Daemon task. */
	return 0;
}
/*-----------------------------------------------------------*/

static void prvTaskPoolDemoTask( void *pvParameters )
{
IotTaskPoolError_t xResult;

	/* Remove compiler warnings about unused parameters. */
	( void ) pvParameters;

	/* The task pool must be created before it can be used. */
//	xResult = IotTaskPool_CreateSystemTaskPool( &xTaskPoolParameters );
//	configASSERT( xResult == IOT_TASKPOOL_SUCCESS );

	/* Attempting to create the task pool again should then appear to succeed
	(in case it is initialised by more than one library), but have no effect. */
//	xResult = IotTaskPool_CreateSystemTaskPool( &xTaskPoolParameters );
//	configASSERT( xResult == IOT_TASKPOOL_SUCCESS );

	for( ;; )
	{
		/* Run through each task pool example in turn.  See the comments in the
		below functions for details of their behaviour. */
		prvExample_BasicSingleJob();
		prvExample_BasicRecyclableJob();

		vTaskDelete( NULL );
	}
}
/*-----------------------------------------------------------*/

static void prvSimpleTaskNotifyCallback( IotTaskPool_t pTaskPool, IotTaskPoolJob_t pJob, void *pUserContext )
{
TaskHandle_t xTaskToNotify = ( TaskHandle_t ) pUserContext;

	/* Remove warnings about unused parameters. */
	( void ) pTaskPool;
	( void ) pJob;

	/* Notify the task that created this job. */
	xTaskNotifyGive( xTaskToNotify );
}
/*-----------------------------------------------------------*/

static void prvExample_BasicSingleJob( void )
{
IotTaskPoolJobStorage_t xJobStorage;
IotTaskPoolJob_t xJob;
IotTaskPoolError_t xResult;
uint32_t ulReturn;
const TickType_t xShortDelay = pdMS_TO_TICKS( 200 );

	/* Ensure the notification count is 0 before scheduling the job. */
	while( ulTaskNotifyTake( pdTRUE, 0 ) != 0 );

	/* Create and schedule a job using the handle of this task as the job's
	context and the function that sends a notification to the task handle as
	the jobs callback function.  The job is created using storage allocated on
	the stack of this function - so no memory is allocated. */
	xResult = IotTaskPool_CreateJob(  prvSimpleTaskNotifyCallback, /* Callback function. */
									  ( void * ) xTaskGetCurrentTaskHandle(), /* Job context. */
									  &xJobStorage,
									  &xJob );
	configASSERT( xResult == IOT_TASKPOOL_SUCCESS );

	xResult = IotTaskPool_ScheduleSystemJob( xJob, 0 );
	configASSERT( xResult == IOT_TASKPOOL_SUCCESS );

	/* Wait for the notification coming from the job's callback function. */
	ulReturn = ulTaskNotifyTake( pdTRUE, xShortDelay );
	configASSERT( ulReturn );
}
/*-----------------------------------------------------------*/

static void prvExample_BasicRecyclableJob( void )
{
IotTaskPoolJob_t xJob;
IotTaskPoolError_t xResult;
uint32_t ulReturn;
const TickType_t xShortDelay = pdMS_TO_TICKS( 200 );

	/* Ensure the notification count is 0 before scheduling the job. */
	while( ulTaskNotifyTake( pdTRUE, 0 ) != 0 );

	/* Create and schedule a job using the handle of this task as the job's
	context and the function that sends a notification to the task handle as
	the jobs callback function.  The job is created as a recyclable job - so it
	is allocated inside the create function, but can then be used again and
	again. */
	xResult = IotTaskPool_CreateRecyclableSystemJob(  prvSimpleTaskNotifyCallback,
											 	 	 ( void * ) xTaskGetCurrentTaskHandle(),
													 &xJob );
	configASSERT( xResult == IOT_TASKPOOL_SUCCESS );

	xResult = IotTaskPool_ScheduleSystemJob( xJob, 0 );
	configASSERT( xResult == IOT_TASKPOOL_SUCCESS );

	/* Wait for the notification coming from the job's callback function. */
	ulReturn = ulTaskNotifyTake( pdTRUE, xShortDelay );
	configASSERT( ulReturn );
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
	/* vApplicationMallocFailedHook() will only be called if
	configUSE_MALLOC_FAILED_HOOK is set to 1 in FreeRTOSConfig.h.  It is a hook
	function that will get called if a call to pvPortMalloc() fails.
	pvPortMalloc() is called internally by the kernel whenever a task, queue,
	timer or semaphore is created.  It is also called by various parts of the
	demo application.  If heap_1.c, heap_2.c or heap_4.c is being used, then the
	size of the	heap available to pvPortMalloc() is defined by
	configTOTAL_HEAP_SIZE in FreeRTOSConfig.h, and the xPortGetFreeHeapSize()
	API function can be used to query the size of free heap space that remains
	(although it does not provide information on how the remaining heap might be
	fragmented).  See http://www.freertos.org/a00111.html for more
	information. */
	vAssertCalled( __LINE__, __FILE__ );
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
	/* vApplicationIdleHook() will only be called if configUSE_IDLE_HOOK is set
	to 1 in FreeRTOSConfig.h.  It will be called on each iteration of the idle
	task.  It is essential that code added to this hook function never attempts
	to block in any way (for example, call xQueueReceive() with a block time
	specified, or call vTaskDelay()).  If application tasks make use of the
	vTaskDelete() API function to delete themselves then it is also important
	that vApplicationIdleHook() is permitted to return to its calling function,
	because it is the responsibility of the idle task to clean up memory
	allocated by the kernel to any task that has since deleted itself. */
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

void vApplicationTickHook( void )
{
	/* This function will be called by each tick interrupt if
	configUSE_TICK_HOOK is set to 1 in FreeRTOSConfig.h.  User code can be
	added here, but the tick hook is called from an interrupt context, so
	code must not attempt to block, and only the interrupt safe FreeRTOS API
	functions can be used (those that end in FromISR()). */
}
/*-----------------------------------------------------------*/

void vApplicationDaemonTaskStartupHook( void )
{
	/* This function will be called once only, when the daemon task starts to
	execute	(sometimes called the timer task).  This is useful if the
	application includes initialisation code that would benefit from executing
	after the scheduler has been started. */
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


 	taskENTER_CRITICAL();
	{
		/* You can step out of this function to debug the assertion by using
		the debugger to set ulSetToNonZeroInDebuggerToContinue to a non-zero
		value. */
		while( ulSetToNonZeroInDebuggerToContinue == 0 )
		{
			__asm volatile( "NOP" );
			__asm volatile( "NOP" );
		}
	}
	taskEXIT_CRITICAL();
}
/*-----------------------------------------------------------*/

/* configUSE_STATIC_ALLOCATION is set to 1, so the application must provide an
implementation of vApplicationGetIdleTaskMemory() to provide the memory that is
used by the Idle task. */
void vApplicationGetIdleTaskMemory( StaticTask_t **ppxIdleTaskTCBBuffer, StackType_t **ppxIdleTaskStackBuffer, uint32_t *pulIdleTaskStackSize )
{
/* If the buffers to be provided to the Idle task are declared inside this
function then they must be declared static - otherwise they will be allocated on
the stack and so not exists after this function exits. */
static StaticTask_t xIdleTaskTCB;
static StackType_t uxIdleTaskStack[ configMINIMAL_STACK_SIZE ];

	/* Pass out a pointer to the StaticTask_t structure in which the Idle task's
	state will be stored. */
	*ppxIdleTaskTCBBuffer = &xIdleTaskTCB;

	/* Pass out the array that will be used as the Idle task's stack. */
	*ppxIdleTaskStackBuffer = uxIdleTaskStack;

	/* Pass out the size of the array pointed to by *ppxIdleTaskStackBuffer.
	Note that, as the array is necessarily of type StackType_t,
	configMINIMAL_STACK_SIZE is specified in words, not bytes. */
	*pulIdleTaskStackSize = configMINIMAL_STACK_SIZE;
}
/*-----------------------------------------------------------*/

/* configUSE_STATIC_ALLOCATION and configUSE_TIMERS are both set to 1, so the
application must provide an implementation of vApplicationGetTimerTaskMemory()
to provide the memory that is used by the Timer service task. */
void vApplicationGetTimerTaskMemory( StaticTask_t **ppxTimerTaskTCBBuffer, StackType_t **ppxTimerTaskStackBuffer, uint32_t *pulTimerTaskStackSize )
{
/* If the buffers to be provided to the Timer task are declared inside this
function then they must be declared static - otherwise they will be allocated on
the stack and so not exists after this function exits. */
static StaticTask_t xTimerTaskTCB;
static StackType_t uxTimerTaskStack[ configTIMER_TASK_STACK_DEPTH ];

	/* Pass out a pointer to the StaticTask_t structure in which the Timer
	task's state will be stored. */
	*ppxTimerTaskTCBBuffer = &xTimerTaskTCB;

	/* Pass out the array that will be used as the Timer task's stack. */
	*ppxTimerTaskStackBuffer = uxTimerTaskStack;

	/* Pass out the size of the array pointed to by *ppxTimerTaskStackBuffer.
	Note that, as the array is necessarily of type StackType_t,
	configMINIMAL_STACK_SIZE is specified in words, not bytes. */
	*pulTimerTaskStackSize = configTIMER_TASK_STACK_DEPTH;
}

