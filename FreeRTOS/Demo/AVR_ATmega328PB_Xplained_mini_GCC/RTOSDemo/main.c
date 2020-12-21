/*
 * FreeRTOS V202012.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

#include <atmel_start.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"

/* Tests. */
#include "regtest.h"
#include "integer.h"
#include "PollQ.h"
#include "partest.h"

/* Priority definitions for most of the tasks in the demo application. */
#define mainCHECK_TASK_PRIORITY			( tskIDLE_PRIORITY + 3 )
#define mainQUEUE_POLL_PRIORITY			( tskIDLE_PRIORITY + 2 )
#define mainLED_BLINK_PRIORITY			( tskIDLE_PRIORITY + 2 )

/* The period between executions of the check task. */
#define mainCHECK_PERIOD				( ( TickType_t ) 1000  )

/* The period to toggle LED. */
#define mainBLINK_LED_OK_HALF_PERIOD	( ( TickType_t ) 100 )

/* The task function for the "Check" task. */
static void vErrorChecks( void *pvParameters );

/* The task function for blinking LED at a certain frequency. */
static void vBlinkOnboardUserLED( void *pvParameters );

int main(void)
{
	/* Initializes MCU, drivers and middleware.
	This is generated from Atmel START project. */
	atmel_start_init();

	/* Standard register test. */
	vStartRegTestTasks();

	/* Optionally enable below tests. This port only has 2KB RAM. */
	vStartIntegerMathTasks( tskIDLE_PRIORITY );
	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
	xTaskCreate( vBlinkOnboardUserLED, "LED", 50, NULL, mainCHECK_TASK_PRIORITY, NULL );

	/* Create the tasks defined within this file. */
	xTaskCreate( vErrorChecks, "Check", configMINIMAL_STACK_SIZE, NULL, mainLED_BLINK_PRIORITY, NULL );

	/* In this port, to use preemptive scheduler define configUSE_PREEMPTION
	as 1 in portmacro.h.  To use the cooperative scheduler define
	configUSE_PREEMPTION as 0. */
	vTaskStartScheduler();
}

/*-----------------------------------------------------------*/
static void vErrorChecks( void *pvParameters )
{
static UBaseType_t uxErrorHasOccurred = 0;
BaseType_t xFirstTimeCheck = pdTRUE;

	/* The parameters are not used. */
	( void ) pvParameters;

	/* Cycle for ever, delaying then checking all the other tasks are still
	operating without error. */
	for( ;; )
	{
		if( xAreRegTestTasksStillRunning() != pdTRUE )
		{
			uxErrorHasOccurred |= 0x01U ;
		}
		if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
		{
			uxErrorHasOccurred |= ( 0x01U << 1);
		}
		if( xArePollingQueuesStillRunning() != pdTRUE )
		{
			uxErrorHasOccurred |= ( 0x01U << 2);
		}

		/* When check task runs before any other tasks, all above checks shall fail.
		To avoid false alarm, clear errors upon first entry. */
		if ( xFirstTimeCheck == pdTRUE )
		{
			uxErrorHasOccurred = 0;
			xFirstTimeCheck = pdFALSE;
		}

		/* Could set break point at below line to verify uxErrorHasOccurred. */
		vTaskDelay( mainCHECK_PERIOD );
	}
}

/*-----------------------------------------------------------*/
static void vBlinkOnboardUserLED( void *pvParameters )
{
	/* The parameters are not used. */
	( void ) pvParameters;

	/* Cycle forever, blink onboard user LED at a certain frequency. */
	for( ;; )
	{
		vParTestToggleLED( 0 );

		vTaskDelay( mainBLINK_LED_OK_HALF_PERIOD );
	}

}

/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
	/* Doesn't do anything yet. */
}

/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( TaskHandle_t xTask, char *pcTaskName )
{
	/* When stack overflow happens, trap instead of attempting to recover.
	Read input arguments to learn about the offending task. */
	for( ;; )
	{
		/* Doesn't do anything yet. */
	}
}

/*-----------------------------------------------------------*/

/* configSUPPORT_STATIC_ALLOCATION is set to 1, so the application must provide an
implementation of vApplicationGetIdleTaskMemory() to provide the memory that is
used by the Idle task. */
void vApplicationGetIdleTaskMemory( StaticTask_t **ppxIdleTaskTCBBuffer,
                                    StackType_t **ppxIdleTaskStackBuffer,
                                    uint32_t *pulIdleTaskStackSize )
{
/* If the buffers to be provided to the Idle task are declared inside this
function then they must be declared static -- otherwise they will be allocated on
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

/* configSUPPORT_STATIC_ALLOCATION and configUSE_TIMERS are both set to 1, so the
application must provide an implementation of vApplicationGetTimerTaskMemory()
to provide the memory that is used by the Timer service task. */
void vApplicationGetTimerTaskMemory( StaticTask_t **ppxTimerTaskTCBBuffer,
                                     StackType_t **ppxTimerTaskStackBuffer,
                                     uint32_t *pulTimerTaskStackSize )
{
/* If the buffers to be provided to the Timer task are declared inside this
function then they must be declared static -- otherwise they will be allocated on
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
    configTIMER_TASK_STACK_DEPTH is specified in words, not bytes. */
    *pulTimerTaskStackSize = configTIMER_TASK_STACK_DEPTH;
}
/*-----------------------------------------------------------*/
