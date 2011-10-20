/*
    FreeRTOS V7.0.2 - Copyright (C) 2011 Real Time Engineers Ltd.


    ***************************************************************************
     *                                                                       *
     *    FreeRTOS tutorial books are available in pdf and paperback.        *
     *    Complete, revised, and edited pdf reference manuals are also       *
     *    available.                                                         *
     *                                                                       *
     *    Purchasing FreeRTOS documentation will not only help you, by       *
     *    ensuring you get running as quickly as possible and with an        *
     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
     *    the FreeRTOS project to continue with its mission of providing     *
     *    professional grade, cross platform, de facto standard solutions    *
     *    for microcontrollers - completely free of charge!                  *
     *                                                                       *
     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
     *                                                                       *
     *    Thank you for using FreeRTOS, and thank you for your support!      *
     *                                                                       *
    ***************************************************************************


    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    >>>NOTE<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.  FreeRTOS is distributed in the hope that it will be useful, but
    WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public
    License and the FreeRTOS license exception along with FreeRTOS; if not it
    can be viewed here: http://www.freertos.org/a00114.html and also obtained
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!

    http://www.FreeRTOS.org - Documentation, latest information, license and
    contact details.

    http://www.SafeRTOS.com - A version that is certified for use in safety
    critical systems.

    http://www.OpenRTOS.com - Commercial support, development, porting,
    licensing and training services.
*/


/* _RB_ Add description here. */


/* Standard includes. */
#include <stdlib.h>
#include <string.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "croutine.h"

/* Demo application includes. */
#include "partest.h"
#include "flash.h"
#include "integer.h"
#include "PollQ.h"
#include "comtest2.h"
#include "semtest.h"
#include "dynamic.h"
#include "BlockQ.h"
#include "blocktim.h"
#include "countsem.h"
#include "GenQTest.h"
#include "recmutex.h"
#include "serial.h"
/*-----------------------------------------------------------*/

/* Constants for the ComTest tasks. */
#define mainCOM_TEST_BAUD_RATE		( ( unsigned long ) 115200 )
#define mainCOM_TEST_LED			( 5 )

/* Priorities for the demo application tasks. */
#define mainLED_TASK_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainCOM_TEST_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainQUEUE_POLL_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainCHECK_TASK_PRIORITY		( tskIDLE_PRIORITY + 4 )
#define mainSEM_TEST_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY		( tskIDLE_PRIORITY + 2 )

/* The rate at which the on board LED will toggle when there is/is not an
error. */
#define mainNO_ERROR_FLASH_PERIOD	( ( portTickType ) 5000 / portTICK_RATE_MS	)
#define mainERROR_FLASH_PERIOD		( ( portTickType ) 500 / portTICK_RATE_MS  )
#define mainON_BOARD_LED_BIT		( ( unsigned long ) 7 )

/*-----------------------------------------------------------*/

/*
 * Checks that all the demo application tasks are still executing without error
 * - as described at the top of the file.
 */
static long prvCheckOtherTasksAreStillRunning( void );

/*
 * The task that executes at the highest priority and calls
 * prvCheckOtherTasksAreStillRunning().	 See the description at the top
 * of the file.
 */
static void prvCheckTask( void *pvParameters );

/*
 * Configure the processor ready to run this demo.
 */
static void prvSetupHardware( void );

/*
 * Writes to and checks the value of each register that is used in the context
 * of a task.
 */
static void prvRegTask1( void *pvParameters );
static void prvRegTask2( void *pvParameters );

/*
 * Specific check to see if the Register test functions are still operating
 * correctly.
 */
static portBASE_TYPE prvAreRegTestTasksStillRunning( void );

/*-----------------------------------------------------------*/

/* Used by the register test tasks to indicated liveness. */
static unsigned long ulRegisterTest1Count = 0;
static unsigned long ulRegisterTest2Count = 0;

/*-----------------------------------------------------------*/

/*
 * Starts all the tasks, then starts the scheduler.
 */
int main( void )
{
	/* Setup the hardware for use with the TriCore evaluation board. */
	prvSetupHardware();

	/* Start standard demo/test application tasks. */
	vStartIntegerMathTasks( tskIDLE_PRIORITY );
	vStartLEDFlashTasks( mainLED_TASK_PRIORITY );
	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
	vStartDynamicPriorityTasks();
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
	vCreateBlockTimeTasks();
	vStartCountingSemaphoreTasks();
	vStartGenericQueueTasks( tskIDLE_PRIORITY );
	vStartRecursiveMutexTasks();
	vAltStartComTestTasks( mainCOM_TEST_PRIORITY, mainCOM_TEST_BAUD_RATE, mainCOM_TEST_LED );
	/* _RB_ Create the timer test task here too. */

	/* Create the register test tasks, as described at the top of this file. */
	xTaskCreate( prvRegTask1, ( signed char * ) "Reg 1", configMINIMAL_STACK_SIZE, &ulRegisterTest1Count, tskIDLE_PRIORITY, NULL );
	xTaskCreate( prvRegTask2, ( signed char * ) "Reg 2", configMINIMAL_STACK_SIZE, &ulRegisterTest2Count, tskIDLE_PRIORITY, NULL );

	/* Start the check task - which is defined in this file. */
	xTaskCreate( prvCheckTask, ( signed char * ) "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

	/* _RB_ start the death tasks here too. */

	/* Now all the tasks have been started - start the scheduler. */
	vTaskStartScheduler();

	/* If all is well then the following line will never be reached.  If
	execution does reach here, then it is highly probably that the heap size
	is too small for the idle and/or timer tasks to be created within
	vTaskStartScheduler(). */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvCheckTask( void *pvParameters )
{
portTickType xDelayPeriod = mainNO_ERROR_FLASH_PERIOD;
portTickType xLastExecutionTime;

	/* Just to stop compiler warnings. */
	( void ) pvParameters;

	/* Initialise xLastExecutionTime so the first call to vTaskDelayUntil()
	works correctly. */
	xLastExecutionTime = xTaskGetTickCount();

	/* Cycle for ever, delaying then checking all the other tasks are still
	operating without error.  If an error is detected then the delay period
	is decreased from mainNO_ERROR_FLASH_PERIOD to mainERROR_FLASH_PERIOD so
	the on board LED flash rate will increase.  NOTE:  This task could easily
	be replaced by a software timer callback to remove the overhead of having
	an extra task. */

	for( ;; )
	{
		/* Delay until it is time to execute again. */
		vTaskDelayUntil( &xLastExecutionTime, xDelayPeriod );

		/* Check all the standard demo application tasks are executing without
		error.	*/
		if( prvCheckOtherTasksAreStillRunning() != pdPASS )
		{
			/* An error has been detected in one of the tasks - flash the LED
			at a higher frequency to give visible feedback that something has
			gone wrong (it might just be that the loop back connector required
			by the comtest tasks has not been fitted). */
			xDelayPeriod = mainERROR_FLASH_PERIOD;
		}

		/* The toggle rate of the LED depends on how long this task delays for.
		An error reduces the delay period and so increases the toggle rate. */
		vParTestToggleLED( mainON_BOARD_LED_BIT );
	}
}
/*-----------------------------------------------------------*/

static long prvCheckOtherTasksAreStillRunning( void )
{
long lReturn = pdPASS;

	/* Check all the demo tasks (other than the flash tasks) to ensure
	that they are all still running, and that none have detected an error. */

	if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}

	if( xAreComTestTasksStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}

	if( xArePollingQueuesStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}

	if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}

	if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}

	if( xAreBlockingQueuesStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}

	if ( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}

	if ( xAreGenericQueueTasksStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}

	if ( xAreRecursiveMutexTasksStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}

	if( prvAreRegTestTasksStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}

	return lReturn;
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
extern void set_cpu_frequency(void);

	/* Set-up the PLL. */
	set_cpu_frequency();

	/* Initialise LED outputs. */
	vParTestInitialise();
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
	/* vApplicationMallocFailedHook() will only be called if
	configUSE_MALLOC_FAILED_HOOK is set to 1 in FreeRTOSConfig.h.  It is a hook
	function that will get called if a call to pvPortMalloc() fails.
	pvPortMalloc() is called internally by the kernel whenever a task, queue,
	timer or semaphore is created.  It is also called by various parts of the
	demo application.  If heap_1.c or heap_2.c are used, then the size of the
	heap available to pvPortMalloc() is defined by configTOTAL_HEAP_SIZE in
	FreeRTOSConfig.h, and the xPortGetFreeHeapSize() API function can be used
	to query the size of free heap space that remains (although it does not
	provide information on how the remaining heap might be fragmented). */
	_debug();
	taskDISABLE_INTERRUPTS();
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationTickHook( void )
{
	/* vApplicationTickHook() will only be called if configUSE_TICK_HOOK is set
	to 1 in FreeRTOSConfig.h.  It is a hook function that will get called during
	each FreeRTOS tick interrupt.  Note that vApplicationTickHook() is called
	from an interrupt context. */
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
	/* vApplicationIdleHook() will only be called if configUSE_IDLE_HOOK is set
	to 1 in FreeRTOSConfig.h.  It will be called on each iteration of the idle
	task.  It is essential that code added to this hook function never attempts
	to block in any way (for example, call xQueueReceive() with a block time
	specified, or call vTaskDelay()).  If the application makes use of the
	vTaskDelete() API function (as this demo application does) then it is also
	important that vApplicationIdleHook() is permitted to return to its calling
	function, because it is the responsibility of the idle task to clean up
	memory allocated by the kernel to any task that has since been deleted. */
}
/*-----------------------------------------------------------*/

static portBASE_TYPE prvAreRegTestTasksStillRunning( void )
{
static unsigned long ulPreviousRegisterTest1Count = 0;
static unsigned long ulPreviousRegisterTest2Count = 0;
portBASE_TYPE xReturn = pdPASS;

	/* Check to see if the Counts have changed since the last check. */
	if( ulRegisterTest1Count == ulPreviousRegisterTest1Count )
	{
		xReturn = pdFAIL;
	}

	if( ulRegisterTest2Count == ulPreviousRegisterTest2Count )
	{
		xReturn = pdFAIL;
	}

	/* Remember the current count for the next time this function is called. */
	ulPreviousRegisterTest1Count = ulRegisterTest1Count;
	ulPreviousRegisterTest2Count = ulRegisterTest2Count;

	return xReturn;
}
/*-----------------------------------------------------------*/

static void prvRegTask1( void *pvParameters )
{
	/* Make space on the stack for the parameter and a counter. */
	__asm volatile( " sub.a %sp, 4 			\n"
					" st.a [%sp], %a4		\n"
					" mov %d15, 0			\n"
					" st.w [%sp]4, %d15		\n" );

	/* Change all of the Context sensitive registers (except SP and RA). */
	__asm volatile(
			" mov %d0, 0		\n"
			" mov %d1, 1		\n"
			" mov %d2, 2		\n"
			" mov %d3, 3		\n"
			" mov %d4, 4		\n"
			" mov %d5, 5		\n"
			" mov %d6, 6		\n"
			" mov %d7, 7		\n"
			" mov %d8, 8		\n"
			" mov %d9, 9		\n"
			" mov %d10, 10		\n"
			" mov %d11, 11		\n"
			" mov %d12, 12		\n"
			" mov %d13, 13		\n"
			" mov %d14, 14		\n"
			" mov %d15, 15		\n"
			" mov.a %a2, 2		\n"
			" mov.a %a3, 3		\n"
			" mov.a %a4, 4		\n"
			" mov.a %a5, 5		\n"
			" mov.a %a6, 6		\n"
			" mov.a %a7, 7		\n"
			" mov.a %a12, 12	\n"
			" mov.a %a13, 13	\n"
			" mov.a %a14, 14	\n" );

	/* Check the values of the registers. */
	__asm(	" _task1_loop:							\n" \
			" eq %d1, %d0, 0						\n" \
			" jne %d1, 1, _task1_error_loop			\n" \
			" eq %d1, %d1, 1						\n" \
			" jne %d1, 1, _task1_error_loop			\n" \
			" eq %d1, %d2, 2						\n" \
			" jne %d1, 1, _task1_error_loop			\n" \
			" eq %d1, %d3, 3						\n" \
			" jne %d1, 1, _task1_error_loop			\n" \
			" eq %d1, %d4, 4						\n" \
			" jne %d1, 1, _task1_error_loop			\n" \
			" eq %d1, %d5, 5						\n" \
			" jne %d1, 1, _task1_error_loop			\n" \
			" eq %d1, %d6, 6						\n" \
			" jne %d1, 1, _task1_error_loop			\n" \
			" eq %d1, %d7, 7						\n" \
			" jne %d1, 1, _task1_error_loop			\n" \
			" eq %d1, %d8, 8						\n" \
			" jne %d1, 1, _task1_error_loop			\n" \
			" eq %d1, %d9, 9						\n" \
			" jne %d1, 1, _task1_error_loop			\n" \
			" eq %d1, %d10, 10						\n" \
			" jne %d1, 1, _task1_error_loop			\n" \
			" eq %d1, %d11, 11						\n" \
			" jne %d1, 1, _task1_error_loop			\n" \
			" eq %d1, %d12, 12						\n" \
			" jne %d1, 1, _task1_error_loop			\n" \
			" eq %d1, %d13, 13						\n" \
			" jne %d1, 1, _task1_error_loop			\n" \
			" eq %d1, %d14, 14						\n" \
			" jne %d1, 1, _task1_error_loop			\n" \
			" eq %d1, %d15, 15						\n" \
			" jne %d1, 1, _task1_error_loop			\n" \
			" mov.a %a15, 2							\n" \
			" jne.a %a15, %a2, _task1_error_loop	\n" \
			" mov.a %a15, 3							\n" \
			" jne.a %a15, %a3, _task1_error_loop	\n" \
			" mov.a %a15, 4							\n" \
			" jne.a %a15, %a4, _task1_error_loop	\n" \
			" mov.a %a15, 5							\n" \
			" jne.a %a15, %a5, _task1_error_loop	\n" \
			" mov.a %a15, 6							\n" \
			" jne.a %a15, %a6, _task1_error_loop	\n" \
			" mov.a %a15, 7							\n" \
			" jne.a %a15, %a7, _task1_error_loop	\n" \
			" mov.a %a15, 12						\n" \
			" jne.a %a15, %a12, _task1_error_loop	\n" \
			" mov.a %a15, 13						\n" \
			" jne.a %a15, %a13, _task1_error_loop	\n" \
			" mov.a %a15, 14						\n" \
			" jne.a %a15, %a14, _task1_error_loop	\n" \
			" j _task1_skip_error_loop				\n"	\
			"_task1_error_loop:						\n"	/* Hitting this error loop will stop the counter incrementing, allowing the check task to recognise an error. */ \
			"	debug								\n"	\
			" j _task1_error_loop					\n"	\
			"_task1_skip_error_loop:				\n" );

	/* Load the parameter address from the stack and modify the value. */
	__asm volatile(									\
			" ld.w %d1, [%sp]4						\n"	\
			" add %d1, %d15, 1						\n"	\
			" st.w [%sp]4, %d1						\n"	\
			" ld.a %a15, [%sp]						\n"	\
			" st.w [%a15], %d1						\n"	\
			" j _task1_loop							\n" );

	/* The parameter is used but in the assembly. */
	(void)pvParameters;
}
/*-----------------------------------------------------------*/

static void prvRegTask2( void *pvParameters )
{
	/* Make space on the stack for the parameter and a counter. */
	__asm volatile( " sub.a %sp, 4 		\n" \
					" st.a [%sp], %a4	\n" \
					" mov %d15, 0		\n" \
					" st.w [%sp]4, %d15	\n" );

	/* Change all of the Context sensitive registers (except SP and RA). */
	__asm volatile(	" mov %d0, 7		\n" \
					" mov %d1, 1		\n" \
					" mov %d2, 5		\n" \
					" mov %d3, 4		\n" \
					" mov %d4, 3		\n" \
					" mov %d5, 2		\n" \
					" mov %d6, 1		\n" \
					" mov %d7, 0		\n" \
					" mov %d8, 15		\n" \
					" mov %d9, 14		\n" \
					" mov %d10, 13		\n" \
					" mov %d11, 12		\n" \
					" mov %d12, 11		\n" \
					" mov %d13, 10		\n" \
					" mov %d14, 9		\n" \
					" mov %d15, 8		\n" \
					" mov.a %a2, 14		\n" \
					" mov.a %a3, 13		\n" \
					" mov.a %a4, 12		\n" \
					" mov.a %a5, 7		\n" \
					" mov.a %a6, 6		\n" \
					" mov.a %a7, 5		\n" \
					" mov.a %a12, 4		\n" \
					" mov.a %a13, 3		\n" \
					" mov.a %a14, 2		\n" );
	/* Yield to force a context switch. */
	taskYIELD();

	/* Check the values of the registers. */
	__asm volatile(	" _task2_loop:							\n" \
					" eq %d1, %d0, 7						\n" \
					" jne %d1, 1, _task2_error_loop			\n" \
					" eq %d1, %d1, 1						\n" \
					" jne %d1, 1, _task2_error_loop			\n" \
					" eq %d1, %d2, 5						\n" \
					" jne %d1, 1, _task2_error_loop			\n" \
					" eq %d1, %d3, 4						\n" \
					" jne %d1, 1, _task2_error_loop			\n" \
					" eq %d1, %d4, 3						\n" \
					" jne %d1, 1, _task2_error_loop			\n" \
					" eq %d1, %d5, 2						\n" \
					" jne %d1, 1, _task2_error_loop			\n" \
					" eq %d1, %d6, 1						\n" \
					" jne %d1, 1, _task2_error_loop			\n" \
					" eq %d1, %d7, 0						\n" \
					" jne %d1, 1, _task2_error_loop			\n" \
					" eq %d1, %d8, 15						\n" \
					" jne %d1, 1, _task2_error_loop			\n" \
					" eq %d1, %d9, 14						\n" \
					" jne %d1, 1, _task2_error_loop			\n" \
					" eq %d1, %d10, 13						\n" \
					" jne %d1, 1, _task2_error_loop			\n" \
					" eq %d1, %d11, 12						\n" \
					" jne %d1, 1, _task2_error_loop			\n" \
					" eq %d1, %d12, 11						\n" \
					" jne %d1, 1, _task2_error_loop			\n" \
					" eq %d1, %d13, 10						\n" \
					" jne %d1, 1, _task2_error_loop			\n" \
					" eq %d1, %d14, 9						\n" \
					" jne %d1, 1, _task2_error_loop			\n" \
					" eq %d1, %d15, 8						\n" \
					" jne %d1, 1, _task2_error_loop			\n" \
					" mov.a %a15, 14						\n" \
					" jne.a %a15, %a2, _task2_error_loop	\n" \
					" mov.a %a15, 13						\n" \
					" jne.a %a15, %a3, _task2_error_loop	\n" \
					" mov.a %a15, 12						\n" \
					" jne.a %a15, %a4, _task2_error_loop	\n" \
					" mov.a %a15, 7							\n" \
					" jne.a %a15, %a5, _task2_error_loop	\n" \
					" mov.a %a15, 6							\n" \
					" jne.a %a15, %a6, _task2_error_loop	\n" \
					" mov.a %a15, 5							\n" \
					" jne.a %a15, %a7, _task2_error_loop	\n" \
					" mov.a %a15, 4							\n" \
					" jne.a %a15, %a12, _task2_error_loop 	\n" \
					" mov.a %a15, 3							\n" \
					" jne.a %a15, %a13, _task2_error_loop	\n" \
					" mov.a %a15, 2							\n" \
					" jne.a %a15, %a14, _task2_error_loop	\n" \
					" j _task2_skip_error_loop				\n"	\
					"_task2_error_loop:						\n"	/* Hitting this error loop will stop the counter incrementing, allowing the check task to recognise an error. */ \
					" j _task2_error_loop					\n"	\
					"_task2_skip_error_loop:				\n"	);

	/* Load the parameter address from the stack and modify the value. */
	__asm volatile(	" ld.w %d1, [%sp]4						\n"	\
					" add %d1, %d1, 1						\n"	\
					" st.w [%sp]4, %d1						\n"	\
					" ld.a %a15, [%sp]						\n"	\
					" st.w [%a15], %d1						\n"	\
					" j _task2_loop                			\n"  );

	/* The parameter is used but in the assembly. */
	(void)pvParameters;
}
/*-----------------------------------------------------------*/

