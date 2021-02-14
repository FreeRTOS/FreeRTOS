/*
 * FreeRTOS Kernel V10.4.0
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


/*
 * Creates all the demo application tasks, then starts the scheduler.  The WEB
 * documentation provides more details of the standard demo application tasks.
 *
 * "Check" hook -  This only executes every five seconds from the tick hook.
 * Its main function is to check that all the standard demo tasks are still
 * operational.  Should any unexpected behaviour within a demo task be discovered
 * the tick hook will write an error to the OLED (via the OLED task).  If all the
 * demo tasks are executing with their expected behaviour then the check task
 * writes PASS to the OLED (again via the OLED task), as described above.
 *
 * Use the following command to execute in QEMU from the IAR IDE:
 * qemu-system-arm -machine lm3s6965evb -s -S -kernel [pat_to]\RTOSDemo.out
 * and set IAR connect GDB server to "localhost,1234" in project debug options.
 */

/*************************************************************************
 * Please ensure to read http://www.freertos.org/portlm3sx965.html
 * which provides information on configuring and running this demo for the
 * various Luminary Micro EKs.
 *************************************************************************/

/* Standard includes. */
#include <stdio.h>
#include <string.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* Demo app includes. */
#include "death.h"
#include "blocktim.h"
#include "semtest.h"
#include "PollQ.h"
#include "GenQTest.h"
#include "QPeek.h"
#include "recmutex.h"
#include "IntQueue.h"
#include "QueueSet.h"
#include "EventGroupsDemo.h"
#include "MessageBufferDemo.h"
#include "StreamBufferDemo.h"
#include "AbortDelay.h"
#include "countsem.h"
#include "dynamic.h"
#include "MessageBufferAMP.h"
#include "QueueOverwrite.h"
#include "QueueSetPolling.h"
#include "StaticAllocation.h"
#include "TaskNotify.h"
#include "TaskNotifyArray.h"
#include "TimerDemo.h"
#include "StreamBufferInterrupt.h"
#include "IntSemTest.h"

/*-----------------------------------------------------------*/

/* Task priorities. */
#define mainQUEUE_POLL_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainCHECK_TASK_PRIORITY				( tskIDLE_PRIORITY + 3 )
#define mainSEM_TEST_PRIORITY				( tskIDLE_PRIORITY + 1 )
#define mainCREATOR_TASK_PRIORITY           ( tskIDLE_PRIORITY + 3 )
#define mainGEN_QUEUE_TASK_PRIORITY			( tskIDLE_PRIORITY )

/*-----------------------------------------------------------*/

void uart_init( void );
static void prvCheckTask( void *pvParameters );

/*-----------------------------------------------------------*/

/*************************************************************************
 * Please ensure to read http://www.freertos.org/portlm3sx965.html
 * which provides information on configuring and running this demo for the
 * various Luminary Micro EKs.
 *************************************************************************/
int main( void )
{
	uart_init();

	/* Start the standard demo tasks. */
	vStartGenericQueueTasks( mainGEN_QUEUE_TASK_PRIORITY );
	vStartInterruptQueueTasks();
	vStartRecursiveMutexTasks();
	vCreateBlockTimeTasks();
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
	vStartQueuePeekTasks();
	vStartQueueSetTasks();
	vStartEventGroupTasks();
	vStartMessageBufferTasks( configMINIMAL_STACK_SIZE );
	vStartStreamBufferTasks();
	vCreateAbortDelayTasks();
	vStartCountingSemaphoreTasks();
	vStartDynamicPriorityTasks();
	vStartMessageBufferAMPTasks( configMINIMAL_STACK_SIZE );
	vStartQueueOverwriteTask( tskIDLE_PRIORITY );
	vStartQueueSetPollingTask();
	vStartStaticallyAllocatedTasks();
	vStartTaskNotifyTask();
	vStartTaskNotifyArrayTask();
	vStartTimerDemoTask( 50 );
	vStartStreamBufferInterruptDemo();
	vStartInterruptSemaphoreTasks();

	/* The suicide tasks must be created last as they need to know how many
	tasks were running prior to their creation in order to ascertain whether
	or not the correct/expected number of tasks are running at any given time. */
	vCreateSuicidalTasks( mainCREATOR_TASK_PRIORITY );

	xTaskCreate( prvCheckTask, "Check", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );

	/* Start the scheduler. */
	vTaskStartScheduler();

	/* Will only get here if there was insufficient memory to create the idle
	task. */
	for( ;; );
}
/*-----------------------------------------------------------*/

void vInitialiseTimerForIntQueueTest( void );
static void prvCheckTask( void *pvParameters )
{
static const char * pcMessage = "PASS";
const TickType_t xTaskPeriod = pdMS_TO_TICKS( 5000UL );
TickType_t xPreviousWakeTime;
extern uint32_t ulNestCount;

	xPreviousWakeTime = xTaskGetTickCount();

	for( ;; )
	{
		vTaskDelayUntil( &xPreviousWakeTime, xTaskPeriod );

		/* Has an error been found in any task? */
		if( xAreStreamBufferTasksStillRunning() != pdTRUE )
		{
			pcMessage = "xAreStreamBufferTasksStillRunning() returned false";
		}
		else if( xAreMessageBufferTasksStillRunning() != pdTRUE )
		{
			pcMessage = "xAreMessageBufferTasksStillRunning() returned false";
		}
		if( xAreGenericQueueTasksStillRunning() != pdTRUE )
		{
			pcMessage = "xAreGenericQueueTasksStillRunning() returned false";
		}
	    else if( xIsCreateTaskStillRunning() != pdTRUE )
	    {
	        pcMessage = "xIsCreateTaskStillRunning() returned false";
	    }
		else if( xAreIntQueueTasksStillRunning() != pdTRUE )
		{
			pcMessage = "xAreIntQueueTasksStillRunning() returned false";
		}
		else if( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
		{
			pcMessage = "xAreBlockTimeTestTasksStillRunning() returned false";
		}
		else if( xAreSemaphoreTasksStillRunning() != pdTRUE )
		{
			pcMessage = "xAreSemaphoreTasksStillRunning() returned false";
		}
		else if( xArePollingQueuesStillRunning() != pdTRUE )
		{
			pcMessage = "xArePollingQueuesStillRunning() returned false";
		}
		else if( xAreQueuePeekTasksStillRunning() != pdTRUE )
		{
			pcMessage = "xAreQueuePeekTasksStillRunning() returned false";
		}
		else if( xAreRecursiveMutexTasksStillRunning() != pdTRUE )
		{
			pcMessage = "xAreRecursiveMutexTasksStillRunning() returned false";
		}
		else if( xAreQueueSetTasksStillRunning() != pdPASS )
		{
			pcMessage = "xAreQueueSetTasksStillRunning() returned false";
		}
		else if( xAreEventGroupTasksStillRunning() != pdTRUE )
		{
			pcMessage = "xAreEventGroupTasksStillRunning() returned false";
		}
		else if( xAreAbortDelayTestTasksStillRunning() != pdTRUE )
		{
			pcMessage = "xAreAbortDelayTestTasksStillRunning() returned false";
		}
		else if( xAreCountingSemaphoreTasksStillRunning() != pdTRUE )
		{
			pcMessage = "xAreCountingSemaphoreTasksStillRunning() returned false";
		}
		else if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
		{
			pcMessage = "xAreDynamicPriorityTasksStillRunning() returned false";
		}
		else if( xAreMessageBufferAMPTasksStillRunning() != pdTRUE )
		{
			pcMessage = "xAreMessageBufferAMPTasksStillRunning() returned false";
		}
		else if( xIsQueueOverwriteTaskStillRunning() != pdTRUE )
		{
			pcMessage = "xIsQueueOverwriteTaskStillRunning() returned false";
		}
		else if( xAreQueueSetPollTasksStillRunning() != pdTRUE )
		{
			pcMessage = "xAreQueueSetPollTasksStillRunning() returned false";
		}
		else if( xAreStaticAllocationTasksStillRunning() != pdTRUE )
		{
			pcMessage = "xAreStaticAllocationTasksStillRunning() returned false";
		}
		else if( xAreTaskNotificationTasksStillRunning() != pdTRUE )
		{
			pcMessage = "xAreTaskNotificationTasksStillRunning() returned false";
		}
		else if( xAreTaskNotificationArrayTasksStillRunning() != pdTRUE )
		{
			pcMessage = "xAreTaskNotificationArrayTasksStillRunning() returned false";
		}
		else if( xAreTimerDemoTasksStillRunning( xTaskPeriod ) != pdTRUE )
		{
			pcMessage = "xAreTimerDemoTasksStillRunning() returned false";
		}
		else if( xIsInterruptStreamBufferDemoStillRunning() != pdTRUE )
		{
			pcMessage = "xIsInterruptStreamBufferDemoStillRunning() returned false";
		}
		else if( xAreInterruptSemaphoreTasksStillRunning() != pdTRUE )
		{
			pcMessage = "xAreInterruptSemaphoreTasksStillRunning() returned false";
		}

		printf( "%s : %d (%d) %s", pcMessage, (int) xTaskGetTickCount(), ulNestCount, "\r\n" );
	}
}
/*-----------------------------------------------------------*/

void vApplicationTickHook( void )
{
	/* Write to a queue that is in use as part of the queue set demo to
	demonstrate using queue sets from an ISR. */
	vQueueSetAccessQueueSetFromISR();

	/* Call the event group ISR tests. */
	vPeriodicEventGroupsProcessing();

	/* Exercise stream buffers from interrupts. */
	vPeriodicStreamBufferProcessing();

	/* Exercise using queue overwrites from interrupts. */
	vQueueOverwritePeriodicISRDemo();

	/* Exercise using Queue Sets from interrupts. */
	vQueueSetPollingInterruptAccess();

	/* Exercise using task notifications from interrupts. */
	xNotifyTaskFromISR();
	xNotifyArrayTaskFromISR();

	/* Exercise software timers from interrupts. */
	vTimerPeriodicISRTests();

	/* Exercise stream buffers from interrupts. */
	vBasicStreamBufferSendFromISR();

	/* Exercise sempahores from interrupts. */
	vInterruptSemaphorePeriodicTest();
}
/*-----------------------------------------------------------*/

volatile char *pcOverflowedTask = NULL; /* Prevent task name being optimised away. */
void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName )
{
	( void ) pxTask;
	pcOverflowedTask = pcTaskName;
	vAssertCalled( __FILE__, __LINE__ );
	for( ;; );
}
/*-----------------------------------------------------------*/

void vAssertCalled( const char *pcFile, uint32_t ulLine )
{
volatile uint32_t ulSetTo1InDebuggerToExit = 0;

	taskENTER_CRITICAL();
	{
		printf( "Assert, file = %s, line = %d\r\n", pcFile, ( int ) ulLine );

		while( ulSetTo1InDebuggerToExit == 0 )
		{
			/* Nothing to do here.  Set the loop variable to a non zero value in
			the debugger to step out of this function to the point that caused
			the assertion. */
			( void ) pcFile;
			( void ) ulLine;
		}
	}
	taskEXIT_CRITICAL();
}

void vApplicationMallocFailedHook( void )
{
	configASSERT( 0 );
}

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
/*-----------------------------------------------------------*/

typedef struct UART_t {
    volatile uint32_t DATA;
    volatile uint32_t STATE;
    volatile uint32_t CTRL;
    volatile uint32_t INTSTATUS;
    volatile uint32_t BAUDDIV;
} UART_t;

#define UART0_ADDR ((UART_t *)(0x40004000))
#define UART_DR(baseaddr) (*(unsigned int *)(baseaddr))

#define UART_STATE_TXFULL (1 << 0)
#define UART_CTRL_TX_EN (1 << 0)
#define UART_CTRL_RX_EN (1 << 1)


void uart_init( void )
{
    UART0_ADDR->BAUDDIV = 16;
    UART0_ADDR->CTRL = UART_CTRL_TX_EN;
}

void UART_OUT( const char * buf )
{
	while( *buf != NULL )
	{
        UART_DR(UART0_ADDR) = *buf;
		buf++;
    }

	UART_DR( UART0_ADDR ) = '\r';
	UART_DR( UART0_ADDR ) = '\n';
}

int __write(int file, char *buf, int len)
{
    int todo;

    for (todo = 0; todo < len; todo++){
        UART_DR(UART0_ADDR) = *buf++;
    }
    return len;
}

