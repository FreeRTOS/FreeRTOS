/*
 * FreeRTOS V202112.00
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/* Standard includes. */
#include <stdio.h>
#include <stdlib.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "timers.h"
#include "semphr.h"

/* Various test includes. */
#include "BlockQ.h"
#include "integer.h"
#include "semtest.h"
#include "PollQ.h"
#include "GenQTest.h"
#include "QPeek.h"
#include "recmutex.h"
#include "flop.h"
#include "TimerDemo.h"
#include "countsem.h"
#include "death.h"
#include "QueueSet.h"
#include "QueueOverwrite.h"
#include "EventGroupsDemo.h"
#include "IntSemTest.h"
#include "IntQueue.h"
#include "TaskNotify.h"
#include "TaskNotifyArray.h"
#include "QueueSetPolling.h"
#include "StaticAllocation.h"
#include "blocktim.h"
#include "AbortDelay.h"
#include "MessageBufferDemo.h"
#include "StreamBufferDemo.h"
#include "StreamBufferInterrupt.h"
#include "RegTests.h"

/**
 * Priorities at which the tasks are created.
 */
#define mainCHECK_TASK_PRIORITY             ( configMAX_PRIORITIES - 2 )
#define mainQUEUE_POLL_PRIORITY             ( tskIDLE_PRIORITY + 1 )
#define mainSEM_TEST_PRIORITY               ( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY                ( tskIDLE_PRIORITY + 2 )
#define mainCREATOR_TASK_PRIORITY           ( tskIDLE_PRIORITY + 3 )
#define mainFLASH_TASK_PRIORITY             ( tskIDLE_PRIORITY + 1 )
#define mainINTEGER_TASK_PRIORITY           ( tskIDLE_PRIORITY )
#define mainGEN_QUEUE_TASK_PRIORITY         ( tskIDLE_PRIORITY )
#define mainFLOP_TASK_PRIORITY              ( tskIDLE_PRIORITY )
#define mainQUEUE_OVERWRITE_PRIORITY        ( tskIDLE_PRIORITY )
#define mainREGISTER_TEST_PRIORITY          ( tskIDLE_PRIORITY )

/* The period of the check task, in ms, converted to ticks using the
 * pdMS_TO_TICKS() macro.  mainNO_ERROR_CHECK_TASK_PERIOD is used if no errors
 * have been found, mainERROR_CHECK_TASK_PERIOD is used if an error has been
 * found. */
#define mainNO_ERROR_CHECK_TASK_PERIOD      pdMS_TO_TICKS( 3000UL )
#define mainERROR_CHECK_TASK_PERIOD         pdMS_TO_TICKS( 500UL )

/**
 * Period used in timer tests.
 */
#define mainTIMER_TEST_PERIOD               ( 50 )

/**
 * Success output messages. This is used by the CI - do not change.
 */
#define mainDEMO_SUCCESS_MESSAGE            "FreeRTOS Demo SUCCESS\r\n"
/*-----------------------------------------------------------*/

/**
 * The task that periodically checks that all the standard demo tasks are
 * still executing and error free.
 */
static void prvCheckTask( void *pvParameters );

/**
 * Called by main() to run the full demo (as opposed to the blinky demo) when
 * mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is set to 0.
 */
void main_full( void );

/**
 * Tick hook used by the full demo, which includes code that interacts with
 * some of the tests.
 */
void vFullDemoTickHook( void );
/*-----------------------------------------------------------*/

void main_full( void )
{
BaseType_t xResult;

    xResult = xTaskCreate( prvCheckTask,
                          "Check",
                          configMINIMAL_STACK_SIZE,
                          NULL,
                          mainCHECK_TASK_PRIORITY,
                          NULL );

    if( xResult == pdPASS )
    {
        #if( configSTART_TASK_NOTIFY_TESTS == 1 )
        {
            vStartTaskNotifyTask();
        }
        #endif /* configSTART_TASK_NOTIFY_TESTS */

        #if( configSTART_TASK_NOTIFY_ARRAY_TESTS == 1 )
        {
            vStartTaskNotifyArrayTask();
        }
        #endif /* configSTART_TASK_NOTIFY_ARRAY_TESTS */

        #if( configSTART_BLOCKING_QUEUE_TESTS == 1 )
        {
            vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
        }
        #endif /* configSTART_BLOCKING_QUEUE_TESTS */

        #if( configSTART_SEMAPHORE_TESTS == 1 )
        {
            vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
        }
        #endif /* configSTART_SEMAPHORE_TESTS */

        #if( configSTART_POLLED_QUEUE_TESTS == 1 )
        {
            vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
        }
        #endif /* configSTART_POLLED_QUEUE_TESTS */

        #if( configSTART_INTEGER_MATH_TESTS == 1 )
        {
            vStartIntegerMathTasks( mainINTEGER_TASK_PRIORITY );
        }
        #endif /* configSTART_INTEGER_MATH_TESTS */

        #if( configSTART_GENERIC_QUEUE_TESTS == 1 )
        {
            vStartGenericQueueTasks( mainGEN_QUEUE_TASK_PRIORITY );
        }
        #endif /* configSTART_GENERIC_QUEUE_TESTS */

        #if( configSTART_PEEK_QUEUE_TESTS == 1 )
        {
            vStartQueuePeekTasks();
        }
        #endif /* configSTART_PEEK_QUEUE_TESTS */

        #if( configSTART_MATH_TESTS == 1 )
        {
            vStartMathTasks( mainFLOP_TASK_PRIORITY );
        }
        #endif /* configSTART_MATH_TESTS */

        #if( configSTART_RECURSIVE_MUTEX_TESTS == 1 )
        {
            vStartRecursiveMutexTasks();
        }
        #endif /* configSTART_RECURSIVE_MUTEX_TESTS */

        #if( configSTART_COUNTING_SEMAPHORE_TESTS == 1 )
        {
            vStartCountingSemaphoreTasks();
        }
        #endif /* configSTART_COUNTING_SEMAPHORE_TESTS */

        #if( configSTART_QUEUE_SET_TESTS == 1 )
        {
            vStartQueueSetTasks();
        }
        #endif /* configSTART_QUEUE_SET_TESTS */

        #if( configSTART_QUEUE_OVERWRITE_TESTS == 1 )
        {
            vStartQueueOverwriteTask( mainQUEUE_OVERWRITE_PRIORITY );
        }
        #endif /* configSTART_QUEUE_OVERWRITE_TESTS */

        #if( configSTART_EVENT_GROUP_TESTS == 1 )
        {
            vStartEventGroupTasks();
        }
        #endif /* configSTART_EVENT_GROUP_TESTS */

        #if( configSTART_INTERRUPT_SEMAPHORE_TESTS == 1 )
        {
            vStartInterruptSemaphoreTasks();
        }
        #endif /* configSTART_INTERRUPT_SEMAPHORE_TESTS */

        #if( configSTART_QUEUE_SET_POLLING_TESTS == 1 )
        {
            vStartQueueSetPollingTask();
        }
        #endif /* configSTART_QUEUE_SET_POLLING_TESTS */

        #if( configSTART_BLOCK_TIME_TESTS == 1 )
        {
            vCreateBlockTimeTasks();
        }
        #endif /* configSTART_BLOCK_TIME_TESTS */

        #if( configSTART_ABORT_DELAY_TESTS == 1 )
        {
            vCreateAbortDelayTasks();
        }
        #endif /* configSTART_ABORT_DELAY_TESTS */

        #if( configSTART_MESSAGE_BUFFER_TESTS == 1 )
        {
            vStartMessageBufferTasks( configMINIMAL_STACK_SIZE );
        }
        #endif /* configSTART_MESSAGE_BUFFER_TESTS */

        #if(configSTART_STREAM_BUFFER_TESTS  == 1 )
        {
            vStartStreamBufferTasks();
        }
        #endif /* configSTART_STREAM_BUFFER_TESTS */

        #if( configSTART_STREAM_BUFFER_INTERRUPT_TESTS == 1 )
        {
            vStartStreamBufferInterruptDemo();
        }
        #endif /* configSTART_STREAM_BUFFER_INTERRUPT_TESTS */

        #if( ( configSTART_TIMER_TESTS == 1 ) && ( configUSE_PREEMPTION != 0 ) )
        {
            /* Don't expect these tasks to pass when preemption is not used. */
            vStartTimerDemoTask( mainTIMER_TEST_PERIOD );
        }
        #endif /* ( configSTART_TIMER_TESTS == 1 ) && ( configUSE_PREEMPTION != 0 ) */

        #if( configSTART_INTERRUPT_QUEUE_TESTS == 1 )
        {
            vStartInterruptQueueTasks();
        }
        #endif /* configSTART_INTERRUPT_QUEUE_TESTS */

        #if( configSTART_REGISTER_TESTS == 1 )
        {
            vStartRegisterTasks( mainREGISTER_TEST_PRIORITY );
        }
        #endif /* configSTART_REGISTER_TESTS */

        #if( configSTART_DELETE_SELF_TESTS == 1 )
        {
            /* The suicide tasks must be created last as they need to know how many
             * tasks were running prior to their creation.  This then allows them to
             * ascertain whether or not the correct/expected number of tasks are
             * running at any given time. */
            vCreateSuicidalTasks( mainCREATOR_TASK_PRIORITY );
        }
        #endif /* configSTART_DELETE_SELF_TESTS */
    }

    vTaskStartScheduler();
}
/*-----------------------------------------------------------*/

void vFullDemoTickHook( void )
{
    /* Called from vApplicationTickHook() when the project is configured to
     * build the full test/demo applications. */

    #if( configSTART_TASK_NOTIFY_TESTS == 1 )
    {
        xNotifyTaskFromISR();
    }
    #endif /* configSTART_TASK_NOTIFY_TESTS */

    #if( configSTART_TASK_NOTIFY_ARRAY_TESTS == 1 )
    {
        xNotifyArrayTaskFromISR();
    }
    #endif /* configSTART_TASK_NOTIFY_ARRAY_TESTS */

    #if( configSTART_QUEUE_SET_TESTS == 1 )
    {
        vQueueSetAccessQueueSetFromISR();
    }
    #endif /* configSTART_QUEUE_SET_TESTS */

    #if( configSTART_QUEUE_OVERWRITE_TESTS == 1 )
    {
        vQueueOverwritePeriodicISRDemo();
    }
    #endif /* configSTART_QUEUE_OVERWRITE_TESTS */

    #if( configSTART_EVENT_GROUP_TESTS == 1 )
    {
        vPeriodicEventGroupsProcessing();
    }
    #endif /* configSTART_EVENT_GROUP_TESTS */

    #if( configSTART_INTERRUPT_SEMAPHORE_TESTS == 1 )
    {
        vInterruptSemaphorePeriodicTest();
    }
    #endif /* configSTART_INTERRUPT_SEMAPHORE_TESTS */

    #if( configSTART_QUEUE_SET_POLLING_TESTS == 1 )
    {
        vQueueSetPollingInterruptAccess();
    }
    #endif /* configSTART_QUEUE_SET_POLLING_TESTS */

    #if( configSTART_STREAM_BUFFER_TESTS == 1 )
    {
        vPeriodicStreamBufferProcessing();
    }
    #endif /* configSTART_STREAM_BUFFER_TESTS */

    #if( configSTART_STREAM_BUFFER_INTERRUPT_TESTS == 1 )
    {
        vBasicStreamBufferSendFromISR();
    }
    #endif /* configSTART_STREAM_BUFFER_INTERRUPT_TESTS */

    #if( ( configSTART_TIMER_TESTS == 1 ) && ( configUSE_PREEMPTION != 0 ) )
    {
        /* Only created when preemption is used. */
        vTimerPeriodicISRTests();
    }
    #endif /* ( configSTART_TIMER_TESTS == 1 ) && ( configUSE_PREEMPTION != 0 ) */

    #if( configSTART_INTERRUPT_QUEUE_TESTS == 1 )
    {
        portYIELD_FROM_ISR( xFirstTimerHandler() );
    }
    #endif /* configSTART_INTERRUPT_QUEUE_TESTS */
}
/*-----------------------------------------------------------*/

static void prvCheckTask( void *pvParameters )
{
TickType_t xNextWakeTime;
TickType_t xCycleFrequency = mainNO_ERROR_CHECK_TASK_PERIOD;
char * const pcPassMessage = mainDEMO_SUCCESS_MESSAGE;
char * pcStatusMessage = pcPassMessage;
extern void vToggleLED( void );

    /* Silence compiler warnings about unused variables. */
    ( void ) pvParameters;

    /* Demo start marker. */
    configPRINT_STRING( "FreeRTOS Demo Start\r\n" );

    /* Initialise xNextWakeTime - this only needs to be done once. */
    xNextWakeTime = xTaskGetTickCount();

    for( ;; )
    {
        /* Place this task in the blocked state until it is time to run again. */
        vTaskDelayUntil( &xNextWakeTime, xCycleFrequency );

        #if( configSTART_TASK_NOTIFY_TESTS == 1 )
        {
            if( xAreTaskNotificationTasksStillRunning() != pdTRUE )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR:  Notification.\r\n";
            }
        }
        #endif /* configSTART_TASK_NOTIFY_TESTS */

        #if( configSTART_TASK_NOTIFY_ARRAY_TESTS == 1 )
        {
            if( xAreTaskNotificationArrayTasksStillRunning() != pdTRUE )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR:  Notification Array.\r\n";
            }
        }
        #endif /* configSTART_TASK_NOTIFY_ARRAY_TESTS */

        #if( configSTART_BLOCKING_QUEUE_TESTS == 1 )
        {
            if( xAreBlockingQueuesStillRunning() != pdTRUE )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: BlockQueue.\r\n";
            }
        }
        #endif /* configSTART_BLOCKING_QUEUE_TESTS */

        #if( configSTART_SEMAPHORE_TESTS == 1 )
        {
            if( xAreSemaphoreTasksStillRunning() != pdTRUE )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: SemTest.\r\n";
            }
        }
        #endif /* configSTART_SEMAPHORE_TESTS */

        #if( configSTART_POLLED_QUEUE_TESTS == 1 )
        {
            if( xArePollingQueuesStillRunning() != pdTRUE )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: PollQueue.\r\n";
            }
        }
        #endif /* configSTART_POLLED_QUEUE_TESTS */

        #if( configSTART_INTEGER_MATH_TESTS == 1 )
        {
            if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: IntMath.\r\n";
            }
        }
        #endif /* configSTART_INTEGER_MATH_TESTS */

        #if( configSTART_GENERIC_QUEUE_TESTS == 1 )
        {
            if( xAreGenericQueueTasksStillRunning() != pdTRUE )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: GenQueue.\r\n";
            }
        }
        #endif /* configSTART_GENERIC_QUEUE_TESTS */

        #if( configSTART_PEEK_QUEUE_TESTS == 1 )
        {
            if( xAreQueuePeekTasksStillRunning() != pdTRUE )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: QueuePeek.\r\n";
            }
        }
        #endif /* configSTART_PEEK_QUEUE_TESTS */

        #if( configSTART_MATH_TESTS == 1 )
        {
            if( xAreMathsTaskStillRunning() != pdPASS )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: Flop.\r\n";
            }
        }
        #endif /* configSTART_MATH_TESTS */

        #if( configSTART_RECURSIVE_MUTEX_TESTS == 1 )
        {
            if( xAreRecursiveMutexTasksStillRunning() != pdTRUE )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: RecMutex.\r\n";
            }
        }
        #endif /* configSTART_RECURSIVE_MUTEX_TESTS */

        #if( configSTART_COUNTING_SEMAPHORE_TESTS == 1 )
        {
            if( xAreCountingSemaphoreTasksStillRunning() != pdTRUE )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: CountSem.\r\n";
            }
        }
        #endif /* configSTART_COUNTING_SEMAPHORE_TESTS */

        #if( configSTART_QUEUE_SET_TESTS == 1 )
        {
            if( xAreQueueSetTasksStillRunning() != pdPASS )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: Queue set.\r\n";
            }
        }
        #endif /* configSTART_QUEUE_SET_TESTS */

        #if( configSTART_QUEUE_OVERWRITE_TESTS == 1 )
        {
            if( xIsQueueOverwriteTaskStillRunning() != pdPASS )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: Queue overwrite.\r\n";
            }
        }
        #endif /* configSTART_QUEUE_OVERWRITE_TESTS */

        #if( configSTART_EVENT_GROUP_TESTS == 1 )
        {
            if( xAreEventGroupTasksStillRunning() != pdTRUE )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: EventGroup.\r\n";
            }
        }
        #endif /* configSTART_EVENT_GROUP_TESTS */

        #if( configSTART_INTERRUPT_SEMAPHORE_TESTS == 1 )
        {
            if( xAreInterruptSemaphoreTasksStillRunning() != pdTRUE )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: IntSem.\r\n";
            }
        }
        #endif /* configSTART_INTERRUPT_SEMAPHORE_TESTS */

        #if( configSTART_QUEUE_SET_POLLING_TESTS == 1 )
        {
            if( xAreQueueSetPollTasksStillRunning() != pdPASS )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: Queue set polling.\r\n";
            }
        }
        #endif /* configSTART_QUEUE_SET_POLLING_TESTS */

        #if( configSTART_BLOCK_TIME_TESTS == 1 )
        {
            if( xAreBlockTimeTestTasksStillRunning() != pdPASS )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: Block time.\r\n";
            }
        }
        #endif /* configSTART_BLOCK_TIME_TESTS */

        #if( configSTART_ABORT_DELAY_TESTS == 1 )
        {
            if( xAreAbortDelayTestTasksStillRunning() != pdPASS )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: Abort delay.\r\n";
            }
        }
        #endif /* configSTART_ABORT_DELAY_TESTS */

        #if( configSTART_MESSAGE_BUFFER_TESTS == 1 )
        {
            if( xAreMessageBufferTasksStillRunning() != pdTRUE )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR:  MessageBuffer.\r\n";
            }
        }
        #endif /* configSTART_MESSAGE_BUFFER_TESTS */

        #if( configSTART_STREAM_BUFFER_TESTS == 1 )
        {
            if( xAreStreamBufferTasksStillRunning() != pdTRUE )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR:  StreamBuffer.\r\n";
            }
        }
        #endif /* configSTART_STREAM_BUFFER_TESTS */

        #if( configSTART_STREAM_BUFFER_INTERRUPT_TESTS == 1 )
        {
            if( xIsInterruptStreamBufferDemoStillRunning() != pdPASS )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: Stream buffer interrupt.\r\n";
            }
        }
        #endif /* configSTART_STREAM_BUFFER_INTERRUPT_TESTS */

        #if( ( configSTART_TIMER_TESTS == 1 ) && ( configUSE_PREEMPTION != 0 ) )
        {
            if( xAreTimerDemoTasksStillRunning( xCycleFrequency ) != pdTRUE )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: TimerDemo.\r\n";
            }
        }
        #endif /* ( configSTART_TIMER_TESTS == 1 ) && ( configUSE_PREEMPTION != 0 ) */

        #if( configSTART_INTERRUPT_QUEUE_TESTS == 1 )
        {
            if( xAreIntQueueTasksStillRunning() != pdTRUE )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: IntQueue.\r\n";
            }
        }
        #endif /* configSTART_INTERRUPT_QUEUE_TESTS */

        #if( configSTART_REGISTER_TESTS == 1 )
        {
            if( xAreRegisterTasksStillRunning() != pdTRUE )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: RegTests.\r\n";
            }
        }
        #endif /* configSTART_REGISTER_TESTS */

        #if( configSTART_DELETE_SELF_TESTS == 1 )
        {
            if( xIsCreateTaskStillRunning() != pdTRUE )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: Death.\r\n";
            }
        }
        #endif /* configSTART_DELETE_SELF_TESTS */

        /* Toggle the LED to show the system status if the UART is not
         * connected. */
        vToggleLED();

        /* If an error has been found then increase the LED toggle rate by
         * increasing the cycle frequency. */
        if( pcStatusMessage != pcPassMessage )
        {
            xCycleFrequency = mainERROR_CHECK_TASK_PERIOD;
        }

        configPRINT_STRING( pcStatusMessage );
    }
}
/*-----------------------------------------------------------*/
