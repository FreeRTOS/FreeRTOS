/*
 * FreeRTOS V202212.00
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
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

/******************************************************************************
 * NOTE 1:  This project provides two demo applications.  A simple blinky style
 * project, and a more comprehensive test and demo application.  The
 * mainCREATE_SIMPLE_BLINKY_DEMO_ONLY setting in main.c is used to select
 * between the two.  See the notes on using mainCREATE_SIMPLE_BLINKY_DEMO_ONLY
 * in main.c.  This file implements the comprehensive test and demo version.
 *
 * NOTE 2:  This file only contains the source code that is specific to the
 * full demo.  Generic functions, such FreeRTOS hook functions, and functions
 * required to configure the hardware, are defined in main.c.
 *
 ******************************************************************************
 *
 * main_full() creates all the demo application tasks and software timers, then
 * starts the scheduler.  The web documentation provides more details of the
 * standard demo application tasks, which provide no particular functionality,
 * but do provide a good example of how to use the FreeRTOS API.
 *
 * In addition to the standard demo tasks, the following tasks and tests are
 * defined and/or created within this file:
 *
 * "Reg test" tasks - These fill both the core registers with known values, then
 * check that each register maintains its expected value for the lifetime of the
 * task.  Each task uses a different set of values.  The reg test tasks execute
 * with a very low priority, so get preempted very frequently.  A register
 * containing an unexpected value is indicative of an error in the context
 * switching mechanism.
 *
 * "Check" task - The check executes every three seconds.  It checks that all
 * the standard demo tasks, and the register check tasks, are not only still
 * executing, but are executing without reporting any errors.  If the check task
 * discovers that a task has either stalled, or reported an error, then it
 * prints an error message to the UART, otherwise it prints "Pass.".
 */

/* Standard includes. */
#include <stdio.h>
#include <string.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "timers.h"
#include "semphr.h"

/* Standard demo application includes. */
#include "dynamic.h"
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
#include "TaskNotify.h"
#include "TaskNotifyArray.h"
#include "QueueSetPolling.h"
#include "StaticAllocation.h"
#include "blocktim.h"
#include "AbortDelay.h"
#include "MessageBufferDemo.h"
#include "StreamBufferDemo.h"
#include "StreamBufferInterrupt.h"

#if ( configSTART_QUEUE_SET_TESTS == 1 )
    #if ( configUSE_QUEUE_SETS != 1 )
        #error To run QUEUE_SET_TESTS and QUEUE_SET_POLLING_TESTS, INCLUDE_xTaskAbortDelay must be set to 1 in FreeRTOSConfig.h.
    #endif
#endif

#if ( configSTART_ABORT_DELAY_TESTS == 1 )
    #if ( INCLUDE_xTaskAbortDelay != 1 )
        #error To run xTaskAbortDelay test, so INCLUDE_xTaskAbortDelay must be set to 1 in FreeRTOSConfig.h.
    #endif
#endif

/* Priorities for the demo application tasks. */
#define mainCHECK_TASK_PRIORITY                 ( configMAX_PRIORITIES - 1 )
#define testrunnerCHECK_TASK_PRIORITY           ( configMAX_PRIORITIES - 2 )
#define testrunnerQUEUE_POLL_PRIORITY           ( tskIDLE_PRIORITY + 1 )
#define testrunnerSEM_TEST_PRIORITY             ( tskIDLE_PRIORITY + 1 )
#define testrunnerBLOCK_Q_PRIORITY              ( tskIDLE_PRIORITY + 2 )
#define testrunnerCREATOR_TASK_PRIORITY         ( tskIDLE_PRIORITY + 3 )
#define testrunnerFLASH_TASK_PRIORITY           ( tskIDLE_PRIORITY + 1 )
#define testrunnerINTEGER_TASK_PRIORITY         ( tskIDLE_PRIORITY )
#define testrunnerGEN_QUEUE_TASK_PRIORITY       ( tskIDLE_PRIORITY )
#define testrunnerFLOP_TASK_PRIORITY            ( tskIDLE_PRIORITY )
#define testrunnerQUEUE_OVERWRITE_PRIORITY      ( tskIDLE_PRIORITY )
#define testrunnerREGISTER_TEST_PRIORITY        ( tskIDLE_PRIORITY )

/* The period of the check task, in ms, converted to ticks using the
pdMS_TO_TICKS() macro.  mainNO_ERROR_CHECK_TASK_PERIOD is used if no errors have
been found, mainERROR_CHECK_TASK_PERIOD is used if an error has been found. */
#define mainNO_ERROR_CHECK_TASK_PERIOD          pdMS_TO_TICKS( 3000UL )
#define mainERROR_CHECK_TASK_PERIOD             pdMS_TO_TICKS( 500UL )

/* Parameters that are passed into the register check tasks solely for the
purpose of ensuring parameters are passed into tasks correctly. */
#define mainREG_TEST_TASK_1_PARAMETER           ( ( void * ) 0x12345678 )
#define mainREG_TEST_TASK_2_PARAMETER           ( ( void * ) 0x87654321 )

/* The base period used by the timer test tasks. */
#define mainTIMER_TEST_PERIOD                   ( 50 )

/* The size of the stack allocated to the check task (as described in the
comments at the top of this file.  This is surprisingly large as it calls
the logging library's print function, which allocates a 128 byte buffer on its
stack. */
#define mainCHECK_TASK_STACK_SIZE_WORDS         200

/* Size of the stacks to allocated for the register check tasks. */
#define mainREG_TEST_STACK_SIZE_WORDS           150

/* Success output messages. This is used by the CI - do not change. */
#define mainDEMO_SUCCESS_MESSAGE                "FreeRTOS Demo SUCCESS\r\n"
/*-----------------------------------------------------------*/

/*
 * Called by main() to run the full demo (as opposed to the blinky demo) when
 * mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is set to 0.
 */
void main_full( void );

/*
 * The check task, as described at the top of this file.
 */
static void prvCheckTask( void *pvParameters );

/*
 * Register check tasks as described at the top of this file.  The nature of
 * these files necessitates that they are written in an assembly file, but the
 * entry points are kept in the C file for the convenience of checking the task
 * parameter.
 */
#if( configSTART_REGISTER_TESTS == 1 )
    static void prvRegTestTaskEntry1( void *pvParameters );
    extern void vRegTest1Implementation( void );
    static void prvRegTestTaskEntry2( void *pvParameters );
    extern void vRegTest2Implementation( void );
#endif /* configSTART_REGISTER_TESTS */

/*
 * Tick hook used by the full demo, which includes code that interacts with
 * some of the tests.
 */
void vFullDemoTickHook( void );

/*-----------------------------------------------------------*/

/* The following two variables are used to communicate the status of the
register check tasks to the check task.  If the variables keep incrementing,
then the register check tasks have not discovered any errors.  If a variable
stops incrementing, then an error has been found. */
#if( configSTART_REGISTER_TESTS == 1 )
    volatile uint32_t ulRegTest1LoopCounter = 0UL, ulRegTest2LoopCounter = 0UL;
#endif /* configSTART_REGISTER_TESTS */

/*-----------------------------------------------------------*/

void main_full( void )
{
    BaseType_t xResult;
    xResult = xTaskCreate( prvCheckTask, "Check", mainCHECK_TASK_STACK_SIZE_WORDS, NULL, mainCHECK_TASK_PRIORITY, NULL );
    /* Start all the other standard demo/test tasks.  They have no particular
    functionality, but do demonstrate how to use the FreeRTOS API and test the
    kernel port. */
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
            vStartBlockingQueueTasks( testrunnerBLOCK_Q_PRIORITY );
        }
        #endif /* configSTART_BLOCKING_QUEUE_TESTS */

        #if( configSTART_SEMAPHORE_TESTS == 1 )
        {
            vStartSemaphoreTasks( testrunnerSEM_TEST_PRIORITY );
        }
        #endif /* configSTART_SEMAPHORE_TESTS */

        #if( configSTART_POLLED_QUEUE_TESTS == 1 )
        {
            vStartPolledQueueTasks( testrunnerQUEUE_POLL_PRIORITY );
        }
        #endif /* configSTART_POLLED_QUEUE_TESTS */

        #if( configSTART_INTEGER_MATH_TESTS == 1 )
        {
            vStartIntegerMathTasks( testrunnerINTEGER_TASK_PRIORITY );
        }
        #endif /* configSTART_INTEGER_MATH_TESTS */

        #if( configSTART_GENERIC_QUEUE_TESTS == 1 )
        {
            vStartGenericQueueTasks( testrunnerGEN_QUEUE_TASK_PRIORITY );
        }
        #endif /* configSTART_GENERIC_QUEUE_TESTS */

        #if( configSTART_PEEK_QUEUE_TESTS == 1 )
        {
            vStartQueuePeekTasks();
        }
        #endif /* configSTART_PEEK_QUEUE_TESTS */

        #if( configSTART_MATH_TESTS == 1 )
        {
            vStartMathTasks( testrunnerFLOP_TASK_PRIORITY );
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
            vStartQueueOverwriteTask( testrunnerQUEUE_OVERWRITE_PRIORITY );
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

        #if( configSTART_DELETE_SELF_TESTS == 1 )
        {
            /* The suicide tasks must be created last as they need to know how many
            * tasks were running prior to their creation.  This then allows them to
            * ascertain whether or not the correct/expected number of tasks are
            * running at any given time. */
            vCreateSuicidalTasks( testrunnerCREATOR_TASK_PRIORITY );
        }
        #endif /* configSTART_DELETE_SELF_TESTS */

        #if configSTART_DYNAMIC_PRIORITY_TESTS == 1
            vStartDynamicPriorityTasks();
        #endif

        /* Create the register check tasks, as described at the top of this    file.
        Use xTaskCreateStatic() to create a task using only statically allocated
        memory. */
        #if( configSTART_REGISTER_TESTS == 1 )
        {
            xTaskCreate( prvRegTestTaskEntry1,          /* The function that implements the task. */
                        "Reg1",                         /* The name of the task. */
                        mainREG_TEST_STACK_SIZE_WORDS,  /* Size of stack to allocate for the task - in words not bytes!. */
                        mainREG_TEST_TASK_1_PARAMETER,  /* Parameter passed into the task. */
                        tskIDLE_PRIORITY,               /* Priority of the task. */
                        NULL );                         /* Can be used to pass out a handle to the created task. */
            xTaskCreate( prvRegTestTaskEntry2, "Reg2", mainREG_TEST_STACK_SIZE_WORDS, mainREG_TEST_TASK_2_PARAMETER, tskIDLE_PRIORITY, NULL );
        }
        #endif /* configSTART_REGISTER_TESTS */
    }

    /* Start the scheduler. */
    vTaskStartScheduler();

    /* If all is well, the scheduler will now be running, and the following
    line will never be reached.  If the following line does execute, then
    there was insufficient FreeRTOS heap memory available for the Idle and/or
    timer tasks to be created.  See the memory management section on the
    FreeRTOS web site for more details on the FreeRTOS heap
    http://www.freertos.org/a00111.html. */
    for( ;; );
}
/*-----------------------------------------------------------*/

static void prvCheckTask( void *pvParameters )
{
TickType_t xDelayPeriod = mainNO_ERROR_CHECK_TASK_PERIOD;
TickType_t xLastExecutionTime;
char * const pcPassMessage = mainDEMO_SUCCESS_MESSAGE;
char * pcStatusMessage = pcPassMessage;
extern void vToggleLED( void );

#if( configSTART_REGISTER_TESTS == 1 )
    uint32_t ulLastRegTest1Value = 0, ulLastRegTest2Value = 0;
#endif /* configSTART_REGISTER_TESTS */

    /* Just to stop compiler warnings. */
    ( void ) pvParameters;

    /* Demo start marker. */
    configPRINT_STRING( "FreeRTOS Demo Start\r\n" );

    /* Initialise xLastExecutionTime so the first call to vTaskDelayUntil()
    works correctly. */
    xLastExecutionTime = xTaskGetTickCount();

    /* Cycle for ever, delaying then checking all the other tasks are still
    operating without error.  The onboard LED is toggled on each iteration.
    If an error is detected then the delay period is decreased from
    mainNO_ERROR_CHECK_TASK_PERIOD to mainERROR_CHECK_TASK_PERIOD.  This has the
    effect of increasing the rate at which the onboard LED toggles, and in so
    doing gives visual feedback of the system status. */
    for( ;; )
    {
        /* Delay until it is time to execute again. */
        vTaskDelayUntil( &xLastExecutionTime, xDelayPeriod );

        /* Check all the demo tasks (other than the flash tasks) to ensure
        that they are all still running, and that none have detected an error. */
        #if( configSTART_TASK_NOTIFY_TESTS == 1 )
        {
            if( xAreTaskNotificationTasksStillRunning() != pdTRUE )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR:  Notification";
            }
        }
        #endif /* configSTART_TASK_NOTIFY_TESTS */

        #if( configSTART_TASK_NOTIFY_ARRAY_TESTS == 1 )
        {
            if( xAreTaskNotificationArrayTasksStillRunning() != pdTRUE )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR:  Notification Array";
            }
        }
        #endif /* configSTART_TASK_NOTIFY_ARRAY_TESTS */

        #if( configSTART_BLOCKING_QUEUE_TESTS == 1 )
        {
            if( xAreBlockingQueuesStillRunning() != pdTRUE )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: BlockQueue";
            }
        }
        #endif /* configSTART_BLOCKING_QUEUE_TESTS */

        #if( configSTART_SEMAPHORE_TESTS == 1 )
        {
            if( xAreSemaphoreTasksStillRunning() != pdTRUE )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: SemTest";
            }
        }
        #endif /* configSTART_SEMAPHORE_TESTS */

        #if( configSTART_POLLED_QUEUE_TESTS == 1 )
        {
            if( xArePollingQueuesStillRunning() != pdTRUE )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: PollQueue";
            }
        }
        #endif /* configSTART_POLLED_QUEUE_TESTS */

        #if( configSTART_INTEGER_MATH_TESTS == 1 )
        {
            if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: IntMath";
            }
        }
        #endif /* configSTART_INTEGER_MATH_TESTS */

        #if( configSTART_GENERIC_QUEUE_TESTS == 1 )
        {
            if( xAreGenericQueueTasksStillRunning() != pdTRUE )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: GenQueue";
            }
        }
        #endif /* configSTART_GENERIC_QUEUE_TESTS */

        #if( configSTART_PEEK_QUEUE_TESTS == 1 )
        {
            if( xAreQueuePeekTasksStillRunning() != pdTRUE )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: QueuePeek";
            }
        }
        #endif /* configSTART_PEEK_QUEUE_TESTS */

        #if( configSTART_MATH_TESTS == 1 )
        {
            if( xAreMathsTaskStillRunning() != pdPASS )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: Flop";
            }
        }
        #endif /* configSTART_MATH_TESTS */

        #if( configSTART_RECURSIVE_MUTEX_TESTS == 1 )
        {
            if( xAreRecursiveMutexTasksStillRunning() != pdTRUE )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: RecMutex";
            }
        }
        #endif /* configSTART_RECURSIVE_MUTEX_TESTS */

        #if( configSTART_COUNTING_SEMAPHORE_TESTS == 1 )
        {
            if( xAreCountingSemaphoreTasksStillRunning() != pdTRUE )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: CountSem";
            }
        }
        #endif /* configSTART_COUNTING_SEMAPHORE_TESTS */

        #if( configSTART_QUEUE_SET_TESTS == 1 )
        {
            if( xAreQueueSetTasksStillRunning() != pdPASS )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: Queue set";
            }
        }
        #endif /* configSTART_QUEUE_SET_TESTS */

        #if( configSTART_QUEUE_OVERWRITE_TESTS == 1 )
        {
            if( xIsQueueOverwriteTaskStillRunning() != pdPASS )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: Queue overwrite";
            }
        }
        #endif /* configSTART_QUEUE_OVERWRITE_TESTS */

        #if( configSTART_EVENT_GROUP_TESTS == 1 )
        {
            if( xAreEventGroupTasksStillRunning() != pdTRUE )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: EventGroup";
            }
        }
        #endif /* configSTART_EVENT_GROUP_TESTS */

        #if( configSTART_INTERRUPT_SEMAPHORE_TESTS == 1 )
        {
            if( xAreInterruptSemaphoreTasksStillRunning() != pdTRUE )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: IntSem";
            }
        }
        #endif /* configSTART_INTERRUPT_SEMAPHORE_TESTS */

        #if( configSTART_QUEUE_SET_POLLING_TESTS == 1 )
        {
            if( xAreQueueSetPollTasksStillRunning() != pdPASS )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: Queue set polling";
            }
        }
        #endif /* configSTART_QUEUE_SET_POLLING_TESTS */

        #if( configSTART_BLOCK_TIME_TESTS == 1 )
        {
            if( xAreBlockTimeTestTasksStillRunning() != pdPASS )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: Block time";
            }
        }
        #endif /* configSTART_BLOCK_TIME_TESTS */

        #if( configSTART_ABORT_DELAY_TESTS == 1 )
        {
            if( xAreAbortDelayTestTasksStillRunning() != pdPASS )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: Abort delay";
            }
        }
        #endif /* configSTART_ABORT_DELAY_TESTS */

        #if( configSTART_MESSAGE_BUFFER_TESTS == 1 )
        {
            if( xAreMessageBufferTasksStillRunning() != pdTRUE )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR:  MessageBuffer";
            }
        }
        #endif /* configSTART_MESSAGE_BUFFER_TESTS */

        #if( configSTART_STREAM_BUFFER_TESTS == 1 )
        {
            if( xAreStreamBufferTasksStillRunning() != pdTRUE )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR:  StreamBuffer";
            }
        }
        #endif /* configSTART_STREAM_BUFFER_TESTS */

        #if( configSTART_STREAM_BUFFER_INTERRUPT_TESTS == 1 )
        {
            if( xIsInterruptStreamBufferDemoStillRunning() != pdPASS )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: Stream buffer interrupt";
            }
        }
        #endif /* configSTART_STREAM_BUFFER_INTERRUPT_TESTS */

        #if( ( configSTART_TIMER_TESTS == 1 ) && ( configUSE_PREEMPTION != 0 ) )
        {
            if( xAreTimerDemoTasksStillRunning( ( TickType_t ) xDelayPeriod ) != pdTRUE )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: TimerDemo";
            }
        }
        #endif /* ( configSTART_TIMER_TESTS == 1 ) && ( configUSE_PREEMPTION != 0 ) */

        #if( configSTART_DELETE_SELF_TESTS == 1 )
        {
            if( xIsCreateTaskStillRunning() != pdTRUE )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: Death";
            }
        }
        #endif /* configSTART_DELETE_SELF_TESTS */

        #if configSTART_DYNAMIC_PRIORITY_TESTS == 1
            if( xAreDynamicPriorityTasksStillRunning() == pdFALSE )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: Dynamic priority demo/tests.\r\n";
            }
        #endif

        #if( configSTART_REGISTER_TESTS == 1 )
        {
            /* Check that the register test 1 task is still running. */
            if( ulLastRegTest1Value == ulRegTest1LoopCounter )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: Register test 1.\r\n";
            }
            ulLastRegTest1Value = ulRegTest1LoopCounter;

            /* Check that the register test 2 task is still running. */
            if( ulLastRegTest2Value == ulRegTest2LoopCounter )
            {
                pcStatusMessage = "FreeRTOS Demo ERROR: Register test 2.\r\n";
            }
            ulLastRegTest2Value = ulRegTest2LoopCounter;
        }
        #endif /* configSTART_REGISTER_TESTS */

        /* Write the status message to the UART. */
        vToggleLED();

        /* If an error has been found then increase the LED toggle rate by
        increasing the cycle frequency. */
        if( pcStatusMessage != pcPassMessage )
        {
            xDelayPeriod = mainERROR_CHECK_TASK_PERIOD;
        }

        configPRINT_STRING( pcStatusMessage );
    }
}
/*-----------------------------------------------------------*/

#if( configSTART_REGISTER_TESTS == 1 )
    static void prvRegTestTaskEntry1( void *pvParameters )
    {
        /* Although the regtest task is written in assembler, its entry point is
        written in C for convenience of checking the task parameter is being passed
        in correctly. */
        if( pvParameters == mainREG_TEST_TASK_1_PARAMETER )
        {
            /* Start the part of the test that is written in assembler. */
            vRegTest1Implementation();
        }

        /* The following line will only execute if the task parameter is found to
        be incorrect.  The check task will detect that the regtest loop counter is
        not being incremented and flag an error. */
        vTaskDelete( NULL );
    }
#endif /* configSTART_REGISTER_TESTS */
/*-----------------------------------------------------------*/

#if( configSTART_REGISTER_TESTS == 1 )
    static void prvRegTestTaskEntry2( void *pvParameters )
    {
        /* Although the regtest task is written in assembler, its entry point is
        written in C for convenience of checking the task parameter is being passed
        in correctly. */
        if( pvParameters == mainREG_TEST_TASK_2_PARAMETER )
        {
            /* Start the part of the test that is written in assembler. */
            vRegTest2Implementation();
        }

        /* The following line will only execute if the task parameter is found to
        be incorrect.  The check task will detect that the regtest loop counter is
        not being incremented and flag an error. */
        vTaskDelete( NULL );
    }
#endif /* configSTART_REGISTER_TESTS */
/*-----------------------------------------------------------*/

void vFullDemoTickHook( void )
{
    /* The full demo includes a software timer demo/test that requires
    build the full test/demo applications. */
    #if( configSTART_TASK_NOTIFY_TESTS == 1 )
    {
        /* Use task notifications from an interrupt. */
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
        /* Call the periodic event group from ISR demo. */
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
        /* Writes to stream buffer byte by byte to test the stream buffer trigger
        level functionality. */
        vPeriodicStreamBufferProcessing();
    }
    #endif /* configSTART_STREAM_BUFFER_TESTS */

    #if( configSTART_STREAM_BUFFER_INTERRUPT_TESTS == 1 )
    {
        /* Writes a string to a string buffer four bytes at a time to demonstrate
        a stream being sent from an interrupt to a task. */        
        vBasicStreamBufferSendFromISR();
    }
    #endif /* configSTART_STREAM_BUFFER_INTERRUPT_TESTS */

    #if( ( configSTART_TIMER_TESTS == 1 ) && ( configUSE_PREEMPTION != 0 ) )
    {
        /* The full demo includes a software timer demo/test that requires
        prodding periodically from the tick interrupt. */

        /* Only created when preemption is used. */
        vTimerPeriodicISRTests();
    }
    #endif /* ( configSTART_TIMER_TESTS == 1 ) && ( configUSE_PREEMPTION != 0 ) */
}
/*-----------------------------------------------------------*/
