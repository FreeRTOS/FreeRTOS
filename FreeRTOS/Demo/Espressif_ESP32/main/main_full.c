/*
 * FreeRTOS V202212.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

/*
 * Common/Minimal demo task wiring + Check task.  Adapted for ESP-IDF
 * (scheduler is already running, so main_full() does not start it).
 */

#include <stdlib.h>
#include <string.h>
#include <stdio.h>

/* Kernel includes. */
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "freertos/queue.h"
#include "freertos/timers.h"
#include "freertos/semphr.h"

/* Standard demo includes. */
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
#include "dynamic.h"
#include "QueueSet.h"
#include "QueueOverwrite.h"
#include "EventGroupsDemo.h"
#include "IntSemTest.h"
#include "TaskNotify.h"
#include "QueueSetPolling.h"
#include "IntQueue.h"
#include "StaticAllocation.h"
#include "blocktim.h"
#include "AbortDelay.h"
#include "MessageBufferDemo.h"
#include "StreamBufferDemo.h"
#include "StreamBufferInterrupt.h"
#include "MessageBufferAMP.h"

#include "IntQueueTimer.h"

/* Priorities at which the tasks are created. */
#define mainCHECK_TASK_PRIORITY         ( tskIDLE_PRIORITY + 1 )
#define mainQUEUE_POLL_PRIORITY         ( tskIDLE_PRIORITY + 1 )
#define mainSEM_TEST_PRIORITY           ( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY            ( tskIDLE_PRIORITY + 2 )
#define mainCREATOR_TASK_PRIORITY       ( tskIDLE_PRIORITY + 3 )
#define mainFLASH_TASK_PRIORITY         ( tskIDLE_PRIORITY + 1 )
#define mainINTEGER_TASK_PRIORITY       ( tskIDLE_PRIORITY )
#define mainGEN_QUEUE_TASK_PRIORITY     ( tskIDLE_PRIORITY )
#define mainFLOP_TASK_PRIORITY          ( tskIDLE_PRIORITY )
#define mainQUEUE_OVERWRITE_PRIORITY    ( tskIDLE_PRIORITY )

#define mainTIMER_TEST_PERIOD           ( 50 )

/* Task function prototypes. */
static void prvCheckTask( void * pvParameters );
static void prvDemoQueueSpaceFunctions( void * pvParameters );
static void prvPermanentlyBlockingSemaphoreTask( void * pvParameters );
static void prvPermanentlyBlockingNotificationTask( void * pvParameters );
static void prvDemonstrateChangingTimerReloadMode( void * pvParameters );
static void prvReloadModeTestTimerCallback( TimerHandle_t xTimer );

/*-----------------------------------------------------------*/

/* Exercised by vFullDemoIdleFunction (vSemaphoreDelete + queue registry). */
static SemaphoreHandle_t xMutexToDelete = NULL;

/*-----------------------------------------------------------*/

/* Some Common/Minimal tests assume that a higher priority task will block a
 * lower priority task from running, which does not hold where tasks of
 * different priorities can run at the same time.  Those tests are left out
 * rather than pinned to one core or given settling delays, either of which
 * would measure scheduling latency rather than the primitive under test.  This
 * follows the convention used by
 * Demo/ThirdParty/Community-Supported-Demos/CORTEX_M0+_RP2040/Standard_smp. */
#if ( configNUMBER_OF_CORES == 1 ) || ( configRUN_MULTIPLE_PRIORITIES == 0 )
    #define mainENABLE_ORDER_DEPENDENT_TESTS    1
#else
    #define mainENABLE_ORDER_DEPENDENT_TESTS    0
#endif

void main_full( void )
{
    /* Scheduler is already running when this runs (the port has no
     * before-scheduler-starts hook).  Boost the calling task above
     * every demo priority so demo tasks created below queue without
     * being dispatched mid-setup. */
    TaskHandle_t xCallingTask = xTaskGetCurrentTaskHandle();
    UBaseType_t uxCallerOriginalPriority = uxTaskPriorityGet( xCallingTask );

    vTaskPrioritySet( xCallingTask, configMAX_PRIORITIES - 1 );

    xTaskCreate( prvCheckTask, "Check", configMINIMAL_STACK_SIZE * 2, NULL, mainCHECK_TASK_PRIORITY, NULL );

    vStartTaskNotifyTask();
    vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
    vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
    vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
    vStartIntegerMathTasks( mainINTEGER_TASK_PRIORITY );
    vStartGenericQueueTasks( mainGEN_QUEUE_TASK_PRIORITY );
    #if ( mainENABLE_ORDER_DEPENDENT_TESTS == 1 )
        vStartQueuePeekTasks();
    #endif
    vStartMathTasks( mainFLOP_TASK_PRIORITY );
    #if ( mainENABLE_ORDER_DEPENDENT_TESTS == 1 )
        vStartRecursiveMutexTasks();
    #endif
    vStartCountingSemaphoreTasks();
    #if ( mainENABLE_ORDER_DEPENDENT_TESTS == 1 )
        vStartDynamicPriorityTasks();
    #endif
    vStartQueueOverwriteTask( mainQUEUE_OVERWRITE_PRIORITY );
    #if ( mainENABLE_ORDER_DEPENDENT_TESTS == 1 )
        vStartEventGroupTasks();
        vStartInterruptSemaphoreTasks();
        vCreateBlockTimeTasks();
    #endif
    vCreateAbortDelayTasks();
    xTaskCreate( prvDemoQueueSpaceFunctions, "QSpace", configMINIMAL_STACK_SIZE * 2, NULL, tskIDLE_PRIORITY, NULL );
    xTaskCreate( prvPermanentlyBlockingSemaphoreTask, "BlockSem", configMINIMAL_STACK_SIZE * 2, NULL, tskIDLE_PRIORITY, NULL );
    xTaskCreate( prvPermanentlyBlockingNotificationTask, "BlockNoti", configMINIMAL_STACK_SIZE * 2, NULL, tskIDLE_PRIORITY, NULL );
    xTaskCreate( prvDemonstrateChangingTimerReloadMode, "TimerMode", configMINIMAL_STACK_SIZE * 2, NULL, configMAX_PRIORITIES - 1, NULL );

    vStartMessageBufferTasks( configMINIMAL_STACK_SIZE * 2 );
    vStartStreamBufferTasks();
    vStartStreamBufferInterruptDemo();
    vStartMessageBufferAMPTasks( configMINIMAL_STACK_SIZE * 2 );

    vStartInterruptQueueTasks();

    #if ( configUSE_QUEUE_SETS == 1 )
    {
        vStartQueueSetTasks();
        vStartQueueSetPollingTask();
    }
    #endif

    vStartStaticallyAllocatedTasks();
    #if ( mainENABLE_ORDER_DEPENDENT_TESTS == 1 )
        vStartTimerDemoTask( mainTIMER_TEST_PERIOD );
    #endif

    /* Suicidal tasks must be created last (they snapshot the live task
     * count). */
    vCreateSuicidalTasks( mainCREATOR_TASK_PRIORITY );

    /* Created here so the idle helper can demonstrate vSemaphoreDelete()
     * + queue registry round-trip. */
    xMutexToDelete = xSemaphoreCreateMutex();

    vTaskPrioritySet( xCallingTask, uxCallerOriginalPriority );
}
/*-----------------------------------------------------------*/

/* Total demo runtime in seconds.  0 = run unbounded (no end summary). */
#ifndef mainDEMO_DURATION_S
    #define mainDEMO_DURATION_S    ( 180 )
#endif

#define mainCYCLE_PERIOD_MS    ( 3000UL )

typedef BaseType_t ( * CheckFn_t )( void );

typedef struct
{
    const char * pcName;
    CheckFn_t    pfnCheck;
} CheckEntry_t;

#if ( mainENABLE_ORDER_DEPENDENT_TESTS == 1 )
    static BaseType_t prvCheckTimerDemo( void )
    {
        return xAreTimerDemoTasksStillRunning( pdMS_TO_TICKS( mainCYCLE_PERIOD_MS ) );
    }
#endif

static const CheckEntry_t xChecks[] =
{
    { "MessageBuffer",      xAreMessageBufferTasksStillRunning       },
    { "TaskNotification",   xAreTaskNotificationTasksStillRunning    },
    { "IntMath",            xAreIntegerMathsTaskStillRunning         },
    { "BlockingQueue",      xAreBlockingQueuesStillRunning           },
    { "SemTest",            xAreSemaphoreTasksStillRunning           },
    { "PollQueue",          xArePollingQueuesStillRunning            },
    { "Flop",               xAreMathsTaskStillRunning                },
    { "CountSem",           xAreCountingSemaphoreTasksStillRunning   },
    { "Death",              xIsCreateTaskStillRunning                },
    { "QueueOverwrite",     xIsQueueOverwriteTaskStillRunning        },
    { "IntStreamBuffer",    xIsInterruptStreamBufferDemoStillRunning },
    { "MessageBufferAMP",   xAreMessageBufferAMPTasksStillRunning    },
    #if ( configUSE_QUEUE_SETS == 1 )
        { "QueueSet",           xAreQueueSetTasksStillRunning            },
        { "QueueSetPolling",    xAreQueueSetPollTasksStillRunning        },
    #endif
    { "StaticAllocation",   xAreStaticAllocationTasksStillRunning    },
    { "GenericQueue",       xAreGenericQueueTasksStillRunning        },
    { "StreamBuffer",       xAreStreamBufferTasksStillRunning        },
    { "AbortDelay",         xAreAbortDelayTestTasksStillRunning      },
    { "IntQueue",           xAreIntQueueTasksStillRunning            },
    #if ( mainENABLE_ORDER_DEPENDENT_TESTS == 1 )
        { "EventGroup",         xAreEventGroupTasksStillRunning          },
        { "QueuePeek",          xAreQueuePeekTasksStillRunning           },
        { "DynamicPriority",    xAreDynamicPriorityTasksStillRunning     },
        { "TimerDemo",          prvCheckTimerDemo                        },
        { "BlockTime",          xAreBlockTimeTestTasksStillRunning       },
        { "IntSem",             xAreInterruptSemaphoreTasksStillRunning  },
        { "RecMutex",           xAreRecursiveMutexTasksStillRunning      },
    #endif
};

#define mainNUM_CHECKS    ( sizeof( xChecks ) / sizeof( xChecks[ 0 ] ) )

static uint32_t prvSumCounts( const uint32_t pulCounts[ mainNUM_CHECKS ] )
{
    uint32_t ulTotal = 0;
    for( size_t i = 0; i < mainNUM_CHECKS; i++ )
    {
        ulTotal += pulCounts[ i ];
    }
    return ulTotal;
}

static void prvCheckTask( void * pvParameters )
{
    const TickType_t xCycleFreq = pdMS_TO_TICKS( mainCYCLE_PERIOD_MS );
    TickType_t xNextWake = xTaskGetTickCount();
    uint32_t ulCycle = 0;
    const uint32_t ulMaxCycles = ( mainDEMO_DURATION_S * 1000UL ) / mainCYCLE_PERIOD_MS;
    uint32_t ulPassCounts[ mainNUM_CHECKS ] = { 0 };
    uint32_t ulFailCounts[ mainNUM_CHECKS ] = { 0 };

    ( void ) pvParameters;

    printf( "\r\n----- Demo run begins -----\r\n" );
    printf( "Cycle period: %lu ms, %u entries per cycle\r\n",
            ( unsigned long ) mainCYCLE_PERIOD_MS,
            ( unsigned ) mainNUM_CHECKS );
    if( mainDEMO_DURATION_S > 0 )
    {
        printf( "Duration: %d s (%lu cycles)\r\n",
                mainDEMO_DURATION_S,
                ( unsigned long ) ulMaxCycles );
    }
    else
    {
        printf( "Duration: unbounded\r\n" );
    }
    printf( "---------------------------\r\n\r\n" );

    for( ; ; )
    {
        vTaskDelayUntil( &xNextWake, xCycleFreq );
        ulCycle++;

        uint32_t ulCyclePass = 0, ulCycleFail = 0;

        printf( "----- Cycle %lu (tick %lu) -----\r\n",
                ( unsigned long ) ulCycle,
                ( unsigned long ) xTaskGetTickCount() );

        for( size_t i = 0; i < mainNUM_CHECKS; i++ )
        {
            const char * pcResult;

            if( xChecks[ i ].pfnCheck() == pdPASS )
            {
                ulPassCounts[ i ]++;
                ulCyclePass++;
                pcResult = "PASS";
            }
            else
            {
                ulFailCounts[ i ]++;
                ulCycleFail++;
                pcResult = "FAIL";
            }

            printf( "test_%s:%s\r\n", xChecks[ i ].pcName, pcResult );
        }

        printf( "Cycle %lu: %lu PASS  %lu FAIL\r\n\r\n",
                ( unsigned long ) ulCycle,
                ( unsigned long ) ulCyclePass,
                ( unsigned long ) ulCycleFail );

        if( ( mainDEMO_DURATION_S > 0 ) && ( ulCycle >= ulMaxCycles ) )
        {
            uint32_t ulTotalPass = prvSumCounts( ulPassCounts );
            uint32_t ulTotalFail = prvSumCounts( ulFailCounts );
            uint32_t ulTotalRun = ulTotalPass + ulTotalFail;

            printf( "\r\n-----------------------\r\n" );
            printf( "Demo run complete: %lu cycles, %lu s.\r\n\r\n",
                    ( unsigned long ) ulCycle,
                    ( unsigned long ) ( ulCycle * mainCYCLE_PERIOD_MS / 1000UL ) );
            printf( "Per-test totals (PASS / FAIL over %lu cycles):\r\n",
                    ( unsigned long ) ulCycle );
            for( size_t i = 0; i < mainNUM_CHECKS; i++ )
            {
                printf( "  test_%-18s %5lu / %5lu\r\n",
                        xChecks[ i ].pcName,
                        ( unsigned long ) ulPassCounts[ i ],
                        ( unsigned long ) ulFailCounts[ i ] );
            }
            printf( "\r\n%lu Tests %lu Failures\r\n",
                    ( unsigned long ) ulTotalRun,
                    ( unsigned long ) ulTotalFail );
            printf( "%s\r\n", ( ulTotalFail == 0 ) ? "OK" : "FAILED" );
            printf( "-----------------------\r\n" );

            vTaskSuspend( NULL );
        }
    }
}
/*-----------------------------------------------------------*/

void vFullDemoIdleFunction( void )
{
    /* One-shot mutex registry round-trip + vSemaphoreDelete demo. */
    if( xMutexToDelete != NULL )
    {
        configASSERT( pcQueueGetName( xMutexToDelete ) == NULL );
        vQueueAddToRegistry( xMutexToDelete, "Test_Mutex" );
        configASSERT( strcmp( pcQueueGetName( xMutexToDelete ), "Test_Mutex" ) == 0 );
        vQueueUnregisterQueue( xMutexToDelete );
        configASSERT( pcQueueGetName( xMutexToDelete ) == NULL );

        vSemaphoreDelete( xMutexToDelete );
        xMutexToDelete = NULL;
    }

    /* Exercise the heap. */
    void * pvAllocated = pvPortMalloc( ( rand() % 500 ) + 1 );
    if( pvAllocated != NULL )
    {
        vPortFree( pvAllocated );
    }
}
/*-----------------------------------------------------------*/

/* IntQueue calls this from a task once the scheduler is running to start its
 * timers.  The ESP32 demo drives the IntQueue handlers from the tick hook
 * instead, so no dedicated timer is needed. */
void vInitialiseTimerForIntQueueTest( void )
{
}
/*-----------------------------------------------------------*/

void vFullDemoTickHookFunction( void )
{
    vQueueOverwritePeriodicISRDemo();

    #if ( configUSE_QUEUE_SETS == 1 )
    {
        vQueueSetAccessQueueSetFromISR();
        vQueueSetPollingInterruptAccess();
    }
    #endif

    #if ( mainENABLE_ORDER_DEPENDENT_TESTS == 1 )
        vPeriodicEventGroupsProcessing();
        vInterruptSemaphorePeriodicTest();
        vTimerPeriodicISRTests();
    #endif
    xNotifyTaskFromISR();
    vPeriodicStreamBufferProcessing();
    vBasicStreamBufferSendFromISR();
    ( void ) xFirstTimerHandler();
    ( void ) xSecondTimerHandler();

    /* The daemon's priority is fixed at creation, so this is checked once rather
     * than on every tick - uxTaskPriorityGetFromISR() takes a kernel critical
     * section. */
    static BaseType_t xTimerPriorityChecked = pdFALSE;

    if( xTimerPriorityChecked == pdFALSE )
    {
        TaskHandle_t xTimerTask = xTimerGetTimerDaemonTaskHandle();
        configASSERT( uxTaskPriorityGetFromISR( xTimerTask ) == configTIMER_TASK_PRIORITY );
        xTimerPriorityChecked = pdTRUE;
    }
}
/*-----------------------------------------------------------*/

static void prvDemoQueueSpaceFunctions( void * pvParameters )
{
    QueueHandle_t xQueue = NULL;
    const UBaseType_t uxQueueLength = 10;
    UBaseType_t uxReturn, x;

    ( void ) pvParameters;

    xQueue = xQueueCreate( uxQueueLength, 0 );
    configASSERT( xQueue );

    for( ; ; )
    {
        for( x = 0; x < uxQueueLength; x++ )
        {
            uxReturn = uxQueueMessagesWaiting( xQueue );

            if( uxReturn != x )
            {
                configASSERT( xQueue == NULL );
            }

            uxReturn = uxQueueSpacesAvailable( xQueue );

            if( uxReturn != ( uxQueueLength - x ) )
            {
                configASSERT( xQueue == NULL );
            }

            xQueueSendToBack( xQueue, NULL, 0 );
        }

        uxReturn = uxQueueMessagesWaiting( xQueue );

        if( uxReturn != uxQueueLength )
        {
            configASSERT( xQueue == NULL );
        }

        uxReturn = uxQueueSpacesAvailable( xQueue );

        if( uxReturn != 0 )
        {
            configASSERT( xQueue == NULL );
        }

        xQueueReset( xQueue );

        #if ( configUSE_PREEMPTION == 0 )
            taskYIELD();
        #endif
    }
}
/*-----------------------------------------------------------*/

static void prvPermanentlyBlockingSemaphoreTask( void * pvParameters )
{
    SemaphoreHandle_t xSemaphore;

    ( void ) pvParameters;

    xSemaphore = xSemaphoreCreateBinary();
    configASSERT( xSemaphore );

    xSemaphoreTake( xSemaphore, portMAX_DELAY );

    configASSERT( pvParameters != NULL );
    vTaskDelete( NULL );
}
/*-----------------------------------------------------------*/

static void prvPermanentlyBlockingNotificationTask( void * pvParameters )
{
    ( void ) pvParameters;

    ulTaskNotifyTake( pdTRUE, portMAX_DELAY );

    configASSERT( pvParameters != NULL );
    vTaskDelete( NULL );
}
/*-----------------------------------------------------------*/

static void prvReloadModeTestTimerCallback( TimerHandle_t xTimer )
{
    intptr_t ulTimerID;

    ulTimerID = ( intptr_t ) pvTimerGetTimerID( xTimer );
    ulTimerID++;
    vTimerSetTimerID( xTimer, ( void * ) ulTimerID );
}
/*-----------------------------------------------------------*/

static void prvDemonstrateChangingTimerReloadMode( void * pvParameters )
{
    TimerHandle_t xTimer;
    const char * const pcTimerName = "TestTimer2";
    const TickType_t x50ms = pdMS_TO_TICKS( 50UL );

    ( void ) pvParameters;

    xTimer = xTimerCreate( pcTimerName, x50ms, pdFALSE, 0, prvReloadModeTestTimerCallback );
    configASSERT( xTimer );
    configASSERT( xTimerIsTimerActive( xTimer ) == pdFALSE );
    configASSERT( xTimerGetTimerDaemonTaskHandle() != NULL );
    configASSERT( strcmp( pcTimerName, pcTimerGetName( xTimer ) ) == 0 );
    configASSERT( xTimerGetPeriod( xTimer ) == x50ms );

    vTimerSetTimerID( xTimer, ( void * ) 0 );
    xTimerStart( xTimer, portMAX_DELAY );
    vTaskDelay( 3UL * x50ms );
    configASSERT( ( ( uintptr_t ) ( pvTimerGetTimerID( xTimer ) ) ) == 1UL );

    vTimerSetReloadMode( xTimer, pdTRUE );
    vTimerSetTimerID( xTimer, ( void * ) 0 );
    xTimerStart( xTimer, 0 );
    vTaskDelay( ( 3UL * x50ms ) + ( x50ms / 2UL ) );
    configASSERT( ( uintptr_t ) ( pvTimerGetTimerID( xTimer ) ) == 3UL );
    configASSERT( xTimerStop( xTimer, 0 ) != pdFAIL );

    vTimerSetReloadMode( xTimer, pdFALSE );
    vTimerSetTimerID( xTimer, ( void * ) 0 );
    xTimerStart( xTimer, 0 );
    vTaskDelay( 3UL * x50ms );
    configASSERT( xTimerStop( xTimer, 0 ) != pdFAIL );
    configASSERT( ( uintptr_t ) ( pvTimerGetTimerID( xTimer ) ) == 1UL );

    xTimerDelete( xTimer, portMAX_DELAY );
    vTaskDelete( NULL );
}
