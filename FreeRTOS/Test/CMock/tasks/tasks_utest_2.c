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
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */
/*! @file tasks_utest_2.c */

/* Tasks includes */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"
#include "task.h"

#include "mock_list.h"
#include "mock_list_macros.h"
#include "mock_timers.h"
#include "mock_portable.h"

/* Test includes. */
#include "unity.h"
#include "global_vars.h"

/* C runtime includes. */
#include <stdbool.h>
#include <string.h>


/* ===========================  EXTERN VARIABLES  =========================== */
extern TCB_t * volatile pxCurrentTCB;
extern List_t pxReadyTasksLists[ configMAX_PRIORITIES ];
extern List_t xDelayedTaskList1;
extern List_t xDelayedTaskList2;
extern List_t * volatile pxDelayedTaskList;
extern List_t * volatile pxOverflowDelayedTaskList;
extern List_t xPendingReadyList;
/* INCLUDE_vTaskDelete */
extern List_t xTasksWaitingTermination;
extern volatile UBaseType_t uxDeletedTasksWaitingCleanUp;
extern List_t xSuspendedTaskList;

extern volatile UBaseType_t uxCurrentNumberOfTasks;
extern volatile TickType_t xTickCount;
extern volatile UBaseType_t uxTopReadyPriority;
extern volatile BaseType_t xSchedulerRunning;
extern volatile TickType_t xPendedTicks;
extern volatile BaseType_t xYieldPending;
extern volatile BaseType_t xNumOfOverflows;
extern UBaseType_t uxTaskNumber;
extern volatile TickType_t xNextTaskUnblockTime;
extern TaskHandle_t xIdleTaskHandle;
extern volatile UBaseType_t uxSchedulerSuspended;


/* ===========================  GLOBAL VARIABLES  =========================== */
static StaticTask_t xIdleTaskTCB;
static StackType_t uxIdleTaskStack[ configMINIMAL_STACK_SIZE ];


/* ===========================  Static Functions  =========================== */
static TaskHandle_t create_task()
{
    TaskFunction_t pxTaskCode = NULL;
    const char * const pcName = { __FUNCTION__ };
    const uint32_t usStackDepth = 300;
    void * const pvParameters = NULL;
    UBaseType_t uxPriority = create_task_priority;
    TaskHandle_t taskHandle;
    BaseType_t ret;

    pvPortMalloc_ExpectAndReturn( sizeof( TCB_t ), &tcb[ created_tasks ] );
    pvPortMalloc_ExpectAndReturn( usStackDepth * sizeof( StackType_t ), stack );

    vListInitialiseItem_Expect( &( tcb[ created_tasks ].xStateListItem ) );
    vListInitialiseItem_Expect( &( tcb[ created_tasks ].xEventListItem ) );
    /* TODO: expect set owner */
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();
    /* TODO: expect set owner */

    pxPortInitialiseStack_ExpectAnyArgsAndReturn( stack );

    if( is_first_task )
    {
        for( int i = ( UBaseType_t ) 0U; i < ( UBaseType_t ) configMAX_PRIORITIES; i++ )
        {
            vListInitialise_ExpectAnyArgs();
        }

        /* Delayed Task List 1 */
        vListInitialise_ExpectAnyArgs();
        /* Delayed Task List 2 */
        vListInitialise_ExpectAnyArgs();
        /* Pending Ready List */
        vListInitialise_ExpectAnyArgs();
        /* INCLUDE_vTaskDelete */
        vListInitialise_ExpectAnyArgs();
        /* INCLUDE_vTaskSuspend */
        vListInitialise_ExpectAnyArgs();
        is_first_task = false;
    }

    vListInsertEnd_ExpectAnyArgs();
    ret = xTaskCreate( pxTaskCode,
                       pcName,
                       usStackDepth,
                       pvParameters,
                       uxPriority,
                       &taskHandle );
    TEST_ASSERT_EQUAL( pdPASS, ret );
    ASSERT_SETUP_TCB_CALLED();
    created_tasks++;
    return taskHandle;
}
/* ============================  HOOK FUNCTIONS  ============================ */
static void dummy_operation()
{
}

void port_allocate_secure_context( BaseType_t stackSize )
{
    HOOK_DIAG();
    port_allocate_secure_context_called = true;
}

void vApplicationIdleHook( void )
{
    HOOK_DIAG();
    vApplicationIdleHook_called = true;
}

void vApplicationMallocFailedHook( void )
{
    vApplicationMallocFailedHook_called = true;
    HOOK_DIAG();
}


void vApplicationGetIdleTaskMemory( StaticTask_t ** ppxIdleTaskTCBBuffer,
                                    StackType_t ** ppxIdleTaskStackBuffer,
                                    uint32_t * pulIdleTaskStackSize )
{
    HOOK_DIAG();

    if( getIddleTaskMemoryValid == true )
    {
        /* Pass out a pointer to the StaticTask_t structure in which the Idle task's
         * state will be stored. */
        *ppxIdleTaskTCBBuffer = &xIdleTaskTCB;

        /* Pass out the array that will be used as the Idle task's stack. */
        *ppxIdleTaskStackBuffer = uxIdleTaskStack;

        /* Pass out the size of the array pointed to by *ppxIdleTaskStackBuffer.
         * Note that, as the array is necessarily of type StackType_t,
         * configMINIMAL_STACK_SIZE is specified in words, not bytes. */
        *pulIdleTaskStackSize = configMINIMAL_STACK_SIZE;
    }
    else
    {
        *ppxIdleTaskTCBBuffer = NULL;
        *ppxIdleTaskStackBuffer = NULL;
        *pulIdleTaskStackSize = 0;
    }

    getIddleTaskMemoryCalled = true;
}

void vConfigureTimerForRunTimeStats( void )
{
    HOOK_DIAG();
}
long unsigned int ulGetRunTimeCounterValue( void )
{
    HOOK_DIAG();
    return 3;
}

void vApplicationTickHook()
{
    HOOK_DIAG();
    vApplicationTickHook_Called = true;
}

void vPortCurrentTaskDying( void * pvTaskToDelete,
                            volatile BaseType_t * pxPendYield )
{
    HOOK_DIAG();
    vTaskDeletePreCalled = true;
}

void vPortEnterCritical( void )
{
    HOOK_DIAG();
    critical_section_counter++;
}

void vPortExitCritical( void )
{
    HOOK_DIAG();
    critical_section_counter--;
}

void port_yield_cb()
{
    HOOK_DIAG();
    port_yield_called = true;
    py_operation();
}

void portSetupTCB_CB( void * tcb )
{
    HOOK_DIAG();
    port_setup_tcb_called = true;
}

void portClear_Interrupt_Mask( UBaseType_t bt )
{
    HOOK_DIAG();
    portClear_Interrupt_called = true;
}

UBaseType_t portSet_Interrupt_Mask( void )
{
    HOOK_DIAG();
    portSet_Interrupt_called = true;
    return 1;
}

void portAssert_if_int_prio_invalid( void )
{
    port_invalid_interrupt_called = true;
}

void vApplicationStackOverflowHook( TaskHandle_t xTask,
                                    char * stack )
{
    vApplicationStackOverflowHook_called = true;
}

/* ============================  Unity Fixtures  ============================ */
/*! called before each testcase */
void setUp( void )
{
    pxCurrentTCB = NULL;
    memset( &tcb, 0x00, sizeof( TCB_t ) );
    ptcb = NULL;
    memset( &pxReadyTasksLists, 0x00, configMAX_PRIORITIES * sizeof( List_t ) );
    memset( &xDelayedTaskList1, 0x00, sizeof( List_t ) );
    memset( &xDelayedTaskList2, 0x00, sizeof( List_t ) );

    /*
     * pxDelayedTaskList = NULL;
     * pxOverflowDelayedTaskList = NULL;
     */
    memset( &xPendingReadyList, 0x00, sizeof( List_t ) );

    memset( &xTasksWaitingTermination, 0x00, sizeof( List_t ) );
    uxDeletedTasksWaitingCleanUp = 0;
    memset( &xSuspendedTaskList, 0x00, sizeof( List_t ) );

    uxCurrentNumberOfTasks = ( UBaseType_t ) 0U;
    xTickCount = ( TickType_t ) 500; /* configINITIAL_TICK_COUNT */
    uxTopReadyPriority = tskIDLE_PRIORITY;
    xSchedulerRunning = pdFALSE;
    xPendedTicks = ( TickType_t ) 0U;
    xYieldPending = pdFALSE;
    xNumOfOverflows = ( BaseType_t ) 0;
    uxTaskNumber = ( UBaseType_t ) 0U;
    xNextTaskUnblockTime = ( TickType_t ) 0U;
    xIdleTaskHandle = NULL;
    uxSchedulerSuspended = ( UBaseType_t ) 0;
    /*  ulTaskSwitchedInTime = 0UL; */
    /*ulTotalRunTime = 0UL; */

    vApplicationTickHook_Called = false;
    vTaskDeletePreCalled = false;
    getIddleTaskMemoryCalled = false;
    is_first_task = true;
    created_tasks = 0;
    port_yield_called = false;
    port_setup_tcb_called = false;
    portClear_Interrupt_called = false;
    portSet_Interrupt_called = false;
    port_invalid_interrupt_called = false;
    vApplicationStackOverflowHook_called = false;
    py_operation = dummy_operation;
}

/*! called after each testcase */
void tearDown( void )
{
    TEST_ASSERT_EQUAL( 0, critical_section_counter );
}

/*! called at the beginning of the whole suite */
void suiteSetUp()
{
}

/*! called at the end of the whole suite */
int suiteTearDown( int numFailures )
{
    return numFailures;
}

/* ===========================  Static Functions  =========================== */



/* ==============================  Test Cases  ============================== */

/*!
 * @brief
 */
void test_xTaskCreateStatic_success( void )
{
    StackType_t puxStackBuffer[ 300 ];
    StaticTask_t pxTaskBuffer[ sizeof( TCB_t ) ];
    TaskFunction_t pxTaskCode = NULL;
    const char * const pcName = { __FUNCTION__ };
    const uint32_t ulStackDepth = 300;
    void * const pvParameters = NULL;
    UBaseType_t uxPriority = 3;
    TaskHandle_t ret;

    memset( puxStackBuffer, 0xa5U, ulStackDepth * sizeof( StackType_t ) );

    vListInitialiseItem_ExpectAnyArgs();
    vListInitialiseItem_ExpectAnyArgs();

    /* set owner */
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();
    /* set owner */
    pxPortInitialiseStack_ExpectAnyArgsAndReturn( puxStackBuffer );

    for( int i = ( UBaseType_t ) 0U; i < ( UBaseType_t ) configMAX_PRIORITIES; i++ )
    {
        vListInitialise_ExpectAnyArgs();
    }

    /* Delayed Task List 1 */
    vListInitialise_ExpectAnyArgs();
    /* Delayed Task List 2 */
    vListInitialise_ExpectAnyArgs();
    /* Pending Ready List */
    vListInitialise_ExpectAnyArgs();
    /* INCLUDE_vTaskDelete */
    vListInitialise_ExpectAnyArgs();
    /* INCLUDE_vTaskSuspend */
    vListInitialise_ExpectAnyArgs();

    vListInsertEnd_ExpectAnyArgs();

    ret = xTaskCreateStatic( pxTaskCode,
                             pcName,
                             ulStackDepth,
                             pvParameters,
                             uxPriority,
                             puxStackBuffer,
                             pxTaskBuffer );
    ptcb = ( TCB_t * ) pxTaskBuffer;
    TEST_ASSERT_EQUAL_PTR( puxStackBuffer, ptcb->pxStack );
    TEST_ASSERT_NOT_EQUAL( NULL, ret );
    TEST_ASSERT_EQUAL( 2, ptcb->ucStaticallyAllocated );
    TEST_ASSERT_EQUAL( 0,
                       memcmp( ptcb->pxStack,
                               puxStackBuffer,
                               ulStackDepth * sizeof( StackType_t ) ) );

    TEST_ASSERT_EQUAL( ptcb->pxEndOfStack,
                       ptcb->pxStack + ( 300 - 1 ) );
    TEST_ASSERT_EQUAL( 0, memcmp( ptcb->pcTaskName, pcName, configMAX_TASK_NAME_LEN - 1 ) );

    TEST_ASSERT_EQUAL( ptcb->uxPriority, uxPriority );

    TEST_ASSERT_EQUAL( 1, uxCurrentNumberOfTasks );
    ASSERT_SETUP_TCB_CALLED();
}

void test_xTaskCreate_success( void )
{
    TaskFunction_t pxTaskCode = NULL;
    const char * const pcName = NULL;
    const uint32_t usStackDepth = 300;
    void * const pvParameters = NULL;
    UBaseType_t uxPriority = configMAX_PRIORITIES;
    TaskHandle_t taskHandle;
    BaseType_t ret;
    StackType_t stack[ ( ( size_t ) usStackDepth ) * sizeof( StackType_t ) ];

    pvPortMalloc_ExpectAndReturn( sizeof( TCB_t ), &tcb[ 0 ] );
    pvPortMalloc_ExpectAndReturn( usStackDepth * sizeof( StackType_t ), stack );

    vListInitialiseItem_Expect( &( tcb[ 0 ].xStateListItem ) );
    vListInitialiseItem_Expect( &( tcb[ 0 ].xEventListItem ) );
    /* set owner */
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();
    /* set owner */
    /* vListInitialiseItem_ExpectAnyArgs(); */
    /*vListInitialiseItem_ExpectAnyArgs(); */

    pxPortInitialiseStack_ExpectAnyArgsAndReturn( stack );

    for( int i = ( UBaseType_t ) 0U; i < ( UBaseType_t ) configMAX_PRIORITIES; i++ )
    {
        vListInitialise_ExpectAnyArgs();
    }

    /* Delayed Task List 1 */
    vListInitialise_ExpectAnyArgs();
    /* Delayed Task List 2 */
    vListInitialise_ExpectAnyArgs();
    /* Pending Ready List */
    vListInitialise_ExpectAnyArgs();
    /* INCLUDE_vTaskDelete */
    vListInitialise_ExpectAnyArgs();
    /* INCLUDE_vTaskSuspend */
    vListInitialise_ExpectAnyArgs();

    vListInsertEnd_ExpectAnyArgs();

    ret = xTaskCreate( pxTaskCode,
                       pcName,
                       usStackDepth,
                       pvParameters,
                       uxPriority,
                       &taskHandle );
    ptcb = ( TCB_t * ) taskHandle;
    TEST_ASSERT_EQUAL( pdPASS, ret );
    TEST_ASSERT_EQUAL( 0, tcb[ 0 ].ucStaticallyAllocated );
    TEST_ASSERT_EQUAL_PTR( &tcb[ 0 ], ptcb );
    TEST_ASSERT_EQUAL( stack, tcb[ 0 ].pxStack );
    TEST_ASSERT_EQUAL( 1, uxCurrentNumberOfTasks );
    TEST_ASSERT_EQUAL( configMAX_PRIORITIES - 1, ptcb->uxPriority );
    TEST_ASSERT_EQUAL( NULL, ptcb->pcTaskName[ 0 ] );
    ASSERT_SETUP_TCB_CALLED();
}

void test_xTaskCreate_fail_stack_malloc( void )
{
    TaskFunction_t pxTaskCode = NULL;
    const char * const pcName = { __FUNCTION__ };
    const uint32_t usStackDepth = 300;
    void * const pvParameters = NULL;
    UBaseType_t uxPriority = 3;
    TaskHandle_t taskHandle;
    BaseType_t ret;

    pvPortMalloc_ExpectAndReturn( sizeof( TCB_t ), NULL );

    ret = xTaskCreate( pxTaskCode,
                       pcName,
                       usStackDepth,
                       pvParameters,
                       uxPriority,
                       &taskHandle );
    TEST_ASSERT_EQUAL( errCOULD_NOT_ALLOCATE_REQUIRED_MEMORY, ret );
    TEST_ASSERT_EQUAL( 0, uxCurrentNumberOfTasks );
    ASSERT_SETUP_TCB_NOT_CALLED();
}

void test_xTaskCreate_fail_tcb_malloc( void )
{
    TaskFunction_t pxTaskCode = NULL;
    const char * const pcName = { __FUNCTION__ };
    const uint32_t usStackDepth = 300;
    void * const pvParameters = NULL;
    UBaseType_t uxPriority = 3;
    TaskHandle_t taskHandle;
    BaseType_t ret;

    pvPortMalloc_ExpectAndReturn( sizeof( TCB_t ), &tcb[ 0 ] );
    pvPortMalloc_ExpectAndReturn( usStackDepth * sizeof( StackType_t ), NULL );
    vPortFree_Expect( &tcb[ 0 ] );

    ret = xTaskCreate( pxTaskCode,
                       pcName,
                       usStackDepth,
                       pvParameters,
                       uxPriority,
                       &taskHandle );
    TEST_ASSERT_EQUAL( errCOULD_NOT_ALLOCATE_REQUIRED_MEMORY, ret );
    TEST_ASSERT_EQUAL( 0, uxCurrentNumberOfTasks );
    ASSERT_SETUP_TCB_NOT_CALLED();
}

void test_vTaskPrioritySet_success_gt_curr_prio( void )
{
    TaskHandle_t taskHandle2;
    TCB_t * ptcb;

    create_task_priority = 3;
    create_task();
    create_task_priority = 4;
    taskHandle2 = create_task();
    ptcb = ( TCB_t * ) taskHandle2;
    TEST_ASSERT_EQUAL_PTR( pxCurrentTCB, taskHandle2 );
    listGET_LIST_ITEM_VALUE_ExpectAnyArgsAndReturn( 0 );
    listSET_LIST_ITEM_VALUE_Expect( &( ptcb->xEventListItem ),
                                    configMAX_PRIORITIES - 5 );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &pxReadyTasksLists[ 5 ],
                                             &( ptcb->xStateListItem ),
                                             pdTRUE );
    uxListRemove_ExpectAndReturn( &( ptcb->xStateListItem ), 0 );
    /* port Reset ready priority */
    /* add task to ready list */
    vListInsertEnd_Expect( &( pxReadyTasksLists[ 5 ] ),
                           &( ptcb->xStateListItem ) );

    TEST_ASSERT_EQUAL( 4, ptcb->uxPriority );
    vTaskPrioritySet( taskHandle2, create_task_priority + 1 );
    TEST_ASSERT_EQUAL( 4 + 1, ptcb->uxPriority );
    ASSERT_PORT_YIELD_NOT_CALLED();
}
