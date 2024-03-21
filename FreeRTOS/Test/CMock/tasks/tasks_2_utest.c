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

/*! @file tasks_utest_2.c */

/* Tasks includes */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"
#include "task.h"

#include "mock_list.h"
#include "mock_list_macros.h"
#include "mock_timers.h"
#include "mock_portable.h"
#include "mock_fake_assert.h"

/* Test includes. */
#include "unity.h"
#include "CException.h"
#include "global_vars.h"

/* C runtime includes. */
#include <stdbool.h>
#include <string.h>
#include <stdlib.h>


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
#ifdef configNUMBER_OF_CORES
    extern volatile BaseType_t xYieldPendings[];
    #define xYieldPending    xYieldPendings[ 0 ]
#else
    extern volatile BaseType_t xYieldPending;
#endif

extern volatile BaseType_t xNumOfOverflows;
extern UBaseType_t uxTaskNumber;
extern volatile TickType_t xNextTaskUnblockTime;
#ifdef configNUMBER_OF_CORES
    extern TaskHandle_t xIdleTaskHandles[];
    #define xIdleTaskHandle    xIdleTaskHandles[ 0 ]
#else
    extern TaskHandle_t xIdleTaskHandle;
#endif
extern volatile UBaseType_t uxSchedulerSuspended;

/**
 * @brief CException code for when a configASSERT should be intercepted.
 */
#define configASSERT_E    0xAA101


/* ===========================  GLOBAL VARIABLES  =========================== */
static StaticTask_t xIdleTaskTCB;
static StackType_t uxIdleTaskStack[ configMINIMAL_STACK_SIZE ];

static TCB_t * ptcb;
static StackType_t stack[ ( ( size_t ) 300 ) * sizeof( StackType_t ) ];
static TCB_t tcb[ 10 ]; /* simulate up to 10 tasks: add more if needed */
static bool getIdleTaskMemoryValid = false;
static uint32_t critical_section_counter = 0;
static bool is_first_task = true;
static uint32_t created_tasks = 0;
static uint32_t create_task_priority = 3;
static port_yield_operation py_operation;
static bool vTaskDeletePre_called = false;
static bool getIdleTaskMemory_called = false;
static bool vApplicationTickHook_called = false;
static bool port_yield_called = false;
static bool port_enable_interrupts_called = false;
static bool port_disable_interrupts_called = false;
static bool port_yield_within_api_called = false;
static bool port_setup_tcb_called = false;
static bool portClear_Interrupt_called = false;
static bool portSet_Interrupt_called = false;
static bool portClear_Interrupt_from_isr_called = false;
static bool portSet_Interrupt_from_isr_called = false;
static bool port_invalid_interrupt_called = false;
static bool vApplicationStackOverflowHook_called = false;
static bool vApplicationIdleHook_called = false;
static bool port_allocate_secure_context_called = false;
static bool port_assert_if_in_isr_called = false;
static bool vApplicationMallocFailedHook_called = false;


/**
 * @brief Global counter for the number of assertions in code.
 */
static int assertionFailed = 0;

/**
 * @brief Flag which denotes if test need to abort on assertion.
 */
static BaseType_t shouldAbortOnAssertion = pdFALSE;

/* ===========================  Static Functions  =========================== */
static void start_scheduler()
{
    vListInitialiseItem_ExpectAnyArgs();
    vListInitialiseItem_ExpectAnyArgs();
    /* set owner */
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();
    /* set owner */

    pxPortInitialiseStack_ExpectAnyArgsAndReturn( uxIdleTaskStack );

    if( is_first_task )
    {
        is_first_task = false;

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
    }

    listINSERT_END_ExpectAnyArgs();

    xTimerCreateTimerTask_ExpectAndReturn( pdPASS );
    xPortStartScheduler_ExpectAndReturn( pdTRUE );
    getIdleTaskMemoryValid = true;
    vTaskStartScheduler();
    ASSERT_GET_IDLE_TASK_MEMORY_CALLED();
    TEST_ASSERT_TRUE( xSchedulerRunning );
    TEST_ASSERT_EQUAL( configINITIAL_TICK_COUNT, xTickCount );
    TEST_ASSERT_EQUAL( portMAX_DELAY, xNextTaskUnblockTime );
}
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
        /* prvInitialiseTaskLists */
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

    /* prvAddTaskToReadyList */
    listINSERT_END_ExpectAnyArgs();
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
    HOOK_DIAG();
}

void vFakePortAssertIfISR( void )
{
    port_assert_if_in_isr_called = true;
    HOOK_DIAG();
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

    if( getIdleTaskMemoryValid == true )
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

    getIdleTaskMemory_called = true;
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
    vApplicationTickHook_called = true;
}

void vPortCurrentTaskDying( void * pvTaskToDelete,
                            volatile BaseType_t * pxPendYield )
{
    HOOK_DIAG();
    vTaskDeletePre_called = true;
}

void vFakePortEnterCriticalSection( void )
{
    HOOK_DIAG();
    critical_section_counter++;
}

void vFakePortExitCriticalSection( void )
{
    HOOK_DIAG();
    critical_section_counter--;
}

void vFakePortYieldWithinAPI()
{
    HOOK_DIAG();
    port_yield_within_api_called = true;
    py_operation();
}

void vFakePortYieldFromISR()
{
    HOOK_DIAG();
}

uint32_t vFakePortDisableInterrupts()
{
    port_disable_interrupts_called = true;
    HOOK_DIAG();
    return 0;
}

void vFakePortEnableInterrupts()
{
    port_enable_interrupts_called = true;
    HOOK_DIAG();
}

void vFakePortYield()
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

void vFakePortClearInterruptMask( UBaseType_t bt )
{
    HOOK_DIAG();
    portClear_Interrupt_called = true;
}

UBaseType_t ulFakePortSetInterruptMask( void )
{
    HOOK_DIAG();
    portSet_Interrupt_called = true;
    return 1;
}

void vFakePortClearInterruptMaskFromISR( UBaseType_t bt )
{
    HOOK_DIAG();
    portClear_Interrupt_from_isr_called = true;
}

UBaseType_t ulFakePortSetInterruptMaskFromISR( void )
{
    HOOK_DIAG();
    portSet_Interrupt_from_isr_called = true;
    return 1;
}

void vFakePortAssertIfInterruptPriorityInvalid( void )
{
    HOOK_DIAG();
    port_invalid_interrupt_called = true;
}

void vApplicationStackOverflowHook( TaskHandle_t xTask,
                                    char * stack )
{
    HOOK_DIAG();
    vApplicationStackOverflowHook_called = true;
}

unsigned int vFakePortGetCoreID( void )
{
    HOOK_DIAG();
    return 0;
}

void vFakePortReleaseTaskLock( void )
{
    HOOK_DIAG();
}

void vFakePortGetTaskLock( void )
{
    HOOK_DIAG();
}

void vFakePortGetISRLock( void )
{
    HOOK_DIAG();
}

void vFakePortReleaseISRLock( void )
{
    HOOK_DIAG();
}

static void vFakeAssertStub( bool x,
                             char * file,
                             int line,
                             int cmock_num_calls )
{
    if( !x )
    {
        assertionFailed++;

        if( shouldAbortOnAssertion == pdTRUE )
        {
            Throw( configASSERT_E );
        }
    }
}

/* ============================  Unity Fixtures  ============================ */
/*! called before each testcase */
void setUp( void )
{
    RESET_ALL_HOOKS();

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
    is_first_task = true;
    created_tasks = 0;
    py_operation = dummy_operation;

    vFakeAssert_StubWithCallback( vFakeAssertStub );
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

/* ==============================  Test Cases  ============================== */

/*!
 * @brief create a static new task with a success path
 */
void test_xTaskCreateStatic_success( void )
{
    StackType_t puxStackBuffer[ 300 ];
    StaticTask_t * pxTaskBuffer = malloc( sizeof( TCB_t ) );
    TaskFunction_t pxTaskCode = NULL;
    const char * const pcName = { __FUNCTION__ };
    const uint32_t ulStackDepth = 300;
    void * const pvParameters = NULL;
    UBaseType_t uxPriority = 3;
    TaskHandle_t ret;

    /* Setup */
    memset( puxStackBuffer, 0xa5U, ulStackDepth * sizeof( StackType_t ) );

    /* Expectations */
    vListInitialiseItem_ExpectAnyArgs();
    vListInitialiseItem_ExpectAnyArgs();

    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();
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

    listINSERT_END_ExpectAnyArgs();

    /* API Call */
    ret = xTaskCreateStatic( pxTaskCode,
                             pcName,
                             ulStackDepth,
                             pvParameters,
                             uxPriority,
                             puxStackBuffer,
                             pxTaskBuffer );
    ptcb = ( TCB_t * ) pxTaskBuffer;
    /* Validations */
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
    free( pxTaskBuffer );
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

    /* Setup */
    /* Expectations */
    pvPortMalloc_ExpectAndReturn( sizeof( TCB_t ), &tcb[ 0 ] );
    pvPortMalloc_ExpectAndReturn( usStackDepth * sizeof( StackType_t ), stack );

    vListInitialiseItem_Expect( &( tcb[ 0 ].xStateListItem ) );
    vListInitialiseItem_Expect( &( tcb[ 0 ].xEventListItem ) );
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();
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

    listINSERT_END_ExpectAnyArgs();

    /* API Call */
    ret = xTaskCreate( pxTaskCode,
                       pcName,
                       usStackDepth,
                       pvParameters,
                       uxPriority,
                       &taskHandle );
    /* Validations */
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
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &pxReadyTasksLists[ 4 ],
                                             &( ptcb->xStateListItem ),
                                             pdTRUE );
    uxListRemove_ExpectAndReturn( &( ptcb->xStateListItem ), 0 );
    /* port Reset ready priority */
    /* add task to ready list macro */

    listINSERT_END_Expect( &( pxReadyTasksLists[ 5 ] ),
                           &( ptcb->xStateListItem ) );

    TEST_ASSERT_EQUAL( 4, ptcb->uxPriority );
    vTaskPrioritySet( taskHandle2, create_task_priority + 1 );
    TEST_ASSERT_EQUAL( 4 + 1, ptcb->uxPriority );
    ASSERT_PORT_YIELD_NOT_CALLED();
}
/* -----------------  testing portCRITICAL_NESTING_IN_TCB ------------------- */

void vTaskEnterCritical( void );
void vTaskExitCritical( void );

void test_vTaskExitCritical_success( void )
{
    TaskHandle_t task_handle;

    /* Setup */
    task_handle = create_task();
    start_scheduler();
    /* Expectations */
    /* API Call */
    vTaskExitCritical();
    /* Validations */
    TEST_ASSERT_EQUAL( 0, task_handle->uxCriticalNesting );
    ASSERT_PORT_ENABLE_INTERRUPT_NOT_CALLED();
}

void test_vTaskExitCritical_success_enable_interrupts( void )
{
    TaskHandle_t task_handle;

    /* Setup */
    task_handle = create_task();
    start_scheduler();
    vTaskEnterCritical();
    ASSERT_IF_IN_ISR_CALLED();
    /* Expectations */
    /* API Call */
    vTaskExitCritical();
    /* Validations */
    TEST_ASSERT_EQUAL( 0, task_handle->uxCriticalNesting );
    ASSERT_PORT_ENABLE_INTERRUPT_CALLED();
}

void test_vTaskExitCritical_success_enable_too_many_nests( void )
{
    TaskHandle_t task_handle;

    /* Setup */
    task_handle = create_task();
    start_scheduler();
    vTaskEnterCritical();
    ASSERT_IF_IN_ISR_CALLED();
    vTaskEnterCritical();
    /* Expectations */
    /* API Call */
    vTaskExitCritical();
    /* Validations */
    TEST_ASSERT_EQUAL( 1, task_handle->uxCriticalNesting );
    ASSERT_PORT_ENABLE_INTERRUPT_NOT_CALLED();
}

void test_vTaskExitCritical_scheduler_off( void )
{
    TaskHandle_t task_handle;

    /* Setup */
    task_handle = create_task();
    /* Expectations */
    /* API Call */
    vTaskExitCritical();
    /* Validations */
    TEST_ASSERT_EQUAL( 0, task_handle->uxCriticalNesting );
    ASSERT_PORT_ENABLE_INTERRUPT_NOT_CALLED();
}

void test_vTaskEnterCritical_success( void )
{
    TaskHandle_t task_handle;

    /* Setup */
    task_handle = create_task();
    start_scheduler();
    /* Expectations */
    /* API Call */
    vTaskEnterCritical();
    /* Validations */
    TEST_ASSERT_EQUAL( 1, task_handle->uxCriticalNesting );
    ASSERT_IF_IN_ISR_CALLED();
}

void test_vTaskEnterCritical_success_twice( void )
{
    TaskHandle_t task_handle;

    /* Setup */
    task_handle = create_task();
    start_scheduler();
    /* Expectations */
    /* API Call */
    vTaskEnterCritical();
    ASSERT_IF_IN_ISR_CALLED();
    vTaskEnterCritical();
    /* Validations */
    TEST_ASSERT_EQUAL( 2, task_handle->uxCriticalNesting );
    ASSERT_IF_IN_ISR_NOT_CALLED();
}

void test_vTaskEnterCritical_no_op_no_sched( void )
{
    TaskHandle_t task_handle;

    /* Setup */
    task_handle = create_task();
    /* Expectations */
    /* API Call */
    vTaskEnterCritical();
    /* Validations */
    TEST_ASSERT_EQUAL( 0, task_handle->uxCriticalNesting );
    ASSERT_IF_IN_ISR_NOT_CALLED();
}
