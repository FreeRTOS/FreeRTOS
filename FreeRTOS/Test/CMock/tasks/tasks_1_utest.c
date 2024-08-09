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

/*! @file tasks_utest_1.c */

/* Tasks includes */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"
#include "fake_port.h"
#include "task.h"

/* Mock includes. */
#include "mock_list.h"
#include "mock_list_macros.h"
#include "mock_timers.h"
#include "mock_portable.h"
#include "mock_fake_assert.h"
#include "mock_fake_infiniteloop.h"

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

/* =============================  DEFINES  ================================== */
#define INITIALIZE_LIST_1E( list, list_item, owner )            \
    do {                                                        \
        ( list ).xListEnd.pxNext = &( list_item );              \
        ( list ).xListEnd.pxPrevious = &( list_item );          \
        ( list ).pxIndex = ( ListItem_t * ) &( list ).xListEnd; \
        ( list ).uxNumberOfItems = 1;                           \
        ( list_item ).pxNext = ( list ).pxIndex;                \
        ( list_item ).pxPrevious = ( list ).pxIndex;            \
        ( list_item ).pvOwner = ( owner );                      \
        ( list_item ).pxContainer = &( list );                  \
    } while( 0 )

#define INITIALIZE_LIST_2E( list, list_item, list_item2, owner, owner2 ) \
    do {                                                                 \
        ( list ).xListEnd.pxNext = &( list_item );                       \
        ( list ).xListEnd.pxPrevious = &( list_item2 );                  \
        ( list ).pxIndex = ( ListItem_t * ) &( list ).xListEnd;          \
        ( list ).uxNumberOfItems = 2;                                    \
        ( list_item ).pxNext = &( list_item2 );                          \
        ( list_item ).pxPrevious = ( list ).pxIndex;                     \
        ( list_item ).pvOwner = ( owner );                               \
        ( list_item ).pxContainer = &( list );                           \
        ( list_item2 ).pxNext = ( list ).pxIndex;                        \
        ( list_item2 ).pxPrevious = &( list_item );                      \
        ( list_item2 ).pvOwner = ( owner2 );                             \
        ( list_item2 ).pxContainer = &( list );                          \
    } while( 0 )

#define taskNOT_WAITING_NOTIFICATION    ( ( uint8_t ) 0 )
#define taskWAITING_NOTIFICATION        ( ( uint8_t ) 1 )
#define taskNOTIFICATION_RECEIVED       ( ( uint8_t ) 2 )
#define TCB_ARRAY                       10 /* simulate up to 10 tasks: add more if needed */

/**
 * @brief CException code for when a configASSERT should be intercepted.
 */
#define configASSERT_E                  0xAA101

/* ===========================  GLOBAL VARIABLES  =========================== */
static StaticTask_t xIdleTaskTCB;
static StackType_t uxIdleTaskStack[ configMINIMAL_STACK_SIZE ];

static TCB_t * ptcb;
static StackType_t stack[ ( ( size_t ) 300 ) * sizeof( StackType_t ) ];
static TCB_t tcb[ TCB_ARRAY ];
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

/* ============================  EXTERN FUNCTIONS  ========================== */
extern void prvCheckTasksWaitingTermination( void );

/* ============================  HOOK FUNCTIONS  ============================ */
static void dummy_operation()
{
}

void vFakePortAssertIfISR( void )
{
    port_assert_if_in_isr_called = true;
    HOOK_DIAG();
}

void vFakePortAllocateSecureContext( BaseType_t stackSize )
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
    vFakeAssert_StubWithCallback( vFakeAssertStub );
    RESET_ALL_HOOKS();
    pxCurrentTCB = NULL;
    memset( &tcb, 0x00, sizeof( TCB_t ) * TCB_ARRAY );
    ptcb = NULL;
    memset( &pxReadyTasksLists, 0x00, configMAX_PRIORITIES * sizeof( List_t ) );
    memset( &xDelayedTaskList1, 0x00, sizeof( List_t ) );
    memset( &xDelayedTaskList2, 0x00, sizeof( List_t ) );

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
    is_first_task = true;
    created_tasks = 0;
    critical_section_counter = 0;

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

static BaseType_t pxHookFunction( void * arg )
{
    BaseType_t * i = arg;

    return *i;
}

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

static void block_task( TaskHandle_t task_to_block )
{
    TCB_t * tcb_to_block = task_to_block;

    TEST_ASSERT_EQUAL( pxCurrentTCB, task_to_block );
    uxListRemove_ExpectAndReturn( &tcb_to_block->xStateListItem, 1 );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &tcb_to_block->xEventListItem,
                                             &xSuspendedTaskList );
    uxListRemove_ExpectAndReturn( &tcb_to_block->xEventListItem, pdTRUE );
    vListInsertEnd_Expect( &xSuspendedTaskList, &tcb_to_block->xStateListItem );
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &xSuspendedTaskList,
                                             uxCurrentNumberOfTasks );
    vTaskSuspend( task_to_block );
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

    pvPortMalloc_ExpectAndReturn( usStackDepth * sizeof( StackType_t ), stack );
    pvPortMalloc_ExpectAndReturn( sizeof( TCB_t ), &tcb[ created_tasks ] );

    vListInitialiseItem_Expect( &( tcb[ created_tasks ].xStateListItem ) );
    vListInitialiseItem_Expect( &( tcb[ created_tasks ].xEventListItem ) );
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();

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

/* ==============================  Test Cases  ============================== */

/*!
 * @brief
 */
void test_xTaskCreateStatic_null_puxStackBuffer( void )
{
    StaticTask_t pxTaskBuffer[ 300 ];
    TaskFunction_t pxTaskCode = NULL;
    const char * const pcName = { "unit test" };
    const uint32_t ulStackDepth = 0;
    void * const pvParameters = NULL;
    UBaseType_t uxPriority = 3;
    TaskHandle_t ret;

    ret = xTaskCreateStatic( pxTaskCode,
                             pcName,
                             ulStackDepth,
                             pvParameters,
                             uxPriority,
                             NULL,
                             pxTaskBuffer );
    TEST_ASSERT_EQUAL( NULL, ret );
    ASSERT_SETUP_TCB_NOT_CALLED();
}


/*!
 * @brief
 */
void test_xTaskCreateStatic_null_pxTaskBuffer( void )
{
    StackType_t puxStackBuffer[ 300 ];

    TaskFunction_t pxTaskCode = NULL;
    const char * const pcName = { "unit test" };
    const uint32_t ulStackDepth = 0;
    void * const pvParameters = NULL;
    UBaseType_t uxPriority = 3;
    TaskHandle_t ret;

    ret = xTaskCreateStatic( pxTaskCode,
                             pcName,
                             ulStackDepth,
                             pvParameters,
                             uxPriority,
                             puxStackBuffer,
                             NULL );
    TEST_ASSERT_EQUAL( NULL, ret );
    TEST_ASSERT_EQUAL( 0, uxCurrentNumberOfTasks );
    ASSERT_SETUP_TCB_NOT_CALLED();
}

/*!
 * @brief
 */
#include <stdio.h>
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

    listINSERT_END_ExpectAnyArgs();

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

    StackType_t * pxTopOfStack = &( ptcb->pxStack[ ulStackDepth - ( uint32_t ) 1 ] );
    pxTopOfStack = ( StackType_t * ) ( ( ( portPOINTER_SIZE_TYPE ) pxTopOfStack )
                                       & ( ~( ( portPOINTER_SIZE_TYPE ) portBYTE_ALIGNMENT_MASK ) ) );

    TEST_ASSERT_EQUAL( ptcb->pxEndOfStack,
                       pxTopOfStack );
    TEST_ASSERT_EQUAL( 0, memcmp( ptcb->pcTaskName, pcName, configMAX_TASK_NAME_LEN - 1 ) );

    TEST_ASSERT_EQUAL( ptcb->uxPriority, uxPriority );

    TEST_ASSERT_EQUAL( ptcb->uxBasePriority, uxPriority );
    TEST_ASSERT_EQUAL( 0, ptcb->uxMutexesHeld );

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

    pvPortMalloc_ExpectAndReturn( usStackDepth * sizeof( StackType_t ), stack );
    pvPortMalloc_ExpectAndReturn( sizeof( TCB_t ), &tcb[ 0 ] );

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

void test_xTaskCreate_success_sched_running( void )
{
    TaskFunction_t pxTaskCode = NULL;
    const char * const pcName = NULL;
    const uint32_t usStackDepth = 300;
    void * const pvParameters = NULL;
    UBaseType_t uxPriority = configMAX_PRIORITIES;
    TaskHandle_t taskHandle;
    BaseType_t ret;
    StackType_t stack[ ( ( size_t ) usStackDepth ) * sizeof( StackType_t ) ];

    start_scheduler();

    pvPortMalloc_ExpectAndReturn( usStackDepth * sizeof( StackType_t ), stack );
    pvPortMalloc_ExpectAndReturn( sizeof( TCB_t ), &tcb[ 0 ] );

    vListInitialiseItem_Expect( &( tcb[ 0 ].xStateListItem ) );
    vListInitialiseItem_Expect( &( tcb[ 0 ].xEventListItem ) );
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();
    pxPortInitialiseStack_ExpectAnyArgsAndReturn( stack );
    listINSERT_END_ExpectAnyArgs();

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
    TEST_ASSERT_EQUAL( 2, uxCurrentNumberOfTasks );
    TEST_ASSERT_EQUAL( configMAX_PRIORITIES - 1, ptcb->uxPriority );
    TEST_ASSERT_EQUAL( NULL, ptcb->pcTaskName[ 0 ] );
    ASSERT_SETUP_TCB_CALLED();
    ASSERT_PORT_YIELD_WITHIN_API_CALLED();
}

void test_xTaskCreate_success_null_task_handle( void )
{
    TaskFunction_t pxTaskCode = NULL;
    const char * const pcName = NULL;
    const uint32_t usStackDepth = 300;
    void * const pvParameters = NULL;
    UBaseType_t uxPriority = configMAX_PRIORITIES;
    BaseType_t ret;
    StackType_t stack[ ( ( size_t ) usStackDepth ) * sizeof( StackType_t ) ];

    pvPortMalloc_ExpectAndReturn( usStackDepth * sizeof( StackType_t ), stack );
    pvPortMalloc_ExpectAndReturn( sizeof( TCB_t ), &tcb[ 0 ] );

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

    ret = xTaskCreate( pxTaskCode,
                       pcName,
                       usStackDepth,
                       pvParameters,
                       uxPriority,
                       NULL );
    TEST_ASSERT_EQUAL( pdPASS, ret );
    TEST_ASSERT_EQUAL( 0, tcb[ 0 ].ucStaticallyAllocated );
    TEST_ASSERT_EQUAL( stack, tcb[ 0 ].pxStack );
    TEST_ASSERT_EQUAL( 1, uxCurrentNumberOfTasks );
    ASSERT_SETUP_TCB_CALLED();
    ASSERT_PORT_YIELD_WITHIN_API_NOT_CALLED();
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

    pvPortMalloc_ExpectAndReturn( usStackDepth * sizeof( StackType_t ), NULL );

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
    StackType_t stack[ ( ( size_t ) usStackDepth ) * sizeof( StackType_t ) ];

    pvPortMalloc_ExpectAndReturn( usStackDepth * sizeof( StackType_t ), stack );
    pvPortMalloc_ExpectAndReturn( sizeof( TCB_t ), NULL );
    vPortFree_Expect( stack );

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

/* -------------------------- INCLUDE_vTaskDelete --------------------------- */
void test_vTaskDelete_success_current_task( void )
{
    /* Setup */
    ptcb = ( TCB_t * ) create_task();
    TEST_ASSERT_EQUAL( 1, uxCurrentNumberOfTasks );

    xSchedulerRunning = pdTRUE;

    /* Expectations */
    uxListRemove_ExpectAndReturn( &ptcb->xStateListItem, pdPASS );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem, NULL );
    vListInsertEnd_ExpectAnyArgs();
    /* API call */
    vTaskDelete( ptcb );
    /* Validations */
    ASSERT_TASK_DELETE_CALLED();
    TEST_ASSERT_EQUAL( 1, uxCurrentNumberOfTasks );
    TEST_ASSERT_EQUAL( 1, uxDeletedTasksWaitingCleanUp );
}

void test_vTaskDelete_success_current_task_ready_empty( void )
{
    /* Setup */
    ptcb = ( TCB_t * ) create_task();
    TEST_ASSERT_EQUAL( 1, uxCurrentNumberOfTasks );

    xSchedulerRunning = pdTRUE;

    /* Expectations */
    uxListRemove_ExpectAndReturn( &ptcb->xStateListItem, pdFAIL );
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &pxReadyTasksLists[ ptcb->uxPriority ], 0 );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem, NULL );
    vListInsertEnd_ExpectAnyArgs();
    /* API call */
    vTaskDelete( ptcb );
    /* Validations */
    ASSERT_TASK_DELETE_CALLED();
    TEST_ASSERT_EQUAL( 1, uxCurrentNumberOfTasks );
    TEST_ASSERT_EQUAL( 1, uxDeletedTasksWaitingCleanUp );
}

void test_vTaskDelete_success_current_task_ready_empty_null_task( void )
{
    /* Setup */
    ptcb = ( TCB_t * ) create_task();
    TEST_ASSERT_EQUAL( 1, uxCurrentNumberOfTasks );

    xSchedulerRunning = pdTRUE;

    /* Expectations */
    uxListRemove_ExpectAndReturn( &ptcb->xStateListItem, pdFAIL );
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &pxReadyTasksLists[ ptcb->uxPriority ], 1 );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem, NULL );
    vListInsertEnd_ExpectAnyArgs();
    /* API call */
    vTaskDelete( NULL );
    /* Validations */
    ASSERT_TASK_DELETE_CALLED();
    TEST_ASSERT_EQUAL( 1, uxCurrentNumberOfTasks );
    TEST_ASSERT_EQUAL( 1, uxDeletedTasksWaitingCleanUp );
}

void test_vTaskDelete_success_current_task_yield( void )
{
    xSchedulerRunning = pdTRUE;
    ptcb = ( TCB_t * ) create_task();

    TEST_ASSERT_EQUAL( 1, uxCurrentNumberOfTasks );

    /* Expectations */
    uxListRemove_ExpectAndReturn( &ptcb->xStateListItem, pdPASS );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem, NULL );
    vListInsertEnd_ExpectAnyArgs();
    /* API call */
    vTaskDelete( ptcb );
    /* Validations */
    ASSERT_TASK_DELETE_CALLED();
    ASSERT_PORT_YIELD_WITHIN_API_CALLED();
    TEST_ASSERT_EQUAL( 1, uxCurrentNumberOfTasks );
    TEST_ASSERT_EQUAL( 1, uxDeletedTasksWaitingCleanUp );
}

void test_vTaskDelete_success_not_current_task( void )
{
    ptcb = ( TCB_t * ) create_task();
    TEST_ASSERT_EQUAL( 1, uxCurrentNumberOfTasks );

    /* Expectations */
    uxListRemove_ExpectAndReturn( &ptcb->xStateListItem, pdPASS );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem,
                                             &xPendingReadyList );
    uxListRemove_ExpectAndReturn( &ptcb->xEventListItem, pdTRUE );
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    vPortFree_ExpectAnyArgs();
    vPortFree_ExpectAnyArgs();
    pxCurrentTCB = NULL;
    /* API call */
    vTaskDelete( ptcb );
    /* Validations */
    TEST_ASSERT_EQUAL( 0, uxCurrentNumberOfTasks );
    TEST_ASSERT_EQUAL( 0, uxDeletedTasksWaitingCleanUp );
}

void test_vTaskDelete_success_not_current_task_no_yield( void )
{
    xSchedulerRunning = pdTRUE;
    ptcb = ( TCB_t * ) create_task();
    TEST_ASSERT_EQUAL( 1, uxCurrentNumberOfTasks );

    /* Expectations */
    uxListRemove_ExpectAndReturn( &ptcb->xStateListItem, pdPASS );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem,
                                             &xPendingReadyList );
    uxListRemove_ExpectAndReturn( &ptcb->xEventListItem, pdTRUE );
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    vPortFree_ExpectAnyArgs();
    vPortFree_ExpectAnyArgs();
    pxCurrentTCB = NULL;
    /* API call */
    vTaskDelete( ptcb );
    /* Validations */
    TEST_ASSERT_EQUAL( 0, uxCurrentNumberOfTasks );
    TEST_ASSERT_EQUAL( 0, uxDeletedTasksWaitingCleanUp );
    ASSERT_PORT_YIELD_WITHIN_API_NOT_CALLED();
}

/**
 * @brief prvCheckTasksWaitingTermination - no waiting task.
 *
 * No task is waiting to be deleted. This test show it's result in the coverage
 * report.
 *
 * <b>Coverage</b>
 * @code{c}
 * while( uxDeletedTasksWaitingCleanUp > ( UBaseType_t ) 0U )
 * {
 *     ...
 * }
 * @endcode
 * ( uxDeletedTasksWaitingCleanUp > ( UBaseType_t ) 0U ) is false.
 */
void test_prvCheckTasksWaitingTermination_no_waiting_task( void )
{
    /* Setup the variables and structure. */
    uxDeletedTasksWaitingCleanUp = 0;

    /* API Call. */
    prvCheckTasksWaitingTermination();

    /* Validation. */

    /* No task is waiting to be cleaned up. Nothing will be updated in this API. This
     * test case shows its result in the coverage report. */
}

/**
 * @brief prvCheckTasksWaitingTermination - delete waiting task.
 *
 * A task is waiting to be deleted. The number of tasks and number of tasks waiting to
 * be deleted are verified in this test case.
 *
 * <b>Coverage</b>
 * @code{c}
 * while( uxDeletedTasksWaitingCleanUp > ( UBaseType_t ) 0U )
 * {
 *     ...
 * }
 * @endcode
 * ( uxDeletedTasksWaitingCleanUp > ( UBaseType_t ) 0U ) is true.
 */
void test_prvCheckTasksWaitingTermination_delete_waiting_task( void )
{
    ptcb = ( TCB_t * ) create_task();

    /* Setup the variables and structure. */
    uxDeletedTasksWaitingCleanUp = 1;
    uxCurrentNumberOfTasks = 1;

    /* Expectations. */
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( ptcb );
    uxListRemove_ExpectAndReturn( &ptcb->xStateListItem, 0 );
    vPortFree_Expect( stack );
    vPortFree_Expect( ptcb );

    /* API Call. */
    prvCheckTasksWaitingTermination();

    /* Validation. */
    TEST_ASSERT_EQUAL( uxDeletedTasksWaitingCleanUp, 0 );
    TEST_ASSERT_EQUAL( uxCurrentNumberOfTasks, 0 );
}

void test_vTaskStartScheduler_success( void )
{
    vListInitialiseItem_ExpectAnyArgs();
    vListInitialiseItem_ExpectAnyArgs();
    /* set owner */
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();
    /* set owner */

    pxPortInitialiseStack_ExpectAnyArgsAndReturn( uxIdleTaskStack );

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

    xTimerCreateTimerTask_ExpectAndReturn( pdPASS );
    xPortStartScheduler_ExpectAndReturn( pdTRUE );
    getIdleTaskMemoryValid = true;
    vTaskStartScheduler();

    ASSERT_GET_IDLE_TASK_MEMORY_CALLED();
    /* should be 2 the idle task and timer task, but the timer task is a mock */
    TEST_ASSERT_EQUAL( 1, uxCurrentNumberOfTasks );
    TEST_ASSERT_EQUAL( pdTRUE, xSchedulerRunning );
}

void test_vTaskStartScheduler_idle_fail( void )
{
    getIdleTaskMemoryValid = false;
    vTaskStartScheduler();

    ASSERT_GET_IDLE_TASK_MEMORY_CALLED();
    /* should be 2 the idle task and timer task, but the timer task is a mock */
    TEST_ASSERT_EQUAL( 0, uxCurrentNumberOfTasks );
    TEST_ASSERT_EQUAL( pdFALSE, xSchedulerRunning );
}

void test_vTaskEndScheduler_success()
{
    /* Setup. */
    TCB_t * pIdleTaskTCB = ( TCB_t * ) create_task();
    TCB_t * pTimerTaskTCB = ( TCB_t * ) create_task();

    uxCurrentNumberOfTasks = 0;
    pIdleTaskTCB = ( TCB_t * ) create_task();
    TEST_ASSERT_EQUAL( 1, uxCurrentNumberOfTasks );
    xIdleTaskHandles[ 0 ] = ( TaskHandle_t ) pIdleTaskTCB;
    pTimerTaskTCB = ( TCB_t * ) create_task();
    TEST_ASSERT_EQUAL( 2, uxCurrentNumberOfTasks );
    ptcb = ( TCB_t * ) create_task();
    TEST_ASSERT_EQUAL( 3, uxCurrentNumberOfTasks );

    xSchedulerRunning = pdTRUE;
    uxDeletedTasksWaitingCleanUp = 0U; /* prvCheckTasksWaitingTermination function call. */

    /* Expectations. */
    /* Delete the timer task. */
    xTimerGetTimerDaemonTaskHandle_ExpectAndReturn( pTimerTaskTCB );
    uxListRemove_ExpectAndReturn( &pTimerTaskTCB->xStateListItem, pdPASS );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &pTimerTaskTCB->xEventListItem, NULL );
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    vPortFree_ExpectAnyArgs();
    vPortFree_ExpectAnyArgs();

    /* Delete the idle task. */
    uxListRemove_ExpectAndReturn( &pIdleTaskTCB->xStateListItem, pdPASS );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &pIdleTaskTCB->xEventListItem, NULL );
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    vPortFree_ExpectAnyArgs();
    vPortFree_ExpectAnyArgs();

    vPortEndScheduler_Expect();

    /* API call. */
    vTaskEndScheduler();

    /* Verification. */
    TEST_ASSERT_EQUAL( pdFALSE, xSchedulerRunning );
}


void test_vTaskSuspendAll_success( void )
{
    vTaskSuspendAll();
    TEST_ASSERT_EQUAL( 1, uxSchedulerSuspended );
    vTaskSuspendAll();
    TEST_ASSERT_EQUAL( 2, uxSchedulerSuspended );
    vTaskSuspendAll();
    TEST_ASSERT_EQUAL( 3, uxSchedulerSuspended );
}

void test_xTaskResumeAll_success_no_tasks( void )
{
    BaseType_t ret;

    vTaskSuspendAll();
    ret = xTaskResumeAll();
    TEST_ASSERT_EQUAL( pdFALSE, ret );
}

void test_xTaskResumeAll_success_1_task_running( void )
{
    BaseType_t ret;

    create_task();
    vTaskSuspendAll();
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    ret = xTaskResumeAll();
    TEST_ASSERT_EQUAL( pdFALSE, ret );
}

void test_xTaskResumeAll_success_2_tasks_running( void )
{
    BaseType_t ret;
    TaskHandle_t taskHandle;

    /* Start the scheduler. */
    xSchedulerRunning = pdTRUE;

    /* Create one running task. */
    create_task_priority = 3;
    taskHandle = create_task();
    pxCurrentTCB = taskHandle;
    vListInsertEnd_Ignore();
    vTaskSuspendAll();
    TEST_ASSERT_EQUAL( 1, uxSchedulerSuspended );

    /* Create another higher priority task when scheduler is suspended. This task
     * will be put into the xPendingReadyList and added to ready list when scheduler
     * is resumed. */
    create_task_priority = 4;
    taskHandle = create_task();
    ptcb = ( TCB_t * ) taskHandle;

    TEST_ASSERT_EQUAL( 2, uxCurrentNumberOfTasks );

    /* Resume the scheduler. */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( ptcb );
    listREMOVE_ITEM_Expect( &( ptcb->xEventListItem ) );
    listREMOVE_ITEM_Expect( &( ptcb->xStateListItem ) );
    listINSERT_END_ExpectAnyArgs();
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    ret = xTaskResumeAll();

    /* The higher priority task should preempt current running task. */
    TEST_ASSERT_EQUAL( pdTRUE, ret );
    TEST_ASSERT_EQUAL( 0, uxSchedulerSuspended );
    TEST_ASSERT_TRUE( xYieldPending );
}

void test_xTaskResumeAll_success_2_tasks_running_xpendedticks_gt_zero( void )
{
    BaseType_t ret;
    TaskHandle_t taskHandle;

    xPendedTicks = 1;

    taskHandle = create_task();
    ptcb = ( TCB_t * ) taskHandle;
    vListInsertEnd_Ignore();
    create_task();
    vTaskSuspendAll();
    TEST_ASSERT_EQUAL( 2, uxCurrentNumberOfTasks );

    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( ptcb );
    listREMOVE_ITEM_Expect( &( ptcb->xEventListItem ) );
    listREMOVE_ITEM_Expect( &( ptcb->xStateListItem ) );
    listINSERT_END_ExpectAnyArgs();
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    /* xTaskIncrementTick */
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &pxReadyTasksLists[ pxCurrentTCB->uxPriority ],
                                             2 );
    ret = xTaskResumeAll();
    TEST_ASSERT_EQUAL( pdTRUE, ret );
    TEST_ASSERT_EQUAL( 0, uxSchedulerSuspended );
    TEST_ASSERT_TRUE( xYieldPending );
}

void test_xTaskResumeAll_success_2_tasks_running_increment_ticks( void )
{
    BaseType_t ret;
    TaskHandle_t task_handle;
    TaskHandle_t task_handle2;

    /* Setup */
    xPendedTicks = 2;

    create_task_priority = 2;
    task_handle = create_task();

    block_task( task_handle );

    create_task_priority = 3;
    task_handle2 = create_task();

    ptcb = ( TCB_t * ) task_handle;
    TEST_ASSERT_EQUAL_PTR( task_handle2, pxCurrentTCB );

    start_scheduler();
    vTaskSuspendAll();

    TEST_ASSERT_EQUAL( 3, uxCurrentNumberOfTasks );

    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( ptcb );
    listREMOVE_ITEM_Expect( &( ptcb->xEventListItem ) );
    listREMOVE_ITEM_Expect( &( ptcb->xStateListItem ) );
    /* prvAddTaskToReadyList */
    listINSERT_END_ExpectAnyArgs();
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    /* xTaskIncrementTick */
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &pxReadyTasksLists[ pxCurrentTCB->uxPriority ],
                                             0 );
    /* xTaskIncrementTick */
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &pxReadyTasksLists[ pxCurrentTCB->uxPriority ],
                                             0 );
    /* API Call */
    ret = xTaskResumeAll();
    /* Expectations */
    TEST_ASSERT_FALSE( ret );
    TEST_ASSERT_EQUAL( 0, uxSchedulerSuspended );
    TEST_ASSERT_FALSE( xYieldPending );
}

void test_xTaskResumeAll_success_2_tasks_running_no_yield( void )
{
    BaseType_t ret;
    TaskHandle_t task_handle;
    TaskHandle_t task_handle2;

    create_task_priority = 2;
    task_handle = create_task();

    block_task( task_handle );

    create_task_priority = 3;
    task_handle2 = create_task();

    ptcb = ( TCB_t * ) task_handle;
    TEST_ASSERT_EQUAL_PTR( task_handle2, pxCurrentTCB );

    start_scheduler();
    vTaskSuspendAll();

    TEST_ASSERT_EQUAL( 3, uxCurrentNumberOfTasks );

    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( ptcb );
    listREMOVE_ITEM_Expect( &( ptcb->xEventListItem ) );
    listREMOVE_ITEM_Expect( &( ptcb->xStateListItem ) );
    /* prvAddTaskToReadyList */
    listINSERT_END_ExpectAnyArgs();
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    ret = xTaskResumeAll();
    TEST_ASSERT_FALSE( ret );
    TEST_ASSERT_EQUAL( 0, uxSchedulerSuspended );
    TEST_ASSERT_FALSE( xYieldPending );
}

/* Test the scenario that adding a task to ready list from xPendingReadyList in xTaskResumeAll
 * doesn't preempt current running task of equal priority. */
void test_xTaskResumeAll_success_2_tasks_eq_prio_running_no_yield( void )
{
    BaseType_t ret;
    TaskHandle_t task_handle;
    TaskHandle_t task_handle2;

    create_task_priority = 3;
    task_handle = create_task();

    block_task( task_handle );

    create_task_priority = 3;
    task_handle2 = create_task();

    ptcb = ( TCB_t * ) task_handle;
    TEST_ASSERT_EQUAL_PTR( task_handle2, pxCurrentTCB );

    start_scheduler();
    vTaskSuspendAll();

    TEST_ASSERT_EQUAL( 3, uxCurrentNumberOfTasks );

    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( ptcb );
    listREMOVE_ITEM_Expect( &( ptcb->xEventListItem ) );
    listREMOVE_ITEM_Expect( &( ptcb->xStateListItem ) );
    /* prvAddTaskToReadyList */
    listINSERT_END_ExpectAnyArgs();
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    ret = xTaskResumeAll();
    TEST_ASSERT_FALSE( ret );
    TEST_ASSERT_EQUAL( 0, uxSchedulerSuspended );
    TEST_ASSERT_FALSE( xYieldPending );
}

/* new priority greater than the current priority */
void test_vTaskPrioritySet_success_gt_curr_prio( void )
{
    TaskHandle_t taskHandle;

    create_task_priority = 3;
    create_task();
    create_task_priority = 4;
    taskHandle = create_task();
    ptcb = ( TCB_t * ) taskHandle;
    TEST_ASSERT_EQUAL_PTR( pxCurrentTCB, taskHandle );
    listGET_LIST_ITEM_VALUE_ExpectAnyArgsAndReturn( 0 );
    listSET_LIST_ITEM_VALUE_Expect( &( ptcb->xEventListItem ),
                                    configMAX_PRIORITIES - 5 );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &pxReadyTasksLists[ 4 ],
                                             &( ptcb->xStateListItem ),
                                             pdTRUE );
    uxListRemove_ExpectAndReturn( &( ptcb->xStateListItem ), 0 );
    /* port Reset ready priority */
    /* add task to ready list */
    listINSERT_END_Expect( &( pxReadyTasksLists[ 5 ] ),
                           &( ptcb->xStateListItem ) );

    TEST_ASSERT_EQUAL( 4, ptcb->uxBasePriority );
    TEST_ASSERT_EQUAL( 4, ptcb->uxPriority );
    vTaskPrioritySet( taskHandle, create_task_priority + 1 );
    TEST_ASSERT_EQUAL( 4 + 1, ptcb->uxBasePriority );
    TEST_ASSERT_EQUAL( 4 + 1, ptcb->uxPriority );
    ASSERT_PORT_YIELD_WITHIN_API_NOT_CALLED();
}

void test_vTaskPrioritySet_success_gt_curr_prio_curr_tcb( void )
{
    TaskHandle_t taskHandle;
    TaskHandle_t taskHandle2;

    create_task_priority = 3;
    taskHandle = create_task();
    create_task_priority = 4;
    taskHandle2 = create_task();
    ptcb = ( TCB_t * ) taskHandle;

    TEST_ASSERT_EQUAL_PTR( pxCurrentTCB, taskHandle2 );

    listGET_LIST_ITEM_VALUE_ExpectAnyArgsAndReturn( 0 );
    listSET_LIST_ITEM_VALUE_Expect( &( ptcb->xEventListItem ), 2 );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &pxReadyTasksLists[ 3 ],
                                             &( ptcb->xStateListItem ),
                                             pdTRUE );
    uxListRemove_ExpectAndReturn( &( ptcb->xStateListItem ), 0 );
    /* port Reset ready priority */
    /* add task to ready list */
    listINSERT_END_Expect( &( pxReadyTasksLists[ 7 ] ),
                           &( ptcb->xStateListItem ) );

    TEST_ASSERT_EQUAL( 3, ptcb->uxBasePriority );
    TEST_ASSERT_EQUAL( 3, ptcb->uxPriority );
    vTaskPrioritySet( taskHandle, create_task_priority + 3 );
    TEST_ASSERT_EQUAL( 4 + 3, ptcb->uxBasePriority );
    TEST_ASSERT_EQUAL( 4 + 3, ptcb->uxPriority );
    ASSERT_PORT_YIELD_WITHIN_API_CALLED();
}

/* Test the scenario that setting a priority of a task in the ready list equal to
 * current task doesn't preempt current running task. */
void test_vTaskPrioritySet_success_eq_curr_prio_curr_tcb( void )
{
    TaskHandle_t taskHandle;
    TaskHandle_t taskHandle2;

    create_task_priority = 3;
    taskHandle = create_task();
    create_task_priority = 4;
    taskHandle2 = create_task();
    ptcb = ( TCB_t * ) taskHandle;

    TEST_ASSERT_EQUAL_PTR( pxCurrentTCB, taskHandle2 );

    listGET_LIST_ITEM_VALUE_ExpectAnyArgsAndReturn( 0 );
    listSET_LIST_ITEM_VALUE_Expect( &( ptcb->xEventListItem ), ( configMAX_PRIORITIES - create_task_priority ) );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &pxReadyTasksLists[ 3 ],
                                             &( ptcb->xStateListItem ),
                                             pdTRUE );
    uxListRemove_ExpectAndReturn( &( ptcb->xStateListItem ), 0 );
    /* port Reset ready priority */
    /* add task to ready list */
    listINSERT_END_Expect( &( pxReadyTasksLists[ 4 ] ),
                           &( ptcb->xStateListItem ) );

    TEST_ASSERT_EQUAL( 3, ptcb->uxBasePriority );
    TEST_ASSERT_EQUAL( 3, ptcb->uxPriority );

    /* Set priority of taskHandle to the same as taskHandle2. */
    vTaskPrioritySet( taskHandle, 4 );
    TEST_ASSERT_EQUAL( 4, ptcb->uxBasePriority );
    TEST_ASSERT_EQUAL( 4, ptcb->uxPriority );

    /* portYIELD_WITHIN_API() should not be called. */
    ASSERT_PORT_YIELD_WITHIN_API_NOT_CALLED();
}

void test_vTaskPrioritySet_success_gt_max_prio( void )
{
    TaskHandle_t taskHandle;

    create_task_priority = 3;
    taskHandle = create_task();
    ptcb = ( TCB_t * ) taskHandle;

    /* expectations */
    listGET_LIST_ITEM_VALUE_ExpectAnyArgsAndReturn( 0x80000000UL );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &pxReadyTasksLists[ 3 ],
                                             &( ptcb->xStateListItem ),
                                             pdTRUE );
    uxListRemove_ExpectAndReturn( &( ptcb->xStateListItem ), 0 );
    listINSERT_END_Expect( &( pxReadyTasksLists[ configMAX_PRIORITIES - 1 ] ),
                           &( ptcb->xStateListItem ) );

    /* API call */
    vTaskPrioritySet( taskHandle, configMAX_PRIORITIES + 5 );

    /* validations */
    TEST_ASSERT_EQUAL( configMAX_PRIORITIES - 1, ptcb->uxBasePriority );
    ASSERT_PORT_YIELD_WITHIN_API_NOT_CALLED();
}

void test_vTaskPrioritySet_success_call_current_null( void )
{
    TaskHandle_t taskHandle;

    create_task_priority = 3;
    taskHandle = create_task();
    ptcb = ( TCB_t * ) taskHandle;

    /* expectations */
    listGET_LIST_ITEM_VALUE_ExpectAnyArgsAndReturn( 0x80000000UL );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &pxReadyTasksLists[ 3 ],
                                             &( ptcb->xStateListItem ),
                                             pdTRUE );
    uxListRemove_ExpectAndReturn( &( ptcb->xStateListItem ), 0 );
    listINSERT_END_Expect( &( pxReadyTasksLists[ 4 ] ),
                           &( ptcb->xStateListItem ) );

    /* API call */
    vTaskPrioritySet( NULL, 4 );

    /* validations */
    TEST_ASSERT_EQUAL( 4, ptcb->uxBasePriority );
    ASSERT_PORT_YIELD_WITHIN_API_NOT_CALLED();
}
/* ensures that setting the same priority for a tasks changes nothing */
void test_vTaskPrioritySet_success_same_prio( void )
{
    TaskHandle_t taskHandle;

    create_task_priority = 3;
    taskHandle = create_task();
    ptcb = ( TCB_t * ) taskHandle;
    TEST_ASSERT_EQUAL_PTR( pxCurrentTCB, ptcb );
    /* expectations */

    /* API call */
    vTaskPrioritySet( taskHandle, 3 );

    /* Validations */
    TEST_ASSERT_EQUAL( 3, ptcb->uxBasePriority );
    TEST_ASSERT_EQUAL( 3, ptcb->uxPriority );
    ASSERT_PORT_YIELD_WITHIN_API_NOT_CALLED();
}


/* ensures if the set priority is less than the current priority and it is the
 * current tcb the task is yielded
 */
void test_vTaskPrioritySet_success_lt_curr_prio_curr_task( void )
{
    TaskHandle_t taskHandle;

    create_task_priority = 3;
    taskHandle = create_task();
    ptcb = ( TCB_t * ) taskHandle;
    TEST_ASSERT_EQUAL_PTR( pxCurrentTCB, ptcb );

    /* Expectations */
    listGET_LIST_ITEM_VALUE_ExpectAnyArgsAndReturn( 0 );
    listSET_LIST_ITEM_VALUE_Expect( &( ptcb->xEventListItem ),
                                    configMAX_PRIORITIES - 2 );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &pxReadyTasksLists[ 3 ],
                                             &( ptcb->xStateListItem ),
                                             pdTRUE );
    uxListRemove_ExpectAndReturn( &( ptcb->xStateListItem ), 1 );
    listINSERT_END_Expect( &( pxReadyTasksLists[ 2 ] ),
                           &( ptcb->xStateListItem ) );
    /* API call */
    vTaskPrioritySet( taskHandle, 2 );

    /* Validations */
    TEST_ASSERT_EQUAL( 2, ptcb->uxBasePriority );
    ASSERT_PORT_YIELD_WITHIN_API_CALLED();
}

/* ensures if the set priority is less than the current priority and it is not
 * the current tcb the task is not yielded
 */
void test_vTaskPrioritySet_success_lt_curr_prio_not_curr_task( void )
{
    TaskHandle_t taskHandle, taskHandle2;

    create_task_priority = 3;
    taskHandle = create_task();
    create_task_priority = 4;
    taskHandle2 = create_task();
    ptcb = ( TCB_t * ) taskHandle;
    TEST_ASSERT_EQUAL_PTR( pxCurrentTCB, taskHandle2 );

    /* Expectations */
    listGET_LIST_ITEM_VALUE_ExpectAnyArgsAndReturn( 0 );
    listSET_LIST_ITEM_VALUE_Expect( &( ptcb->xEventListItem ),
                                    configMAX_PRIORITIES - 2 );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &pxReadyTasksLists[ 3 ],
                                             &( ptcb->xStateListItem ),
                                             pdFALSE );
    /* API call */
    vTaskPrioritySet( taskHandle, 2 );

    /* Validations */
    TEST_ASSERT_EQUAL( 2, ptcb->uxBasePriority );
    ASSERT_PORT_YIELD_WITHIN_API_NOT_CALLED();
}

/* This test ensures that if the base priority is different than that the current
 * priority, the resulting base and current priority will be equal to the new
 * priority when the new priority is greater than the inherited priority.
 */
void test_vTaskPrioritySet_success_gt_curr_prio_diff_base( void )
{
    TaskHandle_t taskHandle, taskHandle2;

    create_task_priority = 3;
    taskHandle = create_task();
    create_task_priority = 4;
    taskHandle2 = create_task();
    ptcb = ( TCB_t * ) taskHandle;
    TEST_ASSERT_EQUAL_PTR( pxCurrentTCB, taskHandle2 );
    /* task handle will inherit the priorit of taskHandle2 */
    listGET_LIST_ITEM_VALUE_ExpectAnyArgsAndReturn( 0x80000000UL );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &pxReadyTasksLists[ 3 ],
                                             &( taskHandle->xStateListItem ),
                                             pdFALSE );
    xTaskPriorityInherit( taskHandle );

    TEST_ASSERT_EQUAL( 4, ptcb->uxPriority );
    TEST_ASSERT_EQUAL( 3, ptcb->uxBasePriority );
    /* Expectations */
    listGET_LIST_ITEM_VALUE_ExpectAnyArgsAndReturn( 0 );
    listSET_LIST_ITEM_VALUE_Expect( &( ptcb->xEventListItem ),
                                    configMAX_PRIORITIES - 5 );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &pxReadyTasksLists[ 4 ],
                                             &( ptcb->xStateListItem ),
                                             pdFALSE );
    /* API call */
    vTaskPrioritySet( taskHandle, 5 );

    /* Validations */
    TEST_ASSERT_EQUAL( 5, ptcb->uxBasePriority );
    TEST_ASSERT_EQUAL( 5, ptcb->uxPriority );
    ASSERT_PORT_YIELD_WITHIN_API_CALLED();
}

/* This test ensures that if the base priority is different less than that the current
 * priority the resulting base  will be equal to the new priority while the
 * current priority will be equal to the inherited priority
 * */
void test_vTaskPrioritySet_success_lt_curr_prio_diff_base( void )
{
    TaskHandle_t taskHandle, taskHandle2;

    create_task_priority = 3;
    taskHandle = create_task();
    create_task_priority = 6;
    taskHandle2 = create_task();
    ptcb = ( TCB_t * ) taskHandle;
    TEST_ASSERT_EQUAL_PTR( pxCurrentTCB, taskHandle2 );
    /* task handle will inherit the priorit of taskHandle2 */
    listGET_LIST_ITEM_VALUE_ExpectAnyArgsAndReturn( 0x80000000UL );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &pxReadyTasksLists[ 3 ],
                                             &( taskHandle->xStateListItem ),
                                             pdFALSE );
    xTaskPriorityInherit( taskHandle );

    TEST_ASSERT_EQUAL( 6, ptcb->uxPriority );
    TEST_ASSERT_EQUAL( 3, ptcb->uxBasePriority );
    /* Expectations */
    listGET_LIST_ITEM_VALUE_ExpectAnyArgsAndReturn( 0 );
    listSET_LIST_ITEM_VALUE_Expect( &( ptcb->xEventListItem ),
                                    configMAX_PRIORITIES - 5 );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &pxReadyTasksLists[ 6 ],
                                             &( ptcb->xStateListItem ),
                                             pdFALSE );
    /* API call */
    vTaskPrioritySet( taskHandle, 5 );

    /* Validations */
    TEST_ASSERT_EQUAL( 5, ptcb->uxBasePriority );
    TEST_ASSERT_EQUAL( 6, ptcb->uxPriority );
    ASSERT_PORT_YIELD_WITHIN_API_NOT_CALLED();
}
/* testing INCLUDE_uxTaskPriorityGet */
/* Ensures the correct priority is returned */
void test_uxTaskPriorityGet_success( void )
{
    TaskHandle_t taskHandle;
    UBaseType_t ret_priority;

    create_task_priority = 3;
    taskHandle = create_task();
    ptcb = ( TCB_t * ) taskHandle;
    TEST_ASSERT_EQUAL_PTR( pxCurrentTCB, ptcb );
    /* expectations */

    /* API call */
    ret_priority = uxTaskPriorityGet( taskHandle );

    /* Validations */
    TEST_ASSERT_EQUAL( 3, ret_priority );
}

void test_uxTaskPriorityGet_success_null_handle( void )
{
    TaskHandle_t taskHandle;
    UBaseType_t ret_priority;

    create_task_priority = 3;
    taskHandle = create_task();
    ptcb = ( TCB_t * ) taskHandle;
    TEST_ASSERT_EQUAL_PTR( pxCurrentTCB, ptcb );
    /* expectations */

    /* API call */
    ret_priority = uxTaskPriorityGet( NULL );

    /* Validations */
    TEST_ASSERT_EQUAL( 3, ret_priority );
}

void test_uxTaskPriorityGetFromISR_success( void )
{
    TaskHandle_t taskHandle;
    UBaseType_t ret_priority;

    create_task_priority = 3;
    taskHandle = create_task();
    ptcb = ( TCB_t * ) taskHandle;
    TEST_ASSERT_EQUAL_PTR( pxCurrentTCB, ptcb );
    ret_priority = uxTaskPriorityGetFromISR( taskHandle );

    TEST_ASSERT_EQUAL( 3, ret_priority );
    ASSERT_PORT_CLEAR_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_PORT_SET_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_INVALID_INTERRUPT_PRIORITY_CALLED();
}

void test_uxTaskPriorityGetFromISR_success_null_handle( void )
{
    TaskHandle_t taskHandle;
    UBaseType_t ret_priority;

    create_task_priority = 3;
    taskHandle = create_task();
    ptcb = ( TCB_t * ) taskHandle;
    TEST_ASSERT_EQUAL_PTR( pxCurrentTCB, ptcb );
    ret_priority = uxTaskPriorityGetFromISR( NULL );

    TEST_ASSERT_EQUAL( 3, ret_priority );
    ASSERT_PORT_CLEAR_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_PORT_SET_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_INVALID_INTERRUPT_PRIORITY_CALLED();
}

/* ----------------------- testing uxTaskBasePriorityGet API --------------------------- */

/**
 * @brief Test uxTaskBasePriorityGet with a task.
 * @details Test uxTaskBasePriorityGet returns the base priority of the task.
 */
void test_uxTaskBasePriorityGet_success( void )
{
    TaskHandle_t taskHandle;
    UBaseType_t ret_priority;

    create_task_priority = 3;
    taskHandle = create_task();
    ptcb = ( TCB_t * ) taskHandle;
    TEST_ASSERT_EQUAL_PTR( pxCurrentTCB, ptcb );
    /* expectations */

    /* API call */
    ret_priority = uxTaskBasePriorityGet( taskHandle );

    /* Validations */
    TEST_ASSERT_EQUAL( 3, ret_priority );
}

/**
 * @brief Test uxTaskBasePriorityGet with current task.
 * @details Test uxTaskBasePriorityGet returns the base priority of current task.
 */
void test_uxTaskBasePriorityGet_success_null_handle( void )
{
    TaskHandle_t taskHandle;
    UBaseType_t ret_priority;

    create_task_priority = 3;
    taskHandle = create_task();
    ptcb = ( TCB_t * ) taskHandle;
    TEST_ASSERT_EQUAL_PTR( pxCurrentTCB, ptcb );
    /* expectations */

    /* API call */
    ret_priority = uxTaskBasePriorityGet( NULL );

    /* Validations */
    TEST_ASSERT_EQUAL( 3, ret_priority );
}

/* ----------------------- testing uxTaskBasePriorityGetFromISR API --------------------------- */

/**
 * @brief Test uxTaskBasePriorityGetFromISR with a task.
 * @details Test uxTaskBasePriorityGetFromISR returns the base priority of the task.
 */
void test_uxTaskBasePriorityGetFromISR_success( void )
{
    TaskHandle_t taskHandle;
    UBaseType_t ret_priority;

    create_task_priority = 3;
    taskHandle = create_task();
    ptcb = ( TCB_t * ) taskHandle;
    TEST_ASSERT_EQUAL_PTR( pxCurrentTCB, ptcb );
    ret_priority = uxTaskBasePriorityGetFromISR( taskHandle );

    TEST_ASSERT_EQUAL( 3, ret_priority );
    ASSERT_PORT_CLEAR_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_PORT_SET_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_INVALID_INTERRUPT_PRIORITY_CALLED();
}

/**
 * @brief Test uxTaskBasePriorityGetFromISR with current task.
 * @details Test uxTaskBasePriorityGetFromISR returns the base priority of current task.
 */
void test_uxTaskBasePriorityGetFromISR_success_null_handle( void )
{
    TaskHandle_t taskHandle;
    UBaseType_t ret_priority;

    create_task_priority = 3;
    taskHandle = create_task();
    ptcb = ( TCB_t * ) taskHandle;
    TEST_ASSERT_EQUAL_PTR( pxCurrentTCB, ptcb );
    ret_priority = uxTaskBasePriorityGetFromISR( NULL );

    TEST_ASSERT_EQUAL( 3, ret_priority );
    ASSERT_PORT_CLEAR_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_PORT_SET_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_INVALID_INTERRUPT_PRIORITY_CALLED();
}

/* ----------------------- testing vTaskDelay API --------------------------- */
void test_vTaskDelay_success_gt_0_yield_called( void )
{
    TaskHandle_t task_handle;

    task_handle = create_task();
    ptcb = ( TCB_t * ) task_handle;
    TickType_t delay = 34;
    /* Expectations */
    /* prvAddCurrentTaskToDelayedList */
    uxListRemove_ExpectAndReturn( &ptcb->xStateListItem, 1 );
    listSET_LIST_ITEM_VALUE_Expect( &ptcb->xStateListItem,
                                    xTickCount + delay );
    vListInsert_Expect( pxDelayedTaskList, &ptcb->xStateListItem );

    /* xTaskResumeAll */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    /* API call */
    vTaskDelay( delay );
    /* Validations */
    ASSERT_PORT_YIELD_WITHIN_API_CALLED();
}

void test_vTaskDelay_success_gt_0_yield_not_called( void )
{
    TaskHandle_t task_handle;

    task_handle = create_task();
    ptcb = ( TCB_t * ) task_handle;
    TickType_t delay = 34;
    /* Expectations */
    /* prvAddCurrentTaskToDelayedList */
    uxListRemove_ExpectAndReturn( &ptcb->xStateListItem, pdTRUE );
    listSET_LIST_ITEM_VALUE_Expect( &ptcb->xStateListItem,
                                    xTickCount + delay );
    vListInsert_Expect( pxDelayedTaskList, &ptcb->xStateListItem );

    /* xTaskResumeAll */

    listLIST_IS_EMPTY_ExpectAndReturn( &xPendingReadyList, pdFALSE );
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAndReturn( &xPendingReadyList, ptcb );
    listREMOVE_ITEM_Expect( &( ptcb->xEventListItem ) );
    listREMOVE_ITEM_Expect( &( ptcb->xStateListItem ) );
    /* prvAddTaskToReadyList */
    listINSERT_END_Expect( &pxReadyTasksLists[ ptcb->uxPriority ],
                           &ptcb->xStateListItem );
    /* back to xTaskResumeAll */
    listLIST_IS_EMPTY_ExpectAndReturn( &xPendingReadyList, pdTRUE );
    /* prvResetNextTaskUnblockTime */
    listLIST_IS_EMPTY_ExpectAndReturn( pxDelayedTaskList, pdTRUE );

    /* API Call */
    vTaskDelay( delay );
    /* Validations */
    ASSERT_PORT_YIELD_WITHIN_API_CALLED();
}

/* Test the scenario that a higher priority task is added to xPendingReadyList when
 * current task calls xTaskDelay. Scheduler yields for the higher priority task in
 * xTaskResumeAll function. */
void test_vTaskDelay_success_gt_0_already_yielded( void )
{
    TaskHandle_t task_handle;
    TaskHandle_t task_handle2;

    /* Create one task. This is the current running task. */
    create_task_priority = 3;
    task_handle = create_task();

    /* Create a higher priority task to be added to xPendingReadyList. */
    create_task_priority = 4;
    task_handle2 = create_task();

    pxCurrentTCB = task_handle;
    ptcb = ( TCB_t * ) task_handle;
    TickType_t delay = 34;
    /* Expectations */
    /* prvAddCurrentTaskToDelayedList */
    uxListRemove_ExpectAndReturn( &ptcb->xStateListItem, pdTRUE );
    listSET_LIST_ITEM_VALUE_Expect( &ptcb->xStateListItem,
                                    xTickCount + delay );
    vListInsert_Expect( pxDelayedTaskList, &ptcb->xStateListItem );

    /* xTaskResumeAll */
    listLIST_IS_EMPTY_ExpectAndReturn( &xPendingReadyList, pdFALSE );
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAndReturn( &xPendingReadyList, task_handle2 );
    listREMOVE_ITEM_Expect( &( task_handle2->xEventListItem ) );
    listREMOVE_ITEM_Expect( &( task_handle2->xStateListItem ) );
    /* prvAddTaskToReadyList */
    listINSERT_END_Expect( &pxReadyTasksLists[ task_handle2->uxPriority ],
                           &task_handle2->xStateListItem );
    /* back to xTaskResumeAll */
    listLIST_IS_EMPTY_ExpectAndReturn( &xPendingReadyList, pdTRUE );
    /* prvResetNextTaskUnblockTime */
    listLIST_IS_EMPTY_ExpectAndReturn( pxDelayedTaskList, pdTRUE );

    /* API Call */
    vTaskDelay( delay );
    /* Validations */
    ASSERT_PORT_YIELD_WITHIN_API_CALLED();
}

/* ensures that with a delay of zero no other operation or sleeping is done, the
 * task in only yielded */
void test_vTaskDelay_success_eq_0( void )
{
    /* API Call */
    vTaskDelay( 0 );
    /* Validations */
    ASSERT_PORT_YIELD_WITHIN_API_CALLED();
}

/* --------------------- testing INCLUDE_eTaskGetState ---------------------- */
void test_eTaskGetState_success_current_tcb( void )
{
    TaskHandle_t task_handle;

    task_handle = create_task();
    ptcb = ( TCB_t * ) task_handle;
    eTaskState ret_task_state;
    /* no Expectations */

    /* API Call */
    ret_task_state = eTaskGetState( task_handle );
    /* Validations */
    TEST_ASSERT_EQUAL( eRunning, ret_task_state );
}

void test_eTaskGetState_success_not_current_tcb_pending_ready( void )
{
    TaskHandle_t task_handle;

    create_task_priority = 3;
    task_handle = create_task();
    create_task_priority = 5;
    create_task();
    ptcb = ( TCB_t * ) task_handle;
    TEST_ASSERT_NOT_EQUAL( pxCurrentTCB, ptcb );
    eTaskState ret_task_state;
    /* Expectations */
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xStateListItem,
                                             NULL );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem,
                                             &xPendingReadyList );

    /* API Call */
    ret_task_state = eTaskGetState( task_handle );
    /* Validations */
    TEST_ASSERT_EQUAL( eReady, ret_task_state );
}

void test_eTaskGetState_success_not_current_tcb_blocked_delayed( void )
{
    TaskHandle_t task_handle;

    create_task_priority = 3;
    task_handle = create_task();
    create_task_priority = 5;
    create_task();
    ptcb = ( TCB_t * ) task_handle;
    TEST_ASSERT_NOT_EQUAL( pxCurrentTCB, ptcb );
    eTaskState ret_task_state;
    /* Expectations */
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xStateListItem,
                                             pxDelayedTaskList );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem,
                                             NULL );

    /* API Call */
    ret_task_state = eTaskGetState( task_handle );
    /* Validations */
    TEST_ASSERT_EQUAL( eBlocked, ret_task_state );
}

void test_eTaskGetState_success_not_current_tcb_blocked_overflow( void )
{
    TaskHandle_t task_handle;

    create_task_priority = 3;
    task_handle = create_task();
    create_task_priority = 5;
    create_task();
    ptcb = ( TCB_t * ) task_handle;
    TEST_ASSERT_NOT_EQUAL( pxCurrentTCB, ptcb );
    eTaskState ret_task_state;
    /* Expectations */
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xStateListItem,
                                             pxOverflowDelayedTaskList );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem,
                                             NULL );

    /* API Call */
    ret_task_state = eTaskGetState( task_handle );
    /* Validations */
    TEST_ASSERT_EQUAL( eBlocked, ret_task_state );
}

void test_eTaskGetState_success_not_current_tcb_ready( void )
{
    TaskHandle_t task_handle;

    create_task_priority = 3;
    task_handle = create_task();
    create_task_priority = 5;
    create_task();
    ptcb = ( TCB_t * ) task_handle;
    TEST_ASSERT_NOT_EQUAL( pxCurrentTCB, ptcb );
    eTaskState ret_task_state;
    /* Expectations */
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xStateListItem,
                                             &pxReadyTasksLists[ 0 ] );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem,
                                             NULL );

    /* API Call */
    ret_task_state = eTaskGetState( task_handle );
    /* Validations */
    TEST_ASSERT_EQUAL( eReady, ret_task_state );
}

void test_eTaskGetState_success_not_current_tcb_suspended( void )
{
    TaskHandle_t task_handle;

    create_task_priority = 3;
    task_handle = create_task();
    create_task_priority = 5;
    create_task();
    ptcb = ( TCB_t * ) task_handle;
    TEST_ASSERT_NOT_EQUAL( pxCurrentTCB, ptcb );
    eTaskState ret_task_state;
    /* Expectations */
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xStateListItem,
                                             &xSuspendedTaskList );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem,
                                             NULL );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem,
                                             NULL );

    /* API Call */
    ret_task_state = eTaskGetState( task_handle );
    /* Validations */
    TEST_ASSERT_EQUAL( eSuspended, ret_task_state );
}

void test_eTaskGetState_success_not_current_tcb_deleted( void )
{
    TaskHandle_t task_handle;

    create_task_priority = 3;
    task_handle = create_task();
    create_task_priority = 5;
    create_task();
    ptcb = ( TCB_t * ) task_handle;
    TEST_ASSERT_NOT_EQUAL( pxCurrentTCB, ptcb );
    eTaskState ret_task_state;
    /* Expectations */
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xStateListItem,
                                             &xTasksWaitingTermination );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem,
                                             NULL );

    /* API Call */
    ret_task_state = eTaskGetState( task_handle );
    /* Validations */
    TEST_ASSERT_EQUAL( eDeleted, ret_task_state );
}

void test_eTaskGetState_success_not_current_tcb_deleted_not_found( void )
{
    TaskHandle_t task_handle;

    create_task_priority = 3;
    task_handle = create_task();
    create_task_priority = 5;
    create_task();
    ptcb = ( TCB_t * ) task_handle;
    TEST_ASSERT_NOT_EQUAL( pxCurrentTCB, ptcb );
    eTaskState ret_task_state;
    /* Expectations */
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xStateListItem,
                                             NULL );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem,
                                             NULL );

    /* API Call */
    ret_task_state = eTaskGetState( task_handle );
    /* Validations */
    TEST_ASSERT_EQUAL( eDeleted, ret_task_state );
}
/*else if( ( pxStateList == &xTasksWaitingTermination ) || ( pxStateList == NULL ) ) */

/* alternatively this can be better solved by launching a thread and calling
 * notification wait, then block on the port yield function hook waiting for this
 * thread to continue, and check the value of  taskWAITING_NOTIFICATION */
void test_eTaskGetState_success_not_current_tcb_wait_notif( void )
{
    TaskHandle_t task_handle;

    create_task_priority = 3;
    task_handle = create_task();
    create_task_priority = 5;
    create_task();
    ptcb = ( TCB_t * ) task_handle;
    /* see note above */
    ptcb->ucNotifyState[ 0 ] = 1; /* taskWAITING_NOTIFICATION */
    TEST_ASSERT_NOT_EQUAL( pxCurrentTCB, ptcb );
    eTaskState ret_task_state;
    /* Expectations */
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xStateListItem,
                                             &xSuspendedTaskList );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem,
                                             NULL );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem,
                                             NULL );

    /* API Call */
    ret_task_state = eTaskGetState( task_handle );
    /* Validations */
    TEST_ASSERT_EQUAL( eBlocked, ret_task_state );
}

void test_eTaskGetState_success_not_current_tcb_blocked( void )
{
    TaskHandle_t task_handle;

    create_task_priority = 3;
    task_handle = create_task();
    create_task_priority = 5;
    create_task();
    ptcb = ( TCB_t * ) task_handle;
    TEST_ASSERT_NOT_EQUAL( pxCurrentTCB, ptcb );
    eTaskState ret_task_state;
    /* Expectations */
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xStateListItem,
                                             &xSuspendedTaskList );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem,
                                             &xSuspendedTaskList );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem,
                                             &xSuspendedTaskList );
    /* API Call */
    ret_task_state = eTaskGetState( task_handle );
    /* Validations */
    TEST_ASSERT_EQUAL( eBlocked, ret_task_state );
}

/* ------------------------- INCLUDE_xTaskDelayUntil ------------------------ */
void test_xTaskDelayUntil_success_gt_tickCount( void )
{
    BaseType_t ret_xtask_delay;
    TickType_t previousWakeTime = xTickCount + 3;
    TaskHandle_t task_handle;

    task_handle = create_task();
    ptcb = ( TCB_t * ) task_handle;
    TEST_ASSERT_EQUAL( pxCurrentTCB, ptcb );

    /* Expectations */
    listLIST_IS_EMPTY_ExpectAndReturn( &xPendingReadyList, pdTRUE );
    /* API Call */
    ret_xtask_delay = xTaskDelayUntil( &previousWakeTime, 4 );
    /* Validations */
    TEST_ASSERT_EQUAL( pdFALSE, ret_xtask_delay );
}


void test_xTaskDelayUntil_success_gt_tickCount_should_delay( void )
{
    BaseType_t ret_xtask_delay;

    xTickCount = 1;
    TickType_t previousWakeTime = xTickCount + 3;
    TaskHandle_t task_handle;

    task_handle = create_task();
    ptcb = ( TCB_t * ) task_handle;
    TEST_ASSERT_EQUAL( pxCurrentTCB, ptcb );
    uxListRemove_ExpectAndReturn( &pxCurrentTCB->xStateListItem, 0 );
    listSET_LIST_ITEM_VALUE_Expect( &pxCurrentTCB->xStateListItem, 3 );
    vListInsert_Expect( pxDelayedTaskList, &ptcb->xStateListItem );
    /* xTaskResumeAll */
    listLIST_IS_EMPTY_ExpectAndReturn( &xPendingReadyList, pdTRUE );

    ret_xtask_delay = xTaskDelayUntil( &previousWakeTime, UINT32_MAX );
    TEST_ASSERT_EQUAL( pdTRUE, ret_xtask_delay );
}

void test_xTaskDelayUntil_success_prev_gt_tickCount2( void )
{
    BaseType_t ret_xtask_delay;
    TickType_t previousWakeTime = xTickCount + 5; /* 500 + 5 = 505 */
    TaskHandle_t task_handle;
    TickType_t xTimeIncrement = UINT32_MAX - 5;

    /* Setup */
    task_handle = create_task();
    ptcb = ( TCB_t * ) task_handle;
    TEST_ASSERT_EQUAL( pxCurrentTCB, ptcb );
    /* Expectations */
    listLIST_IS_EMPTY_ExpectAndReturn( &xPendingReadyList, pdTRUE );
    /* API Call */
    ret_xtask_delay = xTaskDelayUntil( &previousWakeTime, xTimeIncrement );
    /* Validations */
    ASSERT_PORT_YIELD_WITHIN_API_CALLED();
    TEST_ASSERT_FALSE( ret_xtask_delay );
}
/* 0 */


void test_xTaskDelayUntil_success_lt_tickCount( void )
{
    BaseType_t ret_xtask_delay;
    TickType_t previousWakeTime = xTickCount - 3;
    TaskHandle_t task_handle;

    task_handle = create_task();
    ptcb = ( TCB_t * ) task_handle;
    TEST_ASSERT_EQUAL( pxCurrentTCB, ptcb );
    /* Expectations */
    /* prvResetNextTaskUnblockTime */
    uxListRemove_ExpectAndReturn( &pxCurrentTCB->xStateListItem, 0 );
    listSET_LIST_ITEM_VALUE_Expect( &pxCurrentTCB->xStateListItem, 500 + ( ( previousWakeTime + 5 ) - xTickCount ) );
    vListInsert_Expect( pxDelayedTaskList, &ptcb->xStateListItem );
    /* xTaskResumeAll */
    listLIST_IS_EMPTY_ExpectAndReturn( &xPendingReadyList, pdFALSE );
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAndReturn( &xPendingReadyList, ptcb );
    listREMOVE_ITEM_Expect( &( ptcb->xEventListItem ) );
    listREMOVE_ITEM_Expect( &( ptcb->xStateListItem ) );
    /* prvAddTaskToReadyList */
    listINSERT_END_Expect( &pxReadyTasksLists[ ptcb->uxPriority ],
                           &ptcb->xStateListItem );
    /* back to xTaskResumeAll */
    listLIST_IS_EMPTY_ExpectAndReturn( &xPendingReadyList, pdTRUE );
    /* prvResetNextTaskUnblockTime */
    listLIST_IS_EMPTY_ExpectAndReturn( pxDelayedTaskList, pdTRUE );
    /* API Call */
    ret_xtask_delay = xTaskDelayUntil( &previousWakeTime, 5 );
    /* Validations */
    ASSERT_PORT_YIELD_WITHIN_API_CALLED();
    TEST_ASSERT_EQUAL( pdTRUE, ret_xtask_delay );
}

void test_xTaskDelayUntil_success_lt_tickCount1( void )
{
    BaseType_t ret_xtask_delay;
    TickType_t previousWakeTime = xTickCount - 3; /* 500 - 3 = 497 */
    TaskHandle_t task_handle;
    TickType_t xTimeIncrement = 3;

    /* Setup */
    task_handle = create_task();
    ptcb = ( TCB_t * ) task_handle;
    TEST_ASSERT_EQUAL( pxCurrentTCB, ptcb );
    /* Expectations */
    /* xTaskResumeAll */
    listLIST_IS_EMPTY_ExpectAndReturn( &xPendingReadyList, pdFALSE );
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAndReturn( &xPendingReadyList, ptcb );
    listREMOVE_ITEM_Expect( &( ptcb->xEventListItem ) );
    listREMOVE_ITEM_Expect( &( ptcb->xStateListItem ) );
    /* prvAddTaskToReadyList */
    listINSERT_END_Expect( &pxReadyTasksLists[ ptcb->uxPriority ],
                           &ptcb->xStateListItem );
    /* back to xTaskResumeAll */
    listLIST_IS_EMPTY_ExpectAndReturn( &xPendingReadyList, pdTRUE );
    /* prvResetNextTaskUnblockTime */
    listLIST_IS_EMPTY_ExpectAndReturn( pxDelayedTaskList, pdTRUE );
    /* API Call */
    ret_xtask_delay = xTaskDelayUntil( &previousWakeTime, xTimeIncrement );
    /* Validations */
    ASSERT_PORT_YIELD_WITHIN_API_CALLED();
    TEST_ASSERT_FALSE( ret_xtask_delay );
}

void test_xTaskDelayUntil_success_lt_tickCount2( void )
{
    BaseType_t ret_xtask_delay;
    TickType_t previousWakeTime = xTickCount - 3; /* 500 - 3 = 497 */
    TaskHandle_t task_handle;
    TickType_t xTimeIncrement = UINT32_MAX;

    /* Setup */
    task_handle = create_task();
    ptcb = ( TCB_t * ) task_handle;
    TEST_ASSERT_EQUAL( pxCurrentTCB, ptcb );
    /* Expectations */
    /* xTaskResumeAll */
    /* prvResetNextTaskUnblockTime */
    uxListRemove_ExpectAndReturn( &pxCurrentTCB->xStateListItem, 0 );
    listSET_LIST_ITEM_VALUE_Expect( &pxCurrentTCB->xStateListItem,
                                    ( ( previousWakeTime - 1 ) ) );
    vListInsert_Expect( pxOverflowDelayedTaskList, &ptcb->xStateListItem );
    /* xTaskResumeAll */
    listLIST_IS_EMPTY_ExpectAndReturn( &xPendingReadyList, pdFALSE );
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAndReturn( &xPendingReadyList, ptcb );
    listREMOVE_ITEM_Expect( &( ptcb->xEventListItem ) );
    listREMOVE_ITEM_Expect( &( ptcb->xStateListItem ) );
    /* prvAddTaskToReadyList */
    listINSERT_END_Expect( &pxReadyTasksLists[ ptcb->uxPriority ],
                           &ptcb->xStateListItem );
    /* back to xTaskResumeAll */
    listLIST_IS_EMPTY_ExpectAndReturn( &xPendingReadyList, pdTRUE );
    /* prvResetNextTaskUnblockTime */
    listLIST_IS_EMPTY_ExpectAndReturn( pxDelayedTaskList, pdTRUE );
    /* API Call */
    ret_xtask_delay = xTaskDelayUntil( &previousWakeTime, xTimeIncrement );
    /* Validations */
    ASSERT_PORT_YIELD_WITHIN_API_CALLED();
    TEST_ASSERT_TRUE( ret_xtask_delay );
}

/* Test the scenario that a higher priority task is added to xPendingReadyList when
 * current task calls xTaskDelayUntil. Scheduler yields for the higher priority task
 * in vTaskResumeAll function. */
void test_xTaskDelayUntil_success_yield_already( void )
{
    BaseType_t ret_xtask_delay;
    TickType_t previousWakeTime = xTickCount - 3; /* 500 - 3 = 497 */
    TaskHandle_t task_handle;
    TaskHandle_t task_handle2;
    TickType_t xTimeIncrement = UINT32_MAX;

    /* Setup */
    create_task_priority = 3;
    task_handle = create_task();

    /* Create another higher priority task to be added in xPendingReadyList. */
    create_task_priority = 4;
    task_handle2 = create_task();

    ptcb = ( TCB_t * ) task_handle;
    pxCurrentTCB = ( TCB_t * ) task_handle;

    /* Expectations */
    /* xTaskResumeAll */
    /* prvResetNextTaskUnblockTime */
    uxListRemove_ExpectAndReturn( &ptcb->xStateListItem, 0 );
    listSET_LIST_ITEM_VALUE_Expect( &ptcb->xStateListItem,
                                    ( ( previousWakeTime - 1 ) ) );
    vListInsert_Expect( pxOverflowDelayedTaskList, &ptcb->xStateListItem );

    /* xTaskResumeAll */
    listLIST_IS_EMPTY_ExpectAndReturn( &xPendingReadyList, pdFALSE );
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAndReturn( &xPendingReadyList, task_handle2 );
    listREMOVE_ITEM_Expect( &( task_handle2->xEventListItem ) );
    listREMOVE_ITEM_Expect( &( task_handle2->xStateListItem ) );
    /* prvAddTaskToReadyList */
    listINSERT_END_Expect( &pxReadyTasksLists[ task_handle2->uxPriority ],
                           &task_handle2->xStateListItem );
    /* back to xTaskResumeAll */
    listLIST_IS_EMPTY_ExpectAndReturn( &xPendingReadyList, pdTRUE );
    /* prvResetNextTaskUnblockTime */
    listLIST_IS_EMPTY_ExpectAndReturn( pxDelayedTaskList, pdTRUE );
    /* API Call */
    ret_xtask_delay = xTaskDelayUntil( &previousWakeTime, xTimeIncrement );
    /* Validations */
    ASSERT_PORT_YIELD_WITHIN_API_CALLED();
    TEST_ASSERT_TRUE( ret_xtask_delay );
}

/* ----------------------- testing INCLUDE_vTaskSuspend ----------------------*/
void test_vTaskSuspend_success( void )
{
    TaskHandle_t task_handle;

    task_handle = create_task();
    ptcb = task_handle;
    TEST_ASSERT_EQUAL_PTR( ptcb, pxCurrentTCB );
    xSchedulerRunning = pdFALSE;
    /* Expectations */
    uxListRemove_ExpectAndReturn( &ptcb->xStateListItem, 0 );
    /* taskRESET_READY_PRIORITY */
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &pxReadyTasksLists[ ptcb->uxPriority ],
                                             0 );
    /* back */
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem, NULL );
    vListInsertEnd_Expect( &xSuspendedTaskList, &ptcb->xStateListItem );
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &xSuspendedTaskList,
                                             uxCurrentNumberOfTasks );
    /* API Call */
    vTaskSuspend( task_handle );
    /* Validations */
    TEST_ASSERT_EQUAL_PTR( NULL, pxCurrentTCB );
    ASSERT_PORT_YIELD_WITHIN_API_NOT_CALLED();
}

void test_vTaskSuspend_success_sched_running( void )
{
    TaskHandle_t task_handle;

    task_handle = create_task();
    ptcb = task_handle;
    TEST_ASSERT_EQUAL_PTR( ptcb, pxCurrentTCB );
    xSchedulerRunning = pdTRUE;
    /* Expectations */
    uxListRemove_ExpectAndReturn( &ptcb->xStateListItem, 0 );
    /* taskRESET_READY_PRIORITY */
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &pxReadyTasksLists[ ptcb->uxPriority ],
                                             0 );
    /* back */
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem, NULL );
    vListInsertEnd_Expect( &xSuspendedTaskList, &ptcb->xStateListItem );
    /* prvResetNextTaskUnblockTime */
    listLIST_IS_EMPTY_ExpectAndReturn( pxDelayedTaskList, pdTRUE );
    /* API Call */
    vTaskSuspend( task_handle );
    /* Validations */
    TEST_ASSERT_EQUAL( portMAX_DELAY, xNextTaskUnblockTime );
    ASSERT_PORT_YIELD_WITHIN_API_CALLED();
}

void test_vTaskSuspend_success_sched_running_not_curr( void )
{
    TaskHandle_t task_handle, task_handle2;

    create_task_priority = 3;
    task_handle = create_task();
    create_task_priority = 5;
    task_handle2 = create_task();
    ptcb = task_handle;
    TEST_ASSERT_EQUAL_PTR( task_handle2, pxCurrentTCB );
    xSchedulerRunning = pdTRUE;
    /* Expectations */
    uxListRemove_ExpectAndReturn( &ptcb->xStateListItem, 0 );
    /* taskRESET_READY_PRIORITY */
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &pxReadyTasksLists[ ptcb->uxPriority ],
                                             1 );
    /* back */
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem, NULL );
    vListInsertEnd_Expect( &xSuspendedTaskList, &ptcb->xStateListItem );
    /* prvResetNextTaskUnblockTime */
    listLIST_IS_EMPTY_ExpectAndReturn( pxDelayedTaskList, pdTRUE );
    /* API Call */
    vTaskSuspend( task_handle );
    /* Validations */
    TEST_ASSERT_EQUAL( portMAX_DELAY, xNextTaskUnblockTime );
    ASSERT_PORT_YIELD_WITHIN_API_NOT_CALLED();
}

void test_vTaskSuspend_success_switch_context( void )
{
    TaskHandle_t task_handle;

    task_handle = create_task();
    ptcb = task_handle;
    TEST_ASSERT_EQUAL_PTR( ptcb, pxCurrentTCB );
    xSchedulerRunning = pdFALSE;
    uxSchedulerSuspended = pdTRUE;
    ptcb->ucNotifyState[ 0 ] = 1; /* taskWAITING_NOTIFICATION */
    /* Expectations */
    uxListRemove_ExpectAndReturn( &ptcb->xStateListItem, 1 );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem,
                                             &xSuspendedTaskList );
    uxListRemove_ExpectAndReturn( &ptcb->xEventListItem, pdTRUE );
    vListInsertEnd_Expect( &xSuspendedTaskList, &ptcb->xStateListItem );
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &xSuspendedTaskList,
                                             uxCurrentNumberOfTasks + 1 );
    /* API Call */
    vTaskSuspend( NULL );
    /* Validations */
    ASSERT_PORT_YIELD_WITHIN_API_NOT_CALLED();
    TEST_ASSERT_EQUAL( 0, ptcb->ucNotifyState[ 0 ] );
}

void test_vTaskResume_fail_null_handle( void )
{
    vTaskResume( NULL );
    ASSERT_PORT_YIELD_WITHIN_API_NOT_CALLED();
}

void test_vTaskResume_fail_current_tcb_null( void )
{
    create_task();
    vTaskResume( NULL );
    ASSERT_PORT_YIELD_WITHIN_API_NOT_CALLED();
}

void test_vTaskResume_fail_current_tcb( void )
{
    TaskHandle_t task_handle;

    task_handle = create_task();
    vTaskResume( task_handle );
    ASSERT_PORT_YIELD_WITHIN_API_NOT_CALLED();
}

void test_vTaskResume_fail_task_not_suspended( void )
{
    TaskHandle_t task_handle;

    create_task_priority = 3;
    task_handle = create_task();
    create_task_priority = 5;
    create_task();
    ptcb = task_handle;
    /* Expectations */
    /* prvTaskIsTaskSuspended */
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &xSuspendedTaskList,
                                             &ptcb->xStateListItem,
                                             pdFALSE );
    /* API Call */
    vTaskResume( task_handle ); /* not current tcb */
    /* Validations */
    ASSERT_PORT_YIELD_WITHIN_API_NOT_CALLED();
}

void test_vTaskResume_fail_task_ready( void )
{
    TaskHandle_t task_handle;

    create_task_priority = 3;
    task_handle = create_task();
    create_task_priority = 5;
    create_task();
    ptcb = task_handle;
    /* Expectations */
    /* prvTaskIsTaskSuspended */
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &xSuspendedTaskList,
                                             &ptcb->xStateListItem,
                                             pdTRUE );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &xPendingReadyList,
                                             &ptcb->xEventListItem,
                                             pdTRUE );
    /* API Call */
    vTaskResume( task_handle ); /* not current tcb */
    /* Validations */
    ASSERT_PORT_YIELD_WITHIN_API_NOT_CALLED();
}

void test_vTaskResume_fail_task_waiting_notify( void )
{
    UBaseType_t uxIndexToNotify = 2;
    TaskHandle_t task_handle;

    create_task_priority = 3;
    task_handle = create_task();
    create_task_priority = 5;
    create_task();
    ptcb = task_handle;
    ptcb->ucNotifyState[ uxIndexToNotify ] = taskWAITING_NOTIFICATION;
    /* Expectations */
    /* prvTaskIsTaskSuspended */
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &xSuspendedTaskList,
                                             &ptcb->xStateListItem,
                                             pdTRUE );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &xPendingReadyList,
                                             &ptcb->xEventListItem,
                                             pdFALSE );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( NULL,
                                             &ptcb->xEventListItem,
                                             pdTRUE );
    /* API Call */
    vTaskResume( task_handle ); /* not current tcb */
    /* Validations */
    ASSERT_PORT_YIELD_WITHIN_API_NOT_CALLED();

    ptcb->ucNotifyState[ uxIndexToNotify ] = taskWAITING_NOTIFICATION;
}

void test_vTaskResume_fail_task_event_list_not_orphan( void )
{
    TaskHandle_t task_handle;

    create_task_priority = 3;
    task_handle = create_task();
    create_task_priority = 5;
    create_task();
    ptcb = task_handle;
    /* Expectations */
    /* prvTaskIsTaskSuspended */
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &xSuspendedTaskList,
                                             &ptcb->xStateListItem,
                                             pdTRUE );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &xPendingReadyList,
                                             &ptcb->xEventListItem,
                                             pdFALSE );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( NULL,
                                             &ptcb->xEventListItem,
                                             pdFALSE );
    /* API Call */
    vTaskResume( task_handle ); /* not current tcb */
    /* Validations */
    ASSERT_PORT_YIELD_WITHIN_API_NOT_CALLED();
}

void test_vTaskResume_success_task_event_list_orphan( void )
{
    TaskHandle_t task_handle;

    create_task_priority = 3;
    task_handle = create_task();
    create_task_priority = 5;
    create_task();
    ptcb = task_handle;
    /* Expectations */
    /* prvTaskIsTaskSuspended */
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &xSuspendedTaskList,
                                             &ptcb->xStateListItem,
                                             pdTRUE );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &xPendingReadyList,
                                             &ptcb->xEventListItem,
                                             pdFALSE );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( NULL,
                                             &ptcb->xEventListItem,
                                             pdTRUE );
    /* back */
    uxListRemove_ExpectAndReturn( &ptcb->xStateListItem, pdTRUE );
    /* prvAddTaskToReadyList*/
    listINSERT_END_Expect( &pxReadyTasksLists[ 3 ],
                           &ptcb->xStateListItem );
    /* API Call */
    vTaskResume( task_handle ); /* not current tcb */
    /* Validations */
    ASSERT_PORT_YIELD_WITHIN_API_NOT_CALLED();
}

/* Test the scenario that current running task will be preempted if a higher priority
 * task is resumed. */
void test_vTaskResume_success_yield( void )
{
    TaskHandle_t task_handle;
    TaskHandle_t task_handle2;

    create_task_priority = 4;
    task_handle = create_task();
    create_task_priority = 3;
    task_handle2 = create_task();
    ptcb = task_handle;
    /* Expectations */
    /* prvTaskIsTaskSuspended */
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &xSuspendedTaskList,
                                             &ptcb->xStateListItem,
                                             pdTRUE );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &xPendingReadyList,
                                             &ptcb->xEventListItem,
                                             pdFALSE );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( NULL,
                                             &ptcb->xEventListItem,
                                             pdTRUE );

    /* Current running task should be task_handle2 now. */
    pxCurrentTCB = task_handle2;

    /* back */
    uxListRemove_ExpectAndReturn( &ptcb->xStateListItem, pdTRUE );
    /* prvAddTaskToReadyList*/
    listINSERT_END_Expect( &pxReadyTasksLists[ 4 ],
                           &ptcb->xStateListItem );
    /* API Call */
    vTaskResume( task_handle ); /* not current tcb */

    /* Validations */
    ASSERT_PORT_YIELD_WITHIN_API_CALLED();
}


/* Test the scenario that current running task will not be preempted if a equal
 * priority task is resumed. */
void test_vTaskResume_success_eq_curr_prio_not_yield( void )
{
    TaskHandle_t task_handle;
    TaskHandle_t task_handle2;

    create_task_priority = 3;
    task_handle = create_task();
    create_task_priority = 3;
    task_handle2 = create_task();
    ptcb = task_handle;
    /* Expectations */
    /* prvTaskIsTaskSuspended */
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &xSuspendedTaskList,
                                             &ptcb->xStateListItem,
                                             pdTRUE );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &xPendingReadyList,
                                             &ptcb->xEventListItem,
                                             pdFALSE );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( NULL,
                                             &ptcb->xEventListItem,
                                             pdTRUE );

    /* Current running task should be task_handle2 now. */
    pxCurrentTCB = task_handle2;

    /* back */
    uxListRemove_ExpectAndReturn( &ptcb->xStateListItem, pdTRUE );
    /* prvAddTaskToReadyList*/
    listINSERT_END_Expect( &pxReadyTasksLists[ 3 ],
                           &ptcb->xStateListItem );
    /* API Call */
    vTaskResume( task_handle ); /* not current tcb */

    /* Resuming a task with equal priority. */
    ASSERT_PORT_YIELD_WITHIN_API_NOT_CALLED();
}

void test_xTaskResumeFromISR_success( void )
{
    TaskHandle_t task_handle;
    TaskHandle_t task_handle2;
    BaseType_t ret_task_resume;

    create_task_priority = 3;
    task_handle = create_task();

    /* Create another higher priority task to be resumed. */
    create_task_priority = 4;
    task_handle2 = create_task();

    ptcb = task_handle;
    pxCurrentTCB = task_handle;
    /* Expectations */
    /* prvTaskIsTaskSuspended */
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &xSuspendedTaskList,
                                             &task_handle2->xStateListItem,
                                             pdTRUE );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &xPendingReadyList,
                                             &task_handle2->xEventListItem,
                                             pdFALSE );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( NULL,
                                             &task_handle2->xEventListItem,
                                             pdTRUE );
    /* back */
    uxListRemove_ExpectAndReturn( &task_handle2->xStateListItem, pdTRUE );
    /* prvAddTaskToReadyList */
    listINSERT_END_Expect( &pxReadyTasksLists[ create_task_priority ],
                           &task_handle2->xStateListItem );
    /* API Call */
    ret_task_resume = xTaskResumeFromISR( task_handle2 );

    /* Validations */
    TEST_ASSERT_EQUAL( pdTRUE, ret_task_resume );
    ASSERT_INVALID_INTERRUPT_PRIORITY_CALLED();
    ASSERT_PORT_CLEAR_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_PORT_SET_INTERRUPT_FROM_ISR_CALLED();
}

void test_xTaskResumeFromISR_success_sched_suspended( void )
{
    TaskHandle_t task_handle;
    BaseType_t ret_task_resume;

    uxSchedulerSuspended = pdTRUE;
    create_task_priority = 3;
    task_handle = create_task();
    ptcb = task_handle;
    /* Expectations */
    /* prvTaskIsTaskSuspended */
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &xSuspendedTaskList,
                                             &ptcb->xStateListItem,
                                             pdTRUE );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &xPendingReadyList,
                                             &ptcb->xEventListItem,
                                             pdFALSE );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( NULL,
                                             &ptcb->xEventListItem,
                                             pdTRUE );
    /* back */
    vListInsertEnd_Expect( &xPendingReadyList, &ptcb->xEventListItem );
    /* API Call */
    ret_task_resume = xTaskResumeFromISR( task_handle );

    /* Validations */
    TEST_ASSERT_EQUAL( pdFALSE, ret_task_resume );
    ASSERT_INVALID_INTERRUPT_PRIORITY_CALLED();
    ASSERT_PORT_CLEAR_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_PORT_SET_INTERRUPT_FROM_ISR_CALLED();
}

void test_xTaskResumeFromISR_success_task_suspended( void )
{
    TaskHandle_t task_handle;
    BaseType_t ret_task_resume;

    uxSchedulerSuspended = pdTRUE;
    create_task_priority = 3;
    task_handle = create_task();
    ptcb = task_handle;
    /* Expectations */
    /* prvTaskIsTaskSuspended */
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &xSuspendedTaskList,
                                             &ptcb->xStateListItem,
                                             pdFALSE );
    /* API Call */
    ret_task_resume = xTaskResumeFromISR( task_handle );

    /* Validations */
    TEST_ASSERT_EQUAL( pdFALSE, ret_task_resume );
    ASSERT_INVALID_INTERRUPT_PRIORITY_CALLED();
    ASSERT_PORT_CLEAR_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_PORT_SET_INTERRUPT_FROM_ISR_CALLED();
}

void test_xTaskResumeFromISR_success_curr_prio_lt_suspended_task( void )
{
    TaskHandle_t task_handle;
    BaseType_t ret_task_resume;

    uxSchedulerSuspended = pdFALSE;
    create_task_priority = 3;
    task_handle = create_task();
    create_task_priority = 4;
    create_task();
    ptcb = task_handle;
    /* Expectations */
    /* prvTaskIsTaskSuspended */
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &xSuspendedTaskList,
                                             &ptcb->xStateListItem,
                                             pdTRUE );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &xPendingReadyList,
                                             &ptcb->xEventListItem,
                                             pdFALSE );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( NULL,
                                             &ptcb->xEventListItem,
                                             pdTRUE );
    /* back */
    uxListRemove_ExpectAndReturn( &ptcb->xStateListItem, pdTRUE );
    /* prvAddTaskToReadyList */
    listINSERT_END_Expect( &pxReadyTasksLists[ 3 ],
                           &ptcb->xStateListItem );
    /* API Call */
    ret_task_resume = xTaskResumeFromISR( task_handle );

    /* Validations */
    TEST_ASSERT_EQUAL( pdFALSE, ret_task_resume );
    ASSERT_INVALID_INTERRUPT_PRIORITY_CALLED();
    ASSERT_PORT_CLEAR_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_PORT_SET_INTERRUPT_FROM_ISR_CALLED();
}

/* Test the scenario that resuming a suspended task from ISR doesn't preempt current
 * running task or equal priority. */
void test_xTaskResumeFromISR_success_curr_prio_eq_suspended_task( void )
{
    TaskHandle_t task_handle;
    BaseType_t ret_task_resume;

    uxSchedulerSuspended = pdFALSE;

    /* Create a task to be added to the xPendingReadyList. */
    create_task_priority = 3;
    task_handle = create_task();

    /* Create a running task with the same priority. */
    create_task_priority = 3;
    create_task();
    ptcb = task_handle;
    /* Expectations */
    /* prvTaskIsTaskSuspended */
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &xSuspendedTaskList,
                                             &ptcb->xStateListItem,
                                             pdTRUE );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &xPendingReadyList,
                                             &ptcb->xEventListItem,
                                             pdFALSE );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( NULL,
                                             &ptcb->xEventListItem,
                                             pdTRUE );
    /* back */
    uxListRemove_ExpectAndReturn( &ptcb->xStateListItem, pdTRUE );
    /* prvAddTaskToReadyList */
    listINSERT_END_Expect( &pxReadyTasksLists[ create_task_priority ],
                           &ptcb->xStateListItem );
    /* API Call */
    ret_task_resume = xTaskResumeFromISR( task_handle );

    /* Validations */
    TEST_ASSERT_EQUAL( pdFALSE, ret_task_resume );
    ASSERT_INVALID_INTERRUPT_PRIORITY_CALLED();
    ASSERT_PORT_CLEAR_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_PORT_SET_INTERRUPT_FROM_ISR_CALLED();
}

/* testing INCLUDE_xTaskGetHandle */


void test_xtaskGetHandle_success( void )
{
    TaskHandle_t task_handle = NULL, task_handle2;
    ListItem_t list_item;

    task_handle = create_task();
    ptcb = task_handle;
    INITIALIZE_LIST_1E( pxReadyTasksLists[ configMAX_PRIORITIES - 1 ],
                        list_item,
                        ptcb );
    /* Expectations */
    /*  prvSearchForNameWithinSingleList */
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &pxReadyTasksLists[ configMAX_PRIORITIES - 1 ],
                                             1 );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &list_item, ptcb );

    /* vTaskResumeAll */
    listLIST_IS_EMPTY_ExpectAndReturn( &xPendingReadyList, pdTRUE );

    /* API Call */
    task_handle2 = xTaskGetHandle( "create_task" );
    /* Validations */
    TEST_ASSERT_EQUAL_PTR( task_handle, task_handle2 );
}

void test_xtaskGetHandle_success_2elements( void )
{
    TaskHandle_t task_handle = NULL, task_handle2, ret_task_handle;
    ListItem_t list_item, list_item2;

    task_handle = create_task();
    task_handle2 = create_task();
    strcpy( task_handle2->pcTaskName, "task2" );
    ptcb = task_handle;
    INITIALIZE_LIST_2E( pxReadyTasksLists[ configMAX_PRIORITIES - 1 ],
                        list_item, list_item2,
                        ptcb, task_handle2 );

    /* Expectations */
    /*  prvSearchForNameWithinSingleList */
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &pxReadyTasksLists[ configMAX_PRIORITIES - 1 ],
                                             2 );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &list_item, task_handle );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &list_item2, task_handle2 );

    /* vTaskResumeAll */
    listLIST_IS_EMPTY_ExpectAndReturn( &xPendingReadyList, pdTRUE );

    /* API Call */
    ret_task_handle = xTaskGetHandle( "task2" );

    /* Validations */
    TEST_ASSERT_EQUAL_PTR( task_handle2, ret_task_handle );
}

void test_xtaskGetHandle_success_2elements_set_index( void )
{
    TaskHandle_t task_handle = NULL, task_handle2, ret_task_handle;
    ListItem_t list_item, list_item2;

    task_handle = create_task();
    task_handle2 = create_task();
    strcpy( task_handle2->pcTaskName, "task2" );
    ptcb = task_handle;
    INITIALIZE_LIST_2E( pxReadyTasksLists[ configMAX_PRIORITIES - 1 ],
                        list_item, list_item2,
                        task_handle, task_handle2 );
    /* advance index */
    pxReadyTasksLists[ configMAX_PRIORITIES - 1 ].pxIndex =
        pxReadyTasksLists[ configMAX_PRIORITIES - 1 ].pxIndex->pxNext;
    /* advance index */
    pxReadyTasksLists[ configMAX_PRIORITIES - 1 ].pxIndex =
        pxReadyTasksLists[ configMAX_PRIORITIES - 1 ].pxIndex->pxNext;

    /* Expectations */
    /*  prvSearchForNameWithinSingleList */
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &pxReadyTasksLists[ configMAX_PRIORITIES - 1 ],
                                             1 );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &list_item, task_handle );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &list_item2, task_handle2 );

    /* vTaskResumeAll */
    listLIST_IS_EMPTY_ExpectAndReturn( &xPendingReadyList, pdTRUE );

    /* API Call */
    ret_task_handle = xTaskGetHandle( "task2" );
    /* Validations */
    TEST_ASSERT_EQUAL_PTR( task_handle2, ret_task_handle );
}

void test_xtaskGetHandle_fail_no_task_found( void )
{
    TaskHandle_t task_handle, task_handle2, ret_task_handle;
    ListItem_t list_item, list_item2;

    task_handle = create_task();
    task_handle2 = create_task();
    ptcb = task_handle;
    INITIALIZE_LIST_2E( pxReadyTasksLists[ configMAX_PRIORITIES - 1 ],
                        list_item, list_item2,
                        ptcb, task_handle2 );
    /* Expectations */
    /*  prvSearchForNameWithinSingleList */
    listCURRENT_LIST_LENGTH_ExpectAndReturn(
        &pxReadyTasksLists[ configMAX_PRIORITIES - 1 ],
        2 );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &list_item, task_handle );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &list_item2, task_handle2 );

    int i = configMAX_PRIORITIES - 1;

    do
    {
        i--;
        listCURRENT_LIST_LENGTH_ExpectAndReturn( &pxReadyTasksLists[ i ],
                                                 0 );
    } while( i > tskIDLE_PRIORITY );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( pxDelayedTaskList, 0 );
    listCURRENT_LIST_LENGTH_ExpectAndReturn( pxOverflowDelayedTaskList, 0 );
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &xSuspendedTaskList, 0 );
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &xTasksWaitingTermination, 0 );

    /* vTaskResumeAll */
    listLIST_IS_EMPTY_ExpectAndReturn( &xPendingReadyList, pdTRUE );

    /* API Call */
    ret_task_handle = xTaskGetHandle( "create_tasks" );
    /* Validations */
    TEST_ASSERT_EQUAL_PTR( NULL, ret_task_handle );
}


void test_xtaskGetHandle_fail_no_tasks_running( void )
{
    TaskHandle_t task_handle2;

    /* Expectations */
    /*  prvSearchForNameWithinSingleList */
    for( int i = configMAX_PRIORITIES; i > tskIDLE_PRIORITY; --i )
    {
        listCURRENT_LIST_LENGTH_ExpectAndReturn( &pxReadyTasksLists[ i - 1 ], 0 );
    }

    listCURRENT_LIST_LENGTH_ExpectAndReturn( pxDelayedTaskList, 0 );
    listCURRENT_LIST_LENGTH_ExpectAndReturn( pxOverflowDelayedTaskList, 0 );
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &xSuspendedTaskList, 0 );
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &xTasksWaitingTermination, 0 );
    /* API Call */
    task_handle2 = xTaskGetHandle( "create_task" );
    /* Validations */
    TEST_ASSERT_EQUAL_PTR( NULL, task_handle2 );
}

/* testing always available functions */
void test_xTaskGetTickCount_success( void )
{
    TickType_t ret_get_tick_count;

    xTickCount = 565656;
    ret_get_tick_count = xTaskGetTickCount();
    TEST_ASSERT_EQUAL( 565656, ret_get_tick_count );
}

void test_xTaskGetTickCountFromISR_success( void )
{
    TickType_t ret_get_tick_count;

    /* Setup */
    xTickCount = 565656;
    /* Expectations */
    /* API Call */
    ret_get_tick_count = xTaskGetTickCountFromISR();
    /* Validations */
    TEST_ASSERT_EQUAL( 565656, ret_get_tick_count );
    ASSERT_INVALID_INTERRUPT_PRIORITY_CALLED();
    ASSERT_PORT_CLEAR_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_PORT_SET_INTERRUPT_FROM_ISR_CALLED();
}

void test_uxTaskGetNumberOfTasks_success( void )
{
    UBaseType_t ret_task_num;

    create_task();
    create_task();
    create_task();

    ret_task_num = uxTaskGetNumberOfTasks();

    TEST_ASSERT_EQUAL( 3, ret_task_num );
}

void test_pcTaskGetName_success( void )
{
    char * ret_task_name;
    TaskHandle_t task_handle;

    task_handle = create_task();

    ret_task_name = pcTaskGetName( task_handle );
    TEST_ASSERT_EQUAL_STRING( "create_task", ret_task_name );
}

void test_pcTaskGetName_success_null_handle( void )
{
    char * ret_task_name;

    create_task();

    ret_task_name = pcTaskGetName( NULL );
    TEST_ASSERT_EQUAL_STRING( "create_task", ret_task_name );
}

void test_xTaskCatchUpTicks( void )
{
    BaseType_t ret_taskCatchUpTicks;
    TaskHandle_t task_handle;

    task_handle = create_task();
    ptcb = task_handle;
    uxSchedulerSuspended = pdFALSE;

    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 0 );

    /* API Call */
    ret_taskCatchUpTicks = xTaskCatchUpTicks( 1 );
    /* Validations */
    TEST_ASSERT_EQUAL( pdFALSE, ret_taskCatchUpTicks );
    /*TEST_ASSERT_EQUAL( pdTRUE, ret_taskCatchUpTicks ); */
    uxSchedulerSuspended = pdTRUE;
}

void test_xTaskIncrementTick_success_sched_suspended_no_switch( void )
{
    BaseType_t ret_task_incrementtick;
    TickType_t current_ticks = xPendedTicks;

    vTaskSuspendAll();

    /* API Call */
    ret_task_incrementtick = xTaskIncrementTick();
    /* Validations */
    TEST_ASSERT_EQUAL( pdFALSE, ret_task_incrementtick );
    TEST_ASSERT_EQUAL( current_ticks + 1, xPendedTicks );
    ASSERT_APP_TICK_HOOK_CALLED();
}

/* ensures that the delayed task list and overflow list are switched when a
 * tickcount overflow occurs */
void test_xTaskIncrementTick_success_tickCount_overlow( void )
{
    BaseType_t ret_task_incrementtick;
    List_t * delayed, * overflow;

    uxSchedulerSuspended = pdFALSE;
    delayed = pxDelayedTaskList;
    overflow = pxOverflowDelayedTaskList;
    xTickCount = UINT32_MAX; /* overflowed */
    create_task();
    /* Expectations */
    /* taskSWITCH_DELAYED_LISTS */
    listLIST_IS_EMPTY_ExpectAndReturn( pxDelayedTaskList, pdTRUE );
    /* back */
    listLIST_IS_EMPTY_ExpectAndReturn( pxOverflowDelayedTaskList, pdTRUE );
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &pxReadyTasksLists[ pxCurrentTCB->uxPriority ],
                                             2 );
    /* API Call */
    ret_task_incrementtick = xTaskIncrementTick();

    /* Validations */
    TEST_ASSERT_EQUAL( pdTRUE, ret_task_incrementtick );
    ASSERT_APP_TICK_HOOK_CALLED();
    /* make sure the lists are swapped on overflow */
    TEST_ASSERT_EQUAL_PTR( pxOverflowDelayedTaskList, delayed );
    TEST_ASSERT_EQUAL_PTR( pxDelayedTaskList, overflow );
    TEST_ASSERT_EQUAL( 1, xNumOfOverflows );
    TEST_ASSERT_EQUAL( portMAX_DELAY, xNextTaskUnblockTime );
}

void test_xTaskIncrementTick_success_no_switch( void )
{
    BaseType_t ret_task_incrementtick;
    TaskHandle_t task_handle;

    /* setup */
    task_handle = create_task();
    ptcb = task_handle;

    /* Expectations */
    listLIST_IS_EMPTY_ExpectAndReturn( pxDelayedTaskList, pdTRUE );
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &pxReadyTasksLists[ ptcb->uxPriority ],
                                             1 );

    /* API Call */
    ret_task_incrementtick = xTaskIncrementTick();

    /* Validations */
    TEST_ASSERT_EQUAL( pdFALSE, ret_task_incrementtick );
    TEST_ASSERT_EQUAL( portMAX_DELAY, xNextTaskUnblockTime );
    ASSERT_APP_TICK_HOOK_CALLED();
}

void test_xTaskIncrementTick_success_switch( void )
{
    BaseType_t ret_task_incrementtick;
    TaskHandle_t task_handle;

    /* setup */
    task_handle = create_task();
    ptcb = task_handle;
    xPendedTicks = 3;
    xTickCount = UINT32_MAX;

    /* Expectations */
    /* taskSWITCH_DELAYED_LISTS(); */
    listLIST_IS_EMPTY_ExpectAndReturn( pxDelayedTaskList, pdTRUE );
    listLIST_IS_EMPTY_ExpectAndReturn( pxOverflowDelayedTaskList, pdTRUE );
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &pxReadyTasksLists[ ptcb->uxPriority ],
                                             3 );

    /* API Call */
    ret_task_incrementtick = xTaskIncrementTick();

    /* Validations */
    TEST_ASSERT_EQUAL( pdTRUE, ret_task_incrementtick );
    ASSERT_APP_TICK_HOOK_NOT_CALLED();
    TEST_ASSERT_EQUAL( portMAX_DELAY, xNextTaskUnblockTime );
}

void test_xTaskIncrementTick_success_update_next_unblock( void )
{
    BaseType_t ret_task_incrementtick;
    TaskHandle_t task_handle;
    TaskHandle_t task_handle2;

    /* setup */
    task_handle = create_task();
    task_handle2 = create_task();
    ptcb = task_handle;
    xPendedTicks = 3;
    xTickCount = 50;
    xNextTaskUnblockTime = 49; /* tasks due unblocking */
    uxSchedulerSuspended = pdFALSE;

    /* Expectations */
    listLIST_IS_EMPTY_ExpectAndReturn( pxDelayedTaskList, pdFALSE );
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAndReturn( pxDelayedTaskList, task_handle2 );
    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &task_handle2->xStateListItem,
                                             xTickCount + 5 );
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &pxReadyTasksLists[ ptcb->uxPriority ],
                                             3 );

    /* API Call */
    ret_task_incrementtick = xTaskIncrementTick();

    /* Validations */
    TEST_ASSERT_EQUAL( pdTRUE, ret_task_incrementtick );
    ASSERT_APP_TICK_HOOK_NOT_CALLED();
    TEST_ASSERT_EQUAL( xTickCount + 4, xNextTaskUnblockTime );
}

/* Tests the scenario when a task with priority equal to the
 * currently executing task is unblocked as a result of the
 * xTaskIncrementTick call. Also, xPendedTicks is set to
 * non-zero to ensure that tick hook is not called. */
void test_xTaskIncrementTick_success_unblock_tasks( void )
{
    BaseType_t ret_task_incrementtick;
    TaskHandle_t task_handle;
    TaskHandle_t task_handle2;

    /* setup */
    create_task_priority = 4;
    task_handle = create_task();
    create_task_priority = 4;
    task_handle2 = create_task();
    ptcb = task_handle;
    xPendedTicks = 3;
    xTickCount = 50;
    xNextTaskUnblockTime = 49; /* tasks due unblocking */
    uxSchedulerSuspended = pdFALSE;

    /* Expectations */
    listLIST_IS_EMPTY_ExpectAndReturn( pxDelayedTaskList, pdFALSE );
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAndReturn( pxDelayedTaskList, task_handle2 );
    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &task_handle2->xStateListItem,
                                             xTickCount - 5 );
    listREMOVE_ITEM_Expect( &( task_handle2->xStateListItem ) );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &task_handle2->xEventListItem, NULL );
    /* prvAddTaskToReadyList */
    listINSERT_END_Expect( &pxReadyTasksLists[ task_handle2->uxPriority ],
                           &task_handle2->xStateListItem );
    listLIST_IS_EMPTY_ExpectAndReturn( pxDelayedTaskList, pdTRUE );
    /* back */
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &pxReadyTasksLists[ ptcb->uxPriority ],
                                             2 );

    /* API Call */
    ret_task_incrementtick = xTaskIncrementTick();

    /* Validations */
    TEST_ASSERT_EQUAL( pdTRUE, ret_task_incrementtick );
    ASSERT_APP_TICK_HOOK_NOT_CALLED();
    TEST_ASSERT_EQUAL( portMAX_DELAY, xNextTaskUnblockTime );
}

/* Tests the scenario when a task with priority equal to the
 * currently executing task is unblocked as a result of the
 * xTaskIncrementTick call. Also, xPendedTicks is set to 0 to
 * ensure that tick hook is called. */
void test_xTaskIncrementTick_success_unblock_tasks2( void )
{
    BaseType_t ret_task_incrementtick;
    TaskHandle_t task_handle;
    TaskHandle_t task_handle2;

    /* setup */
    task_handle = create_task();
    create_task_priority = 2;
    task_handle2 = create_task();
    ptcb = task_handle;
    xPendedTicks = 0;
    xTickCount = 50;
    xNextTaskUnblockTime = 49; /* tasks due unblocking */
    uxSchedulerSuspended = pdFALSE;
    vTaskMissedYield();

    /* Expectations */
    listLIST_IS_EMPTY_ExpectAndReturn( pxDelayedTaskList, pdFALSE );
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAndReturn( pxDelayedTaskList, task_handle2 );
    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &task_handle2->xStateListItem,
                                             xTickCount - 5 );
    listREMOVE_ITEM_Expect( &( task_handle2->xStateListItem ) );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &task_handle2->xEventListItem,
                                             &xPendingReadyList );
    listREMOVE_ITEM_Expect( &( task_handle2->xEventListItem ) );
    /* prvAddTaskToReadyList */
    listINSERT_END_Expect( &pxReadyTasksLists[ task_handle2->uxPriority ],
                           &task_handle2->xStateListItem );
    listLIST_IS_EMPTY_ExpectAndReturn( pxDelayedTaskList, pdTRUE );
    /* back */
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &pxReadyTasksLists[ ptcb->uxPriority ],
                                             1 );

    /* API Call */
    ret_task_incrementtick = xTaskIncrementTick();

    /* Validations */
    TEST_ASSERT_EQUAL( pdTRUE, ret_task_incrementtick );
    ASSERT_APP_TICK_HOOK_CALLED();
    TEST_ASSERT_EQUAL( portMAX_DELAY, xNextTaskUnblockTime );
}

/**
 * @brief xTaskIncrementTick - Ready a higher priority delayed task.
 *
 * Ready a higher priority delayed task. Verify the return value is pdTRUE.
 *
 * <b>Coverage</b>
 * @code{c}
 * if( pxTCB->uxPriority > pxCurrentTCB->uxPriority )
 * {
 *     xSwitchRequired = pdTRUE;
 * }
 * else
 * {
 *     mtCOVERAGE_TEST_MARKER();
 * }
 * @endcode
 * ( pxTCB->uxPriority > pxCurrentTCB->uxPriority ) is true.
 */
void test_xTaskIncrementTick_success_unblock_higher_prio_task( void )
{
    BaseType_t ret_task_incrementtick;
    TaskHandle_t task_handle;
    TaskHandle_t task_handle2;

    /* setup */
    create_task_priority = 2;
    task_handle = create_task();
    create_task_priority = 1;
    task_handle2 = create_task();

    /* task_handle 2 will be added to pxDelayedTaskList later. To wakeup a higher priority
     * task, uxPriority is set higher than current task, which is 2. */
    task_handle2->uxPriority = 3;
    ptcb = task_handle;
    xPendedTicks = 0;
    xTickCount = 50;
    xNextTaskUnblockTime = 49; /* tasks due unblocking */
    uxSchedulerSuspended = pdFALSE;

    /* Expectations */
    listLIST_IS_EMPTY_ExpectAndReturn( pxDelayedTaskList, pdFALSE );
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAndReturn( pxDelayedTaskList, task_handle2 );
    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &task_handle2->xStateListItem,
                                             xTickCount - 5 );
    listREMOVE_ITEM_Expect( &( task_handle2->xStateListItem ) );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &task_handle2->xEventListItem,
                                             &xPendingReadyList );
    listREMOVE_ITEM_Expect( &( task_handle2->xEventListItem ) );
    /* prvAddTaskToReadyList */
    listINSERT_END_Expect( &pxReadyTasksLists[ task_handle2->uxPriority ],
                           &task_handle2->xStateListItem );
    listLIST_IS_EMPTY_ExpectAndReturn( pxDelayedTaskList, pdTRUE );
    /* back */
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &pxReadyTasksLists[ ptcb->uxPriority ],
                                             1 );

    /* API Call */
    ret_task_incrementtick = xTaskIncrementTick();

    /* Validations */
    TEST_ASSERT_EQUAL( pdTRUE, ret_task_incrementtick );
    ASSERT_APP_TICK_HOOK_CALLED();
    TEST_ASSERT_EQUAL( portMAX_DELAY, xNextTaskUnblockTime );
}

/* Tests the scenario when a task with priority higher than the
 * currently executing task is unblocked as a result of the
 * xTaskIncrementTick call. Also, xPendedTicks is set to
 * non-zero to ensure that tick hook is not called. */
void test_xTaskIncrementTick_success_unblock_tasks3( void )
{
    BaseType_t ret_task_incrementtick;
    TaskHandle_t task_handle;

    /* Setup. */
    create_task_priority = 4;
    task_handle = create_task();
    block_task( task_handle );
    create_task_priority = 3;
    ( void ) create_task();
    ptcb = task_handle;
    xPendedTicks = 3;
    xTickCount = 50;
    xNextTaskUnblockTime = 49; /* Task 2 is due unblocking. */
    uxSchedulerSuspended = pdFALSE;

    /* Expectations. */
    listLIST_IS_EMPTY_ExpectAndReturn( pxDelayedTaskList, pdFALSE );
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAndReturn( pxDelayedTaskList, task_handle );
    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &task_handle->xStateListItem,
                                             xTickCount - 5 );
    listREMOVE_ITEM_Expect( &( task_handle->xStateListItem ) );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &task_handle->xEventListItem, NULL );
    listINSERT_END_Expect( &pxReadyTasksLists[ task_handle->uxPriority ],
                           &task_handle->xStateListItem );
    listLIST_IS_EMPTY_ExpectAndReturn( pxDelayedTaskList, pdTRUE );
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &pxReadyTasksLists[ 3 ], 1 );

    /* API Call */
    ret_task_incrementtick = xTaskIncrementTick();

    /* Validations */
    TEST_ASSERT_EQUAL( pdTRUE, ret_task_incrementtick );
    ASSERT_APP_TICK_HOOK_NOT_CALLED();
    TEST_ASSERT_EQUAL( portMAX_DELAY, xNextTaskUnblockTime );
}

/* testing INCLUDE_xTaskAbortDelay */
void test_xTaskAbortDelay_fail_current_task( void )
{
    BaseType_t ret_taskabort_delay;
    TaskHandle_t task_handle;

    task_handle = create_task();
    ptcb = task_handle;

    /* Expectations */
    listLIST_IS_EMPTY_ExpectAndReturn( &xPendingReadyList, pdTRUE );
    /* API Call */
    ret_taskabort_delay = xTaskAbortDelay( task_handle );
    /* Validations */
    TEST_ASSERT_EQUAL( pdFALSE, ret_taskabort_delay );
    TEST_ASSERT_EQUAL( pdFALSE, ptcb->ucDelayAborted );
}

void test_xTaskAbortDelay_success( void )
{
    BaseType_t ret_taskabort_delay;
    TaskHandle_t task_handle;

    create_task_priority = 4;
    task_handle = create_task();
    ptcb = task_handle;
    create_task_priority = 5;
    create_task();

    /* Expectations */
    /* eTaskGetState */
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xStateListItem,
                                             pxDelayedTaskList );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem, NULL );
    /* back */
    uxListRemove_ExpectAndReturn( &tcb->xStateListItem, pdTRUE );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem, NULL );
    /* prvAddTaskToReadyList */
    listINSERT_END_Expect( &pxReadyTasksLists[ 4 ],
                           &ptcb->xStateListItem );
    /* xTaskResumeAll */
    listLIST_IS_EMPTY_ExpectAndReturn( &xPendingReadyList, pdTRUE );
    /* API Call */
    ret_taskabort_delay = xTaskAbortDelay( task_handle );
    /* Validations */
    TEST_ASSERT_EQUAL( pdTRUE, ret_taskabort_delay );
    TEST_ASSERT_EQUAL( pdFALSE, ptcb->ucDelayAborted );
}

void test_xTaskAbortDelay_success_notdelayed( void )
{
    BaseType_t ret_taskabort_delay;
    TaskHandle_t task_handle;
    TaskHandle_t task_handle2;

    create_task_priority = 6;
    task_handle = create_task();
    ptcb = task_handle;

    /* Expectations 1*/
    uxListRemove_ExpectAndReturn( &ptcb->xStateListItem, 1 );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem,
                                             &xSuspendedTaskList );
    uxListRemove_ExpectAndReturn( &ptcb->xEventListItem, pdTRUE );
    vListInsertEnd_Expect( &xSuspendedTaskList, &ptcb->xStateListItem );
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &xSuspendedTaskList,
                                             uxCurrentNumberOfTasks );
    TEST_ASSERT_EQUAL( pxCurrentTCB, task_handle );

    vTaskSuspend( task_handle );
    TEST_ASSERT_EQUAL( NULL, pxCurrentTCB );

    create_task_priority = 5;
    task_handle2 = create_task();
    TEST_ASSERT_EQUAL( pxCurrentTCB, task_handle2 );

    /* Expectations */
    /* eTaskGetState */
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xStateListItem,
                                             pxDelayedTaskList );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem,
                                             pxDelayedTaskList );
    /* back */
    uxListRemove_ExpectAndReturn( &tcb->xStateListItem, pdTRUE );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem,
                                             pxDelayedTaskList );
    uxListRemove_ExpectAndReturn( &ptcb->xEventListItem, pdTRUE );
    /* prvAddTaskToReadyList */
    listINSERT_END_Expect( &pxReadyTasksLists[ 6 ],
                           &ptcb->xStateListItem );
    /* xTaskResumeAll */
    listLIST_IS_EMPTY_ExpectAndReturn( &xPendingReadyList, pdTRUE );
    /* API Call */
    ret_taskabort_delay = xTaskAbortDelay( task_handle );
    /* Validations */
    TEST_ASSERT_TRUE( ret_taskabort_delay );
    TEST_ASSERT_TRUE( xYieldPending );
    TEST_ASSERT_TRUE( ptcb->ucDelayAborted );
}

/* ------------------ testing INCLUDE_xTaskGetIdleTaskHandle ---------------- */
void test_xTaskGetIdleTaskHandle_success( void )
{
    TaskHandle_t ret_idle_handle;
    int ret;

    start_scheduler();
    /* Api Call */
    ret_idle_handle = xTaskGetIdleTaskHandle();
    ptcb = ret_idle_handle;
    ret = strncmp( ptcb->pcTaskName, configIDLE_TASK_NAME, configMAX_TASK_NAME_LEN - 1 );
    TEST_ASSERT_EQUAL( 0, ret );
}


/* ----------------testing configUSE_APPLICATION_TASK_TAG ------------------- */
void test_vTaskSetApplicationTaskTag_current( void )
{
    create_task();

    vTaskSetApplicationTaskTag( NULL, pxHookFunction );

    TEST_ASSERT_EQUAL( &pxHookFunction, pxCurrentTCB->pxTaskTag );
}

void test_vTaskSetApplicationTaskTag_handle( void )
{
    TaskHandle_t task_handle;

    task_handle = create_task();

    vTaskSetApplicationTaskTag( task_handle, pxHookFunction );
    TEST_ASSERT_EQUAL( &pxHookFunction, task_handle->pxTaskTag );
}

void test_xTaskGetApplicationTaskTag_null_tcb_current( void )
{
    TaskHandle_t task_handle;

    task_handle = create_task();
    vTaskSetApplicationTaskTag( task_handle, pxHookFunction );

    TaskHookFunction_t hook_function;
    hook_function = xTaskGetApplicationTaskTag( NULL );

    TEST_ASSERT_EQUAL( &pxHookFunction, hook_function );
}

void test_xTaskGetApplicationTaskTag_tcb( void )
{
    TaskHandle_t task_handle;

    task_handle = create_task();
    vTaskSetApplicationTaskTag( task_handle, pxHookFunction );

    TaskHookFunction_t hook_function;
    hook_function = xTaskGetApplicationTaskTag( task_handle );

    TEST_ASSERT_EQUAL( &pxHookFunction, hook_function );
}

void test_xTaskGetApplicationTaskTag_no_hook_set( void )
{
    TaskHandle_t task_handle;

    task_handle = create_task();
    TaskHookFunction_t hook_function;

    hook_function = xTaskGetApplicationTaskTag( task_handle );

    TEST_ASSERT_EQUAL( NULL, hook_function );
}

void test_xTaskGetApplicationTaskTagFromISR_success( void )
{
    TaskHandle_t task_handle;

    task_handle = create_task();
    vTaskSetApplicationTaskTag( task_handle, pxHookFunction );

    TaskHookFunction_t hook_function;
    hook_function = xTaskGetApplicationTaskTagFromISR( task_handle );

    TEST_ASSERT_EQUAL( &pxHookFunction, hook_function );
    ASSERT_PORT_CLEAR_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_PORT_SET_INTERRUPT_FROM_ISR_CALLED();
}

void test_xTaskGetApplicationTaskTagFromISR_null_handle( void )
{
    TaskHandle_t task_handle;

    task_handle = create_task();
    vTaskSetApplicationTaskTag( task_handle, pxHookFunction );

    TaskHookFunction_t hook_function;
    hook_function = xTaskGetApplicationTaskTagFromISR( NULL );

    TEST_ASSERT_EQUAL( &pxHookFunction, hook_function );
    ASSERT_PORT_CLEAR_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_PORT_SET_INTERRUPT_FROM_ISR_CALLED();
}

void test_xTaskCallApplicationTaskHook_success( void )
{
    BaseType_t ret_task_hook;
    TaskHandle_t task_handle;
    BaseType_t i = 5;
    void * args = &i;

    task_handle = create_task();
    vTaskSetApplicationTaskTag( task_handle, pxHookFunction );

    ret_task_hook = xTaskCallApplicationTaskHook( task_handle,
                                                  args );
    TEST_ASSERT_EQUAL( i, ret_task_hook );
}

void test_xTaskCallApplicationTaskHook_success_null_handle( void )
{
    BaseType_t ret_task_hook;
    TaskHandle_t task_handle;
    BaseType_t i = 6;
    void * args = &i;

    task_handle = create_task();

    vTaskSetApplicationTaskTag( task_handle, pxHookFunction );

    ret_task_hook = xTaskCallApplicationTaskHook( NULL,
                                                  args );
    TEST_ASSERT_EQUAL( i, ret_task_hook );
}

void test_xTaskCallApplicationTaskHook_fail_no_tag_set( void )
{
    BaseType_t ret_task_hook;
    TaskHandle_t task_handle;
    int i = 7;
    void * args = &i;

    task_handle = create_task();

    ret_task_hook = xTaskCallApplicationTaskHook( task_handle,
                                                  args );
    TEST_ASSERT_EQUAL( pdFAIL, ret_task_hook );
}

/* -------------- end testing configUSE_APPLICATION_TASK_TAG ---------------- */
void test_vTaskSwitchContext( void )
{
    TaskHandle_t task_handle;
    TaskHandle_t task_handle2;
    ListItem_t list_item, list_item2;
    ListItem_t list_item3, list_item4;

    create_task_priority = 3;
    task_handle = create_task();
    create_task_priority = 4;
    task_handle2 = create_task();
    ptcb = task_handle;

    INITIALIZE_LIST_2E( pxReadyTasksLists[ 3 ],
                        list_item, list_item2,
                        ptcb, task_handle2 );
    INITIALIZE_LIST_2E( pxReadyTasksLists[ 4 ],
                        list_item3, list_item4,
                        ptcb, task_handle2 );

    /* Setup */
    uxSchedulerSuspended = pdFALSE;
    pxCurrentTCB->pxTopOfStack = pxCurrentTCB->pxStack + 4; \

    /* Expectations */
    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 0 );

    /* API Call */
    vTaskSwitchContext();

    /* Validations */
    TEST_ASSERT_EQUAL( 24, uxTopReadyPriority );
    TEST_ASSERT_FALSE( xYieldPending );
    ASSERT_APP_STACK_OVERFLOW_HOOK_NOT_CALLED();
}

void test_vTaskSwitchContext_detect_overflow( void )
{
    TaskHandle_t task_handle;
    TaskHandle_t task_handle2;
    ListItem_t list_item, list_item2;
    ListItem_t list_item3, list_item4;

    create_task_priority = 3;
    task_handle = create_task();
    create_task_priority = 4;
    task_handle2 = create_task();
    ptcb = task_handle;

    INITIALIZE_LIST_2E( pxReadyTasksLists[ 3 ],
                        list_item, list_item2,
                        ptcb, task_handle2 );
    INITIALIZE_LIST_2E( pxReadyTasksLists[ 4 ],
                        list_item3, list_item4,
                        ptcb, task_handle2 );

    /* Setup */
    uxSchedulerSuspended = pdFALSE;
    pxCurrentTCB->pxTopOfStack = pxCurrentTCB->pxStack;
    /* Expectations */
    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 0 );

    /* API Call */
    vTaskSwitchContext();

    /* Validations */
    TEST_ASSERT_EQUAL( 24, uxTopReadyPriority );
    TEST_ASSERT_FALSE( xYieldPending );
    ASSERT_APP_STACK_OVERFLOW_HOOK_CALLED();
}

void test_vTaskPlaceOnEventList_success( void )
{
    TaskHandle_t task_handle;
    List_t eventList;

    create_task_priority = 3;
    task_handle = create_task();
    ptcb = task_handle;

    /* Expectations */
    vListInsert_Expect( &eventList, &ptcb->xEventListItem );
    /*  prvAddCurrentTaskToDelayedList */
    uxListRemove_ExpectAndReturn( &ptcb->xStateListItem, 1 );
    listSET_LIST_ITEM_VALUE_Expect( &ptcb->xStateListItem, ( xTickCount + 34 ) );
    vListInsert_Expect( pxDelayedTaskList, &ptcb->xStateListItem );

    /* API call */
    vTaskPlaceOnEventList( &eventList,
                           34 );
    TEST_ASSERT_EQUAL( 0, xNextTaskUnblockTime );
}
void test_vTaskPlaceOnUnorderedEventList( void )
{
    TaskHandle_t task_handle;
    List_t eventList;

    create_task_priority = 3;
    task_handle = create_task();
    ptcb = task_handle;
    xNextTaskUnblockTime = 600;

    uxSchedulerSuspended = pdTRUE;

    /* Expectations */
    listSET_LIST_ITEM_VALUE_Expect( &ptcb->xEventListItem, 32 | 0x80000000UL );
    listINSERT_END_Expect( &eventList, &ptcb->xEventListItem );
    /* prvAddCurrentTaskToDelayedList */
    uxListRemove_ExpectAndReturn( &ptcb->xStateListItem, 1 );
    listSET_LIST_ITEM_VALUE_Expect( &ptcb->xStateListItem, ( xTickCount + 34 ) );
    vListInsert_Expect( pxDelayedTaskList, &ptcb->xStateListItem );
    /* API Call */
    vTaskPlaceOnUnorderedEventList( &eventList, 32, 34 );
    TEST_ASSERT_EQUAL( xTickCount + 34, xNextTaskUnblockTime );
}

/* testing configUSE_TIMERS  */
void test_vTaskPlaceOnEventListRestricted_indefinite( void )
{
    List_t eventList;
    TaskHandle_t task_handle;

    create_task_priority = 3;
    task_handle = create_task();
    ptcb = task_handle;
    /* Expectations */
    listINSERT_END_Expect( &eventList, &ptcb->xEventListItem );
    /* prvAddCurrentTaskToDelayedList */
    uxListRemove_ExpectAndReturn( &ptcb->xStateListItem, 0 );
    listINSERT_END_Expect( &xSuspendedTaskList, &( ptcb->xStateListItem ) );
    /* API Call */
    vTaskPlaceOnEventListRestricted( &eventList, 100, pdTRUE );
}

void test_vTaskPlaceOnEventListRestricted_not_indefinite( void )
{
    List_t eventList;
    TaskHandle_t task_handle;

    create_task_priority = 3;
    task_handle = create_task();
    ptcb = task_handle;
    /* Expectations */
    listINSERT_END_Expect( &eventList, &ptcb->xEventListItem );
    /* prvAddCurrentTaskToDelayedList */
    uxListRemove_ExpectAndReturn( &ptcb->xStateListItem, 1 );
    listSET_LIST_ITEM_VALUE_Expect( &ptcb->xStateListItem, ( xTickCount + 100 ) );
    vListInsert_Expect( pxDelayedTaskList, &ptcb->xStateListItem );
    /* API Call */
    vTaskPlaceOnEventListRestricted( &eventList, 100, pdFALSE );
}

void test_vTaskPlaceOnEventListRestricted_max_wait( void )
{
    List_t eventList;
    TaskHandle_t task_handle;

    create_task_priority = 3;
    task_handle = create_task();
    ptcb = task_handle;
    /* Expectations */
    listINSERT_END_Expect( &eventList, &ptcb->xEventListItem );
    /* prvAddCurrentTaskToDelayedList */
    uxListRemove_ExpectAndReturn( &ptcb->xStateListItem, 1 );
    listSET_LIST_ITEM_VALUE_Expect( &ptcb->xStateListItem, ( xTickCount + portMAX_DELAY ) );
    vListInsert_Expect( pxOverflowDelayedTaskList, &ptcb->xStateListItem );
    /* API Call */
    vTaskPlaceOnEventListRestricted( &eventList, portMAX_DELAY, pdFALSE );
}
/* end testing configUSE_TIMERS  */

void test_xTaskRemoveFromEventList_fail( void )
{
    BaseType_t ret_task_remove;
    TaskHandle_t task_handle;
    List_t eventList;

    /* Setup */
    uxSchedulerSuspended = pdFALSE;
    task_handle = create_task();
    ptcb = task_handle;

    /* Expectations */
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAndReturn( &eventList, ptcb );
    listREMOVE_ITEM_Expect( &( ptcb->xEventListItem ) );
    listREMOVE_ITEM_Expect( &( ptcb->xStateListItem ) );
    /* prvAddTaskToReadyList */
    listINSERT_END_Expect( &pxReadyTasksLists[ create_task_priority ],
                           &ptcb->xStateListItem );
    /* prvResetNextTaskUnblockTime */
    listLIST_IS_EMPTY_ExpectAndReturn( pxDelayedTaskList, pdTRUE );
    /* API Call */
    ret_task_remove = xTaskRemoveFromEventList( &eventList );
    /* Validations */
    TEST_ASSERT_EQUAL( pdFALSE, ret_task_remove );
    TEST_ASSERT_EQUAL( pdFALSE, xYieldPending );
}

void test_xTaskRemoveFromEventList_sched_suspended( void )
{
    BaseType_t ret_task_remove;
    TaskHandle_t task_handle;
    TaskHandle_t task_handle2;
    List_t eventList;

    /* Setup */
    uxSchedulerSuspended = pdTRUE;
    create_task_priority = 3;
    task_handle = create_task();
    ptcb = task_handle; /* unblocked */

    /* block the higher priority task */
    uxListRemove_ExpectAndReturn( &ptcb->xStateListItem, 1 );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem,
                                             &xSuspendedTaskList );
    uxListRemove_ExpectAndReturn( &ptcb->xEventListItem, pdTRUE );
    vListInsertEnd_Expect( &xSuspendedTaskList, &ptcb->xStateListItem );
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &xSuspendedTaskList,
                                             uxCurrentNumberOfTasks );
    TEST_ASSERT_EQUAL( pxCurrentTCB, task_handle );

    vTaskSuspend( task_handle );
    TEST_ASSERT_EQUAL( NULL, pxCurrentTCB );
    create_task_priority = 2;
    task_handle2 = create_task();
    TEST_ASSERT_EQUAL( task_handle2, pxCurrentTCB );

    /* Expectations */
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAndReturn( &eventList, ptcb );
    /*uxListRemove_ExpectAndReturn( &ptcb->xEventListItem, pdTRUE ); */
    listREMOVE_ITEM_Expect( &( ptcb->xEventListItem ) );
    listINSERT_END_Expect( &xPendingReadyList, &ptcb->xEventListItem );
    /* API Call */
    ret_task_remove = xTaskRemoveFromEventList( &eventList );
    /* Validations */
    TEST_ASSERT_EQUAL( pdTRUE, ret_task_remove );
    TEST_ASSERT_EQUAL( pdTRUE, xYieldPending );
}

void test_vTaskRemoveFromUnorderedEventList( void )
{
    ListItem_t list_item;
    TickType_t xItemValue = 500;
    TaskHandle_t task_handle;

    /* Setup */
    uxSchedulerSuspended = pdTRUE;
    create_task_priority = 3;
    task_handle = create_task();
    ptcb = task_handle;

    /* Expectations */
    listSET_LIST_ITEM_VALUE_Expect( &list_item, xItemValue | 0x80000000UL );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &list_item, tcb );
    listREMOVE_ITEM_Expect( &list_item );
    /* prvResetNextTaskUnblockTime */
    listLIST_IS_EMPTY_ExpectAndReturn( pxDelayedTaskList, pdTRUE );
    /* back */
    listREMOVE_ITEM_Expect( &( ptcb->xStateListItem ) );
    /* prvAddTaskToReadyList */
    listINSERT_END_Expect( &pxReadyTasksLists[ create_task_priority ],
                           &ptcb->xStateListItem );

    /* API Call */
    vTaskRemoveFromUnorderedEventList( &list_item,
                                       xItemValue );
    /* Validations */
    TEST_ASSERT_FALSE( xYieldPending );
}

void test_vTaskRemoveFromUnorderedEventList_yielding( void )
{
    ListItem_t list_item;
    TickType_t xItemValue = 500;
    TaskHandle_t task_handle;
    TaskHandle_t task_handle2;

    /* Setup */
    uxSchedulerSuspended = pdTRUE;
    create_task_priority = 3;
    task_handle = create_task();
    ptcb = task_handle;
    /* block the higher priority task */
    block_task( task_handle );
    TEST_ASSERT_EQUAL( NULL, pxCurrentTCB );
    create_task_priority = 2;
    task_handle2 = create_task();
    TEST_ASSERT_EQUAL( task_handle2, pxCurrentTCB );

    /* Expectations */
    listSET_LIST_ITEM_VALUE_Expect( &list_item, xItemValue | 0x80000000UL );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &list_item, tcb );
    /*uxListRemove_ExpectAndReturn( &list_item, pdTRUE ); */
    listREMOVE_ITEM_Expect( &( list_item ) );
    /* prvResetNextTaskUnblockTime */
    listLIST_IS_EMPTY_ExpectAndReturn( pxDelayedTaskList, pdFALSE );
    listGET_ITEM_VALUE_OF_HEAD_ENTRY_ExpectAndReturn( pxDelayedTaskList, 23 );
    /* back */
    /*uxListRemove_ExpectAndReturn( &ptcb->xStateListItem, pdTRUE ); */
    listREMOVE_ITEM_Expect( &( ptcb->xStateListItem ) );
    /* prvAddTaskToReadyList */
    listINSERT_END_Expect( &pxReadyTasksLists[ 3 ],
                           &ptcb->xStateListItem );

    /* API Call */
    vTaskRemoveFromUnorderedEventList( &list_item,
                                       xItemValue );
    /* Validations */
    TEST_ASSERT_TRUE( xYieldPending );
}

void test_vTaskSetTimeOutState_success( void )
{
    TimeOut_t time_out;

    /* API Call */
    vTaskSetTimeOutState( &time_out );
    /* Validations */
    TEST_ASSERT_EQUAL( xNumOfOverflows, time_out.xOverflowCount );
    TEST_ASSERT_EQUAL( xTickCount, time_out.xTimeOnEntering );
}

void test_vTaskInternalSetTimeOutState_success( void )
{
    TimeOut_t time_out;

    /* API Call */
    vTaskInternalSetTimeOutState( &time_out );
    /* Validations */
    TEST_ASSERT_EQUAL( xNumOfOverflows, time_out.xOverflowCount );
    TEST_ASSERT_EQUAL( xTickCount, time_out.xTimeOnEntering );
}

void test_xTaskCheckForTimeOut( void )
{
    BaseType_t ret_check_timeout;
    TimeOut_t time_out;
    TickType_t ticks_to_wait = 5;
    TaskHandle_t task_handle;

    create_task_priority = 3;
    task_handle = create_task();
    ptcb = task_handle;

    ret_check_timeout = xTaskCheckForTimeOut( &time_out,
                                              &ticks_to_wait );
    TEST_ASSERT_TRUE( ret_check_timeout );
}

void test_xTaskCheckForTimeOut_delay_aborted( void )
{
    BaseType_t ret_check_timeout;
    TimeOut_t time_out;
    TickType_t ticks_to_wait = portMAX_DELAY;
    TaskHandle_t task_handle;

    create_task_priority = 3;
    task_handle = create_task();
    ptcb = task_handle;
    ptcb->ucDelayAborted = pdTRUE; /* achieved by calling  xTaskAbortDelay */

    ret_check_timeout = xTaskCheckForTimeOut( &time_out,
                                              &ticks_to_wait );
    TEST_ASSERT_TRUE( ret_check_timeout );
}

void test_xTaskCheckForTimeOut_max_delay( void )
{
    BaseType_t ret_check_timeout;
    TimeOut_t time_out;
    TickType_t ticks_to_wait = portMAX_DELAY;
    TaskHandle_t task_handle;

    create_task_priority = 3;
    task_handle = create_task();
    ptcb = task_handle;

    ret_check_timeout = xTaskCheckForTimeOut( &time_out,
                                              &ticks_to_wait );
    TEST_ASSERT_FALSE( ret_check_timeout );
}

void test_xTaskCheckForTimeOut_overflow( void )
{
    BaseType_t ret_check_timeout;
    TimeOut_t time_out;
    TickType_t ticks_to_wait = 10;
    TaskHandle_t task_handle;

    create_task_priority = 3;
    task_handle = create_task();
    ptcb = task_handle;
    time_out.xOverflowCount = xNumOfOverflows + 2;
    time_out.xTimeOnEntering = xTickCount - 3;

    ret_check_timeout = xTaskCheckForTimeOut( &time_out,
                                              &ticks_to_wait );
    TEST_ASSERT_TRUE( ret_check_timeout );
    TEST_ASSERT_EQUAL( 0, ticks_to_wait );
}

/*const TickType_t xElapsedTime = xConstTickCount - pxTimeOut->xTimeOnEntering; */
void test_xTaskCheckForTimeOut_timeout( void )
{
    BaseType_t ret_check_timeout;
    TimeOut_t time_out;
    TickType_t ticks_to_wait = 1000;
    TaskHandle_t task_handle;

    create_task_priority = 3;
    task_handle = create_task();
    ptcb = task_handle;
    ptcb->ucDelayAborted = pdFALSE;
    time_out.xOverflowCount = xNumOfOverflows;
    time_out.xTimeOnEntering = 3;
    uint32_t expected = ( 1000 - ( xTickCount - time_out.xTimeOnEntering ) );
    /* API Call */
    ret_check_timeout = xTaskCheckForTimeOut( &time_out,
                                              &ticks_to_wait );
    /* Validations */
    TEST_ASSERT_FALSE( ret_check_timeout );
    TEST_ASSERT_EQUAL( expected, ticks_to_wait );
    TEST_ASSERT_EQUAL( xTickCount, time_out.xTimeOnEntering );
}

void test_vTaskMissedYield( void )
{
    TEST_ASSERT_FALSE( xYieldPending );
    vTaskMissedYield();
    TEST_ASSERT_TRUE( xYieldPending );
}

/**
 * @brief prvIdleTask - yield
 *
 * Test prvIdleTask yield for other idle level priority task.
 *
 * <b>Coverage</b>
 * @code{c}
 * #if ( ( configUSE_PREEMPTION == 1 ) && ( configIDLE_SHOULD_YIELD == 1 ) )
 * {
 *     ...
 *     if( listCURRENT_LIST_LENGTH( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ) ) > ( UBaseType_t ) configNUMBER_OF_CORES )
 *     {
 *         taskYIELD();
 *     }
 *     else
 *     {
 *         mtCOVERAGE_TEST_MARKER();
 *     }
 * }
 * #endif
 * @endcode
 * ( listCURRENT_LIST_LENGTH( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ) ) > ( UBaseType_t ) configNUMBER_OF_CORES ) is true.
 */
void test_prvIdleTask_yield( void )
{
    int i = 8;
    void * args = &i;

    create_task_priority = 3;
    create_task();

    /* Setup. */
    uxDeletedTasksWaitingCleanUp = 0;
    portTASK_FUNCTION( prvIdleTask, args );
    ( void ) fool_static2;

    /* Expectations. */
    /* INFINITE_LOOP in prvIdleTask. */
    vFakeInfiniteLoop_ExpectAndReturn( 1 );

    /* List function in prvIdleTask. */
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &pxReadyTasksLists[ 0 ], 2 );

    /* INFINITE_LOOP in prvIdleTask. */
    vFakeInfiniteLoop_ExpectAndReturn( 0 );

    /* API Call. */
    prvIdleTask( args );

    /* Validations. */
    ASSERT_PORT_ALLOCATE_SECURE_CONTEXT_CALLED();
    ASSERT_PORT_YIELD_CALLED();
    ASSERT_APPLICATION_IDLE_HOOK_CALLED();
}

/**
 * @brief prvIdleTask - tickless expected idle time
 *
 * Test prvIdleTask expected idle time condition.
 *
 * <b>Coverage</b>
 * @code{c}
 * #if ( configUSE_TICKLESS_IDLE != 0 )
 * {
 *     TickType_t xExpectedIdleTime;
 *     ...
 *     xExpectedIdleTime = prvGetExpectedIdleTime();
 *
 *     if( xExpectedIdleTime >= configEXPECTED_IDLE_TIME_BEFORE_SLEEP )
 *     {
 *         vTaskSuspendAll();
 *         {
 * #endif
 * @endcode
 * ( xExpectedIdleTime >= configEXPECTED_IDLE_TIME_BEFORE_SLEEP ) is true.
 */
void test_prvIdleTask_tickless_expected_idle_time( void )
{
    int i = 8;
    void * args = &i;

    create_task_priority = 0;
    create_task();

    /* Setup. */
    uxTopReadyPriority = 0;
    xTickCount = 0;
    xNextTaskUnblockTime = configEXPECTED_IDLE_TIME_BEFORE_SLEEP + 1;
    uxDeletedTasksWaitingCleanUp = 0;
    portTASK_FUNCTION( prvIdleTask, args );
    ( void ) fool_static2;

    /* Expectations. */
    /* INFINITE_LOOP in prvIdleTask. */
    vFakeInfiniteLoop_ExpectAndReturn( 1 );

    /* List function in prvIdleTask. */
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &pxReadyTasksLists[ 0 ], 1 );

    /* List functions in prvGetExpectedIdleTime. */
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &pxReadyTasksLists[ 0 ], 1 );
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &pxReadyTasksLists[ 0 ], 1 );

    /* List functions in xTaskResumeAll */
    listLIST_IS_EMPTY_ExpectAndReturn( &xPendingReadyList, pdTRUE );

    /* INFINITE_LOOP in prvIdleTask. */
    vFakeInfiniteLoop_ExpectAndReturn( 0 );

    /* API Call. */
    prvIdleTask( args );

    /* Validations. */
    ASSERT_PORT_ALLOCATE_SECURE_CONTEXT_CALLED();
    ASSERT_APPLICATION_IDLE_HOOK_CALLED();
}

/* implement */
/*configPRE_SUPPRESS_TICKS_AND_SLEEP_PROCESSING( xExpectedIdleTime ); */


/* testing configUSE_TICKLESS_IDLE  */
void test_eTaskConfirmSleepModeStatus_abort_sleep( void )
{
    eSleepModeStatus ret_status;

    /* Setup */
    vTaskMissedYield();
    /* Expectations */
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &xPendingReadyList, 0 );
    /* API Call */
    ret_status = eTaskConfirmSleepModeStatus();
    /* Validations */
    TEST_ASSERT_EQUAL( eAbortSleep, ret_status );
}

void test_eTaskConfirmSleepModeStatus_abort_sleep2( void )
{
    eSleepModeStatus ret_status;

    /* Setup */
    xPendedTicks = 3;
    /* Expectations */
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &xPendingReadyList, 0 );
    /* API Call */
    ret_status = eTaskConfirmSleepModeStatus();
    /* Validations */
    TEST_ASSERT_EQUAL( eAbortSleep, ret_status );
}

void test_eTaskConfirmSleepModeStatus_abort_sleep3( void )
{
    eSleepModeStatus ret_status;

    /* Setup */
    /* Expectations */
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &xPendingReadyList, 3 );
    /* API Call */
    ret_status = eTaskConfirmSleepModeStatus();
    /* Validations */
    TEST_ASSERT_EQUAL( eAbortSleep, ret_status );
}

void test_eTaskConfirmSleepModeStatus_standard_sleep( void )
{
    eSleepModeStatus ret_status;

    /* Setup */
    xPendedTicks = 0;
    /* Expectations */
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &xPendingReadyList, 0 );
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &xSuspendedTaskList, 0 );
    /* API Call */
    ret_status = eTaskConfirmSleepModeStatus();
    /* Validations */
    TEST_ASSERT_EQUAL( eStandardSleep, ret_status );
}

void test_eTaskConfirmSleepModeStatus_no_tasks_waiting_timeout( void )
{
    eSleepModeStatus ret_status;

    /* Setup */
    create_task();
    xPendedTicks = 0;
    /* Expectations */
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &xPendingReadyList, 0 );
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &xSuspendedTaskList, 0 );
    /* API Call */
    ret_status = eTaskConfirmSleepModeStatus();
    /* Validations */
    TEST_ASSERT_EQUAL( eNoTasksWaitingTimeout, ret_status );
}

void test_vTaskStepTick()
{
    TickType_t save_tick_count;

    /* Setup */
    save_tick_count = xTickCount;
    /* Expectations */
    /* API Call */
    vTaskStepTick( 35 );
    /* Validations */
    TEST_ASSERT_EQUAL( 35 + save_tick_count, xTickCount );
}
/* end testing configUSE_TICKLESS_IDLE  */


/* testing configNUM_THREAD_LOCAL_STORAGE_POINTERS */

/* this test ensures that the value set is also retrieved */
void test_vTask_Set_Get_ThreadLocalStoragePointer_success( void )
{
    TaskHandle_t task_handle;
    uint32_t i = 454545;
    void * pValue = &i;
    void * ret_pValue;

    /* Setup */
    create_task_priority = 3;
    task_handle = create_task();
    /* Expectations */
    /* API Call */
    vTaskSetThreadLocalStoragePointer( task_handle,
                                       0,
                                       pValue );
    ret_pValue = pvTaskGetThreadLocalStoragePointer( task_handle, 0 );
    /* Validations */
    TEST_ASSERT_EQUAL_PTR( pValue, ret_pValue );
}

void test_vTask_Set_Get_ThreadLocalStoragePointer_success_null_handle( void )
{
    uint32_t i = 454545;
    void * pValue = &i;
    void * ret_pValue;

    /* Setup */
    create_task_priority = 3;
    create_task();
    /* Expectations */
    /* API Call */
    vTaskSetThreadLocalStoragePointer( NULL,
                                       0,
                                       pValue );
    ret_pValue = pvTaskGetThreadLocalStoragePointer( NULL, 0 );
    /* Validations */
    TEST_ASSERT_EQUAL_PTR( pValue, ret_pValue );
}
void test_vTask_Set_ThreadLocalStoragePointer_fail( void )
{
    TaskHandle_t task_handle;
    uint32_t i = 454545;
    void * pValue = &i;

    /* Setup */
    create_task_priority = 3;
    task_handle = create_task();
    ptcb = task_handle;
    /* Expectations */
    /* API Call */
    vTaskSetThreadLocalStoragePointer( task_handle,
                                       configNUM_THREAD_LOCAL_STORAGE_POINTERS + 2,
                                       pValue );

    #pragma GCC diagnostic ignored "-Warray-bounds"
    void * value = *( ptcb->pvThreadLocalStoragePointers +
                      configNUM_THREAD_LOCAL_STORAGE_POINTERS + 2 );
    #pragma GCC diagnostic error "-Warray-bounds"

    /* this wall cause a warning, since we are reading past the end of the
     * array, could remove this test case since sanitizers would easily catch it
     * */
    TEST_ASSERT_NOT_EQUAL( pValue, value );
}
void test_pvTaskGetThreadLocalStoragePointer_fail( void )
{
    void * ret_pValue;

    ret_pValue = pvTaskGetThreadLocalStoragePointer( NULL,
                                                     configNUM_THREAD_LOCAL_STORAGE_POINTERS + 2 );
    TEST_ASSERT_NULL( ret_pValue );
}
/* ------- end testing configNUM_THREAD_LOCAL_STORAGE_POINTERS -------------- */


/* --- testing INCLUDE_xTaskGetCurrentTaskHandle || configUSE_MUTEXES == 1 -- */
void test_xTaskGetCurrentTaskHandle( void )
{
    TaskHandle_t task_handle;
    TaskHandle_t ret_current_handle;

    /* Setup */
    task_handle = create_task();
    /* Expectations */

    /* API Call */
    ret_current_handle = xTaskGetCurrentTaskHandle();
    /* Validations */
    TEST_ASSERT_EQUAL_PTR( task_handle, ret_current_handle );
}
/* - end testing INCLUDE_xTaskGetCurrentTaskHandle || configUSE_MUTEXES == 1 */

/* testing INCLUDE_xTaskGetSchedulerState  configUSE_TIMERS */
void test_xTaskGetSchedulerState_not_running( void )
{
    BaseType_t ret_sched_state;

    xSchedulerRunning = pdFALSE;

    ret_sched_state = xTaskGetSchedulerState();
    TEST_ASSERT_EQUAL( taskSCHEDULER_NOT_STARTED, ret_sched_state );
}

void test_xTaskGetSchedulerState_running( void )
{
    BaseType_t ret_sched_state;

    start_scheduler();
    ret_sched_state = xTaskGetSchedulerState();
    TEST_ASSERT_EQUAL( taskSCHEDULER_RUNNING, ret_sched_state );
}

void test_xTaskGetSchedulerState_suspended( void )
{
    BaseType_t ret_sched_state;

    start_scheduler();
    vTaskSuspendAll();
    ret_sched_state = xTaskGetSchedulerState();
    TEST_ASSERT_EQUAL( taskSCHEDULER_SUSPENDED, ret_sched_state );
}
/* end testing INCLUDE_xTaskGetSchedulerState  configUSE_TIMERS */

/* ----------------- testing configUSE_MUTEXES == 1 ------------------------- */
void test_xTaskPriorityInherit_fail_null_param( void )
{
    BaseType_t ret_prio_inherit;

    /* Setup */
    /* Expectations */
    /* API Call */
    ret_prio_inherit = xTaskPriorityInherit( NULL );
    /* Validations */
    TEST_ASSERT_FALSE( ret_prio_inherit );
}

void test_xTaskPriorityInherit_fail( void )
{
    BaseType_t ret_prio_inherit;
    TaskHandle_t mutex_holder;

    /* Setup */
    create_task_priority = 3;
    create_task();
    create_task_priority = 4;
    mutex_holder = create_task();
    /* Expectations */
    /* API Call */
    ret_prio_inherit = xTaskPriorityInherit( mutex_holder );
    /* Validations */
    TEST_ASSERT_FALSE( ret_prio_inherit );
}

void test_xTaskPriorityInherit_success_base_less( void )
{
    BaseType_t ret_prio_inherit;
    TaskHandle_t mutex_holder;

    /* Setup */
    create_task_priority = 4;
    mutex_holder = create_task();
    block_task( mutex_holder );

    create_task_priority = 3;
    create_task();
    mutex_holder->uxBasePriority = 2;
    /* Expectations */
    /* API Call */
    ret_prio_inherit = xTaskPriorityInherit( mutex_holder );
    /* Validations */
    TEST_ASSERT_TRUE( ret_prio_inherit );
}

void test_xTaskPriorityInherit_success( void )
{
    BaseType_t ret_prio_inherit;
    TaskHandle_t task_handle;
    TaskHandle_t mutex_holder;

    /* Setup */
    create_task_priority = 3;
    mutex_holder = create_task();
    create_task_priority = 4;
    task_handle = create_task();
    TEST_ASSERT_EQUAL_PTR( pxCurrentTCB, task_handle );
    /* Expectations */
    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &mutex_holder->xEventListItem, 0 );
    listSET_LIST_ITEM_VALUE_Expect( &mutex_holder->xEventListItem,
                                    configMAX_PRIORITIES - task_handle->uxPriority );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &pxReadyTasksLists[ mutex_holder->uxPriority ],
                                             &mutex_holder->xStateListItem, pdFALSE );
    /* API Call */
    ret_prio_inherit = xTaskPriorityInherit( mutex_holder );
    /* Validations */
    TEST_ASSERT_TRUE( ret_prio_inherit );
}

void test_xTaskPriorityInherit_success2( void )
{
    BaseType_t ret_prio_inherit;
    TaskHandle_t task_handle;
    TaskHandle_t mutex_holder;
    BaseType_t ready_prio;

    /* Setup */
    create_task_priority = 3;
    mutex_holder = create_task();
    create_task_priority = 4;
    task_handle = create_task();
    TEST_ASSERT_EQUAL_PTR( pxCurrentTCB, task_handle );
    ready_prio = uxTopReadyPriority;
    /* Expectations */
    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &mutex_holder->xEventListItem, 0 );
    listSET_LIST_ITEM_VALUE_Expect( &mutex_holder->xEventListItem,
                                    configMAX_PRIORITIES - task_handle->uxPriority );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &pxReadyTasksLists[ mutex_holder->uxPriority ],
                                             &mutex_holder->xStateListItem, pdTRUE );
    uxListRemove_ExpectAndReturn( &mutex_holder->xStateListItem, 0 );
    /* prvAddTaskToReadyList */
    listINSERT_END_Expect( &pxReadyTasksLists[ pxCurrentTCB->uxPriority ],
                           &mutex_holder->xStateListItem );
    /* API Call */
    ret_prio_inherit = xTaskPriorityInherit( mutex_holder );
    /* Validations */
    TEST_ASSERT_TRUE( ret_prio_inherit );
    TEST_ASSERT_NOT_EQUAL( uxTopReadyPriority, ready_prio );
}

void test_xTaskPriorityInherit_success3( void )
{
    BaseType_t ret_prio_inherit;
    TaskHandle_t task_handle;
    TaskHandle_t mutex_holder;
    BaseType_t ready_prio;

    /* Setup */
    create_task_priority = 3;
    mutex_holder = create_task();
    create_task_priority = 4;
    task_handle = create_task();
    TEST_ASSERT_EQUAL_PTR( pxCurrentTCB, task_handle );
    ready_prio = uxTopReadyPriority;
    /* Expectations */
    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &mutex_holder->xEventListItem, 0 );
    listSET_LIST_ITEM_VALUE_Expect( &mutex_holder->xEventListItem,
                                    configMAX_PRIORITIES - task_handle->uxPriority );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &pxReadyTasksLists[ mutex_holder->uxPriority ],
                                             &mutex_holder->xStateListItem, pdTRUE );
    uxListRemove_ExpectAndReturn( &mutex_holder->xStateListItem, 1 );
    /* prvAddTaskToReadyList */
    listINSERT_END_Expect( &pxReadyTasksLists[ pxCurrentTCB->uxPriority ],
                           &mutex_holder->xStateListItem );
    /* API Call */
    ret_prio_inherit = xTaskPriorityInherit( mutex_holder );
    /* Validations */
    TEST_ASSERT_TRUE( ret_prio_inherit );
    TEST_ASSERT_EQUAL( uxTopReadyPriority, ready_prio );
}

void test_xTaskPriorityDisinherit_fail_null_task( void )
{
    BaseType_t ret_prio_disinherit;

    /* API Call */
    ret_prio_disinherit = xTaskPriorityDisinherit( NULL );
    /* Validations */
    TEST_ASSERT_FALSE( ret_prio_disinherit );
}

void test_xTaskPriorityDisinherit_success_base_eq_current_priority( void )
{
    BaseType_t ret_prio_disinherit;
    TaskHandle_t mutex_holder;

    /* Setup */
    mutex_holder = create_task();
    mutex_holder->uxMutexesHeld = 1;
    /* Expectations */
    /* API Call */
    ret_prio_disinherit = xTaskPriorityDisinherit( mutex_holder );
    /* Validations */
    TEST_ASSERT_FALSE( ret_prio_disinherit );
}

void test_xTaskPriorityDisinherit_success_base_ne_current_priority( void )
{
    BaseType_t ret_prio_disinherit;
    TaskHandle_t mutex_holder;
    BaseType_t ready_prio;

    /* Setup */
    create_task_priority = 4;
    mutex_holder = create_task();
    mutex_holder->uxMutexesHeld = 1;
    mutex_holder->uxPriority = 5;
    uxTopReadyPriority |= ( 1 << 5 );
    ready_prio = uxTopReadyPriority;
    /* Expectations */
    uxListRemove_ExpectAndReturn( &mutex_holder->xStateListItem, 0 );
    listSET_LIST_ITEM_VALUE_Expect( &mutex_holder->xEventListItem,
                                    configMAX_PRIORITIES - mutex_holder->uxBasePriority );
    /* prvAddTaskToReadyList */
    listINSERT_END_Expect( &pxReadyTasksLists[ mutex_holder->uxBasePriority ],
                           &mutex_holder->xStateListItem );
    /* API Call */
    ret_prio_disinherit = xTaskPriorityDisinherit( mutex_holder );
    /* Validations */
    TEST_ASSERT_TRUE( ret_prio_disinherit );
    TEST_ASSERT_EQUAL( mutex_holder->uxBasePriority, mutex_holder->uxPriority );
    TEST_ASSERT_NOT_EQUAL( uxTopReadyPriority, ready_prio );
}

void test_xTaskPriorityDisinherit_success_base_ne_current_priority2( void )
{
    BaseType_t ret_prio_disinherit;
    TaskHandle_t mutex_holder;
    BaseType_t ready_prio;

    /* Setup */
    create_task_priority = 4;
    mutex_holder = create_task();
    mutex_holder->uxMutexesHeld = 1;
    mutex_holder->uxPriority = 5;
    uxTopReadyPriority |= ( 1 << 5 );
    ready_prio = uxTopReadyPriority;
    /* Expectations */
    uxListRemove_ExpectAndReturn( &mutex_holder->xStateListItem, 1 );
    listSET_LIST_ITEM_VALUE_Expect( &mutex_holder->xEventListItem,
                                    configMAX_PRIORITIES - mutex_holder->uxBasePriority );
    /* prvAddTaskToReadyList */
    listINSERT_END_Expect( &pxReadyTasksLists[ mutex_holder->uxBasePriority ],
                           &mutex_holder->xStateListItem );
    /* API Call */
    ret_prio_disinherit = xTaskPriorityDisinherit( mutex_holder );
    /* Validations */
    TEST_ASSERT_TRUE( ret_prio_disinherit );
    TEST_ASSERT_EQUAL( mutex_holder->uxBasePriority, mutex_holder->uxPriority );
    TEST_ASSERT_EQUAL( uxTopReadyPriority, ready_prio );
}

void test_xTaskPriorityDisinherit_success_mutex_held_gt_1( void )
{
    BaseType_t ret_prio_disinherit;
    TaskHandle_t mutex_holder;

    /* Setup */
    create_task_priority = 4;
    mutex_holder = create_task();
    mutex_holder->uxMutexesHeld = 2;
    mutex_holder->uxPriority = 5;
    /* Expectations */
    /* API Call */
    ret_prio_disinherit = xTaskPriorityDisinherit( mutex_holder );
    /* Validations */
    TEST_ASSERT_FALSE( ret_prio_disinherit );
}

void test_pvTaskIncrementMutexHeldCount_success( void )
{
    TaskHandle_t task_handle;
    TaskHandle_t ret_task_handle;

    task_handle = create_task();
    ret_task_handle = pvTaskIncrementMutexHeldCount();
    TEST_ASSERT_EQUAL_PTR( task_handle, ret_task_handle );
    TEST_ASSERT_EQUAL( 1, task_handle->uxMutexesHeld );
}

void test_pvTaskIncrementMutexHeldCount_fail_null_current_tcb( void )
{
    TaskHandle_t ret_task_handle;

    ret_task_handle = pvTaskIncrementMutexHeldCount();
    TEST_ASSERT_EQUAL( NULL, ret_task_handle );
}

void test_vTaskPriorityDisinheritAfterTimeout_fail_null_handle()
{
    /* Setup */
    /* Expectations */
    /* API Call */
    vTaskPriorityDisinheritAfterTimeout( NULL,
                                         2 );
    /* Validations */
}

void test_vTaskPriorityDisinheritAfterTimeout_success()
{
    TaskHandle_t mutex_holder;

    /* Setup */
    create_task_priority = 4;
    mutex_holder = create_task();
    mutex_holder->uxMutexesHeld = 1;
    /* Expectations */
    /* API Call */
    vTaskPriorityDisinheritAfterTimeout( mutex_holder,
                                         create_task_priority - 1 );
    /* Validations */
    TEST_ASSERT_EQUAL( create_task_priority, mutex_holder->uxPriority );
    TEST_ASSERT_EQUAL( create_task_priority, mutex_holder->uxBasePriority );
}

void test_vTaskPriorityDisinheritAfterTimeout_success2()
{
    TaskHandle_t mutex_holder;

    /* Setup */
    create_task_priority = 4;
    mutex_holder = create_task();
    mutex_holder->uxMutexesHeld = 1;
    /* Expectations */
    /* API Call */
    vTaskPriorityDisinheritAfterTimeout( mutex_holder,
                                         create_task_priority );
    /* Validations */
    TEST_ASSERT_EQUAL( create_task_priority, mutex_holder->uxPriority );
    TEST_ASSERT_EQUAL( create_task_priority, mutex_holder->uxBasePriority );
}

void test_vTaskPriorityDisinheritAfterTimeout_success3()
{
    TaskHandle_t mutex_holder;

    /* Setup */
    create_task_priority = 4;
    mutex_holder = create_task();
    mutex_holder->uxMutexesHeld = 2;
    /* Expectations */
    /* API Call */
    vTaskPriorityDisinheritAfterTimeout( mutex_holder,
                                         create_task_priority + 2 );
    /* Validations */
    TEST_ASSERT_EQUAL( create_task_priority, mutex_holder->uxPriority );
    TEST_ASSERT_EQUAL( create_task_priority, mutex_holder->uxBasePriority );
}

void test_vTaskPriorityDisinheritAfterTimeout_success4()
{
    TaskHandle_t mutex_holder;

    /* Setup */
    create_task_priority = 4;
    mutex_holder = create_task();
    mutex_holder->uxMutexesHeld = 1;
    /* Expectations */
    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &mutex_holder->xEventListItem, 0x80000000UL );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &pxReadyTasksLists[ mutex_holder->uxPriority ],
                                             &mutex_holder->xStateListItem,
                                             pdFALSE );
    /* API Call */
    vTaskPriorityDisinheritAfterTimeout( mutex_holder,
                                         create_task_priority + 2 );
    /* Validations */
    TEST_ASSERT_EQUAL( create_task_priority + 2, mutex_holder->uxPriority );
    TEST_ASSERT_EQUAL( create_task_priority, mutex_holder->uxBasePriority );
}

void test_vTaskPriorityDisinheritAfterTimeout_success5()
{
    TaskHandle_t mutex_holder;

    /* Setup */
    create_task_priority = 4;
    mutex_holder = create_task();
    mutex_holder->uxMutexesHeld = 1;
    mutex_holder->uxPriority = 6;
    /* Expectations */
    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &mutex_holder->xEventListItem, 0 );
    listSET_LIST_ITEM_VALUE_Expect( &mutex_holder->xEventListItem, 0 );
    listSET_LIST_ITEM_VALUE_IgnoreArg_itemValue();
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &pxReadyTasksLists[ mutex_holder->uxPriority ],
                                             &mutex_holder->xStateListItem,
                                             pdTRUE );
    uxListRemove_ExpectAndReturn( &mutex_holder->xStateListItem, 1 );
    /* prvAddTaskToReadyList */
    listINSERT_END_Expect( &pxReadyTasksLists[ mutex_holder->uxBasePriority ],
                           &mutex_holder->xStateListItem );
    /* API Call */
    vTaskPriorityDisinheritAfterTimeout( mutex_holder,
                                         create_task_priority - 2 );
    /* Validations */
    TEST_ASSERT_EQUAL( create_task_priority, mutex_holder->uxPriority );
    TEST_ASSERT_EQUAL( create_task_priority, mutex_holder->uxBasePriority );
}

void test_vTaskPriorityDisinheritAfterTimeout_success6()
{
    TaskHandle_t mutex_holder;

    /* Setup */
    create_task_priority = 4;
    mutex_holder = create_task();
    mutex_holder->uxMutexesHeld = 1;
    /* Expectations */
    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &mutex_holder->xEventListItem, 0 );
    listSET_LIST_ITEM_VALUE_Expect( &mutex_holder->xEventListItem, 0 );
    listSET_LIST_ITEM_VALUE_IgnoreArg_itemValue();
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &pxReadyTasksLists[ mutex_holder->uxPriority ],
                                             &mutex_holder->xStateListItem,
                                             pdTRUE );
    uxListRemove_ExpectAndReturn( &mutex_holder->xStateListItem, 0 );
    /* prvAddTaskToReadyList */
    listINSERT_END_Expect( &pxReadyTasksLists[ create_task_priority + 2 ],
                           &mutex_holder->xStateListItem );
    /* API Call */
    vTaskPriorityDisinheritAfterTimeout( mutex_holder,
                                         create_task_priority + 2 );
    /* Validations */
    TEST_ASSERT_EQUAL( create_task_priority + 2, mutex_holder->uxPriority );
}

/* end testing configUSE_MUTEXES == 1 */

/* ---------------- testing portCRITICAL_NESTING_IN_TCB --------------------- */

/* --------------- end testing portCRITICAL_NESTING_IN_TCB ------------------ */

void test_uxTaskResetEventItemValue( void )
{
    TaskHandle_t task_handle;
    TickType_t ret_task_reset;

    /* Setup */
    task_handle = create_task();
    /* Expectations */
    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &task_handle->xEventListItem, 1 );
    listSET_LIST_ITEM_VALUE_Expect( &task_handle->xEventListItem,
                                    configMAX_PRIORITIES - task_handle->uxPriority );
    /* API Call */
    ret_task_reset = uxTaskResetEventItemValue();
    /* Validations */
    TEST_ASSERT_EQUAL( 1, ret_task_reset );
}

/* ---------- testing configUSE_TASK_NOTIFICATIONS --------------- */

/* called from port task yield, to simulate that another task ran and received
 * the notification */
static void notif_received()
{
    ptcb->ucNotifyState[ 0 ] = 2; /* taskNOTIFICATION_RECEIVED */
}

void test_ulTaskGenericNotifyTake_success( void )
{
    TaskHandle_t task_handle;
    UBaseType_t uxIndexToWait = 0;
    uint32_t ret_gen_notify_take;

    /* Setup */
    task_handle = create_task();
    task_handle->ulNotifiedValue[ uxIndexToWait ] = 0;
    /* Expectations */
    /* xTaskResumeAll */
    listLIST_IS_EMPTY_ExpectAndReturn( &xPendingReadyList, pdTRUE );
    /* API Call */
    ret_gen_notify_take = ulTaskGenericNotifyTake( uxIndexToWait,
                                                   pdFALSE,
                                                   0 );
    /* Validations */
    TEST_ASSERT_EQUAL( 0, ret_gen_notify_take );
    TEST_ASSERT_EQUAL( 0, task_handle->ucNotifyState[ uxIndexToWait ] );
    ASSERT_PORT_YIELD_WITHIN_API_NOT_CALLED();
}

void test_ulTaskGenericNotifyTake_success2( void )
{
    TaskHandle_t task_handle;
    UBaseType_t uxIndexToWait = 0;
    uint32_t ret_gen_notify_take;

    /* Setup */
    task_handle = create_task();
    task_handle->ulNotifiedValue[ uxIndexToWait ] = 2;
    /* Expectations */
    /* xTaskResumeAll */
    listLIST_IS_EMPTY_ExpectAndReturn( &xPendingReadyList, pdTRUE );
    /* API Call */
    ret_gen_notify_take = ulTaskGenericNotifyTake( uxIndexToWait,
                                                   pdFALSE,
                                                   0 );
    /* Validations */
    TEST_ASSERT_EQUAL( 2, ret_gen_notify_take );
    TEST_ASSERT_EQUAL( 0, task_handle->ucNotifyState[ uxIndexToWait ] );
    ASSERT_PORT_YIELD_WITHIN_API_NOT_CALLED();
}

void test_ulTaskGenericNotifyTake_success_clear_count( void )
{
    TaskHandle_t task_handle;
    UBaseType_t uxIndexToWait = 0;
    uint32_t ret_gen_notify_take;

    /* Setup */
    task_handle = create_task();
    task_handle->ulNotifiedValue[ uxIndexToWait ] = 5;
    /* Expectations */
    /* xTaskResumeAll */
    listLIST_IS_EMPTY_ExpectAndReturn( &xPendingReadyList, pdTRUE );
    /* API Call */
    ret_gen_notify_take = ulTaskGenericNotifyTake( uxIndexToWait,
                                                   pdTRUE,
                                                   0 );
    /* Validations */
    TEST_ASSERT_EQUAL( 5, ret_gen_notify_take );
    TEST_ASSERT_EQUAL( 0, task_handle->ucNotifyState[ uxIndexToWait ] );
    ASSERT_PORT_YIELD_WITHIN_API_NOT_CALLED();
}

void test_ulTaskGenericNotifyTake_success_yield( void )
{
    TaskHandle_t task_handle;
    UBaseType_t uxIndexToWait = 0;
    uint32_t ret_gen_notify_take;

    /* Setup */
    task_handle = create_task();
    task_handle->ulNotifiedValue[ uxIndexToWait ] = 0;
    ptcb = task_handle;
    /* Expectations */
    /*  prvAddCurrentTaskToDelayedList */
    uxListRemove_ExpectAndReturn( &ptcb->xStateListItem, 1 );
    listSET_LIST_ITEM_VALUE_Expect( &ptcb->xStateListItem, xTickCount + 9 );
    vListInsert_Expect( pxDelayedTaskList, &ptcb->xStateListItem );
    /* xTaskResumeAll */
    listLIST_IS_EMPTY_ExpectAndReturn( &xPendingReadyList, pdTRUE );
    /* API Call */
    ret_gen_notify_take = ulTaskGenericNotifyTake( uxIndexToWait,
                                                   pdFALSE,
                                                   9 );
    /* Validations */
    TEST_ASSERT_EQUAL( 0, ret_gen_notify_take );
    TEST_ASSERT_EQUAL( 0, task_handle->ucNotifyState[ uxIndexToWait ] );
    ASSERT_PORT_YIELD_WITHIN_API_CALLED();
}

void test_xTaskGenericNotify_success( void )
{
    BaseType_t ret_task_notify;
    TaskHandle_t task_to_notify;
    UBaseType_t uxIndexToNotify = 2;
    uint32_t ulValue = 45;
    eNotifyAction eAction = eSetBits;
    uint32_t pulPreviousNotificationValue;

    /* Setup */
    task_to_notify = create_task();
    task_to_notify->ulNotifiedValue[ uxIndexToNotify ] = 32;
    ptcb = task_to_notify;
    /* Expectations */
    /* API Call */
    ret_task_notify = xTaskGenericNotify( task_to_notify,
                                          uxIndexToNotify,
                                          ulValue,
                                          eAction,
                                          &pulPreviousNotificationValue );
    /* Validations */
    TEST_ASSERT_EQUAL( 1, ret_task_notify );
    TEST_ASSERT_EQUAL( 32, pulPreviousNotificationValue );
}


void test_xTaskGenericNotify_success_null_pull( void )
{
    BaseType_t ret_task_notify;
    TaskHandle_t task_to_notify;
    UBaseType_t uxIndexToNotify = 2;
    uint32_t ulValue = 2;
    eNotifyAction eAction = eSetBits;

    /* Setup */
    task_to_notify = create_task();
    task_to_notify->ulNotifiedValue[ uxIndexToNotify ] = 1;
    task_to_notify->ucNotifyState[ uxIndexToNotify ] = taskWAITING_NOTIFICATION;
    ptcb = task_to_notify;
    /* Expectations */
    listREMOVE_ITEM_Expect( &( ptcb->xStateListItem ) );
    /* prvAddTaskToReadyList */
    listINSERT_END_Expect( &pxReadyTasksLists[ ptcb->uxPriority ],
                           &ptcb->xStateListItem );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem,
                                             &xSuspendedTaskList );
    /* prvResetNextTaskUnblockTime */
    listLIST_IS_EMPTY_ExpectAndReturn( pxDelayedTaskList, pdTRUE );

    /* API Call */
    ret_task_notify = xTaskGenericNotify( ptcb,
                                          uxIndexToNotify,
                                          ulValue,
                                          eAction,
                                          NULL );
    /* Validations */
    TEST_ASSERT_EQUAL( 1, ret_task_notify );
    TEST_ASSERT_EQUAL( 1 | 2, ptcb->ulNotifiedValue[ uxIndexToNotify ] );
    TEST_ASSERT_EQUAL( 2, ptcb->ucNotifyState[ uxIndexToNotify ] );
}

void test_xTaskGenericNotify_success_eIncrement( void )
{
    BaseType_t ret_task_notify;
    TaskHandle_t task_to_notify;
    UBaseType_t uxIndexToNotify = 2;
    uint32_t ulValue = 5;
    eNotifyAction eAction = eIncrement;

    /* Setup */
    task_to_notify = create_task();
    task_to_notify->ulNotifiedValue[ uxIndexToNotify ] = 10;
    task_to_notify->ucNotifyState[ uxIndexToNotify ] = taskWAITING_NOTIFICATION;
    ptcb = task_to_notify;
    /* Expectations */
    listREMOVE_ITEM_Expect( &( ptcb->xStateListItem ) );
    /* prvAddTaskToReadyList */
    listINSERT_END_Expect( &pxReadyTasksLists[ ptcb->uxPriority ],
                           &ptcb->xStateListItem );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem,
                                             &xSuspendedTaskList );
    /* prvResetNextTaskUnblockTime */
    listLIST_IS_EMPTY_ExpectAndReturn( pxDelayedTaskList, pdTRUE );
    /* API Call */
    ret_task_notify = xTaskGenericNotify( ptcb,
                                          uxIndexToNotify,
                                          ulValue,
                                          eAction,
                                          NULL );
    /* Validations */
    TEST_ASSERT_EQUAL( 1, ret_task_notify );
    TEST_ASSERT_EQUAL( 11, ptcb->ulNotifiedValue[ uxIndexToNotify ] );
    TEST_ASSERT_EQUAL( 2, ptcb->ucNotifyState[ uxIndexToNotify ] );
}

void test_xTaskGenericNotify_success_eSetValueWithOverwrite( void )
{
    BaseType_t ret_task_notify;
    TaskHandle_t task_to_notify;
    UBaseType_t uxIndexToNotify = 2;
    uint32_t ulValue = 5;
    eNotifyAction eAction = eSetValueWithOverwrite;

    /* Setup */
    task_to_notify = create_task();
    task_to_notify->ulNotifiedValue[ uxIndexToNotify ] = 1;
    task_to_notify->ucNotifyState[ uxIndexToNotify ] = taskWAITING_NOTIFICATION;
    ptcb = task_to_notify;
    /* Expectations */
    listREMOVE_ITEM_Expect( &( ptcb->xStateListItem ) );
    /* prvAddTaskToReadyList */
    listINSERT_END_Expect( &pxReadyTasksLists[ ptcb->uxPriority ],
                           &ptcb->xStateListItem );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem,
                                             &xSuspendedTaskList );
    /* prvResetNextTaskUnblockTime */
    listLIST_IS_EMPTY_ExpectAndReturn( pxDelayedTaskList, pdTRUE );
    /* API Call */
    ret_task_notify = xTaskGenericNotify( ptcb,
                                          uxIndexToNotify,
                                          ulValue,
                                          eAction,
                                          NULL );
    /* Validations */
    TEST_ASSERT_EQUAL( 1, ret_task_notify );
    TEST_ASSERT_EQUAL( 5, ptcb->ulNotifiedValue[ uxIndexToNotify ] );
    TEST_ASSERT_EQUAL( 2, ptcb->ucNotifyState[ uxIndexToNotify ] );
}

void test_xTaskGenericNotify_success_eSetValueWithoutOverwrite( void )
{
    BaseType_t ret_task_notify;
    TaskHandle_t task_to_notify;
    UBaseType_t uxIndexToNotify = 2;
    uint32_t ulValue = 5;
    eNotifyAction eAction = eSetValueWithoutOverwrite;

    /* Setup */
    task_to_notify = create_task();
    task_to_notify->ulNotifiedValue[ uxIndexToNotify ] = 1;
    task_to_notify->ucNotifyState[ uxIndexToNotify ] = taskWAITING_NOTIFICATION;
    ptcb = task_to_notify;
    /* Expectations */
    listREMOVE_ITEM_Expect( &( ptcb->xStateListItem ) );
    /* prvAddTaskToReadyList */
    listINSERT_END_Expect( &pxReadyTasksLists[ ptcb->uxPriority ],
                           &ptcb->xStateListItem );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem,
                                             &xSuspendedTaskList );
    /* prvResetNextTaskUnblockTime */
    listLIST_IS_EMPTY_ExpectAndReturn( pxDelayedTaskList, pdTRUE );
    /* API Call */
    ret_task_notify = xTaskGenericNotify( ptcb,
                                          uxIndexToNotify,
                                          ulValue,
                                          eAction,
                                          NULL );
    /* Validations */
    TEST_ASSERT_EQUAL( 1, ret_task_notify );
    TEST_ASSERT_EQUAL( 5, ptcb->ulNotifiedValue[ uxIndexToNotify ] );
    TEST_ASSERT_EQUAL( 2, ptcb->ucNotifyState[ uxIndexToNotify ] );
}

void test_xTaskGenericNotify_success_eSetValueWithoutOverwrite_not_rec( void )
{
    BaseType_t ret_task_notify;
    TaskHandle_t task_to_notify;
    UBaseType_t uxIndexToNotify = 2;
    uint32_t ulValue = 5;
    eNotifyAction eAction = eSetValueWithoutOverwrite;

    /* Setup */
    task_to_notify = create_task();
    task_to_notify->ulNotifiedValue[ uxIndexToNotify ] = 11;
    task_to_notify->ucNotifyState[ uxIndexToNotify ] = taskNOTIFICATION_RECEIVED;
    ptcb = task_to_notify;
    /* Expectations */
    /* API Call */
    ret_task_notify = xTaskGenericNotify( ptcb,
                                          uxIndexToNotify,
                                          ulValue,
                                          eAction,
                                          NULL );
    /* Validations */
    TEST_ASSERT_EQUAL( pdFAIL, ret_task_notify );
    TEST_ASSERT_EQUAL( 11, ptcb->ulNotifiedValue[ uxIndexToNotify ] );
    TEST_ASSERT_EQUAL( 2, ptcb->ucNotifyState[ uxIndexToNotify ] );
}

void test_xTaskGenericNotify_success_eNoAction( void )
{
    BaseType_t ret_task_notify;
    TaskHandle_t task_to_notify;
    UBaseType_t uxIndexToNotify = 2;
    uint32_t ulValue = 5;
    eNotifyAction eAction = eNoAction;

    /* Setup */
    task_to_notify = create_task();
    task_to_notify->ulNotifiedValue[ uxIndexToNotify ] = 15;
    task_to_notify->ucNotifyState[ uxIndexToNotify ] = taskNOTIFICATION_RECEIVED;
    ptcb = task_to_notify;
    /* Expectations */
    /* API Call */
    ret_task_notify = xTaskGenericNotify( ptcb,
                                          uxIndexToNotify,
                                          ulValue,
                                          eAction,
                                          NULL );
    /* Validations */
    TEST_ASSERT_EQUAL( pdTRUE, ret_task_notify );
    TEST_ASSERT_EQUAL( 15, ptcb->ulNotifiedValue[ uxIndexToNotify ] );
    TEST_ASSERT_EQUAL( 2, ptcb->ucNotifyState[ uxIndexToNotify ] );
}

void test_xTaskGenericNotify_success_default( void )
{
    BaseType_t ret_task_notify;
    TaskHandle_t task_to_notify;
    TaskHandle_t task_handle_current;
    UBaseType_t uxIndexToNotify = 2;
    uint32_t ulValue = 5;
    eNotifyAction eAction = 10;

    /* Setup */
    create_task_priority = 7;
    task_to_notify = create_task();
    block_task( task_to_notify );
    create_task_priority = 3;
    task_handle_current = create_task(); /* current task */
    TEST_ASSERT_EQUAL_PTR( task_handle_current, pxCurrentTCB );
    task_to_notify->ulNotifiedValue[ uxIndexToNotify ] = 15;
    task_to_notify->ucNotifyState[ uxIndexToNotify ] = taskWAITING_NOTIFICATION;
    ptcb = task_to_notify;
    /* Expectations */
    listREMOVE_ITEM_Expect( &( ptcb->xStateListItem ) );
    /* prvAddTaskToReadyList */
    listINSERT_END_Expect( &pxReadyTasksLists[ ptcb->uxPriority ],
                           &ptcb->xStateListItem );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem,
                                             &xSuspendedTaskList );
    /* prvResetNextTaskUnblockTime */
    listLIST_IS_EMPTY_ExpectAndReturn( pxDelayedTaskList, pdTRUE );
    /* API Call */
    ret_task_notify = xTaskGenericNotify( ptcb,
                                          uxIndexToNotify,
                                          ulValue,
                                          eAction,
                                          NULL );
    /* Validations */
    TEST_ASSERT_EQUAL( pdTRUE, ret_task_notify );
    TEST_ASSERT_EQUAL( 15, ptcb->ulNotifiedValue[ uxIndexToNotify ] );
    TEST_ASSERT_EQUAL( 2, ptcb->ucNotifyState[ uxIndexToNotify ] );
    ASSERT_PORT_YIELD_WITHIN_API_CALLED();
}

void test_xTaskGenericNotify_success_ISR( void )
{
    BaseType_t ret_task_notify;
    TaskHandle_t task_to_notify;
    UBaseType_t uxIndexToNotify = 2;
    uint32_t ulValue = 45;
    eNotifyAction eAction = eSetBits;
    uint32_t pulPreviousNotificationValue;
    BaseType_t pxHigherPriorityTaskWoken = 0;

    /* Setup */
    task_to_notify = create_task();
    task_to_notify->ulNotifiedValue[ uxIndexToNotify ] = 32;
    ptcb = task_to_notify;
    /* Expectations */
    /* API Call */
    ret_task_notify = xTaskGenericNotifyFromISR( task_to_notify,
                                                 uxIndexToNotify,
                                                 ulValue,
                                                 eAction,
                                                 &pulPreviousNotificationValue,
                                                 &pxHigherPriorityTaskWoken );
    /* Validations */
    TEST_ASSERT_EQUAL( 1, ret_task_notify );
    TEST_ASSERT_EQUAL( 32, pulPreviousNotificationValue );
    ASSERT_PORT_CLEAR_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_PORT_SET_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_INVALID_INTERRUPT_PRIORITY_CALLED();
}


void test_xTaskGenericNotify_success_null_pull_ISR( void )
{
    BaseType_t ret_task_notify;
    TaskHandle_t task_to_notify;
    UBaseType_t uxIndexToNotify = 2;
    uint32_t ulValue = 2;
    BaseType_t pxHigherPriorityTaskWoken = 0;
    eNotifyAction eAction = eSetBits;

    /* Setup */
    task_to_notify = create_task();
    task_to_notify->ulNotifiedValue[ uxIndexToNotify ] = 1;
    task_to_notify->ucNotifyState[ uxIndexToNotify ] = taskWAITING_NOTIFICATION;
    ptcb = task_to_notify;
    vTaskSuspendAll();
    /* Expectations */
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem,
                                             &xSuspendedTaskList );
    listINSERT_END_Expect( &xPendingReadyList, &ptcb->xEventListItem );

    /* API Call */
    ret_task_notify = xTaskGenericNotifyFromISR( ptcb,
                                                 uxIndexToNotify,
                                                 ulValue,
                                                 eAction,
                                                 NULL,
                                                 &pxHigherPriorityTaskWoken );
    /* Validations */
    TEST_ASSERT_EQUAL( 1, ret_task_notify );
    TEST_ASSERT_EQUAL( 1 | 2, ptcb->ulNotifiedValue[ uxIndexToNotify ] );
    TEST_ASSERT_EQUAL( 2, ptcb->ucNotifyState[ uxIndexToNotify ] );
    ASSERT_PORT_CLEAR_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_PORT_SET_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_INVALID_INTERRUPT_PRIORITY_CALLED();
}

void test_xTaskGenericNotify_success_eIncrement_ISR( void )
{
    BaseType_t ret_task_notify;
    TaskHandle_t task_to_notify;
    UBaseType_t uxIndexToNotify = 2;
    uint32_t ulValue = 5;
    BaseType_t pxHigherPriorityTaskWoken = 0;
    eNotifyAction eAction = eIncrement;

    /* Setup */
    task_to_notify = create_task();
    task_to_notify->ulNotifiedValue[ uxIndexToNotify ] = 10;
    task_to_notify->ucNotifyState[ uxIndexToNotify ] = taskWAITING_NOTIFICATION;
    ptcb = task_to_notify;
    /* Expectations */
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem,
                                             &xSuspendedTaskList );
    listREMOVE_ITEM_Expect( &( ptcb->xStateListItem ) );

    /* prvAddTaskToReadyList */
    listINSERT_END_Expect( &pxReadyTasksLists[ ptcb->uxPriority ],
                           &ptcb->xStateListItem );
    /* prvResetNextTaskUnblockTime */
    listLIST_IS_EMPTY_ExpectAndReturn( pxDelayedTaskList, pdFALSE );
    listGET_ITEM_VALUE_OF_HEAD_ENTRY_ExpectAndReturn( pxDelayedTaskList, 1000 );

    /* API Call */
    ret_task_notify = xTaskGenericNotifyFromISR( ptcb,
                                                 uxIndexToNotify,
                                                 ulValue,
                                                 eAction,
                                                 NULL,
                                                 &pxHigherPriorityTaskWoken );
    /* Validations */
    TEST_ASSERT_EQUAL( 1, ret_task_notify );
    TEST_ASSERT_EQUAL( 11, ptcb->ulNotifiedValue[ uxIndexToNotify ] );
    TEST_ASSERT_EQUAL( 2, ptcb->ucNotifyState[ uxIndexToNotify ] );
    ASSERT_PORT_CLEAR_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_PORT_SET_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_INVALID_INTERRUPT_PRIORITY_CALLED();
}

void test_xTaskGenericNotify_success_eSetValueWithOverwrite_ISR( void )
{
    BaseType_t ret_task_notify;
    TaskHandle_t task_to_notify;
    UBaseType_t uxIndexToNotify = 2;
    uint32_t ulValue = 5;
    BaseType_t pxHigherPriorityTaskWoken = 0;
    eNotifyAction eAction = eSetValueWithOverwrite;

    /* Setup */
    task_to_notify = create_task();
    task_to_notify->ulNotifiedValue[ uxIndexToNotify ] = 1;
    task_to_notify->ucNotifyState[ uxIndexToNotify ] = taskWAITING_NOTIFICATION;
    ptcb = task_to_notify;
    /* Expectations */
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem,
                                             &xSuspendedTaskList );
    listREMOVE_ITEM_Expect( &( ptcb->xStateListItem ) );
    /* prvAddTaskToReadyList */
    listINSERT_END_Expect( &pxReadyTasksLists[ ptcb->uxPriority ],
                           &ptcb->xStateListItem );
    /* prvResetNextTaskUnblockTime */
    listLIST_IS_EMPTY_ExpectAndReturn( pxDelayedTaskList, pdFALSE );
    listGET_ITEM_VALUE_OF_HEAD_ENTRY_ExpectAndReturn( pxDelayedTaskList, 1000 );

    /* API Call */
    ret_task_notify = xTaskGenericNotifyFromISR( ptcb,
                                                 uxIndexToNotify,
                                                 ulValue,
                                                 eAction,
                                                 NULL,
                                                 &pxHigherPriorityTaskWoken );
    /* Validations */
    TEST_ASSERT_EQUAL( 1, ret_task_notify );
    TEST_ASSERT_EQUAL( 5, ptcb->ulNotifiedValue[ uxIndexToNotify ] );
    TEST_ASSERT_EQUAL( 2, ptcb->ucNotifyState[ uxIndexToNotify ] );
    ASSERT_PORT_CLEAR_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_PORT_SET_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_INVALID_INTERRUPT_PRIORITY_CALLED();
}

void test_xTaskGenericNotify_success_eSetValueWithoutOverwrite_ISR( void )
{
    BaseType_t ret_task_notify;
    TaskHandle_t task_to_notify;
    UBaseType_t uxIndexToNotify = 2;
    uint32_t ulValue = 5;
    BaseType_t pxHigherPriorityTaskWoken = 0;
    eNotifyAction eAction = eSetValueWithoutOverwrite;

    /* Setup */
    task_to_notify = create_task();
    task_to_notify->ulNotifiedValue[ uxIndexToNotify ] = 1;
    task_to_notify->ucNotifyState[ uxIndexToNotify ] = taskWAITING_NOTIFICATION;
    ptcb = task_to_notify;
    /* Expectations */
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem,
                                             &xSuspendedTaskList );
    listREMOVE_ITEM_Expect( &( ptcb->xStateListItem ) );
    /* prvAddTaskToReadyList */
    listINSERT_END_Expect( &pxReadyTasksLists[ ptcb->uxPriority ],
                           &ptcb->xStateListItem );
    /* prvResetNextTaskUnblockTime */
    listLIST_IS_EMPTY_ExpectAndReturn( pxDelayedTaskList, pdFALSE );
    listGET_ITEM_VALUE_OF_HEAD_ENTRY_ExpectAndReturn( pxDelayedTaskList, 1000 );

    /* API Call */
    ret_task_notify = xTaskGenericNotifyFromISR( ptcb,
                                                 uxIndexToNotify,
                                                 ulValue,
                                                 eAction,
                                                 NULL,
                                                 &pxHigherPriorityTaskWoken );
    /* Validations */
    TEST_ASSERT_EQUAL( 1, ret_task_notify );
    TEST_ASSERT_EQUAL( 5, ptcb->ulNotifiedValue[ uxIndexToNotify ] );
    TEST_ASSERT_EQUAL( 2, ptcb->ucNotifyState[ uxIndexToNotify ] );
    TEST_ASSERT_FALSE( pxHigherPriorityTaskWoken );
    ASSERT_PORT_CLEAR_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_PORT_SET_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_INVALID_INTERRUPT_PRIORITY_CALLED();
}

void test_xTaskGenericNotify_success_eSetValueWithoutOverwrite_not_rec_ISR( void )
{
    BaseType_t ret_task_notify;
    TaskHandle_t task_to_notify;
    UBaseType_t uxIndexToNotify = 2;
    uint32_t ulValue = 5;
    BaseType_t pxHigherPriorityTaskWoken = 0;
    eNotifyAction eAction = eSetValueWithoutOverwrite;

    /* Setup */
    task_to_notify = create_task();
    task_to_notify->ulNotifiedValue[ uxIndexToNotify ] = 11;
    task_to_notify->ucNotifyState[ uxIndexToNotify ] = taskNOTIFICATION_RECEIVED;
    ptcb = task_to_notify;
    /* Expectations */
    /* API Call */
    ret_task_notify = xTaskGenericNotifyFromISR( ptcb,
                                                 uxIndexToNotify,
                                                 ulValue,
                                                 eAction,
                                                 NULL,
                                                 &pxHigherPriorityTaskWoken );
    /* Validations */
    TEST_ASSERT_EQUAL( pdFAIL, ret_task_notify );
    TEST_ASSERT_EQUAL( 11, ptcb->ulNotifiedValue[ uxIndexToNotify ] );
    TEST_ASSERT_EQUAL( 2, ptcb->ucNotifyState[ uxIndexToNotify ] );
    TEST_ASSERT_FALSE( pxHigherPriorityTaskWoken );
    ASSERT_PORT_CLEAR_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_PORT_SET_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_INVALID_INTERRUPT_PRIORITY_CALLED();
}

void test_xTaskGenericNotify_success_eNoAction_ISR( void )
{
    BaseType_t ret_task_notify;
    TaskHandle_t task_to_notify;
    UBaseType_t uxIndexToNotify = 2;
    uint32_t ulValue = 5;
    BaseType_t pxHigherPriorityTaskWoken = 0;
    eNotifyAction eAction = eNoAction;

    /* Setup */
    task_to_notify = create_task();
    task_to_notify->ulNotifiedValue[ uxIndexToNotify ] = 15;
    task_to_notify->ucNotifyState[ uxIndexToNotify ] = taskNOTIFICATION_RECEIVED;
    ptcb = task_to_notify;
    /* Expectations */
    /* API Call */
    ret_task_notify = xTaskGenericNotifyFromISR( ptcb,
                                                 uxIndexToNotify,
                                                 ulValue,
                                                 eAction,
                                                 NULL,
                                                 &pxHigherPriorityTaskWoken );
    /* Validations */
    TEST_ASSERT_EQUAL( pdTRUE, ret_task_notify );
    TEST_ASSERT_EQUAL( 15, ptcb->ulNotifiedValue[ uxIndexToNotify ] );
    TEST_ASSERT_EQUAL( 2, ptcb->ucNotifyState[ uxIndexToNotify ] );
    TEST_ASSERT_FALSE( pxHigherPriorityTaskWoken );
    ASSERT_PORT_CLEAR_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_PORT_SET_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_INVALID_INTERRUPT_PRIORITY_CALLED();
}

void test_xTaskGenericNotify_success_default_ISR( void )
{
    BaseType_t ret_task_notify;
    TaskHandle_t task_to_notify;
    TaskHandle_t task_handle_current;
    UBaseType_t uxIndexToNotify = 2;
    uint32_t ulValue = 5;
    BaseType_t pxHigherPriorityTaskWoken = pdFALSE;

    eNotifyAction eAction = 10;

    /* Setup */
    create_task_priority = 7;
    task_to_notify = create_task();
    block_task( task_to_notify );
    create_task_priority = 3;
    task_handle_current = create_task(); /* current task */
    TEST_ASSERT_EQUAL_PTR( task_handle_current, pxCurrentTCB );
    task_to_notify->ulNotifiedValue[ uxIndexToNotify ] = 15;
    task_to_notify->ucNotifyState[ uxIndexToNotify ] = taskWAITING_NOTIFICATION;
    ptcb = task_to_notify;
    /* Expectations */
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem,
                                             &xSuspendedTaskList );
    listREMOVE_ITEM_Expect( &( ptcb->xStateListItem ) );
    /* prvAddTaskToReadyList */
    listINSERT_END_Expect( &pxReadyTasksLists[ ptcb->uxPriority ],
                           &ptcb->xStateListItem );
    /* prvResetNextTaskUnblockTime */
    listLIST_IS_EMPTY_ExpectAndReturn( pxDelayedTaskList, pdTRUE );

    /* API Call */
    ret_task_notify = xTaskGenericNotifyFromISR( ptcb,
                                                 uxIndexToNotify,
                                                 ulValue,
                                                 eAction,
                                                 NULL,
                                                 &pxHigherPriorityTaskWoken );
    /* Validations */
    TEST_ASSERT_EQUAL( pdTRUE, ret_task_notify );
    TEST_ASSERT_EQUAL( 15, ptcb->ulNotifiedValue[ uxIndexToNotify ] );
    TEST_ASSERT_EQUAL( 2, ptcb->ucNotifyState[ uxIndexToNotify ] );
    TEST_ASSERT_TRUE( pxHigherPriorityTaskWoken );
    TEST_ASSERT_TRUE( xYieldPending );
    ASSERT_PORT_CLEAR_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_PORT_SET_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_INVALID_INTERRUPT_PRIORITY_CALLED();
}

void test_xTaskGenericNotify_success_default_ISR_task_woken_null( void )
{
    BaseType_t ret_task_notify;
    TaskHandle_t task_to_notify;
    TaskHandle_t task_handle_current;
    UBaseType_t uxIndexToNotify = 2;
    uint32_t ulValue = 5;

    eNotifyAction eAction = 10;

    /* Setup */
    create_task_priority = 7;
    task_to_notify = create_task();
    block_task( task_to_notify );
    create_task_priority = 3;
    task_handle_current = create_task(); /* current task */
    TEST_ASSERT_EQUAL_PTR( task_handle_current, pxCurrentTCB );
    task_to_notify->ulNotifiedValue[ uxIndexToNotify ] = 15;
    task_to_notify->ucNotifyState[ uxIndexToNotify ] = taskWAITING_NOTIFICATION;
    ptcb = task_to_notify;
    /* Expectations */
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem,
                                             &xSuspendedTaskList );
    listREMOVE_ITEM_Expect( &( ptcb->xStateListItem ) );
    /* prvAddTaskToReadyList */
    listINSERT_END_Expect( &pxReadyTasksLists[ ptcb->uxPriority ],
                           &ptcb->xStateListItem );
    /* prvResetNextTaskUnblockTime */
    listLIST_IS_EMPTY_ExpectAndReturn( pxDelayedTaskList, pdTRUE );

    /* API Call */
    ret_task_notify = xTaskGenericNotifyFromISR( ptcb,
                                                 uxIndexToNotify,
                                                 ulValue,
                                                 eAction,
                                                 NULL,
                                                 NULL );
    /* Validations */
    TEST_ASSERT_EQUAL( pdTRUE, ret_task_notify );
    TEST_ASSERT_EQUAL( 15, ptcb->ulNotifiedValue[ uxIndexToNotify ] );
    TEST_ASSERT_EQUAL( 2, ptcb->ucNotifyState[ uxIndexToNotify ] );
    TEST_ASSERT_TRUE( xYieldPending );
    ASSERT_PORT_CLEAR_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_PORT_SET_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_INVALID_INTERRUPT_PRIORITY_CALLED();
}


void test_xTaskGenericNotifyWait_success_notif_received( void )
{
    UBaseType_t uxIndexToWait = 0;
    uint32_t ulBitsToClearOnEntry = 0;
    uint32_t ulBitsToClearOnExit = 0;
    uint32_t pullNotificationValue;
    TickType_t xTicksToWait = 20;
    BaseType_t ret;

    TaskHandle_t task_handle;

    /* Setup */
    task_handle = create_task();
    ptcb = task_handle;
    ptcb->ucNotifyState[ uxIndexToWait ] = 2; /* taskNOTIFICATION_RECEIVED */
    ptcb->ulNotifiedValue[ uxIndexToWait ] = 5;
    /* Expectations */
    /* xTaskResumeAll */
    listLIST_IS_EMPTY_ExpectAndReturn( &xPendingReadyList, pdTRUE );
    /* API Call */
    ret = xTaskGenericNotifyWait( uxIndexToWait,
                                  ulBitsToClearOnEntry,
                                  ulBitsToClearOnExit,
                                  &pullNotificationValue,
                                  xTicksToWait );
    /* Validations */
    TEST_ASSERT_EQUAL( pdTRUE, ret );
    TEST_ASSERT_EQUAL( 5, pullNotificationValue );
    ASSERT_PORT_YIELD_WITHIN_API_NOT_CALLED();
}

void test_xTaskGenericNotifyWait_success_notif_not_received( void )
{
    UBaseType_t uxIndexToWait = 0;
    uint32_t ulBitsToClearOnEntry = 0;
    uint32_t ulBitsToClearOnExit = 0;
    uint32_t pullNotificationValue;
    TickType_t xTicksToWait = 20;
    BaseType_t ret;

    TaskHandle_t task_handle;

    task_handle = create_task();
    ptcb = task_handle;
    ptcb->ucNotifyState[ uxIndexToWait ] = 1; /* taskWAITING_NOTIFICATION */
    ptcb->ulNotifiedValue[ uxIndexToWait ] = 5;
    /* Expectations */
    uxListRemove_ExpectAndReturn( &ptcb->xStateListItem, 0 );
    listSET_LIST_ITEM_VALUE_Expect( &ptcb->xStateListItem,
                                    xTickCount + xTicksToWait );
    vListInsert_Expect( pxDelayedTaskList, &ptcb->xStateListItem );
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );

    /* API Call */
    ret = xTaskGenericNotifyWait( uxIndexToWait,
                                  ulBitsToClearOnEntry,
                                  ulBitsToClearOnExit,
                                  &pullNotificationValue,
                                  xTicksToWait );
    /* Validations */
    TEST_ASSERT_EQUAL( pdFALSE, ret );
    TEST_ASSERT_EQUAL( 5, pullNotificationValue );
    ASSERT_PORT_YIELD_WITHIN_API_CALLED();
}

void test_xTaskGenericNotifyWait_success_notif_not_received_no_wait( void )
{
    UBaseType_t uxIndexToWait = 0;
    uint32_t ulBitsToClearOnEntry = 0;
    uint32_t ulBitsToClearOnExit = 0;
    uint32_t pullNotificationValue;
    TickType_t xTicksToWait = 0;
    BaseType_t ret;

    TaskHandle_t task_handle;

    /* Setup */
    task_handle = create_task();
    ptcb = task_handle;
    ptcb->ucNotifyState[ uxIndexToWait ] = 1; /* taskWAITING_NOTIFICATION */
    ptcb->ulNotifiedValue[ uxIndexToWait ] = 5;
    /* Expectations */
    /* xTaskResumeAll */
    listLIST_IS_EMPTY_ExpectAndReturn( &xPendingReadyList, pdTRUE );
    /* API Call */
    ret = xTaskGenericNotifyWait( uxIndexToWait,
                                  ulBitsToClearOnEntry,
                                  ulBitsToClearOnExit,
                                  &pullNotificationValue,
                                  xTicksToWait );
    /* Validations */
    TEST_ASSERT_EQUAL( pdFALSE, ret );
    TEST_ASSERT_EQUAL( 5, pullNotificationValue );
    ASSERT_PORT_YIELD_WITHIN_API_NOT_CALLED();
}

void test_xTaskGenericNotifyWait_success_notif_not_received_pull_null( void )
{
    UBaseType_t uxIndexToWait = 0;
    uint32_t ulBitsToClearOnEntry = 0;
    uint32_t ulBitsToClearOnExit = 0;
    TickType_t xTicksToWait = 0;
    BaseType_t ret;

    TaskHandle_t task_handle;

    /* Setup */
    task_handle = create_task();
    ptcb = task_handle;
    ptcb->ucNotifyState[ uxIndexToWait ] = 1; /* taskWAITING_NOTIFICATION */
    ptcb->ulNotifiedValue[ uxIndexToWait ] = 5;
    /* Expectations */
    /* xTaskResumeAll */
    listLIST_IS_EMPTY_ExpectAndReturn( &xPendingReadyList, pdTRUE );
    /* API Call */
    ret = xTaskGenericNotifyWait( uxIndexToWait,
                                  ulBitsToClearOnEntry,
                                  ulBitsToClearOnExit,
                                  NULL,
                                  xTicksToWait );
    /* Validations */
    TEST_ASSERT_FALSE( ret );
    ASSERT_PORT_YIELD_WITHIN_API_NOT_CALLED();
}

void test_xTaskGenericNotifyWait_success_notif_received_while_waiting( void )
{
    UBaseType_t uxIndexToWait = 0;
    uint32_t ulBitsToClearOnEntry = 0;
    uint32_t ulBitsToClearOnExit = 0;
    uint32_t pullNotificationValue;
    TickType_t xTicksToWait = 20;
    BaseType_t ret;

    TaskHandle_t task_handle;

    task_handle = create_task();
    ptcb = task_handle;
    ptcb->ucNotifyState[ uxIndexToWait ] = 1; /* taskWAITING_NOTIFICATION */
    ptcb->ulNotifiedValue[ uxIndexToWait ] = 5;
    /* Expectations */
    uxListRemove_ExpectAndReturn( &ptcb->xStateListItem, 0 );
    listSET_LIST_ITEM_VALUE_Expect( &ptcb->xStateListItem,
                                    xTickCount + xTicksToWait );
    vListInsert_Expect( pxDelayedTaskList, &ptcb->xStateListItem );
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    py_operation = &notif_received;

    /* API Call */
    ret = xTaskGenericNotifyWait( uxIndexToWait,
                                  ulBitsToClearOnEntry,
                                  ulBitsToClearOnExit,
                                  &pullNotificationValue,
                                  xTicksToWait );
    /* Validations */
    TEST_ASSERT_EQUAL( pdTRUE, ret );
    TEST_ASSERT_EQUAL( 5, pullNotificationValue );
    ASSERT_PORT_YIELD_WITHIN_API_CALLED();
}

void test_vTaskGenericNotifyGiveFromISR_success( void )
{
    TaskHandle_t task_to_notify;
    UBaseType_t uxIndexToNotify = 1;
    BaseType_t pxHigherPriorityTaskWoken = pdFALSE;

    /* Setup */
    task_to_notify = create_task();
    task_to_notify->ucNotifyState[ uxIndexToNotify ] = taskWAITING_NOTIFICATION;
    ptcb = task_to_notify;
    /* Expectations */
    /* configASSERT statement */
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem,
                                             &xSuspendedTaskList );
    /*uxListRemove_ExpectAndReturn( &task_to_notify->xStateListItem, pdTRUE ); */
    listREMOVE_ITEM_Expect( &( task_to_notify->xStateListItem ) );
    /* prvAddTaskToReadyList */
    listINSERT_END_Expect( &( pxReadyTasksLists[ task_to_notify->uxPriority ] ), &task_to_notify->xStateListItem );
    /* prvResetNextTaskUnblockTime */
    listLIST_IS_EMPTY_ExpectAndReturn( pxDelayedTaskList, pdFALSE );
    listGET_ITEM_VALUE_OF_HEAD_ENTRY_ExpectAndReturn( pxDelayedTaskList, 1000 );

    /* API Call */
    vTaskGenericNotifyGiveFromISR( task_to_notify,
                                   uxIndexToNotify,
                                   &pxHigherPriorityTaskWoken );
    /* Validations */
    TEST_ASSERT_FALSE( xYieldPending );
    TEST_ASSERT_FALSE( pxHigherPriorityTaskWoken );
    ASSERT_PORT_CLEAR_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_PORT_SET_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_INVALID_INTERRUPT_PRIORITY_CALLED();
}

void test_vTaskGenericNotifyGiveFromISR_success_scheduler_suspended( void )
{
    TaskHandle_t task_to_notify;
    UBaseType_t uxIndexToNotify = 1;
    BaseType_t pxHigherPriorityTaskWoken = pdFALSE;

    /* Setup */
    task_to_notify = create_task();
    task_to_notify->ucNotifyState[ uxIndexToNotify ] = taskWAITING_NOTIFICATION;
    ptcb = task_to_notify;
    vTaskSuspendAll();
    /* Expectations */
    /* configASSERT statement */
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem,
                                             &xSuspendedTaskList );
    listINSERT_END_Expect( &xPendingReadyList, &task_to_notify->xEventListItem );

    /* API Call */
    vTaskGenericNotifyGiveFromISR( task_to_notify,
                                   uxIndexToNotify,
                                   &pxHigherPriorityTaskWoken );
    /* Validations */
    TEST_ASSERT_FALSE( xYieldPending );
    TEST_ASSERT_FALSE( pxHigherPriorityTaskWoken );
    ASSERT_PORT_CLEAR_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_PORT_SET_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_INVALID_INTERRUPT_PRIORITY_CALLED();
}

void test_vTaskGenericNotifyGiveFromISR_success_yield_pending( void )
{
    TaskHandle_t task_to_notify;
    TaskHandle_t task_handle_current;
    UBaseType_t uxIndexToNotify = 1;
    BaseType_t pxHigherPriorityTaskWoken = pdFALSE;

    /* Setup */
    create_task_priority = 7;
    task_to_notify = create_task();
    block_task( task_to_notify );
    create_task_priority = 3;
    task_handle_current = create_task(); /* current task */
    TEST_ASSERT_EQUAL_PTR( task_handle_current, pxCurrentTCB );
    task_to_notify->ulNotifiedValue[ uxIndexToNotify ] = 15;
    task_to_notify->ucNotifyState[ uxIndexToNotify ] = taskWAITING_NOTIFICATION;
    ptcb = task_to_notify;
    vTaskSuspendAll();

    /* Expectations */
    /* configASSERT statement */
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem,
                                             &xSuspendedTaskList );
    listINSERT_END_Expect( &xPendingReadyList, &task_to_notify->xEventListItem );

    /* API Call */
    vTaskGenericNotifyGiveFromISR( task_to_notify,
                                   uxIndexToNotify,
                                   &pxHigherPriorityTaskWoken );
    /* Validations */
    TEST_ASSERT_TRUE( xYieldPending );
    TEST_ASSERT_TRUE( pxHigherPriorityTaskWoken );
    ASSERT_PORT_CLEAR_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_PORT_SET_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_INVALID_INTERRUPT_PRIORITY_CALLED();
}

void test_vTaskGenericNotifyGiveFromISR_success_null_higherpriority_task( void )
{
    TaskHandle_t task_to_notify;
    TaskHandle_t task_handle_current;
    UBaseType_t uxIndexToNotify = 1;

    /* Setup */
    create_task_priority = 7;
    task_to_notify = create_task();
    block_task( task_to_notify );
    create_task_priority = 3;
    task_handle_current = create_task(); /* current task */
    TEST_ASSERT_EQUAL_PTR( task_handle_current, pxCurrentTCB );
    task_to_notify->ulNotifiedValue[ uxIndexToNotify ] = 15;
    task_to_notify->ucNotifyState[ uxIndexToNotify ] = taskWAITING_NOTIFICATION;
    ptcb = task_to_notify;
    vTaskSuspendAll();
    /* Expectations */
    /* configASSERT statement */
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem,
                                             &xSuspendedTaskList );
    listINSERT_END_Expect( &xPendingReadyList, &task_to_notify->xEventListItem );

    /* API Call */
    vTaskGenericNotifyGiveFromISR( task_to_notify,
                                   uxIndexToNotify,
                                   NULL );
    /* Validations */
    TEST_ASSERT_TRUE( xYieldPending );
    ASSERT_PORT_CLEAR_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_PORT_SET_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_INVALID_INTERRUPT_PRIORITY_CALLED();
}

void test_vTaskGenericNotifyGiveFromISR_success_not_waiting( void )
{
    TaskHandle_t task_to_notify;
    UBaseType_t uxIndexToNotify = 1;
    BaseType_t pxHigherPriorityTaskWoken = pdFALSE;

    /* Setup */
    task_to_notify = create_task();
    task_to_notify->ucNotifyState[ uxIndexToNotify ] = taskNOT_WAITING_NOTIFICATION;
    /* Expectations */

    /* API Call */
    vTaskGenericNotifyGiveFromISR( task_to_notify,
                                   uxIndexToNotify,
                                   &pxHigherPriorityTaskWoken );
    /* Validations */
    TEST_ASSERT_FALSE( xYieldPending );
    TEST_ASSERT_FALSE( pxHigherPriorityTaskWoken );
    ASSERT_PORT_CLEAR_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_PORT_SET_INTERRUPT_FROM_ISR_CALLED();
    ASSERT_INVALID_INTERRUPT_PRIORITY_CALLED();
}

void test_xTaskGenericNotifyStateClear_fail()
{
    BaseType_t ret_notify_state_clear;
    TaskHandle_t task_to_notify;
    UBaseType_t uxIndexToClear = 1;

    /* Setup */
    task_to_notify = create_task();
    task_to_notify->ucNotifyState[ uxIndexToClear ] = taskNOT_WAITING_NOTIFICATION;
    /* Expectations */
    /* API Call */
    ret_notify_state_clear = xTaskGenericNotifyStateClear( task_to_notify,
                                                           uxIndexToClear );
    /* Validations */
    TEST_ASSERT_EQUAL( pdFAIL, ret_notify_state_clear );
}

void test_xTaskGenericNotifyStateClear_fail_null_handler()
{
    BaseType_t ret_notify_state_clear;
    TaskHandle_t task_to_notify;
    UBaseType_t uxIndexToClear = 1;

    /* Setup */
    task_to_notify = create_task();
    task_to_notify->ucNotifyState[ uxIndexToClear ] = taskNOT_WAITING_NOTIFICATION;
    /* Expectations */
    /* API Call */
    ret_notify_state_clear = xTaskGenericNotifyStateClear( NULL,
                                                           uxIndexToClear );
    /* Validations */
    TEST_ASSERT_EQUAL( pdFAIL, ret_notify_state_clear );
}

void test_xTaskGenericNotifyStateClear_success()
{
    BaseType_t ret_notify_state_clear;
    TaskHandle_t task_to_notify;
    UBaseType_t uxIndexToClear = 1;

    /* Setup */
    task_to_notify = create_task();
    task_to_notify->ucNotifyState[ uxIndexToClear ] = taskNOTIFICATION_RECEIVED;
    /* Expectations */
    /* API Call */
    ret_notify_state_clear = xTaskGenericNotifyStateClear( task_to_notify,
                                                           uxIndexToClear );
    /* Validations */
    TEST_ASSERT_EQUAL( pdPASS, ret_notify_state_clear );
    TEST_ASSERT_EQUAL( taskNOT_WAITING_NOTIFICATION,
                       task_to_notify->ucNotifyState[ uxIndexToClear ] );
}

void test_ulTaskGenericNotifyValueClear_success()
{
    TaskHandle_t task_to_notify;
    UBaseType_t uxIndexToClear = 1;
    uint32_t ret_notify_clear;
    uint32_t ulBitsToClear = 1;

    /* Setup */
    task_to_notify = create_task();
    task_to_notify->ulNotifiedValue[ uxIndexToClear ] = 1;
    /* Expectations */
    /* API Call */
    ret_notify_clear = ulTaskGenericNotifyValueClear( task_to_notify,
                                                      uxIndexToClear,
                                                      ulBitsToClear );
    /* Validations */
    TEST_ASSERT_EQUAL( 1, ret_notify_clear );
    TEST_ASSERT_EQUAL( 0, task_to_notify->ulNotifiedValue[ uxIndexToClear ] );
}

void test_ulTaskGenericNotifyValueClear_success_null_handle()
{
    TaskHandle_t task_to_notify;
    UBaseType_t uxIndexToClear = 1;
    uint32_t ret_notify_clear;
    uint32_t ulBitsToClear = 1;

    /* Setup */
    task_to_notify = create_task();
    task_to_notify->ulNotifiedValue[ uxIndexToClear ] = 3;
    /* Expectations */
    /* API Call */
    ret_notify_clear = ulTaskGenericNotifyValueClear( NULL,
                                                      uxIndexToClear,
                                                      ulBitsToClear );
    /* Validations */
    TEST_ASSERT_EQUAL( 3, ret_notify_clear );
    TEST_ASSERT_EQUAL( 2, task_to_notify->ulNotifiedValue[ uxIndexToClear ] );
}
/* ---------- end testing configUSE_TASK_NOTIFICATIONS --------------- */

/* ---------------------- testing xTaskGetStaticBuffers ----------------------*/

/**
 * @brief Test xTaskGetStaticBuffers with a static task
 * @details Test xTaskGetStaticBuffers returns the buffers of a statically allocated task
 * @coverage xTaskGetStaticBuffers
 */
void test_xTaskGetStaticBuffers_static_task( void )
{
    StackType_t puxStackBuffer[ 300 ];
    StaticTask_t * pxTaskBuffer = malloc( sizeof( TCB_t ) );
    TaskFunction_t pxTaskCode = NULL;
    const char * const pcName = { __FUNCTION__ };
    const uint32_t ulStackDepth = 300;
    void * const pvParameters = NULL;
    UBaseType_t uxPriority = 3;
    TaskHandle_t xTaskHandle = NULL;
    StackType_t * puxStackBufferRet = NULL;
    StaticTask_t * pxTaskBufferRet = NULL;

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

    listINSERT_END_ExpectAnyArgs();

    xTaskHandle = xTaskCreateStatic( pxTaskCode,
                                     pcName,
                                     ulStackDepth,
                                     pvParameters,
                                     uxPriority,
                                     puxStackBuffer,
                                     pxTaskBuffer );


    TEST_ASSERT_EQUAL( pdTRUE, xTaskGetStaticBuffers( xTaskHandle, &puxStackBufferRet, &pxTaskBufferRet ) );
    TEST_ASSERT_EQUAL( &puxStackBuffer, puxStackBufferRet );
    TEST_ASSERT_EQUAL( pxTaskBuffer, pxTaskBufferRet );

    free( pxTaskBuffer );
}

/**
 * @brief Test xTaskGetStaticBuffers with a dynamically allocated TCB but a statically allocated stack.
 * @details Test xTaskGetStaticBuffers returns the buffers of a statically allocated task
 * @coverage xTaskGetStaticBuffers
 */
void test_xTaskGetStaticBuffers_static_stack_dynamic_tcb( void )
{
    StackType_t puxStackBuffer[ 300 ];
    StaticTask_t * pxTaskBuffer = malloc( sizeof( TCB_t ) );
    TaskFunction_t pxTaskCode = NULL;
    const char * const pcName = { __FUNCTION__ };
    const uint32_t ulStackDepth = 300;
    void * const pvParameters = NULL;
    UBaseType_t uxPriority = 3;
    TaskHandle_t xTaskHandle = NULL;
    StackType_t * puxStackBufferRet = NULL;
    StaticTask_t * pxTaskBufferRet = NULL;

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

    listINSERT_END_ExpectAnyArgs();

    xTaskHandle = xTaskCreateStatic( pxTaskCode,
                                     pcName,
                                     ulStackDepth,
                                     pvParameters,
                                     uxPriority,
                                     puxStackBuffer,
                                     pxTaskBuffer );

    /* Workaround since the portUSING_MPU_WRAPPERS == 1 config is not tested */
    ( ( TCB_t * ) xTaskHandle )->ucStaticallyAllocated = 1;

    TEST_ASSERT_EQUAL( pdTRUE, xTaskGetStaticBuffers( xTaskHandle, &puxStackBufferRet, &pxTaskBufferRet ) );
    TEST_ASSERT_EQUAL( &puxStackBuffer, puxStackBufferRet );
    TEST_ASSERT_EQUAL( NULL, pxTaskBufferRet );

    free( pxTaskBuffer );
}

/**
 * @brief Test xTaskGetStaticBuffers with a static task as the current task and a null task handle argument.
 * @details Test xTaskGetStaticBuffers returns the buffers of a statically allocated task
 * @coverage xTaskGetStaticBuffers
 */
void test_xTaskGetStaticBuffers_static_task_null_handle( void )
{
    StackType_t puxStackBuffer[ 300 ];
    StaticTask_t * pxTaskBuffer = malloc( sizeof( TCB_t ) );
    TaskFunction_t pxTaskCode = NULL;
    const char * const pcName = { __FUNCTION__ };
    const uint32_t ulStackDepth = 300;
    void * const pvParameters = NULL;
    UBaseType_t uxPriority = 3;
    TaskHandle_t xTaskHandle = NULL;
    StackType_t * puxStackBufferRet = NULL;
    StaticTask_t * pxTaskBufferRet = NULL;

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

    listINSERT_END_ExpectAnyArgs();

    xTaskHandle = xTaskCreateStatic( pxTaskCode,
                                     pcName,
                                     ulStackDepth,
                                     pvParameters,
                                     uxPriority,
                                     puxStackBuffer,
                                     pxTaskBuffer );

    pxCurrentTCB = ( TCB_t * ) xTaskHandle;

    TEST_ASSERT_EQUAL( pdTRUE, xTaskGetStaticBuffers( NULL, &puxStackBufferRet, &pxTaskBufferRet ) );
    TEST_ASSERT_EQUAL( &puxStackBuffer, puxStackBufferRet );
    TEST_ASSERT_EQUAL( pxTaskBuffer, pxTaskBufferRet );

    free( pxTaskBuffer );
}

/**
 * @brief Test xTaskGetStaticBuffers with a dynamic task
 * @details Test xTaskGetStaticBuffers returns an error when called on a dynamically allocated task
 * @coverage xTaskGetStaticBuffers
 */
void test_xTaskGetStaticBuffers_dynamic_task( void )
{
    StackType_t * puxStackBufferRet = NULL;
    StaticTask_t * pxTaskBufferRet = NULL;
    TaskHandle_t taskHandle = create_task();

    TEST_ASSERT_EQUAL( pdFALSE, xTaskGetStaticBuffers( taskHandle, &puxStackBufferRet, &pxTaskBufferRet ) );
    TEST_ASSERT_EQUAL( NULL, puxStackBufferRet );
    TEST_ASSERT_EQUAL( NULL, pxTaskBufferRet );
}

/* -------------------- end testing xTaskGetStaticBuffers --------------------*/
