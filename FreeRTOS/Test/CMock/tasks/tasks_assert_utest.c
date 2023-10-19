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
/*! @file tasks_assert_utest.c */

/* ===============================  INCLUDES  =============================== */
/* Tasks includes */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"
#include "fake_port.h"
#include "task.h"

/* C runtime includes. */
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>

/* Test includes. */
#include "unity.h"
#include "unity_memory.h"
#include "CException.h"
#include "global_vars.h"

/* Mock includes. */
#include "mock_fake_assert.h"
#include "mock_portable.h"
#include "mock_list_macros.h"
#include "mock_list.h"
#include "mock_timers.h"

/* =================================  MACROS  =============================== */

/**
 * @brief CException code for when a configASSERT should be intercepted.
 */
#define configASSERT_E    0xAA101

/**
 * @brief simulate up to 10 tasks: add more if needed
 * */
#define TCB_ARRAY         10

/**
 * @brief Expect a configASSERT from the function called.
 *  Break out of the called function when this occurs.
 * @details Use this macro when the call passed in as a parameter is expected
 * to cause invalid memory access.
 */
#define EXPECT_ASSERT_BREAK( call )                 \
    do                                              \
    {                                               \
        shouldAbortOnAssertion = true;              \
        CEXCEPTION_T e = CEXCEPTION_NONE;           \
        Try                                         \
        {                                           \
            call;                                   \
            TEST_FAIL();                            \
        }                                           \
        Catch( e )                                  \
        {                                           \
            TEST_ASSERT_EQUAL( configASSERT_E, e ); \
        }                                           \
    } while( 0 )

/* ============================  GLOBAL VARIABLES =========================== */

/**
 * @brief Global counter for the number of assertions in code.
 */
static int assertionFailed = 0;

/**
 * @brief Flag which denotes if test need to abort on assertion.
 */
static BaseType_t shouldAbortOnAssertion;

/**
 * @brief counts entries to critical sections then subtracts from the variable
 *        when exiting, value should be zero at the end
 */
static uint32_t critical_section_counter = 0;

static bool port_yield_within_api_called = false;
static port_yield_operation py_operation;
static bool port_disable_interrupts_called = false;
static bool port_enable_interrupts_called = false;
static bool port_yield_called = false;
static bool port_setup_tcb_called = false;
static bool portClear_Interrupt_called = false;
static bool portSet_Interrupt_called = false;
static bool portClear_Interrupt_from_isr_called = false;
static bool portSet_Interrupt_from_isr_called = false;
static bool port_invalid_interrupt_called = false;
static bool vApplicationStackOverflowHook_called = false;
static bool getIdleTaskMemoryValid = false;
static StaticTask_t xIdleTaskTCB;
static StackType_t uxIdleTaskStack[ configMINIMAL_STACK_SIZE ];
static bool getIdleTaskMemory_called = false;
static bool vTaskDeletePre_called = false;
static bool vApplicationIdleHook_called = false;
static bool vApplicationTickHook_called = false;

static uint32_t created_tasks = 0;
static TCB_t tcb[ TCB_ARRAY ];
static uint32_t create_task_priority = 3;
static StackType_t stack[ ( ( size_t ) 300 ) * sizeof( StackType_t ) ];
static bool is_first_task = true;

/* ==========================  EXTERN VARIABLES  ============================ */
extern volatile BaseType_t xSchedulerRunning;
extern volatile TickType_t xTickCount;
extern volatile TickType_t xNextTaskUnblockTime;
extern TCB_t * volatile pxCurrentTCB;
extern List_t pxReadyTasksLists[ configMAX_PRIORITIES ];

extern List_t xSuspendedTaskList;
extern List_t xPendingReadyList;
extern List_t xDelayedTaskList1;
extern List_t xDelayedTaskList2;
extern List_t xTasksWaitingTermination;
extern List_t * volatile pxOverflowDelayedTaskList;

extern volatile UBaseType_t uxSchedulerSuspended;

extern volatile UBaseType_t uxCurrentNumberOfTasks;

#if ( defined( configNUMBER_OF_CORES ) && ( configNUMBER_OF_CORES == 1 ) )
    extern TaskHandle_t xIdleTaskHandles[];
    #define xIdleTaskHandle    xIdleTaskHandles[ 0 ]
#else
    extern TaskHandle_t xIdleTaskHandle;
#endif

/* ==========================  CALLBACK FUNCTIONS  ========================== */
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

/* ==========================  STATIC FUNCTIONS  ============================ */
static void validate_and_clear_assertions( void )
{
    TEST_ASSERT_EQUAL( 1, assertionFailed );
    assertionFailed = 0;
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



/* ========================  HOOK FUNCTIONS  =================================*/
void vApplicationTickHook()
{
    HOOK_DIAG();
    vApplicationTickHook_called = true;
}

void vApplicationIdleHook( void )
{
    HOOK_DIAG();
    vApplicationIdleHook_called = true;
}

void vConfigureTimerForRunTimeStats( void )
{
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

/* ===========================  UNITY FIXTURES  ============================= */
/*! called before each test case */
void setUp( void )
{
    assertionFailed = 0;
    shouldAbortOnAssertion = pdTRUE;
    created_tasks = 0;
    is_first_task = true;
    pxCurrentTCB = NULL;
    memset( &pxReadyTasksLists, 0x00, configMAX_PRIORITIES * sizeof( List_t ) );
    memset( &xDelayedTaskList1, 0x00, sizeof( List_t ) );
    memset( &xDelayedTaskList2, 0x00, sizeof( List_t ) );
    memset( &xSuspendedTaskList, 0x00, sizeof( List_t ) );
    memset( &xPendingReadyList, 0x00, sizeof( List_t ) );
    memset( &xTasksWaitingTermination, 0x00, sizeof( List_t ) );
    uxCurrentNumberOfTasks = 0;
    uxSchedulerSuspended = pdFALSE;
    vFakeAssert_StubWithCallback( vFakeAssertStub );
}

/*! called after each test case */
void tearDown( void )
{
    TEST_ASSERT_EQUAL_MESSAGE( 0, assertionFailed, "Assertion check failed in code." );

    mock_fake_assert_Verify();
    mock_fake_assert_Destroy();
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

/* ========================  TEST CASES ===================================== */

/*!
 * @brief This function ensures that the code asserts if the handle name is
 *        greater than configMAX_TASK_NAME_LEN
 */
void test_xTaskGetHandle_assert_large_handle_name( void )
{
    int bigSize = configMAX_TASK_NAME_LEN + 5;
    char handleName[ bigSize ];
    int i;

    for( i = 0; i < bigSize; ++i )
    {
        handleName[ i ] = 'a';
    }

    handleName[ bigSize - 1 ] = '\0';

    EXPECT_ASSERT_BREAK( ( void ) xTaskGetHandle( handleName ) );
    validate_and_clear_assertions();
}

/*!
 * @brief this function ensures that the code asserts if the value of
 *        uxSchedulerSuspended is 1
 */
void test_xTaskResumeAll_assert_scheduler_not_started( void )
{
    EXPECT_ASSERT_BREAK( ( void ) xTaskResumeAll() );

    validate_and_clear_assertions();
}

void test_vTaskGenericNotifyGiveFromISR_assert_xTaskNotify_NULL( void )
{
    BaseType_t pxHigherPriorityTaskWoken;

    EXPECT_ASSERT_BREAK( vTaskGenericNotifyGiveFromISR( NULL,
                                                        1,
                                                        &pxHigherPriorityTaskWoken ) );

    validate_and_clear_assertions();
}

void test_vTaskGenericNotifyGiveFromISR_assert_uxIndexToNotify_out_of_bound( void )
{
    BaseType_t pxHigherPriorityTaskWoken;

    TaskHandle_t xTaskToNotify = ( TaskHandle_t ) 0x1234;

    EXPECT_ASSERT_BREAK( vTaskGenericNotifyGiveFromISR( xTaskToNotify,
                                                        configTASK_NOTIFICATION_ARRAY_ENTRIES + 1,
                                                        &pxHigherPriorityTaskWoken ) );

    validate_and_clear_assertions();
}

/*!
 * @brief This test ensures that the code asserts if the scheduler is running,
 *        the current TCB is the TCB to delete and the scheduler is not
 *        suspended
 */
void test_vTaskDelete_assert_schedulerSuspended( void )
{
    TCB_t * ptcb = create_task();

    start_scheduler();

    uxListRemove_ExpectAndReturn( &ptcb->xStateListItem, pdPASS );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem, NULL );
    vListInsertEnd_ExpectAnyArgs();

    vTaskSuspendAll();

    EXPECT_ASSERT_BREAK( vTaskDelete( ptcb ) );

    validate_and_clear_assertions();
}

/*!
 * @brief This test ensures that the code asserts if pxPreviousWakeTime is equal
 *        to NULL
 */
void test_vTaskDelayUntil_assert_pxPreviousWakeTime_NULL( void )
{
    EXPECT_ASSERT_BREAK( xTaskDelayUntil( NULL, 23 ) );

    validate_and_clear_assertions();
}

/*!
 * @brief This test ensures that the code asserts if xTimeIncrement is less than
 *        or equal to zero
 */
void test_vTaskDelayUntil_assert_xTimeIncrement_lte_zero( void )
{
    TickType_t xPreviousWakeTime;

    EXPECT_ASSERT_BREAK( xTaskDelayUntil( &xPreviousWakeTime, 0 ) );

    validate_and_clear_assertions();
}

/*!
 * @brief This test ensures that the code asserts if uxSchedulerSuspended is not
 *        equal to 1
 */
void test_vTaskDelayUntil_assert_uxSchedulerSuspended_neq_1( void )
{
    TickType_t xPreviousWakeTime;

    vTaskSuspendAll();

    EXPECT_ASSERT_BREAK( xTaskDelayUntil( &xPreviousWakeTime, 6 ) );

    validate_and_clear_assertions();
}

/*!
 * @brief This test ensures that the code asserts if uxSchedulerSuspended is not
 *        equal to 1
 */
void test_vTaskDelay_assert_uxSchedulerSuspended_neq_1( void )
{
    vTaskSuspendAll();

    EXPECT_ASSERT_BREAK( vTaskDelay( 23 ) );

    validate_and_clear_assertions();
}

/*!
 * @brief This test ensures that the code asserts if uxSchedulerSuspended is not
 *        equal to 1
 */
void test_eTaskGetState_assert_TCB_ne_NULL( void )
{
    EXPECT_ASSERT_BREAK( eTaskGetState( NULL ) );
    validate_and_clear_assertions();
}

/*!
 * @brief This test ensures that the code asserts if uxSchedulerSuspended is not
 *        equal to 1
 */
void test_vTaskSuspend_assert_scheduler_suspended_neq_zero( void )
{
    TCB_t * ptcb = create_task();

    uxSchedulerSuspended = 1;
    uxListRemove_ExpectAnyArgsAndReturn( 1 );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem, NULL );
    vListInsertEnd_ExpectAnyArgs();
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );

    EXPECT_ASSERT_BREAK( vTaskSuspend( ptcb ) );

    validate_and_clear_assertions();
}

/*!
 * @brief This test ensures that the code asserts if we pass NULL as a parameter
 *        to vTaskResume
 */
void test_vTaskResume_assert_null_xTaskToResume_handle( void )
{
    EXPECT_ASSERT_BREAK( vTaskResume( NULL ) );

    validate_and_clear_assertions();
}

/*!
 * @brief This test ensures that the code asserts if we pass NULL as a parameter
 *        to xTaskResumeFromISR
 */
void test_xTaskResumeFromISR_assert_null_xTaskToResume_handle( void )
{
    EXPECT_ASSERT_BREAK( xTaskResumeFromISR( NULL ) );

    validate_and_clear_assertions();
}


/*!
 * @brief This test ensures that the code asserts when vTaskStartScheduler
 *        is creating a new idle task or timer task and
 *        it returns errCOULD_NOT_ALLOCATE_REQUIRED_MEMORY
 */
void test_vTaskStartScheduler_assert_could_not_allocate_memory( void )
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

    xTimerCreateTimerTask_ExpectAndReturn( errCOULD_NOT_ALLOCATE_REQUIRED_MEMORY );
    EXPECT_ASSERT_BREAK( vTaskStartScheduler() );

    validate_and_clear_assertions();
}

/*!
 * @brief This test ensures that the code asserts when we pass NULL as a task
 *        handle to pcTaskGetName
 */
void test_pcTaskGetName_assert_xTaskToQuery_is_null( void )
{
    EXPECT_ASSERT_BREAK( pcTaskGetName( NULL ) );

    validate_and_clear_assertions();
}

/*!
 * @brief This test ensures that the code asserts when the idle task
 *         could not be created (handle = NULL) and then
 *         we call xTaskGetIdleTaskHandle
 */
void test_xTaskGetIdleTaskHandle_assert_xIdleTaskHandles_0_is_null( void )
{
    xIdleTaskHandles[ 0 ] = NULL; /* idle task is not created */

    EXPECT_ASSERT_BREAK( xTaskGetIdleTaskHandle() );

    validate_and_clear_assertions();
}

/*!
 * @brief This test ensures that the code asserts when xTaskCatchUpTicks is
 *        called and the scheduler is suspended
 */
void test_xTaskCatchUpTicks_assert_scheduler_suspended( void )
{
    uxSchedulerSuspended = 1;
    EXPECT_ASSERT_BREAK( xTaskCatchUpTicks( 23 ) );

    validate_and_clear_assertions();
}

/*!
 * @brief This test ensures that the code asserts when we call xTaskAbortDelay
 *        with xTask equals to NULL
 */
void test_xTaskAbortDelay_assert_xTask_null( void )
{
    EXPECT_ASSERT_BREAK( xTaskAbortDelay( NULL ) );

    validate_and_clear_assertions();
}

/*!
 * @brief This test ensures that the code asserts when vTaskPlaceOnEventList is
 *        called with pxEventList equals to NULL
 */
void test_vTaskPlaceOnEventList_assert_pxEventList_null( void )
{
    EXPECT_ASSERT_BREAK( vTaskPlaceOnEventList( NULL, 2 ) );

    validate_and_clear_assertions();
}

/*!
 * @brief This test ensures that the code asserts when we call
 *        vTaskPlaceOnEventList with pxEventList equals to NULL
 */
void test_vTaskPlaceOnUnorderedEventList_assert_pxEventList_null( void )
{
    EXPECT_ASSERT_BREAK( vTaskPlaceOnUnorderedEventList( NULL, 2, 3 ) );
    validate_and_clear_assertions();
}

/*!
 * @brief This test ensures that the code asserts when
 *        vTaskPlaceOnUnorderedEventList is called while the scheduler is
 *        not suspended
 */
void test_vTaskPlaceOnUnorderedEventList_assert_scheduler_suspended_eq_zero( void )
{
    List_t xEventList;

    EXPECT_ASSERT_BREAK( vTaskPlaceOnUnorderedEventList( &xEventList, 2, 3 ) );
    validate_and_clear_assertions();
}

/*!
 * @brief This test ensures that the code asserts when
 * vTaskPlaceOnEventListRestricted is called with pxEventList is equal to NULL
 */
void test_vTaskPlaceOnEventListRestricted_assert_pxEventList_eq_NULL( void )
{
    EXPECT_ASSERT_BREAK( vTaskPlaceOnEventListRestricted( NULL, 2, 3 ) );

    validate_and_clear_assertions();
}

/*!
 * @brief This test ensures that the code asserts when the list head entry for
 *        xEventList is NULL
 */
void test_xTaskRemoveFromEventList_assert_event_list_head_entry_null( void )
{
    List_t xEventList;

    listGET_OWNER_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( NULL );

    EXPECT_ASSERT_BREAK( xTaskRemoveFromEventList( &xEventList ) );

    validate_and_clear_assertions();
}

/*!
 * @brief This test ensures that the code asserts when
 * vTaskRemoveFromUnorderedEventList and the scheduler is not suspended
 */
void test_vTaskRemoveFromUnorderedEventList_assert_scheduler_running( void )
{
    ListItem_t xEventListItem;

    uxSchedulerSuspended = pdFALSE;

    EXPECT_ASSERT_BREAK( vTaskRemoveFromUnorderedEventList( &xEventListItem, 2 ) );

    validate_and_clear_assertions();
}

/*!
 * @brief This test ensures that the code asserts when pxUnblockedTCB is null
 */
void test_vTaskRemoveFromUnorderedEventList_assert_( void )
{
    ListItem_t xEventListItem;

    uxSchedulerSuspended = pdTRUE;

    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( NULL );

    EXPECT_ASSERT_BREAK( vTaskRemoveFromUnorderedEventList( &xEventListItem, 2 ) );

    validate_and_clear_assertions();
}

/*!
 * @brief This test ensures that the code asserts when vTaskSettimeOutState is
 *        called with a timeout of zero
 */
void test_vTaskSetTimeOutState_assert_timeout_zero( void )
{
    EXPECT_ASSERT_BREAK( vTaskSetTimeOutState( 0 ) );

    validate_and_clear_assertions();
}

/*!
 * @brief This test ensures that the code asserts when pxTimeout is NULL
 */
void test_xTaskCheckForTimeOut_assert_pxTimeOut_null( void )
{
    TickType_t pxTicksToWait;

    EXPECT_ASSERT_BREAK( xTaskCheckForTimeOut( NULL, &pxTicksToWait ) );

    validate_and_clear_assertions();
}

/*!
 * @brief This test ensures that the code asserts when pxTicksToWait is NULL
 */
void test_xTaskCheckForTimeOut_assert_pxTicksToWait_null( void )
{
    TimeOut_t xTimeOut;

    EXPECT_ASSERT_BREAK( xTaskCheckForTimeOut( &xTimeOut, NULL ) );

    validate_and_clear_assertions();
}

/*!
 * @brief This test ensures that the code asserts when the passed tcb is not
 *        equal to the current tcb
 */
void test_xTaskPriorityDisinherit_assert_tcp_neq_current_tcb( void )
{
    create_task();
    TCB_t * ptcb2 = create_task();

    EXPECT_ASSERT_BREAK( xTaskPriorityDisinherit( ptcb2 ) );

    validate_and_clear_assertions();
}

/*!
 * @brief This test ensures that the code asserts when xTaskPriorityDisinherit
 *        is called with no help mutexes
 */
void test_xTaskPriorityDisinherit_assert_no_mutexes_are_held( void )
{
    TCB_t * ptcb = create_task();

    EXPECT_ASSERT_BREAK( xTaskPriorityDisinherit( ptcb ) );

    validate_and_clear_assertions();
}

/*!
 * @brief This test ensures that the code asserts when the tcb belinging to the
 *        handle is null, or just the handle itself is null
 */
void test_vTaskSetThreadLocalStoragePointer_assert_task_handle_null( void )
{
    EXPECT_ASSERT_BREAK( vTaskSetThreadLocalStoragePointer( NULL, 1, NULL ) );

    validate_and_clear_assertions();
}

/*!
 * @brief This test ensures that the code asserts when a value that is not
 *        defined is assigned to TCB_t -> uxStaticallyAllocated
 */
void test_prvCheckTasksWaitingTermination_assert_out_of_bound_ucStaticallyAllocated( void )

{
    create_task();
    TCB_t * ptcb = create_task();

    ptcb->ucStaticallyAllocated = 3; /* out of range value */

    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( NULL );
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );

    EXPECT_ASSERT_BREAK( vTaskDelete( ptcb ) );

    validate_and_clear_assertions();
}

/*!
 * @brief This test ensures that the code asserts when no mutexes are help byt
 * the tcb
 */
void test_vTaskPriorityDisinheritAfterTimeout_assert_no_held_mutexes( void )
{
    TCB_t * ptcb = create_task();

    EXPECT_ASSERT_BREAK( vTaskPriorityDisinheritAfterTimeout( ptcb, 3 ) );
    validate_and_clear_assertions();
}

/*!
 * @brief This test ensures that the code asserts when tcb is the current tcb
 */
void test_vTaskPriorityDisinheritAfterTimeout_assert_tcb_eq_currentTCB( void )
{
    TCB_t * ptcb = create_task();

    pxCurrentTCB = ptcb;

    pvTaskIncrementMutexHeldCount();

    EXPECT_ASSERT_BREAK( vTaskPriorityDisinheritAfterTimeout( ptcb, 5 ) );

    validate_and_clear_assertions();
}

/*!
 * @brief This test ensures that the code asserts when uxIndexToWait is greater
 *        than of equal to configTASK_NOTIFICATION_ARRAY_ENTRIES
 */
void test_ulTaskGenericNotifyTake_assert_index_gte_config_array_entries( void )
{
    UBaseType_t uxIndex = configTASK_NOTIFICATION_ARRAY_ENTRIES + 2;

    EXPECT_ASSERT_BREAK( ulTaskGenericNotifyTake( uxIndex, 23, 22 ) );

    validate_and_clear_assertions();
}

/*!
 * @brief This test ensures that the code asserts when uxIndexToWait is greater
 *        than of equal to configTASK_NOTIFICATION_ARRAY_ENTRIES
 */
void test_xTaskGenericNotifyWait_assert_index_gte_config_array_entries( void )
{
    UBaseType_t uxIndex = configTASK_NOTIFICATION_ARRAY_ENTRIES + 2;

    EXPECT_ASSERT_BREAK( xTaskGenericNotifyWait( uxIndex, 23, 22, NULL, 23 ) );

    validate_and_clear_assertions();
}

/*!
 * @brief This test ensures that the code asserts when uxIndexToNotify is
 * greater than of equal to configTASK_NOTIFICATION_ARRAY_ENTRIES
 */
void test_xTaskGenericNotify_assert_index_gte_config_array_entries( void )
{
    TCB_t * ptcb = create_task();
    UBaseType_t uxIndex = configTASK_NOTIFICATION_ARRAY_ENTRIES + 2;

    EXPECT_ASSERT_BREAK( xTaskGenericNotify( ptcb, uxIndex, 23,
                                             eSetBits, NULL ) );
    validate_and_clear_assertions();
}

/*!
 * @brief This test ensures that the code asserts when the task to notify is
 *        null
 */
void test_xTaskGenericNotify_assert_null_task_to_notify( void )
{
    UBaseType_t uxIndex = configTASK_NOTIFICATION_ARRAY_ENTRIES - 1;

    EXPECT_ASSERT_BREAK( xTaskGenericNotify( NULL, uxIndex,
                                             23, eSetBits, NULL ) );
    validate_and_clear_assertions();
}

/*!
 * @brief This test ensures that the code asserts when the default action is
 *        reached which we should never get there
 */
void test_xTaskGenericNotify_assert_default_action_tickcount_ne_zero( void )
{
    TCB_t * ptcb = create_task();
    UBaseType_t uxIndex = configTASK_NOTIFICATION_ARRAY_ENTRIES - 1;

    xTickCount = 3;
    EXPECT_ASSERT_BREAK( xTaskGenericNotify( ptcb, uxIndex, 3,
                                             eSetValueWithoutOverwrite + 1,
                                             NULL ) );
    validate_and_clear_assertions();
}

/*!
 * @brief This test ensures that the code asserts when the task state is
 *        taskWAITING_NOTIFICATION and the task is on an event list
 */
void test_xTaskGenericNotify_assert( void )
{
    TCB_t * ptcb = create_task();
    UBaseType_t uxIndex = configTASK_NOTIFICATION_ARRAY_ENTRIES - 1;

    ptcb->ucNotifyState[ uxIndex ] = 1; /* taskWAITING_NOTIFICATION */
    xTickCount = 0;

    listREMOVE_ITEM_ExpectAnyArgs();
    listINSERT_END_ExpectAnyArgs();
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( ( void * ) 1 );
    EXPECT_ASSERT_BREAK( xTaskGenericNotify( ptcb, uxIndex, 3,
                                             eSetValueWithoutOverwrite + 1,
                                             NULL ) );
    validate_and_clear_assertions();
}

/*!
 * @brief This test ensures that the code asserts when uxIndexToNotify is
 *        greater than of equal to configTASK_NOTIFICATION_ARRAY_ENTRIES
 */
void test_xTaskGenericNotifyFromISR_assert_index_gte_config_array_entries( void )
{
    TCB_t * ptcb = create_task();
    UBaseType_t uxIndex = configTASK_NOTIFICATION_ARRAY_ENTRIES + 2;

    EXPECT_ASSERT_BREAK( xTaskGenericNotifyFromISR( ptcb, uxIndex, 23,
                                                    eSetBits, NULL, NULL ) );
    validate_and_clear_assertions();
}

/*!
 * @brief This test ensures that the code asserts when the task to notify is
 *        null
 */
void test_xTaskGenericNotifyFromISR_assert_null_task_to_notify( void )
{
    UBaseType_t uxIndex = configTASK_NOTIFICATION_ARRAY_ENTRIES - 1;

    EXPECT_ASSERT_BREAK( xTaskGenericNotifyFromISR( NULL, uxIndex,
                                                    23, eSetBits, NULL, NULL ) );
    validate_and_clear_assertions();
}

/*!
 * @brief This test ensures that the code asserts when the default action is
 *        reached which we should never get there
 */
void test_xTaskGenericNotifyFromISR_assert_default_action_should_not_get( void )
{
    TCB_t * ptcb = create_task();
    UBaseType_t uxIndex = configTASK_NOTIFICATION_ARRAY_ENTRIES - 1;

    xTickCount = 3;
    EXPECT_ASSERT_BREAK( xTaskGenericNotifyFromISR( ptcb, uxIndex, 3,
                                                    eSetValueWithoutOverwrite + 1,
                                                    NULL, NULL ) );
    validate_and_clear_assertions();
}

/*!
 * @brief This test ensures that the code asserts when the task state is
 *        taskWAITING_NOTIFICATION and the task is on an event list
 */
void test_xTaskGenericNotifyFromISR_assert( void )
{
    UBaseType_t uxIndex = configTASK_NOTIFICATION_ARRAY_ENTRIES - 1;
    TCB_t * ptcb = create_task();

    ptcb->ucNotifyState[ uxIndex ] = 1; /* taskWAITING_NOTIFICATION */
    xTickCount = 0;

    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( ( void * ) 1 );
    EXPECT_ASSERT_BREAK( xTaskGenericNotifyFromISR( ptcb, uxIndex, 3,
                                                    eSetValueWithoutOverwrite + 1,
                                                    NULL, NULL ) );
    validate_and_clear_assertions();
}

/*!
 * @brief This test ensures that the code asserts when the index passed is
 *        greater than or equal to configTASK_NOTIFICATION_ARRAY_ENTRIES
 */
void test_xTaskGenericNotifyStateClear_assert_index_gte_array_entries( void )
{
    EXPECT_ASSERT_BREAK( xTaskGenericNotifyStateClear( NULL,
                                                       configTASK_NOTIFICATION_ARRAY_ENTRIES + 2 ) );
    validate_and_clear_assertions();
}
