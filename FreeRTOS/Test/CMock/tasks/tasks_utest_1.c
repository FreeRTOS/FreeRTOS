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
/*! @file tasks_utest.c */

/* C runtime includes. */
/*#include <stdlib.h> */
#include <stdbool.h>
#include <string.h>

/* Test includes. */
#include "unity.h"

/* Tasks includes */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"

#include "mock_list.h"
#include "mock_list_macros.h"
#include "mock_timers.h"
#include "mock_portable.h"

#include "task.h"

typedef struct tskTaskControlBlock       /* The old naming convention is used to prevent breaking kernel aware debuggers. */
{
    volatile StackType_t * pxTopOfStack; /*< Points to the location of the last item placed on the tasks stack.  THIS MUST BE THE FIRST MEMBER OF THE TCB STRUCT. */

    #if ( portUSING_MPU_WRAPPERS == 1 )
        xMPU_SETTINGS xMPUSettings; /*< The MPU settings are defined as part of the port layer.  THIS MUST BE THE SECOND MEMBER OF THE TCB STRUCT. */
    #endif

    ListItem_t xStateListItem;                  /*< The list that the state list item of a task is reference from denotes the state of that task (Ready, Blocked, Suspended ). */
    ListItem_t xEventListItem;                  /*< Used to reference a task from an event list. */
    UBaseType_t uxPriority;                     /*< The priority of the task.  0 is the lowest priority. */
    StackType_t * pxStack;                      /*< Points to the start of the stack. */
    char pcTaskName[ configMAX_TASK_NAME_LEN ]; /*< Descriptive name given to the task when created.  Facilitates debugging only. */ /*lint !e971 Unqualified char types are allowed for strings and single characters only. */

    #if ( ( portSTACK_GROWTH > 0 ) || ( configRECORD_STACK_HIGH_ADDRESS == 1 ) )
        StackType_t * pxEndOfStack; /*< Points to the highest valid address for the stack. */
    #endif

    #if ( portCRITICAL_NESTING_IN_TCB == 1 )
        UBaseType_t uxCriticalNesting; /*< Holds the critical section nesting depth for ports that do not maintain their own count in the port layer. */
    #endif

    #if ( configUSE_TRACE_FACILITY == 1 )
        UBaseType_t uxTCBNumber;  /*< Stores a number that increments each time a TCB is created.  It allows debuggers to determine when a task has been deleted and then recreated. */
        UBaseType_t uxTaskNumber; /*< Stores a number specifically for use by third party trace code. */
    #endif

    #if ( configUSE_MUTEXES == 1 )
        UBaseType_t uxBasePriority; /*< The priority last assigned to the task - used by the priority inheritance mechanism. */
        UBaseType_t uxMutexesHeld;
    #endif

    #if ( configUSE_APPLICATION_TASK_TAG == 1 )
        TaskHookFunction_t pxTaskTag;
    #endif

    #if ( configNUM_THREAD_LOCAL_STORAGE_POINTERS > 0 )
        void * pvThreadLocalStoragePointers[ configNUM_THREAD_LOCAL_STORAGE_POINTERS ];
    #endif

    #if ( configGENERATE_RUN_TIME_STATS == 1 )
        uint32_t ulRunTimeCounter; /*< Stores the amount of time the task has spent in the Running state. */
    #endif

    #if ( configUSE_NEWLIB_REENTRANT == 1 )

        /* Allocate a Newlib reent structure that is specific to this task.
         * Note Newlib support has been included by popular demand, but is not
         * used by the FreeRTOS maintainers themselves.  FreeRTOS is not
         * responsible for resulting newlib operation.  User must be familiar with
         * newlib and must provide system-wide implementations of the necessary
         * stubs. Be warned that (at the time of writing) the current newlib design
         * implements a system-wide malloc() that must be provided with locks.
         *
         * See the third party link http://www.nadler.com/embedded/newlibAndFreeRTOS.html
         * for additional information. */
        struct  _reent xNewLib_reent;
    #endif

    #if ( configUSE_TASK_NOTIFICATIONS == 1 )
        volatile uint32_t ulNotifiedValue[ configTASK_NOTIFICATION_ARRAY_ENTRIES ];
        volatile uint8_t ucNotifyState[ configTASK_NOTIFICATION_ARRAY_ENTRIES ];
    #endif

    /* See the comments in FreeRTOS.h with the definition of
     * tskSTATIC_AND_DYNAMIC_ALLOCATION_POSSIBLE. */
    #if ( tskSTATIC_AND_DYNAMIC_ALLOCATION_POSSIBLE != 0 ) /*lint !e731 !e9029 Macro has been consolidated for readability reasons. */
        uint8_t ucStaticallyAllocated;                     /*< Set to pdTRUE if the task is a statically allocated to ensure no attempt is made to free the memory. */
    #endif

    #if ( INCLUDE_xTaskAbortDelay == 1 )
        uint8_t ucDelayAborted;
    #endif

    #if ( configUSE_POSIX_ERRNO == 1 )
        int iTaskErrno;
    #endif
} tskTCB;

typedef tskTCB TCB_t;



/* ===========================  DEFINES CONSTANTS  ========================== */
typedef void (*port_yield_operation)(void);

/* ===========================  GLOBAL VARIABLES  =========================== */

static TCB_t * ptcb;
static TCB_t tcb[10]; /* simulate up to 10 tasks: add them if needed */
StackType_t stack[ ( ( size_t ) 300 ) * sizeof( StackType_t ) ];
static bool vApplicationTickHook_Called  = false;
static bool vTaskDeletePreCalled = false;
static bool getIddleTaskMemoryValid = false;
static bool getIddleTaskMemoryCalled = false;
static uint32_t critical_section_counter = 0;
static bool is_first_task = true;
static uint32_t created_tasks = 0;
static bool port_yield_called = false;
static uint32_t created_task_priority = 3;
static bool port_setup_tcb_called  = false;
static port_yield_operation py_operation;
static bool portClear_Interrupt_called = false;
static bool portSet_Interrupt_called = false;
static bool port_invalid_interrupt_called = false;

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
/* configGENERATE_RUN_TIME_STATS */
//extern uint32_t ulTaskSwitchedInTime;
//extern volatile uint32_t ulTotalRunTime;

/* ============================  MACRO FUNCTIONS  ============================ */
#define ASSERT_SETUP_TCB_CALLED()                                              \
        do {                                                                   \
            TEST_ASSERT_EQUAL( true, port_setup_tcb_called );                  \
            port_setup_tcb_called = false;                                     \
        } while ( 0 )
#define ASSERT_SETUP_TCB_NOT_CALLED()                                          \
        do {                                                                   \
            TEST_ASSERT_EQUAL( false, port_setup_tcb_called );                 \
        } while ( 0 )

#define ASSERT_PORT_YIELD_CALLED()                                             \
        do {                                                                   \
            TEST_ASSERT_EQUAL( true, port_yield_called );                      \
            port_yield_called = false;                                         \
        } while ( 0 )

#define ASSERT_PORT_YIELD_NOT_CALLED()                                         \
        do {                                                                   \
            TEST_ASSERT_EQUAL( false, port_yield_called );                     \
        } while ( 0 )

#define ASSERT_TASK_DELETE_CALLED()                                            \
        do {                                                                   \
            TEST_ASSERT_EQUAL( true, vTaskDeletePreCalled );                   \
             vTaskDeletePreCalled = false;                                     \
        } while ( 0 )

#define ASSERT_TASK_DELETE_NOT_CALLED()                                        \
        do {                                                                   \
            TEST_ASSERT_EQUAL( false, vTaskDeletePreCalled );                  \
        } while ( 0 )

#define ASSERT_APP_TICK_HOOK_CALLED()                                            \
        do {                                                                   \
            TEST_ASSERT_EQUAL( true, vApplicationTickHook_Called );                   \
             vApplicationTickHook_Called = false;                                     \
        } while ( 0 )

#define  ASSERT_APP_TICK_HOOK_NOT_CALLED()                                        \
        do {                                                                   \
            TEST_ASSERT_EQUAL( false, vApplicationTickHook_Called );                  \
        } while ( 0 )

#define ASSERT_PORT_CLEAR_INTERRUPT_CALLED()                                   \
        do {                                                                   \
            TEST_ASSERT_EQUAL( true, portClear_Interrupt_called );             \
            portClear_Interrupt_called = false;                                \
        } while ( 0 )
#define ASSERT_PORT_CLEAR_INTERRUPT_NOT_CALLED()                               \
        do {                                                                   \
            TEST_ASSERT_EQUAL( false, portClear_Interrupt_called );            \
        } while ( 0 )

#define ASSERT_PORT_SET_INTERRUPT_CALLED()                                     \
        do {                                                                   \
            TEST_ASSERT_EQUAL( true, portSet_Interrupt_called );               \
            portSet_Interrupt_called = false;                                  \
        } while ( 0 )
#define ASSERT_PORT_SET_INTERRUPT_NOT_CALLED()                                 \
        do {                                                                   \
            TEST_ASSERT_EQUAL( false, portSet_Interrupt_called );              \
        } while ( 0 )

#define ASSERT_INVALID_INTERRUPT_PRIORITY_CALLED()                             \
        do {                                                                   \
            TEST_ASSERT_EQUAL(true, port_invalid_interrupt_called);            \
            port_invalid_interrupt_called = false;                             \
        } while( 0 )

/* ============================  HOOK FUNCTIONS  ============================ */
#define HOOK_DIAG() \
    do { \
    printf("%s called\n", __FUNCTION__); \
    } while (0) 
#undef HOOK_DIAG
#define HOOK_DIAG()


static void dummy_opration()
{
}

void vApplicationIdleHook( void )
{
    HOOK_DIAG();
}

void vApplicationMallocFailedHook( void )
{
    HOOK_DIAG();
}

static StaticTask_t xIdleTaskTCB;
static StackType_t uxIdleTaskStack[ configMINIMAL_STACK_SIZE ];

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

void portClear_Interrupt_Mask(UBaseType_t bt)
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

void portAssert_if_int_prio_invalid(void)
{
    port_invalid_interrupt_called = true;
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
    pxDelayedTaskList = NULL;
    pxOverflowDelayedTaskList = NULL;
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
  //  ulTaskSwitchedInTime = 0UL;
    //ulTotalRunTime = 0UL;

    vApplicationTickHook_Called  = false;
    vTaskDeletePreCalled = false;
    getIddleTaskMemoryCalled = false;
    is_first_task = true;
    created_tasks = 0;
    port_yield_called  = false;
    port_setup_tcb_called = false;
    portClear_Interrupt_called = false;
    portSet_Interrupt_called = false;
    port_invalid_interrupt_called = false;
    py_operation = dummy_opration;
}

/*! called after each testcase */
void tearDown( void )
{
    TEST_ASSERT_EQUAL( 0, critical_section_counter );

    /*
     * vPortEndScheduler_Expect();
     * vTaskEndScheduler();
     */
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

static TaskHandle_t create_task()
{
    TaskFunction_t pxTaskCode = NULL;
    const char * const pcName = { __FUNCTION__ };
    const uint32_t usStackDepth = 300;
    void * const pvParameters = NULL;
    UBaseType_t uxPriority = created_task_priority;
    TaskHandle_t taskHandle;
    BaseType_t ret;

    pvPortMalloc_ExpectAndReturn( usStackDepth * sizeof( StackType_t ), stack );
    pvPortMalloc_ExpectAndReturn( sizeof( TCB_t ), &tcb[created_tasks] );

    vListInitialiseItem_Expect( &( tcb[created_tasks].xStateListItem ) );
    vListInitialiseItem_Expect( &( tcb[created_tasks].xEventListItem ) );
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
    StackType_t buffer[ 300 ];
    StaticTask_t pxTaskBuffer[ sizeof( TCB_t ) ];
    TaskFunction_t pxTaskCode = NULL;
    const char * const pcName = { __FUNCTION__ };
    const uint32_t ulStackDepth = 300;
    void * const pvParameters = NULL;
    UBaseType_t uxPriority = 3;
    TaskHandle_t ret;

    memset( buffer, 0xa5U, ulStackDepth * sizeof( StackType_t ) );

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
                               buffer,
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
    TCB_t * tcbPtr;

    pvPortMalloc_ExpectAndReturn( usStackDepth * sizeof( StackType_t ), stack );
    pvPortMalloc_ExpectAndReturn( sizeof( TCB_t ), &tcb[0] );

    vListInitialiseItem_Expect( &( tcb[0].xStateListItem ) );
    vListInitialiseItem_Expect( &( tcb[0].xEventListItem ) );
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
    TEST_ASSERT_EQUAL( 0, tcb[0].ucStaticallyAllocated );
    TEST_ASSERT_EQUAL_PTR( &tcb[0], ptcb );
    TEST_ASSERT_EQUAL( stack, tcb[0].pxStack );
    TEST_ASSERT_EQUAL( 1, uxCurrentNumberOfTasks );
    TEST_ASSERT_EQUAL( configMAX_PRIORITIES - 1, ptcb->uxPriority );
    TEST_ASSERT_EQUAL( NULL, ptcb->pcTaskName[0]);
    ASSERT_SETUP_TCB_CALLED();
}

void test_xTaskCreate_success_null_task_handle( void )
{
    TaskFunction_t pxTaskCode = NULL;
    const char * const pcName = NULL;
    const uint32_t usStackDepth = 300;
    void * const pvParameters = NULL;
    UBaseType_t uxPriority = configMAX_PRIORITIES;
    TaskHandle_t taskHandle;
    BaseType_t ret;
    StackType_t stack[ ( ( size_t ) usStackDepth ) * sizeof( StackType_t ) ];
    TCB_t * tcbPtr;

    pvPortMalloc_ExpectAndReturn( usStackDepth * sizeof( StackType_t ), stack );
    pvPortMalloc_ExpectAndReturn( sizeof( TCB_t ), &tcb[0] );

    vListInitialiseItem_Expect( &( tcb[0].xStateListItem ) );
    vListInitialiseItem_Expect( &( tcb[0].xEventListItem ) );
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
                       NULL );
    TEST_ASSERT_EQUAL( pdPASS, ret );
    TEST_ASSERT_EQUAL( 0, tcb[0].ucStaticallyAllocated );
    TEST_ASSERT_EQUAL( stack, tcb[0].pxStack );
    TEST_ASSERT_EQUAL( 1, uxCurrentNumberOfTasks );
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
void test_vTaskDelete_sucess_current_task( void )
{
    TCB_t * tcbPtr;

    tcbPtr = ( TCB_t * ) create_task( );

    TEST_ASSERT_EQUAL( 1, uxCurrentNumberOfTasks );

    /* Expectations */
    uxListRemove_ExpectAndReturn( &tcbPtr->xStateListItem, pdPASS );
    listLIST_ITEM_CONTAINER_ExpectAndReturn(&tcbPtr->xEventListItem, NULL);
    vListInsertEnd_ExpectAnyArgs();
    /* API call */
    vTaskDelete( tcbPtr );
    /* Validations */
    ASSERT_TASK_DELETE_CALLED();
    TEST_ASSERT_EQUAL( 1, uxCurrentNumberOfTasks );
    TEST_ASSERT_EQUAL( 1, uxDeletedTasksWaitingCleanUp );
}

void test_vTaskDelete_sucess_current_task_ready_empty( void )
{
    TCB_t * tcbPtr;

    tcbPtr = ( TCB_t * ) create_task( );

    TEST_ASSERT_EQUAL( 1, uxCurrentNumberOfTasks );

    /* Expectations */
    uxListRemove_ExpectAndReturn( &tcbPtr->xStateListItem, pdFAIL );
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &pxReadyTasksLists[tcbPtr->uxPriority], 0 );
    listLIST_ITEM_CONTAINER_ExpectAndReturn(&tcbPtr->xEventListItem, NULL);
    vListInsertEnd_ExpectAnyArgs();
    /* API call */
    vTaskDelete( tcbPtr );
    /* Validations */
    ASSERT_TASK_DELETE_CALLED();
    TEST_ASSERT_EQUAL( 1, uxCurrentNumberOfTasks );
    TEST_ASSERT_EQUAL( 1, uxDeletedTasksWaitingCleanUp );
}

void test_vTaskDelete_sucess_current_task_ready_empty_null_task( void )
{
    TCB_t * tcbPtr;

    tcbPtr = ( TCB_t * ) create_task( );

    TEST_ASSERT_EQUAL( 1, uxCurrentNumberOfTasks );

    /* Expectations */
    uxListRemove_ExpectAndReturn( &tcbPtr->xStateListItem, pdFAIL );
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &pxReadyTasksLists[tcbPtr->uxPriority], 1 );
    listLIST_ITEM_CONTAINER_ExpectAndReturn(&tcbPtr->xEventListItem, NULL);
    vListInsertEnd_ExpectAnyArgs();
    /* API call */
    vTaskDelete( NULL );
    /* Validations */
    ASSERT_TASK_DELETE_CALLED();
    TEST_ASSERT_EQUAL( 1, uxCurrentNumberOfTasks );
    TEST_ASSERT_EQUAL( 1, uxDeletedTasksWaitingCleanUp );
}

void test_vTaskDelete_sucess_current_task_yield( void )
{
    TCB_t * tcbPtr;

    xSchedulerRunning = pdTRUE;
    tcbPtr = ( TCB_t * ) create_task( );

    TEST_ASSERT_EQUAL( 1, uxCurrentNumberOfTasks );

    /* Expectations */
    uxListRemove_ExpectAndReturn( &tcbPtr->xStateListItem, pdPASS );
    listLIST_ITEM_CONTAINER_ExpectAndReturn(&tcbPtr->xEventListItem, NULL);
    vListInsertEnd_ExpectAnyArgs();
    /* API call */
    vTaskDelete( tcbPtr );
    /* Validations */
    ASSERT_TASK_DELETE_CALLED();
    ASSERT_PORT_YIELD_CALLED();
    TEST_ASSERT_EQUAL( 1, uxCurrentNumberOfTasks );
    TEST_ASSERT_EQUAL( 1, uxDeletedTasksWaitingCleanUp );
}

void test_vTaskDelete_sucess_not_current_task( void )
{
    TCB_t * tcbPtr;

    tcbPtr = ( TCB_t * ) create_task( );
    TEST_ASSERT_EQUAL( 1, uxCurrentNumberOfTasks );

    /* Expectations */
    uxListRemove_ExpectAndReturn( &tcbPtr->xStateListItem, pdPASS );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &tcbPtr->xEventListItem,
                                             &xPendingReadyList );
    uxListRemove_ExpectAndReturn(&tcbPtr->xEventListItem, pdTRUE);
    vPortFree_ExpectAnyArgs();
    vPortFree_ExpectAnyArgs();
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn (pdTRUE);
    pxCurrentTCB = NULL;
    /* API call */
    vTaskDelete( tcbPtr );
    /* Validations */
    TEST_ASSERT_EQUAL( 0, uxCurrentNumberOfTasks );
    TEST_ASSERT_EQUAL( 0, uxDeletedTasksWaitingCleanUp );
}

void test_vTaskDelete_sucess_not_current_task_no_yield( void )
{
    TCB_t * tcbPtr;

    xSchedulerRunning = pdTRUE;
    tcbPtr = ( TCB_t * ) create_task( );
    TEST_ASSERT_EQUAL( 1, uxCurrentNumberOfTasks );

    /* Expectations */
    uxListRemove_ExpectAndReturn( &tcbPtr->xStateListItem, pdPASS );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &tcbPtr->xEventListItem,
                                             &xPendingReadyList );
    uxListRemove_ExpectAndReturn(&tcbPtr->xEventListItem, pdTRUE);
    vPortFree_ExpectAnyArgs();
    vPortFree_ExpectAnyArgs();
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn (pdTRUE);
    pxCurrentTCB = NULL;
    /* API call */
    vTaskDelete( tcbPtr );
    /* Validations */
    TEST_ASSERT_EQUAL( 0, uxCurrentNumberOfTasks );
    TEST_ASSERT_EQUAL( 0, uxDeletedTasksWaitingCleanUp );
    ASSERT_PORT_YIELD_NOT_CALLED();
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

    vListInsertEnd_ExpectAnyArgs();

    xTimerCreateTimerTask_ExpectAndReturn( pdPASS );
    xPortStartScheduler_ExpectAndReturn( pdTRUE );
    getIddleTaskMemoryValid = true;
    vTaskStartScheduler();

    TEST_ASSERT_EQUAL( true, getIddleTaskMemoryCalled );
    /* should be 2 the idle task and timer task, but the timer task is a mock */
    TEST_ASSERT_EQUAL( 1, uxCurrentNumberOfTasks );
    TEST_ASSERT_EQUAL( pdTRUE, xSchedulerRunning );
}

void test_vTaskStartScheduler_idle_fail( void )
{
    getIddleTaskMemoryValid = false;
    vTaskStartScheduler();

    TEST_ASSERT_EQUAL( true, getIddleTaskMemoryCalled );
    /* should be 2 the idle task and timer task, but the timer task is a mock */
    TEST_ASSERT_EQUAL( 0, uxCurrentNumberOfTasks );
    TEST_ASSERT_EQUAL( pdFALSE, xSchedulerRunning );
}

void test_vTaskEndScheduler_success()
{
    vPortEndScheduler_Expect();
    vTaskEndScheduler();
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
    TCB_t * ptcb;
    TaskHandle_t taskHandle;

    taskHandle = create_task( );
    ptcb = ( TCB_t * ) taskHandle;
    vListInsertEnd_Ignore();
    create_task( );
    vTaskSuspendAll();
    TEST_ASSERT_EQUAL( 2, uxCurrentNumberOfTasks );

    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn(ptcb);
    uxListRemove_ExpectAndReturn(&(ptcb->xEventListItem), pdPASS);
    uxListRemove_ExpectAndReturn(&(ptcb->xStateListItem), pdPASS);
    vListInsertEnd_ExpectAnyArgs();
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    ret = xTaskResumeAll();
    TEST_ASSERT_EQUAL( pdTRUE, ret );
    TEST_ASSERT_EQUAL( 0, uxSchedulerSuspended );
}

/* new priority greater than the current priority */
void test_vTaskPrioritySet_success_gt_curr_prio(void)
{
    TaskHandle_t taskHandle;
    TaskHandle_t taskHandle2;
    TCB_t * ptcb;
    created_task_priority = 3;
    taskHandle = create_task();
    created_task_priority = 4;
    taskHandle2 = create_task();
    ptcb = (TCB_t*) taskHandle2;
    TEST_ASSERT_EQUAL_PTR(pxCurrentTCB, taskHandle2);
    listGET_LIST_ITEM_VALUE_ExpectAnyArgsAndReturn(0);
    listSET_LIST_ITEM_VALUE_Expect( &(ptcb->xEventListItem),
                                    configMAX_PRIORITIES  - 5 );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &pxReadyTasksLists [5],
                                             &( ptcb->xStateListItem ),
                                             pdTRUE );
    uxListRemove_ExpectAndReturn(&(ptcb->xStateListItem), 0);
    /* port Reset ready priority */
    /* add task to ready list */
    vListInsertEnd_Expect( &( pxReadyTasksLists[ 5 ] ),
                           &( ptcb->xStateListItem ) );

    TEST_ASSERT_EQUAL ( 4, ptcb->uxBasePriority );
    TEST_ASSERT_EQUAL ( 4, ptcb->uxPriority );
    vTaskPrioritySet( taskHandle2, created_task_priority + 1);
    TEST_ASSERT_EQUAL ( 4 + 1, ptcb->uxBasePriority );
    TEST_ASSERT_EQUAL ( 4 + 1, ptcb->uxPriority );
    ASSERT_PORT_YIELD_NOT_CALLED();
}

void test_vTaskPrioritySet_success_gt_curr_prio_curr_tcb(void)
{
    TaskHandle_t taskHandle;
    TaskHandle_t taskHandle2;
    TCB_t * ptcb;
    created_task_priority = 3;
    taskHandle = create_task();
    created_task_priority = 4;
    taskHandle2 = create_task();
    ptcb = (TCB_t*) taskHandle;

    TEST_ASSERT_EQUAL_PTR( pxCurrentTCB, taskHandle2 );

    listGET_LIST_ITEM_VALUE_ExpectAnyArgsAndReturn(0);
    listSET_LIST_ITEM_VALUE_Expect( &(ptcb->xEventListItem), 2);
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &pxReadyTasksLists [5],
                                             &( ptcb->xStateListItem ),
                                             pdTRUE );
    uxListRemove_ExpectAndReturn( &(ptcb->xStateListItem), 0 );
    /* port Reset ready priority */
    /* add task to ready list */
    vListInsertEnd_Expect( &( pxReadyTasksLists[ 5 ] ),
                           &( ptcb->xStateListItem ) );

    TEST_ASSERT_EQUAL ( 3, ptcb->uxBasePriority );
    TEST_ASSERT_EQUAL ( 3, ptcb->uxPriority );
    vTaskPrioritySet( taskHandle, created_task_priority + 3 );
    TEST_ASSERT_EQUAL ( 4 + 3, ptcb->uxBasePriority );
    TEST_ASSERT_EQUAL ( 4 + 3, ptcb->uxPriority );
    ASSERT_PORT_YIELD_CALLED();
}


void test_vTaskPrioritySet_success_gt_max_prio(void)
{
    TaskHandle_t taskHandle;
    TCB_t * ptcb;
    created_task_priority = 3;
    taskHandle = create_task();
    ptcb = (TCB_t*) taskHandle;

    /* expectations */
    listGET_LIST_ITEM_VALUE_ExpectAnyArgsAndReturn(0x80000000UL);
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &pxReadyTasksLists [5],
                                             &( ptcb->xStateListItem ),
                                             pdTRUE );
    uxListRemove_ExpectAndReturn( &(ptcb->xStateListItem), 0 );
    vListInsertEnd_Expect( &( pxReadyTasksLists[ 5 ] ),
                           &( ptcb->xStateListItem ) );

    /* API call */
    vTaskPrioritySet(taskHandle, configMAX_PRIORITIES + 5);

    /* validations */
    TEST_ASSERT_EQUAL(configMAX_PRIORITIES - 1, ptcb->uxBasePriority);
    ASSERT_PORT_YIELD_NOT_CALLED();
}

void test_vTaskPrioritySet_success_call_current_null(void)
{
    TaskHandle_t taskHandle;
    TCB_t * ptcb;
    created_task_priority = 3;
    taskHandle = create_task();
    ptcb = (TCB_t*) taskHandle;

    /* expectations */
    listGET_LIST_ITEM_VALUE_ExpectAnyArgsAndReturn(0x80000000UL);
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &pxReadyTasksLists [5],
                                             &( ptcb->xStateListItem ),
                                             pdTRUE );
    uxListRemove_ExpectAndReturn( &(ptcb->xStateListItem), 0 );
    vListInsertEnd_Expect( &( pxReadyTasksLists[ 5 ] ),
                           &( ptcb->xStateListItem ) );

    /* API call */
    vTaskPrioritySet(NULL, 4);

    /* validations */
    TEST_ASSERT_EQUAL(4, ptcb->uxBasePriority);
    ASSERT_PORT_YIELD_NOT_CALLED();
}
/* ensures that setting the same priority for a tasks changes nothing */
void test_vTaskPrioritySet_success_same_prio(void)
{
    TaskHandle_t taskHandle;
    TCB_t * ptcb;
    created_task_priority = 3;
    taskHandle = create_task();
    ptcb = (TCB_t*) taskHandle;
    TEST_ASSERT_EQUAL_PTR( pxCurrentTCB, ptcb );
    /* expectations */

    /* API call */
    vTaskPrioritySet(taskHandle, 3);

    /* Validations */
    TEST_ASSERT_EQUAL(3, ptcb->uxBasePriority);
    TEST_ASSERT_EQUAL(3, ptcb->uxPriority);
    ASSERT_PORT_YIELD_NOT_CALLED();
}


/* ensures if the set priority is less thatn the current priority and it is the
 * current tcb the task is yielded
 */
void test_vTaskPrioritySet_success_lt_curr_prio_curr_task(void)
{
    TaskHandle_t taskHandle;
    TCB_t * ptcb;
    created_task_priority = 3;
    taskHandle = create_task();
    ptcb = (TCB_t*) taskHandle;
    TEST_ASSERT_EQUAL_PTR( pxCurrentTCB, ptcb );

    /* Expectations */
    listGET_LIST_ITEM_VALUE_ExpectAnyArgsAndReturn(0);
    listSET_LIST_ITEM_VALUE_Expect( &(ptcb->xEventListItem),
                                    configMAX_PRIORITIES - 2 );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &pxReadyTasksLists [5],
                                             &( ptcb->xStateListItem ),
                                             pdTRUE );
    uxListRemove_ExpectAndReturn( &(ptcb->xStateListItem), 1 );
    vListInsertEnd_Expect( &( pxReadyTasksLists[ 5 ] ),
                           &( ptcb->xStateListItem ) );
    /* API call */
    vTaskPrioritySet(taskHandle, 2);

    /* Validations */
    TEST_ASSERT_EQUAL(2, ptcb->uxBasePriority);
    ASSERT_PORT_YIELD_CALLED();
}

/* ensures if the set priority is less thatn the current priority and it is not
 * the current tcb the task is not yielded
 */
void test_vTaskPrioritySet_success_lt_curr_prio_not_curr_task(void)
{
    TaskHandle_t taskHandle, taskHandle2;
    TCB_t * ptcb;
    created_task_priority = 3;
    taskHandle = create_task();
    created_task_priority = 4;
    taskHandle2 = create_task();
    ptcb = (TCB_t*) taskHandle;
    TEST_ASSERT_EQUAL_PTR( pxCurrentTCB, taskHandle2 );

    /* Expectations */
    listGET_LIST_ITEM_VALUE_ExpectAnyArgsAndReturn(0);
    listSET_LIST_ITEM_VALUE_Expect( &(ptcb->xEventListItem),
                                    configMAX_PRIORITIES - 2 );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &pxReadyTasksLists [5],
                                             &( ptcb->xStateListItem ),
                                             pdFALSE );
    /* API call */
    vTaskPrioritySet(taskHandle, 2);

    /* Validations */
    TEST_ASSERT_EQUAL(2, ptcb->uxBasePriority);
    ASSERT_PORT_YIELD_NOT_CALLED();
}

/* This test ensures that if the base priority is different greater than that the current
 * priority the resulting base  will be equal to the new priority while the
 * current priority will be equal to the inherited priority
 * and port yield hook will be called
 * */
void test_vTaskPrioritySet_success_gt_curr_prio_diff_base(void)
{
    TaskHandle_t taskHandle, taskHandle2;
    TCB_t * ptcb;
    created_task_priority = 3;
    taskHandle = create_task();
    created_task_priority = 4;
    taskHandle2 = create_task();
    ptcb = (TCB_t*) taskHandle;
    TEST_ASSERT_EQUAL_PTR( pxCurrentTCB, taskHandle2 );
    /* task handle will inherit the priorit of taskHandle2 */
    listGET_LIST_ITEM_VALUE_ExpectAnyArgsAndReturn(0x80000000UL);
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &pxReadyTasksLists [3],
                                             &( taskHandle->xStateListItem ),
                                             pdFALSE );
    xTaskPriorityInherit(taskHandle);

    TEST_ASSERT_EQUAL(4, ptcb->uxPriority);
    TEST_ASSERT_EQUAL(3, ptcb->uxBasePriority);
    /* Expectations */
    listGET_LIST_ITEM_VALUE_ExpectAnyArgsAndReturn(0);
    listSET_LIST_ITEM_VALUE_Expect( &(ptcb->xEventListItem),
                                    configMAX_PRIORITIES - 5 );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &pxReadyTasksLists [5],
                                             &( ptcb->xStateListItem ),
                                             pdFALSE );
    /* API call */
    vTaskPrioritySet(taskHandle, 5);

    /* Validations */
    TEST_ASSERT_EQUAL(5, ptcb->uxBasePriority);
    TEST_ASSERT_EQUAL(4, ptcb->uxPriority);
    ASSERT_PORT_YIELD_CALLED();
}

/* This test ensures that if the base priority is different less than that the current
 * priority the resulting base  will be equal to the new priority while the
 * current priority will be equal to the inherited priority
 * */
void test_vTaskPrioritySet_success_lt_curr_prio_diff_base(void)
{
    TaskHandle_t taskHandle, taskHandle2;
    TCB_t * ptcb;
    created_task_priority = 3;
    taskHandle = create_task();
    created_task_priority = 6;
    taskHandle2 = create_task();
    ptcb = (TCB_t*) taskHandle;
    TEST_ASSERT_EQUAL_PTR( pxCurrentTCB, taskHandle2 );
    /* task handle will inherit the priorit of taskHandle2 */
    listGET_LIST_ITEM_VALUE_ExpectAnyArgsAndReturn(0x80000000UL);
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &pxReadyTasksLists [3],
                                             &( taskHandle->xStateListItem ),
                                             pdFALSE );
    xTaskPriorityInherit(taskHandle);

    TEST_ASSERT_EQUAL(6, ptcb->uxPriority);
    TEST_ASSERT_EQUAL(3, ptcb->uxBasePriority);
    /* Expectations */
    listGET_LIST_ITEM_VALUE_ExpectAnyArgsAndReturn(0);
    listSET_LIST_ITEM_VALUE_Expect( &(ptcb->xEventListItem),
                                    configMAX_PRIORITIES - 5 );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &pxReadyTasksLists [5],
                                             &( ptcb->xStateListItem ),
                                             pdFALSE );
    /* API call */
    vTaskPrioritySet(taskHandle, 5);

    /* Validations */
    TEST_ASSERT_EQUAL(5, ptcb->uxBasePriority);
    TEST_ASSERT_EQUAL(6, ptcb->uxPriority);
    ASSERT_PORT_YIELD_NOT_CALLED();
}
/* testing INCLUDE_uxTaskPriorityGet */
/* Ensures the correct priority is returned */
void test_uxTaskPriorityGet_success(void)
{
    TaskHandle_t taskHandle;
    UBaseType_t ret_priority;
    TCB_t * ptcb;
    created_task_priority = 3;
    taskHandle = create_task();
    ptcb = (TCB_t*) taskHandle;
    TEST_ASSERT_EQUAL_PTR( pxCurrentTCB, ptcb );
    /* expectations */

    /* API call */
    ret_priority = uxTaskPriorityGet(taskHandle);

    /* Validations */
    TEST_ASSERT_EQUAL(3, ret_priority);
}

void test_uxTaskPriorityGet_success_null_handle(void)
{
    TaskHandle_t taskHandle;
    UBaseType_t ret_priority;
    TCB_t * ptcb;
    created_task_priority = 3;
    taskHandle = create_task();
    ptcb = (TCB_t*) taskHandle;
    TEST_ASSERT_EQUAL_PTR( pxCurrentTCB, ptcb );
    /* expectations */

    /* API call */
    ret_priority = uxTaskPriorityGet(NULL);

    /* Validations */
    TEST_ASSERT_EQUAL(3, ret_priority);
}

void test_uxTaskPriorityGetFromISR_success( void )
{
    TaskHandle_t taskHandle;
    UBaseType_t ret_priority;
    TCB_t * ptcb;
    created_task_priority = 3;
    taskHandle = create_task();
    ptcb = (TCB_t*) taskHandle;
    TEST_ASSERT_EQUAL_PTR( pxCurrentTCB, ptcb );
    ret_priority = uxTaskPriorityGetFromISR( taskHandle );

    TEST_ASSERT_EQUAL(3, ret_priority);
    ASSERT_PORT_CLEAR_INTERRUPT_CALLED();
    ASSERT_PORT_SET_INTERRUPT_CALLED();
    ASSERT_INVALID_INTERRUPT_PRIORITY_CALLED();
}

void test_uxTaskPriorityGetFromISR_success_null_handle( void )
{
    TaskHandle_t taskHandle;
    UBaseType_t ret_priority;
    TCB_t * ptcb;
    created_task_priority = 3;
    taskHandle = create_task();
    ptcb = (TCB_t*) taskHandle;
    TEST_ASSERT_EQUAL_PTR( pxCurrentTCB, ptcb );
    ret_priority = uxTaskPriorityGetFromISR( NULL );

    TEST_ASSERT_EQUAL(3, ret_priority);
    ASSERT_PORT_CLEAR_INTERRUPT_CALLED();
    ASSERT_PORT_SET_INTERRUPT_CALLED();
    ASSERT_INVALID_INTERRUPT_PRIORITY_CALLED();
}

/* ----------------------- testing vTaskDelay API --------------------------- */
void test_vTaskDelay_success_gt_0_yield_called(void)
{
    TaskHandle_t task_handle;
    task_handle = create_task();
    ptcb = ( TCB_t * )task_handle;
    TickType_t delay = 34;
    /* Expectations */
    /* prvAddCurrentTaskToDelayedList */
    uxListRemove_ExpectAndReturn(&ptcb->xStateListItem, 1);
    listSET_LIST_ITEM_VALUE_Expect( &ptcb->xStateListItem,
                                    xTickCount + delay );
    vListInsert_Expect(pxOverflowDelayedTaskList, &ptcb->xStateListItem);

    /* xTaskResumeAll */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    /* API call */
    vTaskDelay(delay);
    /* Validations */
    ASSERT_PORT_YIELD_CALLED();

}

void test_vTaskDelay_success_gt_0_yield_not_called(void)
{
    TaskHandle_t task_handle;
    task_handle = create_task();
    ptcb = ( TCB_t * )task_handle;
    TickType_t delay = 34;
    /* Expectations */
    /* prvAddCurrentTaskToDelayedList */
    uxListRemove_ExpectAndReturn(&ptcb->xStateListItem, pdTRUE);
    listSET_LIST_ITEM_VALUE_Expect( &ptcb->xStateListItem,
                                    xTickCount + delay );
    vListInsert_Expect(pxOverflowDelayedTaskList, &ptcb->xStateListItem);

    /* xTaskResumeAll */

    listLIST_IS_EMPTY_ExpectAndReturn( &xPendingReadyList, pdFALSE );
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAndReturn(&xPendingReadyList, ptcb);
    uxListRemove_ExpectAndReturn(&ptcb->xEventListItem, pdTRUE);
    uxListRemove_ExpectAndReturn(&ptcb->xStateListItem, pdTRUE);
    /* prvAddTaskToReadyList */
    vListInsertEnd_Expect(&pxReadyTasksLists[ptcb->uxPriority],
                            & ptcb->xStateListItem);
    /* back to xTaskResumeAll */
    listLIST_IS_EMPTY_ExpectAndReturn(&xPendingReadyList, pdTRUE);
    /* prvResetNextTaskUnblockTime */
    listLIST_IS_EMPTY_ExpectAndReturn(&xPendingReadyList, pdTRUE);

    /* API call */
    vTaskDelay(delay);
    /* Validations */
    ASSERT_PORT_YIELD_CALLED();
}

/* ensures that with a delay of zero no other operation or sleeping is done, the
 * task in only yielded */
void test_vTaskDelay_success_eq_0(void)
{
    vTaskDelay(0);
    ASSERT_PORT_YIELD_CALLED();
}

/* --------------------- testing INCLUDE_eTaskGetState ---------------------- */
void test_eTaskGetState_success_current_tcb(void)
{
    TaskHandle_t task_handle;
    task_handle = create_task();
    ptcb = ( TCB_t * )task_handle;
    eTaskState ret_task_state;
    /* no Expectations */

    /* API Call */
    ret_task_state = eTaskGetState(task_handle);
    /* Validations */
    TEST_ASSERT_EQUAL(eRunning, ret_task_state);
}

void test_eTaskGetState_success_not_current_tcb_blocked_delayed(void)
{
    TaskHandle_t task_handle;
    created_task_priority = 3;
    task_handle = create_task();
    created_task_priority = 5;
    create_task();
    ptcb = ( TCB_t * )task_handle;
    TEST_ASSERT_NOT_EQUAL( pxCurrentTCB, ptcb );
    eTaskState ret_task_state;
    /* Expectations */
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xStateListItem,
                                             pxDelayedTaskList );

    /* API Call */
    ret_task_state = eTaskGetState(task_handle);
    /* Validations */
    TEST_ASSERT_EQUAL(eBlocked, ret_task_state);
}

void test_eTaskGetState_success_not_current_tcb_blocked_overflow(void)
{
    TaskHandle_t task_handle;
    created_task_priority = 3;
    task_handle = create_task();
    created_task_priority = 5;
    create_task();
    ptcb = ( TCB_t * )task_handle;
    TEST_ASSERT_NOT_EQUAL( pxCurrentTCB, ptcb );
    eTaskState ret_task_state;
    /* Expectations */
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xStateListItem,
                                             pxOverflowDelayedTaskList );

    /* API Call */
    ret_task_state = eTaskGetState(task_handle);
    /* Validations */
    TEST_ASSERT_EQUAL(eBlocked, ret_task_state);
}

void test_eTaskGetState_success_not_current_tcb_ready(void)
{
    TaskHandle_t task_handle;
    created_task_priority = 3;
    task_handle = create_task();
    created_task_priority = 5;
    create_task();
    ptcb = ( TCB_t * )task_handle;
    TEST_ASSERT_NOT_EQUAL( pxCurrentTCB, ptcb );
    eTaskState ret_task_state;
    /* Expectations */
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xStateListItem,
                                             &pxReadyTasksLists[0] );

    /* API Call */
    ret_task_state = eTaskGetState(task_handle);
    /* Validations */
    TEST_ASSERT_EQUAL(eReady, ret_task_state);
}

void test_eTaskGetState_success_not_current_tcb_suspended(void)
{
    TaskHandle_t task_handle;
    created_task_priority = 3;
    task_handle = create_task();
    created_task_priority = 5;
    create_task();
    ptcb = ( TCB_t * )task_handle;
    TEST_ASSERT_NOT_EQUAL( pxCurrentTCB, ptcb );
    eTaskState ret_task_state;
    /* Expectations */
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xStateListItem,
                                             &xSuspendedTaskList );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem,
                                             NULL);

    /* API Call */
    ret_task_state = eTaskGetState(task_handle);
    /* Validations */
    TEST_ASSERT_EQUAL( eSuspended, ret_task_state );
}

void test_eTaskGetState_success_not_current_tcb_deleted(void)
{
    TaskHandle_t task_handle;
    created_task_priority = 3;
    task_handle = create_task();
    created_task_priority = 5;
    create_task();
    ptcb = ( TCB_t * )task_handle;
    TEST_ASSERT_NOT_EQUAL( pxCurrentTCB, ptcb );
    eTaskState ret_task_state;
    /* Expectations */
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xStateListItem,
                                             &xTasksWaitingTermination );

    /* API Call */
    ret_task_state = eTaskGetState(task_handle);
    /* Validations */
    TEST_ASSERT_EQUAL( eDeleted, ret_task_state );
}

void test_eTaskGetState_success_not_current_tcb_deleted_not_found(void)
{
    TaskHandle_t task_handle;
    created_task_priority = 3;
    task_handle = create_task();
    created_task_priority = 5;
    create_task();
    ptcb = ( TCB_t * )task_handle;
    TEST_ASSERT_NOT_EQUAL( pxCurrentTCB, ptcb );
    eTaskState ret_task_state;
    /* Expectations */
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xStateListItem,
                                             NULL );
    /* API Call */
    ret_task_state = eTaskGetState(task_handle);
    /* Validations */
    TEST_ASSERT_EQUAL( eDeleted, ret_task_state );
}
//else if( ( pxStateList == &xTasksWaitingTermination ) || ( pxStateList == NULL ) )

/* alternatively this can be better solved by launching a thread and calling
 * notification wait, then block on the port yield function hook waiting for this
 * thread to continue, and check the value of  taskWAITING_NOTIFICATION */
void test_eTaskGetState_success_not_current_tcb_wait_notif(void)
{
    TaskHandle_t task_handle;
    created_task_priority = 3;
    task_handle = create_task();
    created_task_priority = 5;
    create_task();
    ptcb = ( TCB_t * )task_handle;
    /* see note above */
    ptcb->ucNotifyState[0] = 1; /* taskWAITING_NOTIFICATION */
    TEST_ASSERT_NOT_EQUAL( pxCurrentTCB, ptcb );
    eTaskState ret_task_state;
    /* Expectations */
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xStateListItem,
                                             &xSuspendedTaskList );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem,
                                             NULL);

    /* API Call */
    ret_task_state = eTaskGetState(task_handle);
    /* Validations */
    TEST_ASSERT_EQUAL( eBlocked, ret_task_state );
}

void test_eTaskGetState_success_not_current_tcb_blocked(void)
{
    TaskHandle_t task_handle;
    created_task_priority = 3;
    task_handle = create_task();
    created_task_priority = 5;
    create_task();
    ptcb = ( TCB_t * )task_handle;
    TEST_ASSERT_NOT_EQUAL( pxCurrentTCB, ptcb );
    eTaskState ret_task_state;
    /* Expectations */
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xStateListItem,
                                             &xSuspendedTaskList );
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xEventListItem,
                                             &xSuspendedTaskList );
    /* API Call */
    ret_task_state = eTaskGetState(task_handle);
    /* Validations */
    TEST_ASSERT_EQUAL( eBlocked, ret_task_state );
}

/* ------------------------- INCLUDE_xTaskDelayUntil ------------------------ */
void test_xTaskDelayUntil_success_gt_tickCount(void)
{
    BaseType_t ret_xtask_delay;
    TickType_t previousWakeTime = xTickCount + 3;
    TaskHandle_t task_handle;

    task_handle = create_task();
    ptcb = ( TCB_t * )task_handle;
    TEST_ASSERT_EQUAL( pxCurrentTCB, ptcb );

    /* Expectations */
    listLIST_IS_EMPTY_ExpectAndReturn(&xPendingReadyList, pdTRUE);
 //   uxListRemove_ExpectAndReturn(&ptcb->xStateListItem, 0);
    /* API Call */
    ret_xtask_delay = xTaskDelayUntil( &previousWakeTime, 4 );
    /* Validations */
    TEST_ASSERT_EQUAL(pdFALSE, ret_xtask_delay);
}


void test_xTaskDelayUntil_success_gt_tickCount_should_delay(void)
{
    BaseType_t ret_xtask_delay;
    xTickCount  = 1;
    TickType_t previousWakeTime = xTickCount + 3;
    //TickType_t previousWakeTime =  INT32_MAX + 3;
    TaskHandle_t task_handle;

    task_handle = create_task();
    ptcb = ( TCB_t * )task_handle;
    TEST_ASSERT_EQUAL( pxCurrentTCB, ptcb );
    uxListRemove_ExpectAndReturn( &pxCurrentTCB->xStateListItem, 0);
    listSET_LIST_ITEM_VALUE_Expect(&pxCurrentTCB->xStateListItem, 3);
    vListInsert_Expect(pxOverflowDelayedTaskList, &ptcb->xStateListItem);
    listLIST_IS_EMPTY_ExpectAndReturn(&xPendingReadyList, pdTRUE);

    ret_xtask_delay = xTaskDelayUntil( &previousWakeTime, UINT32_MAX  );
    TEST_ASSERT_EQUAL(pdTRUE, ret_xtask_delay);
}


void test_xTaskDelayUntil_success_lt_tickCount(void)
{
    BaseType_t ret_xtask_delay;
    TickType_t previousWakeTime = xTickCount - 3;
    TaskHandle_t task_handle;

    task_handle = create_task();
    ptcb = ( TCB_t * )task_handle;
    TEST_ASSERT_EQUAL( pxCurrentTCB, ptcb );
    /* Expectations */
    /* prvResetNextTaskUnblockTime */
    uxListRemove_ExpectAndReturn( &pxCurrentTCB->xStateListItem, 0);
    listSET_LIST_ITEM_VALUE_Expect(&pxCurrentTCB->xStateListItem,500 + ((previousWakeTime + 5) -  xTickCount));
    vListInsert_Expect(pxOverflowDelayedTaskList, &ptcb->xStateListItem);
    /* xTaskResumeAll */
    listLIST_IS_EMPTY_ExpectAndReturn( &xPendingReadyList, pdFALSE );
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAndReturn(&xPendingReadyList, ptcb);
    uxListRemove_ExpectAndReturn(&ptcb->xEventListItem, pdTRUE);
    uxListRemove_ExpectAndReturn(&ptcb->xStateListItem, pdTRUE);
    /* prvAddTaskToReadyList */
    vListInsertEnd_Expect(&pxReadyTasksLists[ptcb->uxPriority],
                            & ptcb->xStateListItem);
    /* back to xTaskResumeAll */
    listLIST_IS_EMPTY_ExpectAndReturn(&xPendingReadyList, pdTRUE);
    /* prvResetNextTaskUnblockTime */
    listLIST_IS_EMPTY_ExpectAndReturn(&xPendingReadyList, pdTRUE);
    /* API Call */
    ret_xtask_delay = xTaskDelayUntil( &previousWakeTime, 5 );
    /* Validations */
    ASSERT_PORT_YIELD_CALLED();
    TEST_ASSERT_EQUAL(pdTRUE, ret_xtask_delay);
}

/* ----------------------- testing Task notifications ----------------------- */
void test_ulTaskGenericNotifyTake_sucess(void)
{
    /*
    UBaseType_t uxIndexToWait;
    BaseType_t xClearCounterOnExit;
    TickType_t xTicksToWait;
    uint32_t ret;

    ret = ulTaskGenericNotifyTake( uxIndexToWait,
                                   xClearCounterOnExit,
                                   xTicksToWait );
    */
}

/*
void test_xTaskGenericNotify_success( void )
{
    BaseType_t ret;
    TaskHandle_t xTaskToNotify;
    UBaseType_t uxIndexToNotify;
    uint32_t ulValue;
    eNotifyAction eAction;
    uint32_t * pulPreviousNotificationValue;

    ret = xTaskGenericNotify( xTaskToNotify,
                              uxIndexToNotify,
                              ulValue,
                              eAction,
                              pulPreviousNotificationValue );
}
*/

void test_xTaskGenericNotifyWait_success_notif_recieved( void )
{
    UBaseType_t uxIndexToWait = 0;
    uint32_t ulBitsToClearOnEntry = 0;
    uint32_t ulBitsToClearOnExit = 0;
    uint32_t pullNotificationValue;
    TickType_t xTicksToWait = 20;
    BaseType_t ret;

    TaskHandle_t task_handle;
    TCB_t * ptcb;

    task_handle = create_task();
    ptcb = task_handle;
    ptcb->ucNotifyState[ uxIndexToWait ] = 2;    /* taskNOTIFICATION_RECEIVED */
    ptcb->ulNotifiedValue[ uxIndexToWait ] = 5;

    ret = xTaskGenericNotifyWait( uxIndexToWait,
                                  ulBitsToClearOnEntry,
                                  ulBitsToClearOnExit,
                                  &pullNotificationValue,
                                  xTicksToWait );
    TEST_ASSERT_EQUAL(pdTRUE, ret);
    TEST_ASSERT_EQUAL(5, pullNotificationValue);
}

void test_xTaskGenericNotifyWait_success_notif_not_recieved( void )
{
    UBaseType_t uxIndexToWait = 0;
    uint32_t ulBitsToClearOnEntry = 0;
    uint32_t ulBitsToClearOnExit = 0;
    uint32_t pullNotificationValue;
    TickType_t xTicksToWait = 20;
    BaseType_t ret;

    TaskHandle_t task_handle;
    TCB_t * ptcb;

    task_handle = create_task();
    ptcb = task_handle;
    ptcb->ucNotifyState[ uxIndexToWait ] = 1;    /* taskWAITING_NOTIFICATION */
    ptcb->ulNotifiedValue[ uxIndexToWait ] = 5;
    /* Expectations */
    uxListRemove_ExpectAndReturn( &ptcb->xStateListItem, 0 );
    listSET_LIST_ITEM_VALUE_Expect( &ptcb->xStateListItem,
                                    xTickCount + xTicksToWait );
    vListInsert_Expect(pxOverflowDelayedTaskList, &ptcb->xStateListItem);

    /* API Call */
    ret = xTaskGenericNotifyWait( uxIndexToWait,
                                  ulBitsToClearOnEntry,
                                  ulBitsToClearOnExit,
                                  &pullNotificationValue,
                                  xTicksToWait );
    /* Validations */
    TEST_ASSERT_EQUAL(pdFALSE, ret);
    TEST_ASSERT_EQUAL(5, pullNotificationValue);
    ASSERT_PORT_YIELD_CALLED();
}

static BaseType_t pxHookFunction(void * arg)
{
    BaseType_t *i =  arg;
    return *i;
}

/* called from port task yield, to simulate that another task ran and received
 * the notification */
static void notif_received()
{
    ptcb->ucNotifyState[0] = 2; /* taskNOTIFICATION_RECEIVED */
}

void test_xTaskGenericNotifyWait_success_notif_recieved_while_waiting( void )
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
    ptcb->ucNotifyState[ uxIndexToWait ] = 1;    /* taskWAITING_NOTIFICATION */
    ptcb->ulNotifiedValue[ uxIndexToWait ] = 5;
    /* Expectations */
    uxListRemove_ExpectAndReturn( &ptcb->xStateListItem, 0 );
    listSET_LIST_ITEM_VALUE_Expect( &ptcb->xStateListItem,
                                    xTickCount + xTicksToWait );
    vListInsert_Expect(pxOverflowDelayedTaskList, &ptcb->xStateListItem);
    py_operation = &notif_received;

    /* API Call */
    ret = xTaskGenericNotifyWait( uxIndexToWait,
                                  ulBitsToClearOnEntry,
                                  ulBitsToClearOnExit,
                                  &pullNotificationValue,
                                  xTicksToWait );
    /* Validations */
    TEST_ASSERT_EQUAL(pdTRUE, ret);
    TEST_ASSERT_EQUAL(5, pullNotificationValue);
    ASSERT_PORT_YIELD_CALLED();
}

/* ----------------------- testing INCLUDE_vTaskSuspend ----------------------*/
void test_vTaskSuspend_success( void )
{
    TaskHandle_t task_handle;

    task_handle = create_task();
    ptcb = task_handle;
    TEST_ASSERT_EQUAL_PTR(ptcb, pxCurrentTCB);
    xSchedulerRunning = pdFALSE;
    /* Expectations */
    uxListRemove_ExpectAndReturn(&ptcb->xStateListItem, 0 );
    /* taskRESET_READY_PRIORITY */
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &pxReadyTasksLists[ptcb->uxPriority],
                                             0 );
    /* back */
    listLIST_ITEM_CONTAINER_ExpectAndReturn(&ptcb->xEventListItem, NULL );
    vListInsertEnd_Expect(&xSuspendedTaskList, &ptcb->xStateListItem );
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &xSuspendedTaskList,
                                             uxCurrentNumberOfTasks );
    /* API Call */
    vTaskSuspend( task_handle );
    /* Validations */
    TEST_ASSERT_EQUAL_PTR(NULL, pxCurrentTCB);
    ASSERT_PORT_YIELD_NOT_CALLED();
}

void test_vTaskSuspend_success_shced_running( void )
{
    TaskHandle_t task_handle;

    task_handle = create_task();
    ptcb = task_handle;
    TEST_ASSERT_EQUAL_PTR(ptcb, pxCurrentTCB);
    xSchedulerRunning = pdTRUE;
    /* Expectations */
    uxListRemove_ExpectAndReturn(&ptcb->xStateListItem, 0 );
    /* taskRESET_READY_PRIORITY */
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &pxReadyTasksLists[ptcb->uxPriority],
                                             0 );
    /* back */
    listLIST_ITEM_CONTAINER_ExpectAndReturn(&ptcb->xEventListItem, NULL );
    vListInsertEnd_Expect(&xSuspendedTaskList, &ptcb->xStateListItem );
    /* prvResetNextTaskUnblockTime */
    listLIST_IS_EMPTY_ExpectAndReturn(pxDelayedTaskList, pdTRUE);
    /* API Call */
    vTaskSuspend( task_handle );
    /* Validations */
    TEST_ASSERT_EQUAL (portMAX_DELAY, xNextTaskUnblockTime);
    ASSERT_PORT_YIELD_CALLED();
}

void test_vTaskSuspend_success_shced_running_not_curr( void )
{
    TaskHandle_t task_handle, task_handle2;

    created_task_priority = 3;
    task_handle = create_task();
    created_task_priority = 5;
    task_handle2 = create_task();
    ptcb = task_handle;
    TEST_ASSERT_EQUAL_PTR(task_handle2, pxCurrentTCB);
    xSchedulerRunning = pdTRUE;
    /* Expectations */
    uxListRemove_ExpectAndReturn(&ptcb->xStateListItem, 0 );
    /* taskRESET_READY_PRIORITY */
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &pxReadyTasksLists[ptcb->uxPriority],
                                             1 );
    /* back */
    listLIST_ITEM_CONTAINER_ExpectAndReturn(&ptcb->xEventListItem, NULL );
    vListInsertEnd_Expect(&xSuspendedTaskList, &ptcb->xStateListItem );
    /* prvResetNextTaskUnblockTime */
    listLIST_IS_EMPTY_ExpectAndReturn(pxDelayedTaskList, pdTRUE);
    /* API Call */
    vTaskSuspend( task_handle );
    /* Validations */
    TEST_ASSERT_EQUAL (portMAX_DELAY, xNextTaskUnblockTime);
    ASSERT_PORT_YIELD_NOT_CALLED();
}

void test_vTaskSuspend_success_switch_context( void )
{
    TaskHandle_t task_handle;

    task_handle = create_task();
    ptcb = task_handle;
    TEST_ASSERT_EQUAL_PTR(ptcb, pxCurrentTCB);
    xSchedulerRunning = pdFALSE;
    uxSchedulerSuspended = pdTRUE;
    ptcb->ucNotifyState[ 0 ] = 1; /* taskWAITING_NOTIFICATION */;
    /* Expectations */
    uxListRemove_ExpectAndReturn(&ptcb->xStateListItem, 1 );
    listLIST_ITEM_CONTAINER_ExpectAndReturn(&ptcb->xEventListItem,
                                            &xSuspendedTaskList );
    uxListRemove_ExpectAndReturn( &ptcb->xEventListItem, pdTRUE);
    vListInsertEnd_Expect(&xSuspendedTaskList, &ptcb->xStateListItem );
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &xSuspendedTaskList,
                                             uxCurrentNumberOfTasks + 1);
    /* API Call */
    vTaskSuspend( NULL );
    /* Validations */
    ASSERT_PORT_YIELD_NOT_CALLED();
    TEST_ASSERT_EQUAL( 0, ptcb->ucNotifyState[ 0 ] );
}

void test_vTaskResume_fail_null_handle(void)
{
    vTaskResume(NULL);
    ASSERT_PORT_YIELD_NOT_CALLED();
}

void test_vTaskResume_fail_current_tcb_null(void)
{
    create_task();
    vTaskResume(NULL);
    ASSERT_PORT_YIELD_NOT_CALLED();
}

void test_vTaskResume_fail_current_tcb(void)
{
    TaskHandle_t task_handle;
    task_handle = create_task();
    vTaskResume(task_handle);
    ASSERT_PORT_YIELD_NOT_CALLED();
}

void test_vTaskResume_fail_task_not_suspended(void)
{
    TaskHandle_t task_handle;
    created_task_priority = 3;
    task_handle = create_task();
    created_task_priority = 5;
    create_task();
    ptcb = task_handle;
    /* Expectations */
    /* prvTaskIsTaskSuspended */
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &xSuspendedTaskList,
                                             &ptcb->xStateListItem,
                                             pdFALSE );
    /* API Call */
    vTaskResume(task_handle); /* not current tcb */
    /* Validations */
    ASSERT_PORT_YIELD_NOT_CALLED();
}

void test_vTaskResume_fail_task_ready(void)
{
    TaskHandle_t task_handle;
    created_task_priority = 3;
    task_handle = create_task();
    created_task_priority = 5;
    create_task();
    ptcb = task_handle;
    /* Expectations */
    /* prvTaskIsTaskSuspended */
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &xSuspendedTaskList,
                                             &ptcb->xStateListItem,
                                             pdTRUE );
    listIS_CONTAINED_WITHIN_ExpectAndReturn ( &xPendingReadyList,
                                              &ptcb->xEventListItem,
                                              pdTRUE);
    /* API Call */
    vTaskResume(task_handle); /* not current tcb */
    /* Validations */
    ASSERT_PORT_YIELD_NOT_CALLED();
}

void test_vTaskResume_fail_task_event_list_not_orphan(void)
{
    TaskHandle_t task_handle;
    created_task_priority = 3;
    task_handle = create_task();
    created_task_priority = 5;
    create_task();
    ptcb = task_handle;
    /* Expectations */
    /* prvTaskIsTaskSuspended */
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &xSuspendedTaskList,
                                             &ptcb->xStateListItem,
                                             pdTRUE );
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &xPendingReadyList,
                                              &ptcb->xEventListItem,
                                              pdFALSE);
    listIS_CONTAINED_WITHIN_ExpectAndReturn( NULL,
                                             &ptcb->xEventListItem,
                                             pdFALSE);
    /* API Call */
    vTaskResume(task_handle); /* not current tcb */
    /* Validations */
    ASSERT_PORT_YIELD_NOT_CALLED();
}

void test_vTaskResume_success_task_event_list_orphan(void)
{
    TaskHandle_t task_handle;
    created_task_priority = 3;
    task_handle = create_task();
    created_task_priority = 5;
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
    uxListRemove_ExpectAndReturn( &ptcb->xStateListItem, pdTRUE);
    /* prvAddTaskToReadyList*/
    vListInsertEnd_Expect( &pxReadyTasksLists[ created_task_priority ],
                           &ptcb->xStateListItem );
    /* API Call */
    vTaskResume(task_handle); /* not current tcb */
    /* Validations */
    ASSERT_PORT_YIELD_NOT_CALLED();
}

void test_vTaskResume_success_yield(void)
{
    TaskHandle_t task_handle;
    created_task_priority = 3;
    task_handle = create_task();
    created_task_priority = 3;
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
    uxListRemove_ExpectAndReturn( &ptcb->xStateListItem, pdTRUE);
    /* prvAddTaskToReadyList*/
    vListInsertEnd_Expect( &pxReadyTasksLists[ created_task_priority ],
                           &ptcb->xStateListItem );
    /* API Call */
    vTaskResume(task_handle); /* not current tcb */
    /* Validations */
    ASSERT_PORT_YIELD_CALLED();
}

void test_xTaskResumeFromISR_success( void )
{
    TaskHandle_t task_handle;
    BaseType_t ret_task_resume;
    created_task_priority = 3;
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
    uxListRemove_ExpectAndReturn( &ptcb->xStateListItem, pdTRUE );
    /* prvAddTaskToReadyList */
    vListInsertEnd_Expect( &pxReadyTasksLists[ created_task_priority ],
                           &ptcb->xStateListItem );
    /* API Call */
    ret_task_resume = xTaskResumeFromISR(task_handle);

    /* Validations */
    TEST_ASSERT_EQUAL(pdTRUE, ret_task_resume);
    ASSERT_INVALID_INTERRUPT_PRIORITY_CALLED();
    ASSERT_PORT_CLEAR_INTERRUPT_CALLED();
    ASSERT_PORT_SET_INTERRUPT_CALLED();
}

void test_xTaskResumeFromISR_success_sched_suspended( void )
{
    TaskHandle_t task_handle;
    BaseType_t ret_task_resume;
    uxSchedulerSuspended = pdTRUE;
    created_task_priority = 3;
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
    vListInsertEnd_Expect(&xPendingReadyList, &ptcb->xEventListItem);
    /* API Call */
    ret_task_resume = xTaskResumeFromISR(task_handle);

    /* Validations */
    TEST_ASSERT_EQUAL(pdFALSE, ret_task_resume);
    ASSERT_INVALID_INTERRUPT_PRIORITY_CALLED();
    ASSERT_PORT_CLEAR_INTERRUPT_CALLED();
    ASSERT_PORT_SET_INTERRUPT_CALLED();
}

void test_xTaskResumeFromISR_success_task_suspended( void )
{
    TaskHandle_t task_handle;
    BaseType_t ret_task_resume;
    uxSchedulerSuspended = pdTRUE;
    created_task_priority = 3;
    task_handle = create_task();
    ptcb = task_handle;
    /* Expectations */
    /* prvTaskIsTaskSuspended */
    listIS_CONTAINED_WITHIN_ExpectAndReturn( &xSuspendedTaskList,
                                             &ptcb->xStateListItem,
                                             pdFALSE );
    /* API Call */
    ret_task_resume = xTaskResumeFromISR(task_handle);

    /* Validations */
    TEST_ASSERT_EQUAL(pdFALSE, ret_task_resume);
    ASSERT_INVALID_INTERRUPT_PRIORITY_CALLED();
    ASSERT_PORT_CLEAR_INTERRUPT_CALLED();
    ASSERT_PORT_SET_INTERRUPT_CALLED();
}

void test_xTaskResumeFromISR_success_curr_prio_lt_suspended_task( void )
{
    TaskHandle_t task_handle;
    BaseType_t ret_task_resume;
    uxSchedulerSuspended = pdFALSE;
    created_task_priority = 3;
    task_handle = create_task();
    created_task_priority = 4;
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
    vListInsertEnd_Expect( &pxReadyTasksLists[ created_task_priority ],
                           &ptcb->xStateListItem );
    /* API Call */
    ret_task_resume = xTaskResumeFromISR(task_handle);

    /* Validations */
    TEST_ASSERT_EQUAL(pdFALSE, ret_task_resume);
    ASSERT_INVALID_INTERRUPT_PRIORITY_CALLED();
    ASSERT_PORT_CLEAR_INTERRUPT_CALLED();
    ASSERT_PORT_SET_INTERRUPT_CALLED();
}

/* testing INCLUDE_xTaskGetHandle */

#define INITIALIZE_LIST_1E( list, owner) \
    do {                                           \
        ListItem_t list_item; \
        (list).xListEnd.pxNext = &(list_item);       \
        (list).xListEnd.pxPrevious = &(list_item);       \
        (list).pxIndex = &(list).xListEnd;         \
        (list).uxNumberOfItems = 1;               \
        (list_item).pxNext = (list).pxIndex;     \
        (list_item).pxPrevious = (list).pxIndex;     \
        (list_item).pvOwner = (owner);             \
        (list_item).pxContainer = &(list);             \
    } while (0)

#define INITIALIZE_LIST_2E( list, owner, owner2) \
    do {                                           \
        ListItem_t list_item; \
        ListItem_t list_item2; \
        (list).xListEnd.pxNext = &(list_item);       \
        (list).xListEnd.pxPrevious = &(list_item2);       \
        (list).pxIndex = &(list).xListEnd;         \
        (list).uxNumberOfItems = 2;               \
        (list_item).pxNext = &(list_item2);     \
        (list_item).pxPrevious = (list).pxIndex;     \
        (list_item).pvOwner = (owner);             \
        (list_item).pxContainer = &(list);             \
\
        (list_item2).pxNext = (list).pxIndex;     \
        (list_item2).pxPrevious = &(list_item);     \
        (list_item2).pvOwner = (owner2);             \
        (list_item2).pxContainer = &(list);             \
    } while (0)

void test_xtaskGetHandle_success(void)
{
    TaskHandle_t task_handle = NULL, task_handle2;
    task_handle = create_task();
    ptcb = task_handle;
    INITIALIZE_LIST_1E( pxReadyTasksLists[configMAX_PRIORITIES - 1],
                         ptcb );
    /* Expectations */
    /*  prvSearchForNameWithinSingleList */
    listCURRENT_LIST_LENGTH_ExpectAndReturn(&pxReadyTasksLists[ configMAX_PRIORITIES - 1 ],
                                            1);
    /* vTaskResumeAll */
    listLIST_IS_EMPTY_ExpectAndReturn(&xPendingReadyList, pdTRUE);

    /* API Call */
    task_handle2 = xTaskGetHandle( "create_task" );
    /* Validations */
    TEST_ASSERT_EQUAL_PTR(task_handle, task_handle2);
}

void test_xtaskGetHandle_success_2elements(void)
{
    TaskHandle_t task_handle = NULL, task_handle2, ret_task_handle;
    task_handle = create_task();
    task_handle2 = create_task();
    ptcb = task_handle;
    INITIALIZE_LIST_2E( pxReadyTasksLists[configMAX_PRIORITIES - 1],
                         ptcb, task_handle2 );
    /* Expectations */
    /*  prvSearchForNameWithinSingleList */
    listCURRENT_LIST_LENGTH_ExpectAndReturn(&pxReadyTasksLists[ configMAX_PRIORITIES - 1 ],
                                            1);
    /* vTaskResumeAll */
    listLIST_IS_EMPTY_ExpectAndReturn(&xPendingReadyList, pdTRUE);

    /* API Call */
    ret_task_handle = xTaskGetHandle( "create_task" );
    /* Validations */
    TEST_ASSERT_EQUAL_PTR(task_handle2, ret_task_handle);
}

void test_xtaskGetHandle_success_2elements_set_index(void)
{
    TaskHandle_t task_handle = NULL, task_handle2, ret_task_handle;
    task_handle = create_task();
    task_handle2 = create_task();
    ptcb = task_handle;
    INITIALIZE_LIST_2E( pxReadyTasksLists[configMAX_PRIORITIES - 1],
                         ptcb, task_handle2 );
    pxReadyTasksLists[configMAX_PRIORITIES - 1].pxIndex = pxReadyTasksLists[configMAX_PRIORITIES - 1].pxIndex->pxNext;
    pxReadyTasksLists[configMAX_PRIORITIES - 1].pxIndex = pxReadyTasksLists[configMAX_PRIORITIES - 1].pxIndex->pxNext;
    /* Expectations */
    /*  prvSearchForNameWithinSingleList */
    listCURRENT_LIST_LENGTH_ExpectAndReturn(&pxReadyTasksLists[ configMAX_PRIORITIES - 1 ],
                                            1);
    /* vTaskResumeAll */
    listLIST_IS_EMPTY_ExpectAndReturn(&xPendingReadyList, pdTRUE);

    /* API Call */
    ret_task_handle = xTaskGetHandle( "create_task" );
    /* Validations */
    TEST_ASSERT_EQUAL_PTR(task_handle2, ret_task_handle);
}

void test_xtaskGetHandle_fail_no_task_found(void)
{
    TaskHandle_t task_handle, task_handle2, ret_task_handle;
    task_handle = create_task();
    task_handle2 = create_task();
    ptcb = task_handle;
    INITIALIZE_LIST_2E( pxReadyTasksLists[configMAX_PRIORITIES - 1],
                         ptcb, task_handle2 );
    /* Expectations */
    /*  prvSearchForNameWithinSingleList */
    listCURRENT_LIST_LENGTH_ExpectAndReturn(
                                &pxReadyTasksLists[ configMAX_PRIORITIES - 1 ],
                                2 );
    int i = configMAX_PRIORITIES - 1;
    do
    {
        i--;
        listCURRENT_LIST_LENGTH_ExpectAndReturn(&pxReadyTasksLists[ i ],
                0);
    } while (i > tskIDLE_PRIORITY);
    listCURRENT_LIST_LENGTH_ExpectAndReturn(pxDelayedTaskList, 0);
    listCURRENT_LIST_LENGTH_ExpectAndReturn( pxOverflowDelayedTaskList, 0);
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &xSuspendedTaskList, 0);
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &xTasksWaitingTermination, 0);
    /* vTaskResumeAll */
    listLIST_IS_EMPTY_ExpectAndReturn(&xPendingReadyList, pdTRUE);

    /* API Call */
    ret_task_handle = xTaskGetHandle( "create_tasks" );
    /* Validations */
    TEST_ASSERT_EQUAL_PTR(NULL, ret_task_handle);
}


void test_xtaskGetHandle_fail_no_taks_running(void)
{
    TaskHandle_t task_handle2;
    /* Expectations */
    /*  prvSearchForNameWithinSingleList */
    for (int i = configMAX_PRIORITIES; i > tskIDLE_PRIORITY; --i)
    {
        listCURRENT_LIST_LENGTH_ExpectAndReturn( &pxReadyTasksLists[ i ], 0);
    }
    listCURRENT_LIST_LENGTH_ExpectAndReturn( pxDelayedTaskList, 0);
    listCURRENT_LIST_LENGTH_ExpectAndReturn( pxOverflowDelayedTaskList, 0);
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &xSuspendedTaskList , 0);
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &xTasksWaitingTermination, 0);
    /* API Call */
    task_handle2 = xTaskGetHandle( "create_task" );
    /* Validations */
    TEST_ASSERT_EQUAL_PTR( NULL, task_handle2);
}

/* testing always available functions */
void test_xTaskGetTickCount_sucess(void)
{
    TickType_t  ret_get_tick_count;
    xTickCount = 565656;
    ret_get_tick_count = xTaskGetTickCount();
    TEST_ASSERT_EQUAL(565656, ret_get_tick_count);
}

void test_xTaskGetTickCountFromISR_success(void)
{
    TickType_t  ret_get_tick_count;
    xTickCount = 565656;

    ret_get_tick_count = xTaskGetTickCountFromISR();

    TEST_ASSERT_EQUAL(565656, ret_get_tick_count);
    ASSERT_INVALID_INTERRUPT_PRIORITY_CALLED();
    ASSERT_PORT_CLEAR_INTERRUPT_CALLED();
    ASSERT_PORT_SET_INTERRUPT_CALLED();
}

void test_uxTaskGetNumberOfTasks_success(void)
{
    UBaseType_t  ret_task_num;

    create_task();
    create_task();
    create_task();

    ret_task_num = uxTaskGetNumberOfTasks();

    TEST_ASSERT_EQUAL(3, ret_task_num);
}

void test_pcTaskGetName_success(void)
{
    char * ret_task_name;
    TaskHandle_t task_handle;
    task_handle = create_task();

    ret_task_name = pcTaskGetName(task_handle);
    TEST_ASSERT_EQUAL_STRING("create_task", ret_task_name);

}

void test_pcTaskGetName_success_null_handle(void)
{
    char * ret_task_name;
    create_task();

    ret_task_name = pcTaskGetName(NULL);
    TEST_ASSERT_EQUAL_STRING("create_task", ret_task_name);

}
void test_xTaskCatchUpTicks(void)
{
    BaseType_t ret_taskCatchUpTicks;
    TaskHandle_t task_handle;
    task_handle = create_task();
    ptcb = task_handle;
    uxSchedulerSuspended = pdTRUE;
    /* API Call */
    ret_taskCatchUpTicks = xTaskCatchUpTicks( 500 );
    /* Validations */
    TEST_ASSERT_EQUAL(pdFALSE, ret_taskCatchUpTicks);
}

void test_xTaskIncrementTick_success_sched_suspended_no_switch( void )
{
    BaseType_t  ret_task_incrementtick;
    TickType_t  current_ticks = xPendedTicks;

    vTaskSuspendAll();

    /* API Call */
    ret_task_incrementtick = xTaskIncrementTick();
    /* Validations */
    TEST_ASSERT_EQUAL(pdFALSE, ret_task_incrementtick);
    TEST_ASSERT_EQUAL( current_ticks + 1, xPendedTicks);
    ASSERT_APP_TICK_HOOK_CALLED();
}

/* ensures that the delayed task list and overflow list are switched when a
 * tickcount overflow occurs */
void test_xTaskIncrementTick_success_tickCount_overlow( void )
{
    BaseType_t  ret_task_incrementtick;
    List_t * delayed, * overflow;
    TaskHandle_t task_handle;

    uxSchedulerSuspended  = pdFALSE;
    delayed = pxDelayedTaskList;
    overflow = pxOverflowDelayedTaskList;
    xTickCount = 0;          /* overflowed */
    task_handle = create_task();

    /* Expectations */
    /* prvResetNextTaskUnblockTime */
    listLIST_IS_EMPTY_ExpectAndReturn(pxDelayedTaskList, pdTRUE);
    /* back */
    listCURRENT_LIST_LENGTH_ExpectAndReturn(&pxReadyTasksLists[pxCurrentTCB->uxPriority],
                                            2);
    /* API Call */
    ret_task_incrementtick = xTaskIncrementTick();

    /* Validations */
    TEST_ASSERT_EQUAL( pdTRUE, ret_task_incrementtick );
    ASSERT_APP_TICK_HOOK_CALLED();
    /* make sure the lists are swapped on overflow */
    TEST_ASSERT_EQUAL_PTR(pxOverflowDelayedTaskList, delayed);
    TEST_ASSERT_EQUAL_PTR(pxDelayedTaskList, overflow);
    TEST_ASSERT_EQUAL(1, xNumOfOverflows);
    TEST_ASSERT_EQUAL(portMAX_DELAY, xNextTaskUnblockTime);
}

void test_xTaskIncrementTick_success_no_switch( void )
{
    BaseType_t  ret_task_incrementtick;
    TaskHandle_t task_handle;

    /* setup */
    task_handle = create_task();
    ptcb = task_handle;

    /* Expectations */
    listLIST_IS_EMPTY_ExpectAndReturn(pxDelayedTaskList, pdTRUE);
    listCURRENT_LIST_LENGTH_ExpectAndReturn(&pxReadyTasksLists[ptcb->uxPriority],
                1);

    /* API Call */
    ret_task_incrementtick = xTaskIncrementTick();

    /* Validations */
    TEST_ASSERT_EQUAL(pdFALSE, ret_task_incrementtick);
    TEST_ASSERT_EQUAL(portMAX_DELAY, xNextTaskUnblockTime);
    ASSERT_APP_TICK_HOOK_CALLED();
}

void test_xTaskIncrementTick_success_switch( void )
{
    BaseType_t  ret_task_incrementtick;
    TaskHandle_t task_handle;

    /* setup */
    task_handle = create_task();
    ptcb = task_handle;
    xPendedTicks = 3;

    /* Expectations */
    listLIST_IS_EMPTY_ExpectAndReturn(pxDelayedTaskList, pdTRUE);
    listCURRENT_LIST_LENGTH_ExpectAndReturn(&pxReadyTasksLists[ptcb->uxPriority],
                3);

    /* API Call */
    ret_task_incrementtick = xTaskIncrementTick();

    /* Validations */
    TEST_ASSERT_EQUAL(pdTRUE, ret_task_incrementtick);
    ASSERT_APP_TICK_HOOK_NOT_CALLED();
    TEST_ASSERT_EQUAL(portMAX_DELAY, xNextTaskUnblockTime);
}

void test_xTaskIncrementTick_success_update_next_unblock( void )
{
    BaseType_t  ret_task_incrementtick;
    TaskHandle_t task_handle;
    TaskHandle_t task_handle2;

    /* setup */
    task_handle = create_task();
    task_handle2 = create_task();
    ptcb = task_handle;
    xPendedTicks = 3;
    xTickCount = 50;
    xNextTaskUnblockTime = 49;  /* tasks due unblocking */
    uxSchedulerSuspended  = pdFALSE;

    /* Expectations */
    listLIST_IS_EMPTY_ExpectAndReturn(pxDelayedTaskList, pdFALSE);
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAndReturn(pxDelayedTaskList, task_handle2);
    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &task_handle2->xStateListItem,
                                             xTickCount + 5 );
    listCURRENT_LIST_LENGTH_ExpectAndReturn(&pxReadyTasksLists[ptcb->uxPriority],
                                            3);

    /* API Call */
    ret_task_incrementtick = xTaskIncrementTick();

    /* Validations */
    TEST_ASSERT_EQUAL(pdTRUE, ret_task_incrementtick);
    ASSERT_APP_TICK_HOOK_NOT_CALLED();
    TEST_ASSERT_EQUAL(xTickCount + 4, xNextTaskUnblockTime);
}

void test_xTaskIncrementTick_success_unblock_tasks( void )
{
    BaseType_t  ret_task_incrementtick;
    TaskHandle_t task_handle;
    TaskHandle_t task_handle2;

    /* setup */
    task_handle = create_task();
    task_handle2 = create_task();
    ptcb = task_handle;
    xPendedTicks = 3;
    xTickCount = 50;
    xNextTaskUnblockTime = 49;  /* tasks due unblocking */
    uxSchedulerSuspended  = pdFALSE;

    /* Expectations */
    listLIST_IS_EMPTY_ExpectAndReturn(pxDelayedTaskList, pdFALSE);
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAndReturn(pxDelayedTaskList, task_handle2);
    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &task_handle2->xStateListItem,
                                             xTickCount - 5 );
    uxListRemove_ExpectAndReturn(&task_handle2->xStateListItem, pdTRUE);
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &task_handle2->xEventListItem, NULL);
    /* prvAddTaskToReadyList */
    vListInsertEnd_Expect( &pxReadyTasksLists[ task_handle2->uxPriority ],
                           &task_handle2->xStateListItem );
    listLIST_IS_EMPTY_ExpectAndReturn(pxDelayedTaskList, pdTRUE);
    /* back */
    listCURRENT_LIST_LENGTH_ExpectAndReturn(&pxReadyTasksLists[ptcb->uxPriority],
                                            1);

    /* API Call */
    ret_task_incrementtick = xTaskIncrementTick();

    /* Validations */
    TEST_ASSERT_EQUAL(pdTRUE, ret_task_incrementtick);
    ASSERT_APP_TICK_HOOK_NOT_CALLED();
    TEST_ASSERT_EQUAL(portMAX_DELAY, xNextTaskUnblockTime);
}

void test_xTaskIncrementTick_success_unblock_tasks2( void )
{
    BaseType_t  ret_task_incrementtick;
    TaskHandle_t task_handle;
    TaskHandle_t task_handle2;

    /* setup */
    task_handle = create_task();
    created_task_priority = 2;
    task_handle2 = create_task();
    ptcb = task_handle;
    xPendedTicks = 0;
    xTickCount = 50;
    xNextTaskUnblockTime = 49;  /* tasks due unblocking */
    uxSchedulerSuspended  = pdFALSE;
    vTaskMissedYield( );

    /* Expectations */
    listLIST_IS_EMPTY_ExpectAndReturn(pxDelayedTaskList, pdFALSE);
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAndReturn(pxDelayedTaskList, task_handle2);
    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &task_handle2->xStateListItem,
                                             xTickCount - 5 );
    uxListRemove_ExpectAndReturn(&task_handle2->xStateListItem, pdTRUE);
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &task_handle2->xEventListItem,
                                             &xPendingReadyList);
    uxListRemove_ExpectAndReturn(&task_handle2->xEventListItem, pdTRUE);
    /* prvAddTaskToReadyList */
    vListInsertEnd_Expect( &pxReadyTasksLists[ task_handle2->uxPriority ],
                           &task_handle2->xStateListItem );
    listLIST_IS_EMPTY_ExpectAndReturn(pxDelayedTaskList, pdTRUE);
    /* back */
    listCURRENT_LIST_LENGTH_ExpectAndReturn(&pxReadyTasksLists[ptcb->uxPriority],
                                            1);

    /* API Call */
    ret_task_incrementtick = xTaskIncrementTick();

    /* Validations */
    TEST_ASSERT_EQUAL(pdTRUE, ret_task_incrementtick);
    ASSERT_APP_TICK_HOOK_CALLED();
    TEST_ASSERT_EQUAL(portMAX_DELAY, xNextTaskUnblockTime);
}
/* testing INCLUDE_xTaskAbortDelay */
void test_xTaskAbortDelay_fail_current_task(void)
{
    BaseType_t ret_taskabort_delay;
    TaskHandle_t task_handle;

    task_handle = create_task();
    ptcb = task_handle;

    /* Expectations */
    listLIST_IS_EMPTY_ExpectAndReturn(&xPendingReadyList, pdTRUE);
    /* API Call */
    ret_taskabort_delay = xTaskAbortDelay( task_handle );
    /* Validations */
    TEST_ASSERT_EQUAL(pdFALSE, ret_taskabort_delay);
    TEST_ASSERT_EQUAL(pdFALSE, ptcb->ucDelayAborted);
}

void test_xTaskAbortDelay_success(void)
{
    BaseType_t ret_taskabort_delay;
    TaskHandle_t task_handle;

    created_task_priority = 4;
    task_handle = create_task();
    ptcb = task_handle;
    created_task_priority = 5;
    create_task();

    /* Expectations */
    /* eTaskGetState */
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xStateListItem,
                                             pxDelayedTaskList );
    /* back */
    uxListRemove_ExpectAndReturn(&tcb->xStateListItem, pdTRUE);
    listLIST_ITEM_CONTAINER_ExpectAndReturn(&ptcb->xEventListItem, NULL);
    /* prvAddTaskToReadyList */
    vListInsertEnd_Expect( &pxReadyTasksLists[ created_task_priority ],
                           &ptcb->xStateListItem );
    /* xTaskResumeAll */
    listLIST_IS_EMPTY_ExpectAndReturn(&xPendingReadyList, pdTRUE);
    /* API Call */
    ret_taskabort_delay = xTaskAbortDelay( task_handle );
    /* Validations */
    TEST_ASSERT_EQUAL(pdTRUE, ret_taskabort_delay);
    TEST_ASSERT_EQUAL(pdFALSE, ptcb->ucDelayAborted);
}

void test_xTaskAbortDelay_success_notdelayed(void)
{
    BaseType_t ret_taskabort_delay;
    TaskHandle_t task_handle;
    TaskHandle_t task_handle2;

    created_task_priority = 6;
    task_handle = create_task();
    ptcb = task_handle;

    /* Expectations 1*/
    uxListRemove_ExpectAndReturn(&ptcb->xStateListItem, 1 );
    listLIST_ITEM_CONTAINER_ExpectAndReturn(&ptcb->xEventListItem,
                                            &xSuspendedTaskList );
    uxListRemove_ExpectAndReturn( &ptcb->xEventListItem, pdTRUE);
    vListInsertEnd_Expect(&xSuspendedTaskList, &ptcb->xStateListItem );
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &xSuspendedTaskList,
                                             uxCurrentNumberOfTasks) ;
    TEST_ASSERT_EQUAL(pxCurrentTCB, task_handle);

    vTaskSuspend(task_handle);
    TEST_ASSERT_EQUAL(NULL, pxCurrentTCB);

    created_task_priority = 5;
    task_handle2 = create_task();
    TEST_ASSERT_EQUAL(pxCurrentTCB, task_handle2);

    /* Expectations */
    /* eTaskGetState */
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &ptcb->xStateListItem,
                                             pxDelayedTaskList );
    /* back */
    uxListRemove_ExpectAndReturn(&tcb->xStateListItem, pdTRUE);
    listLIST_ITEM_CONTAINER_ExpectAndReturn(&ptcb->xEventListItem,
                                            pxDelayedTaskList);
    uxListRemove_ExpectAndReturn(&ptcb->xEventListItem, pdTRUE);
    /* prvAddTaskToReadyList */
    vListInsertEnd_Expect( &pxReadyTasksLists[ created_task_priority ],
                           &ptcb->xStateListItem );
    /* xTaskResumeAll */
    listLIST_IS_EMPTY_ExpectAndReturn(&xPendingReadyList, pdTRUE);
    /* API Call */
    ret_taskabort_delay = xTaskAbortDelay( task_handle );
    /* Validations */
    TEST_ASSERT_TRUE( ret_taskabort_delay );
    TEST_ASSERT_TRUE( xYieldPending );
    TEST_ASSERT_TRUE( ptcb->ucDelayAborted );
}

/* testing INCLUDE_xTaskGetIdleTaskHandle */

void test_xTaskGetIdleTaskHandle_success(void)
{
    TaskHandle_t ret_idle_handle;
    int ret;

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

    vListInsertEnd_ExpectAnyArgs();

    xTimerCreateTimerTask_ExpectAndReturn( pdPASS );
    xPortStartScheduler_ExpectAndReturn( pdTRUE );
    getIddleTaskMemoryValid = true;
    vTaskStartScheduler();
    TEST_ASSERT_EQUAL( true, getIddleTaskMemoryCalled );
    ret_idle_handle = xTaskGetIdleTaskHandle( );
    ptcb = ret_idle_handle;
    ret = strcmp( ptcb->pcTaskName, "IDLE");
    TEST_ASSERT_EQUAL(0, ret);
}


/* testing configUSE_APPLICATION_TASK_TAG */
void test_vTaskSetApplicationTaskTag_current(void)
{
    create_task();

    vTaskSetApplicationTaskTag( NULL, pxHookFunction);

    TEST_ASSERT_EQUAL( &pxHookFunction, pxCurrentTCB->pxTaskTag);
}

void test_vTaskSetApplicationTaskTag_handle(void)
{
    TaskHandle_t task_handle;
    task_handle = create_task();

    vTaskSetApplicationTaskTag( task_handle, pxHookFunction);
    TEST_ASSERT_EQUAL( &pxHookFunction, task_handle->pxTaskTag);
}

void test_xTaskGetApplicationTaskTag_null_tcb_current(void)
{
    TaskHandle_t task_handle;
    task_handle = create_task();
    vTaskSetApplicationTaskTag( task_handle, pxHookFunction);

    TaskHookFunction_t hook_function;
    hook_function = xTaskGetApplicationTaskTag(NULL);

    TEST_ASSERT_EQUAL(&pxHookFunction, hook_function);
}

void test_xTaskGetApplicationTaskTag_tcb(void)
{
    TaskHandle_t task_handle;
    task_handle = create_task();
    vTaskSetApplicationTaskTag( task_handle, pxHookFunction);

    TaskHookFunction_t hook_function;
    hook_function = xTaskGetApplicationTaskTag(task_handle);

    TEST_ASSERT_EQUAL(&pxHookFunction, hook_function);
}

void test_xTaskGetApplicationTaskTag_no_hook_set(void)
{
    TaskHandle_t task_handle;
    task_handle = create_task();
    TaskHookFunction_t hook_function;

    hook_function = xTaskGetApplicationTaskTag(task_handle);

    TEST_ASSERT_EQUAL(NULL, hook_function);
}

void test_xTaskGetApplicationTaskTagFromISR_success(void)
{
    TaskHandle_t task_handle;
    task_handle = create_task();
    vTaskSetApplicationTaskTag( task_handle, pxHookFunction);

    TaskHookFunction_t hook_function;
    hook_function = xTaskGetApplicationTaskTagFromISR(task_handle);

    TEST_ASSERT_EQUAL(&pxHookFunction, hook_function);
    ASSERT_PORT_CLEAR_INTERRUPT_CALLED();
    ASSERT_PORT_SET_INTERRUPT_CALLED();
}

void test_xTaskGetApplicationTaskTagFromISR_null_handle(void)
{
    TaskHandle_t task_handle;
    task_handle = create_task();
    vTaskSetApplicationTaskTag( task_handle, pxHookFunction);

    TaskHookFunction_t hook_function;
    hook_function = xTaskGetApplicationTaskTagFromISR(NULL);

    TEST_ASSERT_EQUAL(&pxHookFunction, hook_function);
    ASSERT_PORT_CLEAR_INTERRUPT_CALLED();
    ASSERT_PORT_SET_INTERRUPT_CALLED();
}

void test_xTaskCallApplicationTaskHook_success(void)
{
    BaseType_t  ret_task_hook;
    TaskHandle_t task_handle;
    BaseType_t i = 5;
    void * args = &i;
    task_handle = create_task();
    vTaskSetApplicationTaskTag( task_handle, pxHookFunction );

    ret_task_hook = xTaskCallApplicationTaskHook( task_handle,
                                                  args );
    TEST_ASSERT_EQUAL(i, ret_task_hook);
}

void test_xTaskCallApplicationTaskHook_success_null_handle(void)
{
    BaseType_t  ret_task_hook;
    TaskHandle_t task_handle;
    BaseType_t i = 6;
    void * args = &i;
    task_handle = create_task();

    vTaskSetApplicationTaskTag( task_handle, pxHookFunction );

    ret_task_hook = xTaskCallApplicationTaskHook( NULL,
                                                  args );
    TEST_ASSERT_EQUAL(i, ret_task_hook);
}

void test_xTaskCallApplicationTaskHook_fail_no_tag_set(void)
{
    BaseType_t  ret_task_hook;
    TaskHandle_t task_handle;
    int i = 7;
    void * args = &i;
    task_handle = create_task();

    ret_task_hook = xTaskCallApplicationTaskHook( task_handle,
                                                  args );
    TEST_ASSERT_EQUAL(pdFAIL, ret_task_hook);
}

/* end testing configUSE_APPLICATION_TASK_TAG */


void test_vTaskSwitchContext( void )
{
    TaskHandle_t task_handle;
    TaskHandle_t task_handle2;

    created_task_priority = 3;
    task_handle = create_task();
    created_task_priority = 4;
    task_handle2 = create_task();
    ptcb = task_handle;

    INITIALIZE_LIST_2E( pxReadyTasksLists[3],
                        ptcb, task_handle2 );
    INITIALIZE_LIST_2E( pxReadyTasksLists[4],
                        ptcb, task_handle2 );

    /* Setup */
    uxSchedulerSuspended = pdFALSE;
    /* Expectations */

    /* API Call */
    vTaskSwitchContext( );

    /* Validations */
    TEST_ASSERT_EQUAL( 24, uxTopReadyPriority );
    TEST_ASSERT_FALSE( xYieldPending );
}

void test_vTaskPlaceOnEventList_success( void )
{
    TaskHandle_t task_handle;
    List_t  eventList;

    created_task_priority = 3;
    task_handle = create_task();
    ptcb = task_handle;


    /* Expectations */
    vListInsert_Expect(&eventList, &ptcb->xEventListItem);
    /*  prvAddCurrentTaskToDelayedList */
    uxListRemove_ExpectAndReturn(&ptcb->xStateListItem, 1);
    listSET_LIST_ITEM_VALUE_Expect(&ptcb->xStateListItem, (xTickCount + 34));
    vListInsert_Expect(pxDelayedTaskList, &ptcb->xStateListItem);

    /* API call */
    vTaskPlaceOnEventList( &eventList,
                            34 );
    TEST_ASSERT_EQUAL( 0, xNextTaskUnblockTime );
}
void test_vTaskPlaceOnUnorderedEventList( void)
{
    TaskHandle_t task_handle;
    List_t eventList;

    created_task_priority = 3;
    task_handle = create_task();
    ptcb = task_handle;
    xNextTaskUnblockTime  = 600;

    /* Expectations */
    listSET_LIST_ITEM_VALUE_Expect(&ptcb->xEventListItem,  32 | 0x80000000UL);
    vListInsertEnd_Expect(&eventList, &ptcb->xEventListItem);
    /* prvAddCurrentTaskToDelayedList */
    uxListRemove_ExpectAndReturn(&ptcb->xStateListItem, 1);
    listSET_LIST_ITEM_VALUE_Expect(&ptcb->xStateListItem, (xTickCount + 34));
    vListInsert_Expect(pxDelayedTaskList, &ptcb->xStateListItem);
    /* API Call */
    vTaskPlaceOnUnorderedEventList( &eventList, 32, 34);
    TEST_ASSERT_EQUAL( xTickCount + 34, xNextTaskUnblockTime );
}

/* testing configUSE_TIMERS  */
void test_vTaskPlaceOnEventListRestricted_indefinite(void)
{
    List_t eventList;
    TaskHandle_t task_handle;

    created_task_priority = 3;
    task_handle = create_task();
    ptcb = task_handle;
    /* Expectations */
    vListInsertEnd_Expect(&eventList, &ptcb->xEventListItem);
    /* prvAddCurrentTaskToDelayedList */
    uxListRemove_ExpectAndReturn(&ptcb->xStateListItem, 0);
    vListInsertEnd_Expect( &xSuspendedTaskList, &( ptcb->xStateListItem ) );
    /* API Call */
    vTaskPlaceOnEventListRestricted( &eventList, 100, pdTRUE);

}

void test_vTaskPlaceOnEventListRestricted_not_indefinite(void)
{
    List_t eventList;
    TaskHandle_t task_handle;

    created_task_priority = 3;
    task_handle = create_task();
    ptcb = task_handle;
    /* Expectations */
    vListInsertEnd_Expect(&eventList, &ptcb->xEventListItem);
    /* prvAddCurrentTaskToDelayedList */
    uxListRemove_ExpectAndReturn(&ptcb->xStateListItem, 1);
    listSET_LIST_ITEM_VALUE_Expect(&ptcb->xStateListItem, (xTickCount + 100));
    vListInsert_Expect(pxDelayedTaskList, &ptcb->xStateListItem);
    /* API Call */
    vTaskPlaceOnEventListRestricted( &eventList, 100, pdFALSE);
}

void test_vTaskPlaceOnEventListRestricted_max_wait(void)
{
    List_t eventList;
    TaskHandle_t task_handle;

    created_task_priority = 3;
    task_handle = create_task();
    ptcb = task_handle;
    /* Expectations */
    vListInsertEnd_Expect(&eventList, &ptcb->xEventListItem);
    /* prvAddCurrentTaskToDelayedList */
    uxListRemove_ExpectAndReturn(&ptcb->xStateListItem, 1);
    listSET_LIST_ITEM_VALUE_Expect(&ptcb->xStateListItem, (xTickCount + portMAX_DELAY));
    vListInsert_Expect(pxDelayedTaskList, &ptcb->xStateListItem);
    /* API Call */
    vTaskPlaceOnEventListRestricted( &eventList, portMAX_DELAY, pdFALSE);
}
/* end testing configUSE_TIMERS  */

void test_xTaskRemoveFromEventList_fail(void)
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
    uxListRemove_ExpectAndReturn( &ptcb->xEventListItem, pdTRUE );
    uxListRemove_ExpectAndReturn( &ptcb->xStateListItem, pdTRUE );
    /* prvAddTaskToReadyList */
    vListInsertEnd_Expect( &pxReadyTasksLists[ created_task_priority ],
                           &ptcb->xStateListItem );
    /* prvResetNextTaskUnblockTime */
    listLIST_IS_EMPTY_ExpectAndReturn(pxDelayedTaskList, pdTRUE);
    /* API Call */
    ret_task_remove = xTaskRemoveFromEventList( &eventList );
    /* Validations */
    TEST_ASSERT_EQUAL( pdFALSE, ret_task_remove );
    TEST_ASSERT_EQUAL( pdFALSE, xYieldPending );
}

void test_xTaskRemoveFromEventList_sched_suspended(void)
{
    BaseType_t ret_task_remove;
    TaskHandle_t task_handle;
    TaskHandle_t task_handle2;
    List_t eventList;

    /* Setup */
    uxSchedulerSuspended = pdTRUE;
    created_task_priority = 3;
    task_handle = create_task();
    ptcb = task_handle; /* unblocked */

    /* block the higher priority task */
    uxListRemove_ExpectAndReturn(&ptcb->xStateListItem, 1 );
    listLIST_ITEM_CONTAINER_ExpectAndReturn(&ptcb->xEventListItem,
                                            &xSuspendedTaskList );
    uxListRemove_ExpectAndReturn( &ptcb->xEventListItem, pdTRUE);
    vListInsertEnd_Expect(&xSuspendedTaskList, &ptcb->xStateListItem );
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &xSuspendedTaskList,
                                             uxCurrentNumberOfTasks) ;
    TEST_ASSERT_EQUAL(pxCurrentTCB, task_handle);

    vTaskSuspend(task_handle);
    TEST_ASSERT_EQUAL(NULL, pxCurrentTCB);
    created_task_priority = 2;
    task_handle2 = create_task();
    TEST_ASSERT_EQUAL(task_handle2, pxCurrentTCB);

    /* Expectations */
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAndReturn( &eventList, ptcb );
    uxListRemove_ExpectAndReturn( &ptcb->xEventListItem, pdTRUE );
    vListInsertEnd_Expect(&xPendingReadyList, &ptcb->xEventListItem);
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
    created_task_priority = 3;
    task_handle = create_task();
    ptcb = task_handle;

    /* Expectations */
    listSET_LIST_ITEM_VALUE_Expect( &list_item, xItemValue | 0x80000000UL);
    listGET_LIST_ITEM_OWNER_ExpectAndReturn(&list_item, tcb);
    uxListRemove_ExpectAndReturn(&list_item, pdTRUE);
    /* prvResetNextTaskUnblockTime */
    listLIST_IS_EMPTY_ExpectAndReturn(pxDelayedTaskList, pdTRUE);
    /* back */
    uxListRemove_ExpectAndReturn(&ptcb->xStateListItem, pdTRUE);
    /* prvAddTaskToReadyList */
    vListInsertEnd_Expect( &pxReadyTasksLists[ created_task_priority ],
                           &ptcb->xStateListItem );

    /* API Call */
    vTaskRemoveFromUnorderedEventList( &list_item,
                                       xItemValue );
    /* Validations */
    TEST_ASSERT_FALSE(xYieldPending);
}

void test_vTaskRemoveFromUnorderedEventList_yielding( void )
{
    ListItem_t list_item;
    TickType_t xItemValue = 500;
    TaskHandle_t task_handle;
    TaskHandle_t task_handle2;

    /* Setup */
    uxSchedulerSuspended = pdTRUE;
    created_task_priority = 3;
    task_handle = create_task();
    ptcb = task_handle;
    /* block the higher priority task */
    uxListRemove_ExpectAndReturn(&ptcb->xStateListItem, 1 );
    listLIST_ITEM_CONTAINER_ExpectAndReturn(&ptcb->xEventListItem,
                                            &xSuspendedTaskList );
    uxListRemove_ExpectAndReturn( &ptcb->xEventListItem, pdTRUE);
    vListInsertEnd_Expect(&xSuspendedTaskList, &ptcb->xStateListItem );
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &xSuspendedTaskList,
                                             uxCurrentNumberOfTasks) ;
    TEST_ASSERT_EQUAL(pxCurrentTCB, task_handle);

    vTaskSuspend(task_handle);
    TEST_ASSERT_EQUAL(NULL, pxCurrentTCB);
    created_task_priority = 2;
    task_handle2 = create_task();
    TEST_ASSERT_EQUAL(task_handle2, pxCurrentTCB);

    /* Expectations */
    listSET_LIST_ITEM_VALUE_Expect( &list_item, xItemValue | 0x80000000UL);
    listGET_LIST_ITEM_OWNER_ExpectAndReturn(&list_item, tcb);
    uxListRemove_ExpectAndReturn(&list_item, pdTRUE);
    /* prvResetNextTaskUnblockTime */
    listLIST_IS_EMPTY_ExpectAndReturn(pxDelayedTaskList, pdTRUE);
    /* back */
    uxListRemove_ExpectAndReturn(&ptcb->xStateListItem, pdTRUE);
    /* prvAddTaskToReadyList */
    vListInsertEnd_Expect( &pxReadyTasksLists[ created_task_priority ],
                           &ptcb->xStateListItem );

    /* API Call */
    vTaskRemoveFromUnorderedEventList( &list_item,
                                       xItemValue );
    /* Validations */
    TEST_ASSERT_TRUE(xYieldPending);
}

void test_vTaskSetTimeOutState_success(void)
{
    TimeOut_t time_out;

    /* API Call */
    vTaskSetTimeOutState( &time_out );
    /* Validations */
    TEST_ASSERT_EQUAL( xNumOfOverflows, time_out.xOverflowCount );
    TEST_ASSERT_EQUAL( xTickCount, time_out.xTimeOnEntering );
}

void test_vTaskInternalSetTimeOutState_success(void)
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
    TickType_t  ticks_to_wait = 5;
    TaskHandle_t task_handle;
    created_task_priority = 3;
    task_handle = create_task();
    ptcb = task_handle;

    ret_check_timeout = xTaskCheckForTimeOut( &time_out,
                                              &ticks_to_wait );
    TEST_ASSERT_TRUE(ret_check_timeout);
}

void test_xTaskCheckForTimeOut_delay_aborted( void )
{
    BaseType_t ret_check_timeout;
    TimeOut_t time_out;
    TickType_t  ticks_to_wait = portMAX_DELAY;
    TaskHandle_t task_handle;
    created_task_priority = 3;
    task_handle = create_task();
    ptcb = task_handle;
    ptcb->ucDelayAborted = pdTRUE; /* achieved by calling  xTaskAbortDelay */

    ret_check_timeout = xTaskCheckForTimeOut( &time_out,
                                              &ticks_to_wait );
    TEST_ASSERT_TRUE(ret_check_timeout);
}

void test_xTaskCheckForTimeOut_max_delay( void )
{
    BaseType_t ret_check_timeout;
    TimeOut_t time_out;
    TickType_t  ticks_to_wait = portMAX_DELAY;
    TaskHandle_t task_handle;
    created_task_priority = 3;
    task_handle = create_task();
    ptcb = task_handle;

    ret_check_timeout = xTaskCheckForTimeOut( &time_out,
                                              &ticks_to_wait );
    TEST_ASSERT_FALSE(ret_check_timeout);
}

void test_xTaskCheckForTimeOut_overflow( void )
{
    BaseType_t ret_check_timeout;
    TimeOut_t time_out;
    TickType_t  ticks_to_wait = 10;
    TaskHandle_t task_handle;
    created_task_priority = 3;
    task_handle = create_task();
    ptcb = task_handle;
    time_out.xOverflowCount = xNumOfOverflows + 2;
    time_out.xTimeOnEntering  = xTickCount - 3;

    ret_check_timeout = xTaskCheckForTimeOut( &time_out,
                                              &ticks_to_wait );
    TEST_ASSERT_TRUE(ret_check_timeout);
    TEST_ASSERT_EQUAL(0, ticks_to_wait);
}

    //const TickType_t xElapsedTime = xConstTickCount - pxTimeOut->xTimeOnEntering;
void test_xTaskCheckForTimeOut_timeout( void )
{
    BaseType_t ret_check_timeout;
    TimeOut_t time_out;
    TickType_t  ticks_to_wait = 1000;
    TaskHandle_t task_handle;
    created_task_priority = 3;
    task_handle = create_task();
    ptcb = task_handle;
    ptcb->ucDelayAborted = pdFALSE;
    time_out.xOverflowCount = xNumOfOverflows;
    time_out.xTimeOnEntering  =  3;
    uint32_t expected = (1000 - (xTickCount - time_out.xTimeOnEntering));
    /* API Call */
    ret_check_timeout = xTaskCheckForTimeOut( &time_out,
                                              &ticks_to_wait );
    /* Validations */
    TEST_ASSERT_FALSE(ret_check_timeout);
    TEST_ASSERT_EQUAL(expected, ticks_to_wait);
    TEST_ASSERT_EQUAL(xTickCount, time_out.xTimeOnEntering);
}


void test_vTaskMissedYield( void )
{
    TEST_ASSERT_FALSE(xYieldPending);
    vTaskMissedYield( );
    TEST_ASSERT_TRUE(xYieldPending);
}

void test_prvIddleTask( void )
{
    int i = 8;
    void *args = &i;
    portTASK_FUNCTION( prvIdleTask, args);
}













/*
xtaskdelayuntil
vtaskdelay
etaskgetstate
uxTaskPriorityGet
uxTaskPriorityGetFromISR
vTaskSuspend
set critical nesting in tcb
*/

/* expected , actual */
