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
extern uint32_t ulTaskSwitchedInTime;
extern volatile uint32_t ulTotalRunTime;

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
    pxDelayedTaskList = NULL;
    pxOverflowDelayedTaskList = NULL;
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
    uxSchedulerSuspended = ( UBaseType_t ) pdFALSE;
    ulTaskSwitchedInTime = 0UL;
    ulTotalRunTime = 0UL;

    vTaskDeletePreCalled = false;
    getIddleTaskMemoryCalled = false;
    is_first_task = true;
    created_tasks = 0;
    port_yield_called  = false;
    port_setup_tcb_called = false;
    portClear_Interrupt_called = false;
    portSet_Interrupt_called = false;
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
                                       & ( ~( ( portPOINTER_SIZE_TYPE ) portBYTE_ALIGNMENT_MASK ) ) ); /*lint !e923 !e9033 !e9078 MISRA exception.  Avoiding casts between pointers and integers is not practical.  Size differences accounted for using portPOINTER_SIZE_TYPE type.  Checked by assert(). */

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

    /* API Call */
    vTaskSuspend( task_handle );
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
