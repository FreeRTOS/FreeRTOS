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
/*! @file timers_utest.c */


/* Test includes. */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"
#include "portmacro.h"
#include "timers.h"

#include "global_vars.h"

#include "unity.h"
#include "unity_memory.h"

/* Mock includes. */
#include "mock_queue.h"
#include "mock_list.h"
#include "mock_list_macros.h"
#include "mock_fake_assert.h"
#include "mock_portable.h"
#include "mock_task.h"

/* C runtime includes. */
#include <stdlib.h>
#include <stdbool.h>
#include <pthread.h>

void stopTimers();

/* ============================  GLOBAL VARIABLES =========================== */
static uint16_t usMallocFreeCalls = 0;
static uint32_t critical_section_counter;
static char task_memory[ 200 ];

static TickType_t saved_last_time = 0;

static bool port_yield_within_api_called = false;
static bool vApplicationDaemonTaskStartupHook_Called = false;
static bool xCallback_Test_Called = pdFALSE;
static bool pended_function_4_end_called = pdFALSE;
static bool xCallback_Test_1_end_called = pdFALSE;
static bool xCallback_Test_2_end_called = pdFALSE;

/* =================================  DEFINES  ============================== */
#define DEFAULT_TIMER_PERIOD    1000
#define DEFAULT_TIMER_NAME      "ut_timer"

/* =============================  FUNCTION MACROS  ========================== */
#define ASSERT_APPLICATION_DAEMON_STARTUP_HOOK_CALLED()               \
    do {                                                              \
        TEST_ASSERT_TRUE( vApplicationDaemonTaskStartupHook_Called ); \
        vApplicationDaemonTaskStartupHook_Called = pdFALSE;           \
    } while( 0 )

#define ASSERT_XCALLBACK_TEST_CALLED()             \
    do {                                           \
        TEST_ASSERT_TRUE( xCallback_Test_Called ); \
        xCallback_Test_Called = pdFALSE;           \
    } while( 0 )

#define ASSERT_PENDED_FUNCTION_4_END_CALLED()             \
    do {                                                  \
        TEST_ASSERT_TRUE( pended_function_4_end_called ); \
        pended_function_4_end_called = pdFALSE;           \
    } while( 0 )

#define ASSERT_XCALLBACK_TEST_1_END_CALLED()             \
    do {                                                 \
        TEST_ASSERT_TRUE( xCallback_Test_1_end_called ); \
        xCallback_Test_1_end_called = pdFALSE;           \
    } while( 0 )

#define ASSERT_XCALLBACK_TEST_2_END_CALLED()             \
    do {                                                 \
        TEST_ASSERT_TRUE( xCallback_Test_2_end_called ); \
        xCallback_Test_2_end_called = pdFALSE;           \
    } while( 0 )

#define ASSERT_PORT_YIELD_WITHIN_API_CALLED()             \
    do {                                                  \
        TEST_ASSERT_TRUE( port_yield_within_api_called ); \
        port_yield_within_api_called = pdFALSE;           \
    } while( 0 )

/* =============================  FUNCTION HOOKS  =========================== */
void vFakePortEnterCriticalSection( void )
{
    critical_section_counter++;
}

void vFakePortExitCriticalSection( void )
{
    critical_section_counter--;
}

void vFakePortYieldWithinAPI()
{
    HOOK_DIAG();
    port_yield_within_api_called = true;
    pthread_exit( NULL );
}

void vApplicationGetTimerTaskMemory( StaticTask_t ** ppxTimerTaskTCBBuffer,
                                     StackType_t ** ppxTimerTaskStackBuffer,
                                     uint32_t * pulTimerTaskStackSize )
{
    static StaticTask_t xTimerTaskTCB;
    static StackType_t uxTimerTaskStack[ configTIMER_TASK_STACK_DEPTH ];

    *ppxTimerTaskTCBBuffer = &xTimerTaskTCB;
    *ppxTimerTaskStackBuffer = uxTimerTaskStack;
    *pulTimerTaskStackSize = configTIMER_TASK_STACK_DEPTH;
}


void vApplicationDaemonTaskStartupHook( void )
{
    vApplicationDaemonTaskStartupHook_Called = pdTRUE;
    HOOK_DIAG();
}

/* ==========================  CALLBACK FUNCTIONS  ========================== */
static void xCallback_Test( TimerHandle_t xTimer )
{
    HOOK_DIAG();
    xCallback_Test_Called = pdTRUE;
}
typedef void (* PendedFunction_t)( void *,
                                   uint32_t );

static void pended_function( void * arg1,
                             uint32_t arg2 )
{
    HOOK_DIAG();
}
static int32_t end_4_timer = 0;
static void pended_function_4_end( void * arg1,
                                   uint32_t arg2 )
{
    HOOK_DIAG();
    static int i = 4;
    pended_function_4_end_called = pdTRUE;

    if( end_4_timer - 1 <= 0 )
    {
        pthread_exit( &i );
    }

    end_4_timer--;
}

static int32_t end_1_timer = 0;
static void xCallback_Test_1_end( TimerHandle_t xTimer )
{
    HOOK_DIAG();
    static int i = 1;

    xCallback_Test_1_end_called = pdTRUE;

    if( end_1_timer - 1 <= 0 )
    {
        pthread_exit( &i );
    }

    end_1_timer--;
}

static int32_t end_2_timer = 0;
static void xCallback_Test_2_end( TimerHandle_t xTimer )
{
    HOOK_DIAG();
    static int i = 2;

    xCallback_Test_2_end_called = pdTRUE;

    if( end_2_timer - 1 <= 0 )
    {
        pthread_exit( &i );
    }

    end_2_timer--;
}

/* Function hook to xQueueReceive used to end the testcase */

/*
 * static BaseType_t end_queue_receive(QueueHandle_t queue,
 *                                  void *const message,
 *                                  TickType_t delay,
 *                                  int callnum)
 * {
 *  HOOK_DIAG();
 *  static int i = 5;
 *  pthread_exit( &i );
 * }
 */

/**
 * @brief Callback for vTaskYieldTaskWithinAPI used by tests for yield counts
 *
 * NumCalls is checked in the test assert.
 */
static void vTaskYieldWithinAPI_Callback( int NumCalls )
{
    ( void ) NumCalls;

    portYIELD_WITHIN_API();
}

/* =============================  STATIC FUNCTIONS  ========================= */
static void * timer_thread_function( void * args )
{
    void * pvParameters = NULL;

    portTASK_FUNCTION( prvTimerTask, pvParameters );
    ( void ) fool_static2; /* ignore unused variable warning */
    /* API Call */
    prvTimerTask( pvParameters );
    return NULL;
}

static void create_timer_task( void )
{
    BaseType_t ret_xtimer;
    QueueHandle_t queue_handle = ( QueueHandle_t ) 3; /* not zero */
    TaskHandle_t timer_handle = ( TaskHandle_t ) task_memory;

    /* Setup */
    /* Expectations */
    vListInitialise_ExpectAnyArgs();
    vListInitialise_ExpectAnyArgs();
    xQueueGenericCreateStatic_ExpectAnyArgsAndReturn( queue_handle );
    vQueueAddToRegistry_ExpectAnyArgs();
    xTaskCreateStatic_ExpectAnyArgsAndReturn( timer_handle );
    /* API Call */
    ret_xtimer = xTimerCreateTimerTask();
    /* Validations */
    TEST_ASSERT_TRUE( ret_xtimer );
}

static TimerHandle_t create_timer()
{
    uint32_t pvTimerID = 0;
    TimerHandle_t xTimer = NULL;
    StaticTimer_t pxTimerBuffer[ sizeof( StaticTimer_t ) ];
    QueueHandle_t queue_handle = ( QueueHandle_t ) 3; /* not zero */

    /*pvPortMalloc_ExpectAndReturn( sizeof( Timer_t ), &pxNewTimer ); */
    vListInitialise_ExpectAnyArgs();
    vListInitialise_ExpectAnyArgs();
    xQueueGenericCreateStatic_ExpectAnyArgsAndReturn( queue_handle );
    vQueueAddToRegistry_ExpectAnyArgs();
    vListInitialiseItem_ExpectAnyArgs();

    xTimer = xTimerCreateStatic( DEFAULT_TIMER_NAME,
                                 DEFAULT_TIMER_PERIOD,
                                 pdTRUE,
                                 ( void * ) &pvTimerID,
                                 xCallback_Test,
                                 pxTimerBuffer );
    return xTimer;
}

/* ============================  UNITY FIXTURES  =========================== */
void setUp( void )
{
    vFakeAssert_Ignore();
    port_yield_within_api_called = pdFALSE;
    xCallback_Test_Called = pdFALSE;
    pended_function_4_end_called = pdFALSE;
    xCallback_Test_1_end_called = pdFALSE;
    xCallback_Test_2_end_called = pdFALSE;
    /* Track calls to malloc / free */
    UnityMalloc_StartTest();
    critical_section_counter = 0;
    stopTimers();
}

/*! called before each testcase */
void tearDown( void )
{
    TEST_ASSERT_EQUAL_INT_MESSAGE( 0, usMallocFreeCalls,
                                   "free is not called the same number of times as malloc,"
                                   "you might have a memory leak!!" );
    usMallocFreeCalls = 0;
    vApplicationDaemonTaskStartupHook_Called = pdFALSE;

    UnityMalloc_EndTest();
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


/* ==============================  TEST FUNCTIONS  ========================== */

/*!
 * @brief success testcase for calling the test function the very first time
 *        expects pdPASS
 */
void test_xTimerCreateTimerTask_success( void )
{
    BaseType_t ret_xtimer;
    QueueHandle_t queue_handle = ( QueueHandle_t ) 3; /* not zero */
    char task_memory[ 200 ];
    TaskHandle_t timer_handle = ( TaskHandle_t ) task_memory;

    /* Setup */
    /* Expectations */
    vListInitialise_ExpectAnyArgs();
    vListInitialise_ExpectAnyArgs();
    xQueueGenericCreateStatic_ExpectAnyArgsAndReturn( queue_handle );
    vQueueAddToRegistry_ExpectAnyArgs();
    xTaskCreateStatic_ExpectAnyArgsAndReturn( timer_handle );
    /* API Call */
    ret_xtimer = xTimerCreateTimerTask();
    /* Validations */
    TEST_ASSERT_TRUE( ret_xtimer );
}

/*!
 * @brief failed test case, could not create a static task
 *        expects pdFAIL
 */
void test_xTimerCreateTimerTask_fail_null_task( void )
{
    BaseType_t ret_xtimer;
    QueueHandle_t queue_handle = ( QueueHandle_t ) 3; /* not zero */

    /* Setup */
    /* Expectations */
    vListInitialise_ExpectAnyArgs();
    vListInitialise_ExpectAnyArgs();
    xQueueGenericCreateStatic_ExpectAnyArgsAndReturn( queue_handle );
    vQueueAddToRegistry_ExpectAnyArgs();
    xTaskCreateStatic_ExpectAnyArgsAndReturn( NULL );
    /* API Call */
    ret_xtimer = xTimerCreateTimerTask();
    /* Validations */
    TEST_ASSERT_FALSE( ret_xtimer );
}

/*!
 * @brief success test case, when the timer task function has already been called
 *        expects pdFAIL
 */
void test_xTimerCreateTimerTask_fail_null_queue( void )
{
    BaseType_t ret_xtimer;

    /* Setup */
    /* Expectations */
    vListInitialise_ExpectAnyArgs();
    vListInitialise_ExpectAnyArgs();
    xQueueGenericCreateStatic_ExpectAnyArgsAndReturn( NULL );
    /* API Call */
    ret_xtimer = xTimerCreateTimerTask();
    /* Validations */
    TEST_ASSERT_FALSE( ret_xtimer );
}

/*!
 * @brief success test case, creates a new timer
 *        expects pdPASS
 */
void test_xTimerCreateStatic_success( void )
{
    TimerHandle_t ret_timer_create;
    UBaseType_t pvTimerID;
    StaticTimer_t pxTimerBuffer[ sizeof( StaticTimer_t ) ];

    /* Setup */
    /* Expectations */
    /* prvInitialiseNewTimer */
    /* prvCheckForValidListAndQueue */
    vListInitialise_ExpectAnyArgs();
    vListInitialise_ExpectAnyArgs();
    xQueueGenericCreateStatic_ExpectAnyArgsAndReturn( NULL );
    /* Back prvInitialiseNewTimer */
    vListInitialiseItem_ExpectAnyArgs();
    /* API Call */
    ret_timer_create = xTimerCreateStatic( "ut_timer_task",
                                           pdMS_TO_TICKS( 1000 ),
                                           pdTRUE,
                                           ( void * ) &pvTimerID,
                                           xCallback_Test,
                                           pxTimerBuffer );
    /* Validations */
    TEST_ASSERT_TRUE( ret_timer_create );
}

/*!
 * @brief failed testcase, passing a null buffer
 *        expects pdFAIL
 */
void test_xTimerCreateStatic_fail_null_buffer( void )
{
    TimerHandle_t ret_timer_create;
    UBaseType_t pvTimerID;

    /* Setup */
    /* Expectations */
    /* API Call */
    ret_timer_create = xTimerCreateStatic( "ut_timer_task",
                                           pdMS_TO_TICKS( 1000 ),
                                           pdTRUE,
                                           ( void * ) &pvTimerID,
                                           xCallback_Test,
                                           NULL );
    /* Validations */
    TEST_ASSERT_FALSE( ret_timer_create );
}

/*!
 * @brief success testcase, adding a timer event to the queue
 *        expects pdPASS
 */
void test_xTimerGenericCommand_success_queue_pass( void )
{
    BaseType_t ret_timer_generic;
    TimerHandle_t xTimer;
    BaseType_t pxHigherPriorityTaskWoken = pdFALSE;
    const TickType_t xTicksToWait = 400;

    /* Setup */
    xTimer = create_timer();
    /* Expectations */

    xQueueGenericSendFromISR_ExpectAnyArgsAndReturn( pdPASS );
    /* API Call */
    ret_timer_generic = xTimerGenericCommand( xTimer,
                                              tmrFIRST_FROM_ISR_COMMAND,
                                              34,
                                              &pxHigherPriorityTaskWoken,
                                              xTicksToWait );
    /* Validations */
    TEST_ASSERT_TRUE( ret_timer_generic );
}

/*!
 * @brief failed testcase, adding a timer event to the queue fails
 *        expects pdFAIL
 */
void test_xTimerGenericCommand_fail_queue_fail( void )
{
    BaseType_t ret_timer_generic;
    TimerHandle_t xTimer;
    BaseType_t pxHigherPriorityTaskWoken = pdFALSE;
    const TickType_t xTicksToWait = 400;

    /* Setup */
    xTimer = create_timer();
    /* Expectations */

    xQueueGenericSendFromISR_ExpectAnyArgsAndReturn( pdFAIL );
    /* API Call */
    ret_timer_generic = xTimerGenericCommand( xTimer,
                                              tmrFIRST_FROM_ISR_COMMAND,
                                              34,
                                              &pxHigherPriorityTaskWoken,
                                              xTicksToWait );
    /* Validations */
    TEST_ASSERT_FALSE( ret_timer_generic );
}

/*!
 * @brief success testcase, adding a timer event from isr to the queue while
 *        the scheduler is running
 *        expects pdPASS
 */
void test_xTimerGenericCommand_success_sched_running( void )
{
    BaseType_t ret_timer_generic;
    TimerHandle_t xTimer;
    BaseType_t pxHigherPriorityTaskWoken = pdFALSE;
    const TickType_t xTicksToWait = 400;

    /* Setup */
    xTimer = create_timer();
    /* Expectations */
    xTaskGetSchedulerState_ExpectAndReturn( taskSCHEDULER_RUNNING );
    xQueueGenericSend_ExpectAnyArgsAndReturn( pdPASS );
    /* API Call */
    ret_timer_generic = xTimerGenericCommand( xTimer,
                                              tmrCOMMAND_START,
                                              34,
                                              &pxHigherPriorityTaskWoken,
                                              xTicksToWait );
    /* Validations */
    TEST_ASSERT_TRUE( ret_timer_generic );
}

/*!
 * @brief success testcase, adding a timer event from isr to the queue while
 *        the scheduler is *NOT* running
 *        expects pdPASS
 */
void test_xTimerGenericCommand_success_sched_not_running( void )
{
    BaseType_t ret_timer_generic;
    TimerHandle_t xTimer;
    BaseType_t pxHigherPriorityTaskWoken = pdFALSE;
    const TickType_t xTicksToWait = 400;

    /* Setup */
    xTimer = create_timer();
    /* Expectations */
    xTaskGetSchedulerState_ExpectAndReturn( taskSCHEDULER_NOT_STARTED );
    xQueueGenericSend_ExpectAnyArgsAndReturn( pdPASS );

    /* API Call */
    ret_timer_generic = xTimerGenericCommand( xTimer,
                                              tmrCOMMAND_START,
                                              34,
                                              &pxHigherPriorityTaskWoken,
                                              xTicksToWait );
    /* Validations */
    TEST_ASSERT_TRUE( ret_timer_generic );
}

/*!
 * @brief failed testcase, adding a timer event while the timer task is not
 *        running ( xTimerCreate[Static] has not been already called )
 *        expects pdFALSE
 */
void test_xTimerGenericCommand_success_null_timer_not_started( void )
{
    BaseType_t ret_timer_generic;
    TimerHandle_t xTimer = NULL;
    BaseType_t pxHigherPriorityTaskWoken = pdFALSE;
    const TickType_t xTicksToWait = 400;

    /* Setup */
    /* Expectations */
    /* API Call */
    ret_timer_generic = xTimerGenericCommand( xTimer,
                                              tmrCOMMAND_START,
                                              34,
                                              &pxHigherPriorityTaskWoken,
                                              xTicksToWait );
    /* Validations */
    TEST_ASSERT_FALSE( ret_timer_generic );
}

/*!
 * @brief success testcase, getter for the timer handle daemon
 *        expects a non NULL value
 */
void test_xTimerGetTimerDaemonTaskHandle_success( void )
{
    TaskHandle_t ret_get_timer_handle;

    /* Setup */
    create_timer_task();
    /* Expectations */
    /* API Call */
    ret_get_timer_handle = xTimerGetTimerDaemonTaskHandle();
    /* Validations */
    TEST_ASSERT_NOT_NULL( ret_get_timer_handle );
}

/*!
 * @brief success testcase, getter for the timer period in ticks
 *        expects a similar value to the one created
 */
void test_xTimerGetPeriod_success( void )
{
    TickType_t ret_get_period;
    TimerHandle_t xTimer;

    /* Setup */
    xTimer = create_timer();
    /* Expectations */
    /* API Call */
    ret_get_period = xTimerGetPeriod( xTimer );
    /* Validations */
    TEST_ASSERT_EQUAL( DEFAULT_TIMER_PERIOD, ret_get_period );
}

/*!
 * @brief success testcase, set and test timer reload mode
 */
void test_vTimer_Set_Get_ReloadMode_success( void )
{
    TimerHandle_t xTimer;
    UBaseType_t reload_mode;

    /* Setup */
    xTimer = create_timer();
    /* Expectations */
    /* API Call */
    vTimerSetReloadMode( xTimer, pdTRUE );
    reload_mode = uxTimerGetReloadMode( xTimer );
    /* Validations */
    TEST_ASSERT_TRUE( ( xTimer->ucStatus & tmrSTATUS_IS_AUTORELOAD ) );
    TEST_ASSERT_TRUE( reload_mode );

    /* API Call */
    vTimerSetReloadMode( xTimer, pdFALSE );
    reload_mode = uxTimerGetReloadMode( xTimer );
    /* Validations */
    TEST_ASSERT_FALSE( xTimer->ucStatus & tmrSTATUS_IS_AUTORELOAD );
    TEST_ASSERT_FALSE( reload_mode );
}

/*!
 * @brief success testcase, get timer expiry time
 */
void test_xTimerGetExpiryTime( void )
{
    TickType_t ret_timer_expiry;
    TimerHandle_t xTimer;

    /* Setup */
    xTimer = create_timer();
    /* Expectations */
    listGET_LIST_ITEM_VALUE_ExpectAnyArgsAndReturn( 35 );
    /* API Call */
    ret_timer_expiry = xTimerGetExpiryTime( xTimer );
    /* Validations */
    TEST_ASSERT_EQUAL( 35, ret_timer_expiry );
}

/*!
 * @brief success testcase, get and test the default timer name
 */
void test_pcTimerGetName( void )
{
    TimerHandle_t xTimer;
    const char * ret_timer_name;

    /* Setup */
    xTimer = create_timer();
    /* Expectations */
    /* API Call */
    ret_timer_name = pcTimerGetName( xTimer );
    /* Validations */
    TEST_ASSERT_EQUAL_STRING( DEFAULT_TIMER_NAME, ret_timer_name );
}

/*!
 * @brief success testcase, get timer status and test if it is active
 */
void test_xTimerIsTimerActive_true( void )
{
    BaseType_t ret_is_timer_active;

    TimerHandle_t xTimer;

    /* Setup */
    xTimer = create_timer();
    xTimer->ucStatus |= tmrSTATUS_IS_ACTIVE;
    /* Expectations */
    /* API Call */
    ret_is_timer_active = xTimerIsTimerActive( xTimer );
    /* Validations */
    TEST_ASSERT_TRUE( ret_is_timer_active );
}

/*!
 * @brief success testcase, get timer status and test if it is active
 *        expects the timer not to be active by default
 */
void test_xTimerIsTimerActive_false( void )
{
    BaseType_t ret_is_timer_active;
    TimerHandle_t xTimer;

    /* Setup */
    xTimer = create_timer();
    /* Expectations */
    /* API Call */
    ret_is_timer_active = xTimerIsTimerActive( xTimer );
    /* Validations */
    TEST_ASSERT_FALSE( ret_is_timer_active );
}

/*!
 * @brief success testcase, set timer ID then tests if it was set properly
 */
void test_vTimerSetTimerID( void )
{
    TimerHandle_t xTimer;
    UBaseType_t pvNewID = 45;
    UBaseType_t * saved_pvNewID;

    /* Setup */
    xTimer = create_timer();
    /* Expectations */
    /* API Call */
    vTimerSetTimerID( xTimer, ( void * ) &pvNewID );
    /* Validations */
    TEST_ASSERT_EQUAL( pvNewID, ( *( UBaseType_t * ) xTimer->pvTimerID ) );

    saved_pvNewID = pvTimerGetTimerID( xTimer );
    TEST_ASSERT_EQUAL( pvNewID, *saved_pvNewID );
}

/*!
 * @brief success testcase, sets a pended function call
 */
void test_xTimerPendFunctionCall_success( void )
{
    BaseType_t ret_timer_pend;
    UBaseType_t pvParameter1 = 0xb0b0b0;
    uint32_t ulParameter2 = 0xa0a0a0;

    /* Setup */
    /* Expectations */
    xQueueGenericSend_ExpectAnyArgsAndReturn( pdTRUE );
    /* API Call */
    ret_timer_pend = xTimerPendFunctionCall( pended_function,
                                             ( void * ) &pvParameter1,
                                             ulParameter2,
                                             500 );
    /* Validations */
    TEST_ASSERT_EQUAL( pdTRUE, ret_timer_pend );
}

/*!
 * @brief success testcase, sets a pended function call from ISR
 */
void test_xTimerPendFunctionCallFromISR_success( void )
{
    BaseType_t ret_timer_pend;
    UBaseType_t pvParameter1 = 0xb0b0b0;
    uint32_t ulParameter2 = 0xa0a0a0;
    BaseType_t xHigherPriorityTaskWoken = pdFALSE;

    /* Setup */
    /* Expectations */
    xQueueGenericSendFromISR_ExpectAnyArgsAndReturn( pdTRUE );
    /* API Call */
    ret_timer_pend = xTimerPendFunctionCallFromISR( pended_function,
                                                    ( void * ) &pvParameter1,
                                                    ulParameter2,
                                                    &xHigherPriorityTaskWoken );
    /* Validations */
    TEST_ASSERT_EQUAL( pdTRUE, ret_timer_pend );
}

/*!
 * @brief success testcase, expired timer is calling the callback
 */
void test_timer_function_expired_callback( void )
{
    Timer_t xTimer = { 0 };
    pthread_t thread_id;
    int * retVal;

    /* Setup */
    end_1_timer = 1; /* exit right from the first expired timer callback */
    xTimer.ucStatus = tmrSTATUS_IS_ACTIVE;
    xTimer.xTimerPeriodInTicks = 0;
    xTimer.pxCallbackFunction = xCallback_Test_1_end;
    /* Expectations */
    /* prvGetNextExpireTime */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    /* returns xNextExpireTime */
    listGET_ITEM_VALUE_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( 3 );
    /* prvProcessTimerOrBlockTask */
    vTaskSuspendAll_Expect();
    /* prvSampleTimeNow */

    /* returns xTimeNow > xNextExpireTime timer expired */
    xTaskGetTickCount_ExpectAndReturn( saved_last_time + 500 ); /* time now / static last_time = 0 */
    saved_last_time += 500;
    /* back to prvProcessTimerOrBlockTask */
    xTaskResumeAll_ExpectAndReturn( pdTRUE );
    /* prvProcessExpiredTimer */
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( &xTimer );
    uxListRemove_ExpectAndReturn( &xTimer.xTimerListItem, pdTRUE );

    /* API Call */
    pthread_create( &thread_id, NULL, &timer_thread_function, NULL );
    pthread_join( thread_id, ( void ** ) &retVal );
    /* Validations */
    TEST_ASSERT_EQUAL( 1, *retVal );
    ASSERT_XCALLBACK_TEST_1_END_CALLED();
}

/*!
 * @brief success testcase, port yields when no context switch happens because of
 *        resuming the scheduler
 */
void test_timer_function_success3( void )
{
    pthread_t thread_id;
    int * retVal;

    /* Setup */
    /* Expectations */
    /* prvGetNextExpireTime */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    /*listGET_ITEM_VALUE_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( 3 ); */
    /* prvProcessTimerOrBlockTask */
    vTaskSuspendAll_Expect();
    /* prvSampleTimeNow */
    xTaskGetTickCount_ExpectAndReturn( saved_last_time + 500 ); /* time now / static last_time = 0 */
    saved_last_time += 500;
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    /* back to prvProcessTimerOrBlockTask */
    vQueueWaitForMessageRestricted_ExpectAnyArgs();
    xTaskResumeAll_ExpectAndReturn( pdFALSE ); /* no context switch.. yield */
    /* yield called */
    vTaskYieldWithinAPI_Stub( vTaskYieldWithinAPI_Callback );

    /* API Call */
    pthread_create( &thread_id, NULL, &timer_thread_function, NULL );
    pthread_join( thread_id, ( void ** ) &retVal );
    /* Validations */
    ASSERT_PORT_YIELD_WITHIN_API_CALLED();
}

/*!
 * @brief success testcase,  timer callback called
 */
void test_timer_function_success4( void )
{
    Timer_t xTimer = { 0 };
    pthread_t thread_id;
    int * retVal;
    CallbackParameters_t callback_param;

    /* Setup */
    callback_param.pxCallbackFunction = &pended_function_4_end;
    callback_param.pvParameter1 = NULL;
    callback_param.ulParameter2 = 0xa9a9a9a9;
    end_1_timer = 2;
    DaemonTaskMessage_t xMessage;
    xMessage.xMessageID = tmrCOMMAND_START;
    xMessage.u.xCallbackParameters = callback_param;
    xMessage.u.xTimerParameters.pxTimer = &xTimer;
    xMessage.u.xTimerParameters.xMessageValue = saved_last_time + 300;

    xTimer.xTimerPeriodInTicks = 20;
    xTimer.pxCallbackFunction = xCallback_Test_1_end;
    xTimer.ucStatus |= tmrSTATUS_IS_AUTORELOAD;
    /* Expectations */
    /* prvGetNextExpireTime */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    /*listGET_ITEM_VALUE_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( 3 ); */
    /* prvProcessTimerOrBlockTask */
    vTaskSuspendAll_Expect();
    /* prvSampleTimeNow */
    xTaskGetTickCount_ExpectAndReturn( saved_last_time + 500 ); /* time now / static last_time = 0 */
    saved_last_time += 500;
    /* back to prvProcessTimerOrBlockTask */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    vQueueWaitForMessageRestricted_ExpectAnyArgs();
    xTaskResumeAll_ExpectAndReturn( pdTRUE );
    /* yield called */
    /* prvProcessReceivedCommands */
    xQueueReceive_ExpectAndReturn( NULL, NULL, tmrNO_DELAY, pdPASS );
    xQueueReceive_IgnoreArg_xQueue();
    xQueueReceive_IgnoreArg_pvBuffer();
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xMessage,
                                             sizeof( DaemonTaskMessage_t ) );
    listIS_CONTAINED_WITHIN_ExpectAnyArgsAndReturn( pdFALSE );
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    /*   prvSampleTimeNow*/
    xTaskGetTickCount_ExpectAndReturn( saved_last_time - 50 ); /* time now / static last_time = 0 */
    saved_last_time -= 50;
    /*     prvSwitchTimerLists */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_ITEM_VALUE_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( 50 );
    /*       prvProcessExpiredTimer */
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( &xTimer );
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    /* callback called from prvProcessExpiredTimer*/
    /* back to prvProcessReceivedCommands from prvSampleTimeNow*/
    /*   prvInsertTimerInActiveList */
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();
    /* back to prvProcessReceivedCommands  */
    /* prvReloadTimer */
    /*   prvInsertTimerInActiveList */
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();
    /* API Call */
    pthread_create( &thread_id, NULL, &timer_thread_function, NULL );
    pthread_join( thread_id, ( void ** ) &retVal );
    /* Validations */
    TEST_ASSERT_EQUAL( 1, *retVal );
    ASSERT_APPLICATION_DAEMON_STARTUP_HOOK_CALLED();
    ASSERT_XCALLBACK_TEST_1_END_CALLED();
}

void test_timer_function_success5( void )
{
    Timer_t xTimer = { 0 };
    pthread_t thread_id;
    int * retVal;
    CallbackParameters_t callback_param;

    /* Setup */
    callback_param.pxCallbackFunction = &pended_function_4_end;
    callback_param.pvParameter1 = NULL;
    callback_param.ulParameter2 = 0xa9a9a9a9;
    end_1_timer = 2;



    DaemonTaskMessage_t xMessage;
    xMessage.xMessageID = tmrCOMMAND_START;
    xMessage.u.xCallbackParameters = callback_param;
    xMessage.u.xTimerParameters.pxTimer = &xTimer;



    end_4_timer = 10;
    DaemonTaskMessage_t xMessage2;
    xMessage2.xMessageID = tmrCOMMAND_EXECUTE_CALLBACK_FROM_ISR;
    xMessage2.u.xCallbackParameters = callback_param;
    xMessage2.u.xTimerParameters.pxTimer = &xTimer;
    xTimer.ucStatus |= tmrSTATUS_IS_AUTORELOAD;
    xTimer.xTimerPeriodInTicks = 0;
    xTimer.pxCallbackFunction = xCallback_Test_1_end;
    /* Expectations */
    /* prvGetNextExpireTime */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    /*listGET_ITEM_VALUE_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( 3 ); */
    /* prvProcessTimerOrBlockTask */
    vTaskSuspendAll_Expect();
    /* prvSampleTimeNow */
    xTaskGetTickCount_ExpectAndReturn( saved_last_time + 500 ); /* time now / static last_time = 0 */
    saved_last_time += 500;
    /* prvSwitchTimerLists */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    /* back to prvProcessTimerOrBlockTask */
    vQueueWaitForMessageRestricted_ExpectAnyArgs();
    xTaskResumeAll_ExpectAndReturn( pdTRUE );
    /* yield called */
    /* prvProcessReceivedCommands */
    xQueueReceive_ExpectAndReturn( NULL, NULL, tmrNO_DELAY, pdPASS );
    xQueueReceive_IgnoreArg_xQueue();
    xQueueReceive_IgnoreArg_pvBuffer();
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xMessage2,
                                             sizeof( DaemonTaskMessage_t ) );



    xQueueReceive_ExpectAndReturn( NULL, NULL, tmrNO_DELAY, pdPASS );
    xQueueReceive_IgnoreArg_xQueue();
    xQueueReceive_IgnoreArg_pvBuffer();
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xMessage,
                                             sizeof( DaemonTaskMessage_t ) );

    listIS_CONTAINED_WITHIN_ExpectAnyArgsAndReturn( pdFALSE );
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    /* prvSampleTimeNow*/
    xTaskGetTickCount_ExpectAndReturn( saved_last_time - 50 ); /* time now / static last_time = 0 */
    saved_last_time -= 50;
    /* prvSwitchTimerLists */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    /*  prvInsertTimerInActiveList */
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();
    /* back to prvProcessReceivedCommands  */
    /*   prvReloadTimer */
    /*     prvInsertTimerInActiveList */
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();
    /* back to prvProcessReceivedCommands  */
    /*   prvReloadTimer */
    /*     prvInsertTimerInActiveList */
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();
    /* back to prvProcessReceivedCommands  */
    /* callback called ending the test */
    /* xQueueReceive_AddCallback(end_queue_receive); */

    /* API Call */
    pthread_create( &thread_id, NULL, &timer_thread_function, NULL );
    pthread_join( thread_id, ( void ** ) &retVal );
    /* Validations */
    TEST_ASSERT_FALSE( port_yield_within_api_called );
    ASSERT_PENDED_FUNCTION_4_END_CALLED();
}

void test_timer_function_success6( void )
{
    Timer_t xTimer = { 0 };
    pthread_t thread_id;
    int * retVal;
    CallbackParameters_t callback_param;

    /* Setup */
    callback_param.pxCallbackFunction = &pended_function_4_end;
    callback_param.pvParameter1 = NULL;
    callback_param.ulParameter2 = 0xa9a9a9a9;
    end_1_timer = 2;
    DaemonTaskMessage_t xMessage;
    xMessage.xMessageID = tmrCOMMAND_START;
    xMessage.u.xCallbackParameters = callback_param;
    xMessage.u.xTimerParameters.pxTimer = &xTimer;
    xTimer.ucStatus = 0;
    xTimer.xTimerPeriodInTicks = 0;
    xTimer.pxCallbackFunction = xCallback_Test_1_end;
    /* Expectations */
    /* prvGetNextExpireTime */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    /*listGET_ITEM_VALUE_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( 3 ); */
    /* prvProcessTimerOrBlockTask */
    vTaskSuspendAll_Expect();
    /* prvSampleTimeNow */
    xTaskGetTickCount_ExpectAndReturn( saved_last_time + 500 ); /* time now / static last_time = 0 */
    saved_last_time += 500;
    /* prvSwitchTimerLists */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    /* back to prvProcessTimerOrBlockTask */
    vQueueWaitForMessageRestricted_ExpectAnyArgs();
    xTaskResumeAll_ExpectAndReturn( pdTRUE );
    /* yield called */
    /* prvProcessReceivedCommands */
    xQueueReceive_ExpectAndReturn( NULL, NULL, tmrNO_DELAY, pdPASS );
    xQueueReceive_IgnoreArg_xQueue();
    xQueueReceive_IgnoreArg_pvBuffer();
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xMessage,
                                             sizeof( DaemonTaskMessage_t ) );
    listIS_CONTAINED_WITHIN_ExpectAnyArgsAndReturn( pdFALSE );
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    /* prvSampleTimeNow*/
    xTaskGetTickCount_ExpectAndReturn( saved_last_time - 50 ); /* time now / static last_time = 0 */
    saved_last_time -= 50;
    /* prvSwitchTimerLists */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    /* prvInsertTimerInActiveList */
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();
    /* prvProcessReceivedCommands */
    xQueueReceive_ExpectAnyArgsAndReturn( pdFAIL );
    /* back prvTimerTask */
    /* prvGetNextExpireTime */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_ITEM_VALUE_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( saved_last_time + 1 );
    /* prvProcessTimerOrBlockTask */
    vTaskSuspendAll_Expect();
    /* prvSampleTimeNow */
    xTaskGetTickCount_ExpectAndReturn( saved_last_time - 5 ); /* time now / static last_time = 0 */
    saved_last_time -= 5;
    /* prvSwitchTimerLists */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    /* back prvProcessTimerOrBlockTask */
    xTaskResumeAll_ExpectAndReturn( pdFALSE );
    /* prvProcessReceivedCommands */
    xQueueReceive_ExpectAndReturn( NULL, NULL, tmrNO_DELAY, pdPASS );
    xQueueReceive_IgnoreArg_xQueue();
    xQueueReceive_IgnoreArg_pvBuffer();
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xMessage,
                                             sizeof( DaemonTaskMessage_t ) );
    listIS_CONTAINED_WITHIN_ExpectAnyArgsAndReturn( pdTRUE );
    /* prvInsertTimerInActiveList */
    xTaskGetTickCount_ExpectAndReturn( saved_last_time - 50 ); /* time now / static last_time = 0 */
    saved_last_time -= 50;
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    /* prvInsertTimerInActiveList */
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();

    /* API Call */
    pthread_create( &thread_id, NULL, &timer_thread_function, NULL );
    pthread_join( thread_id, ( void ** ) &retVal );
    /* Validations */
    TEST_ASSERT_EQUAL( 1, *retVal );
}

void test_timer_function_success2( void )
{
    Timer_t xTimer = { 0 };
    pthread_t thread_id;
    int * retVal;
    DaemonTaskMessage_t xMessage;
    CallbackParameters_t callback_param;

    end_4_timer = 1;

    /* Setup */
    xTimer.ucStatus |= tmrSTATUS_IS_AUTORELOAD;
    xTimer.xTimerPeriodInTicks = UINT32_MAX;
    xTimer.pxCallbackFunction = xCallback_Test;

    callback_param.pxCallbackFunction = &pended_function_4_end;
    callback_param.pvParameter1 = NULL;
    callback_param.ulParameter2 = 0xa9a9a9a9;
    xMessage.xMessageID = -1;
    xMessage.u.xCallbackParameters = callback_param;
    /* Expectations */
    /* prvGetNextExpireTime */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_ITEM_VALUE_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( 3 );
    /* prvProcessTimerOrBlockTask */
    vTaskSuspendAll_Expect();
    /* prvSampleTimeNow */
    xTaskGetTickCount_ExpectAndReturn( saved_last_time + 500 ); /* time now / static last_time = 0 */
    saved_last_time += 500;
    /* back to prvProcessTimerOrBlockTask */
    xTaskResumeAll_ExpectAndReturn( pdTRUE );
    /* prvProcessExpiredTimer */
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( &xTimer );
    uxListRemove_ExpectAndReturn( &xTimer.xTimerListItem, pdTRUE );
    /* prvInsertTimerInActiveList */
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();
    vListInsert_ExpectAnyArgs();
    /* prvProcessReceivedCommands */
    xQueueReceive_ExpectAndReturn( NULL, NULL, tmrNO_DELAY, pdPASS );
    xQueueReceive_IgnoreArg_xQueue();
    xQueueReceive_IgnoreArg_pvBuffer();
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xMessage, sizeof( DaemonTaskMessage_t ) );

    /* API Call */
    pthread_create( &thread_id, NULL, &timer_thread_function, NULL );
    pthread_join( thread_id, ( void ** ) &retVal );
    /*prvTimerTask(pvParameters); */
    /* Validations */
    TEST_ASSERT_EQUAL( 4, *retVal );
    ASSERT_XCALLBACK_TEST_CALLED();
}
void test_timer_function_success3_command_start( void )
{
    Timer_t xTimer = { 0 };
    pthread_t thread_id;
    int * retVal;

    end_2_timer = 2;

    /* Setup */
    xTimer.ucStatus |= tmrSTATUS_IS_AUTORELOAD;
    xTimer.pxCallbackFunction = xCallback_Test_2_end;
    xTimer.xTimerPeriodInTicks = 0;

    /* Expectations */
    /* prvGetNextExpireTime */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_ITEM_VALUE_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( 3 );
    /* prvProcessTimerOrBlockTask */
    vTaskSuspendAll_Expect();
    /* prvSampleTimeNow */
    xTaskGetTickCount_ExpectAndReturn( saved_last_time + 100 ); /* time now / static last_time = 0 */
    saved_last_time += 100;
    /* back to prvProcessTimerOrBlockTask */
    xTaskResumeAll_ExpectAndReturn( pdTRUE );
    /* prvProcessExpiredTimer */
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( &xTimer );
    uxListRemove_ExpectAndReturn( &xTimer.xTimerListItem, pdTRUE );
    /* prvInsertTimerInActiveList */
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();
    /* prvProcessReceivedCommands */
    saved_last_time -= 50;

    /* API Call */
    pthread_create( &thread_id, NULL, &timer_thread_function, NULL );
    pthread_join( thread_id, ( void ** ) &retVal );
    /* Validations */
    TEST_ASSERT_EQUAL( 2, *retVal );
}

void test_timer_function_success3_command_start2( void )
{
    Timer_t xTimer = { 0 };
    pthread_t thread_id;
    int * retVal;

    end_2_timer = 2;

    /* Setup */
    xTimer.ucStatus |= tmrSTATUS_IS_AUTORELOAD;
    xTimer.pxCallbackFunction = xCallback_Test_2_end;
    xTimer.xTimerPeriodInTicks = 0;

    /* Expectations */
    /* prvGetNextExpireTime */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_ITEM_VALUE_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( 3 );
    /* prvProcessTimerOrBlockTask */
    vTaskSuspendAll_Expect();
    /* prvSampleTimeNow */
    xTaskGetTickCount_ExpectAndReturn( saved_last_time + 100 ); /* time now / static last_time = 0 */
    saved_last_time += 100;
    /* back to prvProcessTimerOrBlockTask */
    xTaskResumeAll_ExpectAndReturn( pdTRUE );
    /* prvProcessExpiredTimer */
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( &xTimer );
    uxListRemove_ExpectAndReturn( &xTimer.xTimerListItem, pdTRUE );
    /* prvInsertTimerInActiveList */
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();
    /* prvProcessReceivedCommands */
    saved_last_time -= 50;

    /* API Call */
    pthread_create( &thread_id, NULL, &timer_thread_function, NULL );
    pthread_join( thread_id, ( void ** ) &retVal );
    /* Validations */
    TEST_ASSERT_EQUAL( 2, *retVal );
}

void test_timer_function_success3_command_start3( void )
{
    Timer_t xTimer = { 0 };
    pthread_t thread_id;
    int * retVal;

    end_2_timer = 3;

    /* Setup */
    xTimer.ucStatus |= tmrSTATUS_IS_AUTORELOAD;
    xTimer.pxCallbackFunction = xCallback_Test_2_end;
    xTimer.xTimerPeriodInTicks = 0;

    /* Expectations */
    /* prvGetNextExpireTime */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_ITEM_VALUE_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( 3 );
    /* prvProcessTimerOrBlockTask */
    vTaskSuspendAll_Expect();
    /* prvSampleTimeNow */
    xTaskGetTickCount_ExpectAndReturn( saved_last_time + 100 ); /* time now / static last_time = 0 */
    saved_last_time += 100;
    /* back to prvProcessTimerOrBlockTask */
    xTaskResumeAll_ExpectAndReturn( pdTRUE );
    /* prvProcessExpiredTimer */
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( &xTimer );
    uxListRemove_ExpectAndReturn( &xTimer.xTimerListItem, pdTRUE );
    /* prvInsertTimerInActiveList */
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();
    saved_last_time -= 50;

    /* API Call */
    pthread_create( &thread_id, NULL, &timer_thread_function, NULL );
    pthread_join( thread_id, ( void ** ) &retVal );
    /* Validations */
    TEST_ASSERT_EQUAL( 2, *retVal );
}

void test_timer_function_success3_command_start4( void )
{
    Timer_t xTimer = { 0 };
    pthread_t thread_id;
    int * retVal;
    DaemonTaskMessage_t xMessage;
    CallbackParameters_t callback_param;

    end_2_timer = 3;

    /* Setup */
    xTimer.ucStatus &= ~tmrSTATUS_IS_AUTORELOAD;
    xTimer.pxCallbackFunction = xCallback_Test_2_end;
    xTimer.xTimerPeriodInTicks = 0;

    callback_param.pxCallbackFunction = &pended_function_4_end;
    callback_param.pvParameter1 = NULL;
    callback_param.ulParameter2 = 0xa9a9a9a9;
    xMessage.xMessageID = tmrCOMMAND_START;
    xMessage.u.xCallbackParameters = callback_param;
    xMessage.u.xTimerParameters.pxTimer = &xTimer;
    /* Expectations */
    /* prvGetNextExpireTime */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_ITEM_VALUE_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( 3 );
    /* prvProcessTimerOrBlockTask */
    vTaskSuspendAll_Expect();
    /* prvSampleTimeNow */
    xTaskGetTickCount_ExpectAndReturn( saved_last_time + 100 ); /* time now / static last_time = 0 */
    saved_last_time += 100;
    /* back to prvProcessTimerOrBlockTask */
    xTaskResumeAll_ExpectAndReturn( pdTRUE );
    /* prvProcessExpiredTimer */
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( &xTimer );
    uxListRemove_ExpectAndReturn( &xTimer.xTimerListItem, pdTRUE );
    /* prvInsertTimerInActiveList */
    /*listSET_LIST_ITEM_VALUE_ExpectAnyArgs(); */
    /* prvProcessReceivedCommands */
    xQueueReceive_ExpectAndReturn( NULL, NULL, tmrNO_DELAY, pdPASS );
    xQueueReceive_IgnoreArg_xQueue();
    xQueueReceive_IgnoreArg_pvBuffer();
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xMessage, sizeof( DaemonTaskMessage_t ) );
    listIS_CONTAINED_WITHIN_ExpectAnyArgsAndReturn( pdFALSE );
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    /* prvSampleTimeNow*/
    xTaskGetTickCount_ExpectAndReturn( saved_last_time - 50 ); /* time now / static last_time = 0 */
    saved_last_time -= 50;
    /* prvSwitchTimerLists */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_ITEM_VALUE_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( 600 );
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( &xTimer );
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    /* prvInsertTimerInActiveList */
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();

    /* API Call */
    pthread_create( &thread_id, NULL, &timer_thread_function, NULL );
    pthread_join( thread_id, ( void ** ) &retVal );
    /* Validations */
    TEST_ASSERT_EQUAL( 2, *retVal );
}

void test_timer_function_success3_command_start5( void )
{
    Timer_t xTimer = { 0 };
    Timer_t xTimer2 = { 0 };
    pthread_t thread_id;
    int * retVal;

    DaemonTaskMessage_t xMessage;
    DaemonTaskMessage_t xMessage2;
    CallbackParameters_t callback_param;

    end_2_timer = 2;
    end_4_timer = 1;

    /* Setup */
    xTimer.ucStatus |= tmrSTATUS_IS_AUTORELOAD;
    xTimer.pxCallbackFunction = xCallback_Test_2_end;
    xTimer.xTimerPeriodInTicks = UINT32_MAX;

    xTimer2.ucStatus |= tmrSTATUS_IS_AUTORELOAD;
    xTimer2.pxCallbackFunction = xCallback_Test_2_end;
    xTimer2.xTimerPeriodInTicks = saved_last_time + 50;

    callback_param.pxCallbackFunction = &pended_function_4_end;
    callback_param.pvParameter1 = NULL;
    callback_param.ulParameter2 = 0xa9a9a9a9;

    xMessage.xMessageID = tmrCOMMAND_START;
    xMessage.u.xCallbackParameters = callback_param;
    xMessage.u.xTimerParameters.pxTimer = &xTimer;
    xMessage.u.xTimerParameters.xMessageValue = saved_last_time - 500;

    xMessage2.xMessageID = tmrCOMMAND_EXECUTE_CALLBACK;
    xMessage2.u.xCallbackParameters = callback_param;
    /* Expectations */
    /* prvGetNextExpireTime */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_ITEM_VALUE_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( 3 );
    /* prvProcessTimerOrBlockTask */
    vTaskSuspendAll_Expect();
    /* prvSampleTimeNow */
    xTaskGetTickCount_ExpectAndReturn( saved_last_time + 1000 ); /* time now / static last_time = 0 */
    saved_last_time += 1000;
    /* back to prvProcessTimerOrBlockTask */
    xTaskResumeAll_ExpectAndReturn( pdTRUE );
    /* prvProcessExpiredTimer */
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( &xTimer );
    uxListRemove_ExpectAndReturn( &xTimer.xTimerListItem, pdTRUE );
    /* prvInsertTimerInActiveList */
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();
    vListInsert_ExpectAnyArgs();
    /* prvProcessReceivedCommands */
    xQueueReceive_ExpectAndReturn( NULL, NULL, tmrNO_DELAY, pdPASS );
    xQueueReceive_IgnoreArg_xQueue();
    xQueueReceive_IgnoreArg_pvBuffer();
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xMessage, sizeof( DaemonTaskMessage_t ) );
    listIS_CONTAINED_WITHIN_ExpectAnyArgsAndReturn( pdFALSE );
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    /* prvSampleTimeNow*/
    xTaskGetTickCount_ExpectAndReturn( saved_last_time + 5000 ); /* time now / static last_time = 0 */
    saved_last_time += 5000;
    /* prvInsertTimerInActiveList */
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();
    vListInsert_ExpectAnyArgs();
    /* back to prvProcessReceivedCommands */
    xQueueReceive_ExpectAndReturn( NULL, NULL, tmrNO_DELAY, pdPASS );
    xQueueReceive_IgnoreArg_xQueue();
    xQueueReceive_IgnoreArg_pvBuffer();
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xMessage2, sizeof( DaemonTaskMessage_t ) );
    /* API Call */
    pthread_create( &thread_id, NULL, &timer_thread_function, NULL );
    pthread_join( thread_id, ( void ** ) &retVal );
    /* Validations */
    TEST_ASSERT_EQUAL( 4, *retVal );
}

void test_timer_function_success3_command_stop( void )
{
    Timer_t xTimer = { 0 };
    Timer_t xTimer2 = { 0 };
    pthread_t thread_id;
    int * retVal;

    DaemonTaskMessage_t xMessage;
    DaemonTaskMessage_t xMessage2;
    CallbackParameters_t callback_param;

    end_2_timer = 2;
    end_4_timer = 1;

    /* Setup */
    xTimer.ucStatus |= tmrSTATUS_IS_AUTORELOAD;
    xTimer.ucStatus |= tmrSTATUS_IS_ACTIVE;
    xTimer.pxCallbackFunction = xCallback_Test_2_end;
    xTimer.xTimerPeriodInTicks = UINT32_MAX;

    xTimer2.ucStatus |= tmrSTATUS_IS_AUTORELOAD;
    xTimer2.pxCallbackFunction = xCallback_Test_2_end;
    xTimer2.xTimerPeriodInTicks = saved_last_time + 50;

    callback_param.pxCallbackFunction = &pended_function_4_end;
    callback_param.pvParameter1 = NULL;
    callback_param.ulParameter2 = 0xa9a9a9a9;

    xMessage.xMessageID = tmrCOMMAND_STOP;
    xMessage.u.xCallbackParameters = callback_param;
    xMessage.u.xTimerParameters.pxTimer = &xTimer;
    xMessage.u.xTimerParameters.xMessageValue = saved_last_time - 500;

    xMessage2.xMessageID = tmrCOMMAND_EXECUTE_CALLBACK; /* used to end the loop */
    xMessage2.u.xCallbackParameters = callback_param;
    /* Expectations */
    /* prvGetNextExpireTime */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_ITEM_VALUE_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( 3 );
    /* prvProcessTimerOrBlockTask */
    vTaskSuspendAll_Expect();
    /* prvSampleTimeNow */
    xTaskGetTickCount_ExpectAndReturn( saved_last_time + 1000 ); /* time now / static last_time = 0 */
    saved_last_time += 1000;
    /* back to prvProcessTimerOrBlockTask */
    xTaskResumeAll_ExpectAndReturn( pdTRUE );
    /* prvProcessExpiredTimer */
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( &xTimer );
    uxListRemove_ExpectAndReturn( &xTimer.xTimerListItem, pdTRUE );
    /* prvInsertTimerInActiveList */
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();
    vListInsert_ExpectAnyArgs();
    /* prvProcessReceivedCommands */
    xQueueReceive_ExpectAndReturn( NULL, NULL, tmrNO_DELAY, pdPASS );
    xQueueReceive_IgnoreArg_xQueue();
    xQueueReceive_IgnoreArg_pvBuffer();
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xMessage, sizeof( DaemonTaskMessage_t ) );
    listIS_CONTAINED_WITHIN_ExpectAnyArgsAndReturn( pdFALSE );
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    /* prvSampleTimeNow*/
    xTaskGetTickCount_ExpectAndReturn( saved_last_time + 5000 ); /* time now / static last_time = 0 */
    saved_last_time += 5000;
    /* back to prvProcessReceivedCommands */
    xQueueReceive_ExpectAndReturn( NULL, NULL, tmrNO_DELAY, pdPASS );
    xQueueReceive_IgnoreArg_xQueue();
    xQueueReceive_IgnoreArg_pvBuffer();
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xMessage2, sizeof( DaemonTaskMessage_t ) );
    /* API Call */
    pthread_create( &thread_id, NULL, &timer_thread_function, NULL );
    pthread_join( thread_id, ( void ** ) &retVal );
    /* Validations */
    TEST_ASSERT_EQUAL( 4, *retVal );
    TEST_ASSERT_FALSE( xTimer.ucStatus & tmrSTATUS_IS_ACTIVE );
}

void test_timer_function_success3_command_change_period( void )
{
    Timer_t xTimer = { 0 };
    Timer_t xTimer2 = { 0 };
    pthread_t thread_id;
    int * retVal;

    DaemonTaskMessage_t xMessage;
    DaemonTaskMessage_t xMessage2;
    CallbackParameters_t callback_param;

    end_2_timer = 2;
    end_4_timer = 1;

    /* Setup */
    xTimer.ucStatus |= tmrSTATUS_IS_AUTORELOAD;
    xTimer.ucStatus &= ~tmrSTATUS_IS_ACTIVE;
    xTimer.pxCallbackFunction = xCallback_Test_2_end;
    xTimer.xTimerPeriodInTicks = UINT32_MAX;

    xTimer2.ucStatus |= tmrSTATUS_IS_AUTORELOAD;
    xTimer2.pxCallbackFunction = xCallback_Test_2_end;
    xTimer2.xTimerPeriodInTicks = saved_last_time;

    callback_param.pxCallbackFunction = &pended_function_4_end;
    callback_param.pvParameter1 = NULL;
    callback_param.ulParameter2 = 0xa9a9a9a9;

    xMessage.xMessageID = tmrCOMMAND_CHANGE_PERIOD;
    xMessage.u.xCallbackParameters = callback_param;
    xMessage.u.xTimerParameters.pxTimer = &xTimer;
    xMessage.u.xTimerParameters.xMessageValue = saved_last_time;

    xMessage2.xMessageID = tmrCOMMAND_EXECUTE_CALLBACK; /* used to end the loop */
    xMessage2.u.xCallbackParameters = callback_param;
    /* Expectations */
    /* prvGetNextExpireTime */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_ITEM_VALUE_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( 3 );
    /* prvProcessTimerOrBlockTask */
    vTaskSuspendAll_Expect();
    /* prvSampleTimeNow */
    xTaskGetTickCount_ExpectAndReturn( saved_last_time ); /* time now / static last_time = 0 */
    /* back to prvProcessTimerOrBlockTask */
    xTaskResumeAll_ExpectAndReturn( pdTRUE );
    /* prvProcessExpiredTimer */
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( &xTimer );
    uxListRemove_ExpectAndReturn( &xTimer.xTimerListItem, pdTRUE );
    /* prvInsertTimerInActiveList */
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();
    vListInsert_ExpectAnyArgs();
    /* prvProcessReceivedCommands */
    xQueueReceive_ExpectAndReturn( NULL, NULL, tmrNO_DELAY, pdPASS );
    xQueueReceive_IgnoreArg_xQueue();
    xQueueReceive_IgnoreArg_pvBuffer();
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xMessage, sizeof( DaemonTaskMessage_t ) );
    listIS_CONTAINED_WITHIN_ExpectAnyArgsAndReturn( pdFALSE );
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    /* prvSampleTimeNow*/
    xTaskGetTickCount_ExpectAndReturn( saved_last_time ); /* time now / static last_time = 0 */
    /* prvInsertTimerInActiveList */
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();
    vListInsert_ExpectAnyArgs();
    /* back to prvProcessReceivedCommands */
    xQueueReceive_ExpectAndReturn( NULL, NULL, tmrNO_DELAY, pdPASS );
    xQueueReceive_IgnoreArg_xQueue();
    xQueueReceive_IgnoreArg_pvBuffer();
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xMessage2, sizeof( DaemonTaskMessage_t ) );
    /* API Call */
    pthread_create( &thread_id, NULL, &timer_thread_function, NULL );
    pthread_join( thread_id, ( void ** ) &retVal );
    /* Validations */
    TEST_ASSERT_EQUAL( 4, *retVal );
    TEST_ASSERT_TRUE( xTimer.ucStatus & tmrSTATUS_IS_ACTIVE );
    TEST_ASSERT_EQUAL( saved_last_time, xTimer.xTimerPeriodInTicks );
}

void test_timer_function_success3_command_delete_static( void )
{
    Timer_t xTimer = { 0 };
    Timer_t xTimer2 = { 0 };
    pthread_t thread_id;
    int * retVal;

    DaemonTaskMessage_t xMessage;
    DaemonTaskMessage_t xMessage2;
    CallbackParameters_t callback_param;

    end_2_timer = 2;
    end_4_timer = 1;

    /* Setup */
    xTimer.ucStatus |= tmrSTATUS_IS_AUTORELOAD;
    xTimer.ucStatus |= tmrSTATUS_IS_STATICALLY_ALLOCATED;
    xTimer.ucStatus &= ~tmrSTATUS_IS_ACTIVE;
    xTimer.pxCallbackFunction = xCallback_Test_2_end;
    xTimer.xTimerPeriodInTicks = UINT32_MAX;

    xTimer2.ucStatus |= tmrSTATUS_IS_AUTORELOAD;
    xTimer2.pxCallbackFunction = xCallback_Test_2_end;
    xTimer2.xTimerPeriodInTicks = saved_last_time;

    callback_param.pxCallbackFunction = &pended_function_4_end;
    callback_param.pvParameter1 = NULL;
    callback_param.ulParameter2 = 0xa9a9a9a9;

    xMessage.xMessageID = tmrCOMMAND_DELETE;
    xMessage.u.xCallbackParameters = callback_param;
    xMessage.u.xTimerParameters.pxTimer = &xTimer;
    xMessage.u.xTimerParameters.xMessageValue = saved_last_time;

    xMessage2.xMessageID = tmrCOMMAND_EXECUTE_CALLBACK; /* used to end the loop */
    xMessage2.u.xCallbackParameters = callback_param;
    /* Expectations */
    /* prvGetNextExpireTime */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_ITEM_VALUE_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( 3 );
    /* prvProcessTimerOrBlockTask */
    vTaskSuspendAll_Expect();
    /* prvSampleTimeNow */
    xTaskGetTickCount_ExpectAndReturn( saved_last_time ); /* time now / static last_time = 0 */
    /* back to prvProcessTimerOrBlockTask */
    xTaskResumeAll_ExpectAndReturn( pdTRUE );
    /* prvProcessExpiredTimer */
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( &xTimer );
    uxListRemove_ExpectAndReturn( &xTimer.xTimerListItem, pdTRUE );
    /* prvInsertTimerInActiveList */
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();
    vListInsert_ExpectAnyArgs();
    /* prvProcessReceivedCommands */
    xQueueReceive_ExpectAndReturn( NULL, NULL, tmrNO_DELAY, pdPASS );
    xQueueReceive_IgnoreArg_xQueue();
    xQueueReceive_IgnoreArg_pvBuffer();
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xMessage, sizeof( DaemonTaskMessage_t ) );
    listIS_CONTAINED_WITHIN_ExpectAnyArgsAndReturn( pdFALSE );
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    /* prvSampleTimeNow*/
    xTaskGetTickCount_ExpectAndReturn( saved_last_time ); /* time now / static last_time = 0 */
    /* back to prvProcessReceivedCommands */
    xQueueReceive_ExpectAndReturn( NULL, NULL, tmrNO_DELAY, pdPASS );
    xQueueReceive_IgnoreArg_xQueue();
    xQueueReceive_IgnoreArg_pvBuffer();
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xMessage2, sizeof( DaemonTaskMessage_t ) );
    /* API Call */
    pthread_create( &thread_id, NULL, &timer_thread_function, NULL );
    pthread_join( thread_id, ( void ** ) &retVal );
    /* Validations */
    TEST_ASSERT_EQUAL( 4, *retVal );
    TEST_ASSERT_FALSE( xTimer.ucStatus & tmrSTATUS_IS_ACTIVE );
}


void test_timer_function_success3_command_unknown( void )
{
    Timer_t xTimer = { 0 };
    Timer_t xTimer2 = { 0 };
    pthread_t thread_id;
    int * retVal;

    DaemonTaskMessage_t xMessage;
    DaemonTaskMessage_t xMessage2;
    CallbackParameters_t callback_param;

    end_2_timer = 2;
    end_4_timer = 1;

    /* Setup */
    xTimer.ucStatus |= tmrSTATUS_IS_AUTORELOAD;
    xTimer.ucStatus &= ~tmrSTATUS_IS_STATICALLY_ALLOCATED;
    xTimer.ucStatus &= ~tmrSTATUS_IS_ACTIVE;
    xTimer.pxCallbackFunction = xCallback_Test_2_end;
    xTimer.xTimerPeriodInTicks = UINT32_MAX;

    xTimer2.ucStatus |= tmrSTATUS_IS_AUTORELOAD;
    xTimer2.pxCallbackFunction = xCallback_Test_2_end;
    xTimer2.xTimerPeriodInTicks = saved_last_time;

    callback_param.pxCallbackFunction = &pended_function_4_end;
    callback_param.pvParameter1 = NULL;
    callback_param.ulParameter2 = 0xa9a9a9a9;

    xMessage.xMessageID = tmrCOMMAND_CHANGE_PERIOD_FROM_ISR + 1;
    xMessage.u.xCallbackParameters = callback_param;
    xMessage.u.xTimerParameters.pxTimer = &xTimer;
    xMessage.u.xTimerParameters.xMessageValue = saved_last_time;

    xMessage2.xMessageID = tmrCOMMAND_EXECUTE_CALLBACK; /* used to end the loop */
    xMessage2.u.xCallbackParameters = callback_param;
    /* Expectations */
    /* prvGetNextExpireTime */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_ITEM_VALUE_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( 3 );
    /* prvProcessTimerOrBlockTask */
    vTaskSuspendAll_Expect();
    /* prvSampleTimeNow */
    xTaskGetTickCount_ExpectAndReturn( saved_last_time ); /* time now / static last_time = 0 */
    /* back to prvProcessTimerOrBlockTask */
    xTaskResumeAll_ExpectAndReturn( pdTRUE );
    /* prvProcessExpiredTimer */
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( &xTimer );
    uxListRemove_ExpectAndReturn( &xTimer.xTimerListItem, pdTRUE );
    /* prvInsertTimerInActiveList */
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();
    vListInsert_ExpectAnyArgs();
    /* prvProcessReceivedCommands */
    xQueueReceive_ExpectAndReturn( NULL, NULL, tmrNO_DELAY, pdPASS );
    xQueueReceive_IgnoreArg_xQueue();
    xQueueReceive_IgnoreArg_pvBuffer();
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xMessage, sizeof( DaemonTaskMessage_t ) );
    listIS_CONTAINED_WITHIN_ExpectAnyArgsAndReturn( pdFALSE );
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    /* prvSampleTimeNow*/
    xTaskGetTickCount_ExpectAndReturn( saved_last_time ); /* time now / static last_time = 0 */
    /* back to prvProcessReceivedCommands */
    xQueueReceive_ExpectAndReturn( NULL, NULL, tmrNO_DELAY, pdPASS );
    xQueueReceive_IgnoreArg_xQueue();
    xQueueReceive_IgnoreArg_pvBuffer();
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xMessage2, sizeof( DaemonTaskMessage_t ) );
    /* API Call */
    pthread_create( &thread_id, NULL, &timer_thread_function, NULL );
    pthread_join( thread_id, ( void ** ) &retVal );
    /* Validations */
    TEST_ASSERT_EQUAL( 4, *retVal );
}

void test_timer_function_success_wrap_timer( void )
{
    Timer_t xTimer = { 0 };
    pthread_t thread_id;
    int * retVal;
    CallbackParameters_t callback_param;

    /* Setup */
    callback_param.pxCallbackFunction = &pended_function_4_end;
    callback_param.pvParameter1 = NULL;
    callback_param.ulParameter2 = 0xa9a9a9a9;
    end_1_timer = 2;
    end_4_timer = 2;
    DaemonTaskMessage_t xMessage;

    xMessage.xMessageID = tmrCOMMAND_START;
    xMessage.u.xCallbackParameters = callback_param;
    xMessage.u.xTimerParameters.pxTimer = &xTimer;
    xMessage.u.xTimerParameters.xMessageValue = saved_last_time + 600;

    xTimer.xTimerPeriodInTicks = UINT32_MAX;
    xTimer.pxCallbackFunction = xCallback_Test_1_end;
    xTimer.ucStatus |= tmrSTATUS_IS_AUTORELOAD;
    /* Expectations */
    /* prvGetNextExpireTime */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    /*listGET_ITEM_VALUE_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( 3 ); */
    /* prvProcessTimerOrBlockTask */
    vTaskSuspendAll_Expect();
    /* prvSampleTimeNow */
    xTaskGetTickCount_ExpectAndReturn( saved_last_time + 500 ); /* time now / static last_time = 0 */
    saved_last_time += 500;
    /* back to prvProcessTimerOrBlockTask */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    vQueueWaitForMessageRestricted_ExpectAnyArgs();
    xTaskResumeAll_ExpectAndReturn( pdTRUE );
    /* yield called */
    /* prvProcessReceivedCommands */
    xQueueReceive_ExpectAndReturn( NULL, NULL, tmrNO_DELAY, pdPASS );
    xQueueReceive_IgnoreArg_xQueue();
    xQueueReceive_IgnoreArg_pvBuffer();
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xMessage,
                                             sizeof( DaemonTaskMessage_t ) );
    listIS_CONTAINED_WITHIN_ExpectAnyArgsAndReturn( pdFALSE );
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );


    /* prvSampleTimeNow*/
    xTaskGetTickCount_ExpectAndReturn( saved_last_time - 50 ); /* time now / static last_time = 0 */
    saved_last_time -= 50;
    /* prvSwitchTimerLists */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_ITEM_VALUE_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( 50 );
    /* prvProcessExpiredTimer */
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( &xTimer );
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    /* prvReloadTimer */
    /* prvInsertTimerInActiveList */
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();
    vListInsert_ExpectAnyArgs();
    /* callback called in prvProcessExpiredtimer */
    /* back prvSwitchTimerLists */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    /* back prvSampleTimeNow */
    /* back prvProcessReceivedCommands */


    /* prvInsertTimerInActiveList */
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();
    vListInsert_ExpectAnyArgs();
    /* back prvProcessReceivedCommands */

    xQueueReceive_ExpectAndReturn( NULL, NULL, tmrNO_DELAY, pdPASS );
    xQueueReceive_IgnoreArg_xQueue();
    xQueueReceive_IgnoreArg_pvBuffer();
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xMessage,
                                             sizeof( DaemonTaskMessage_t ) );
    listIS_CONTAINED_WITHIN_ExpectAnyArgsAndReturn( pdFALSE );
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    /* prvSampleTimeNow */
    xTaskGetTickCount_ExpectAndReturn( saved_last_time - 50 ); /* time now / static last_time = 0 */
    saved_last_time -= 50;
    /* prvSwitchTimerLists */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_ITEM_VALUE_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( 50 );
    /* prvProcessExpiredTimer */
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( &xTimer );
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();
    vListInsert_ExpectAnyArgs();

    /* API Call */
    pthread_create( &thread_id, NULL, &timer_thread_function, NULL );
    pthread_join( thread_id, ( void ** ) &retVal );
    /* Validations */
    TEST_ASSERT_EQUAL( 1, *retVal );
}

void test_xTimerGetStaticBuffer_static( void )
{
    TimerHandle_t ret_timer_create;
    UBaseType_t pvTimerID;
    StaticTimer_t pxTimerBuffer[ sizeof( StaticTimer_t ) ];
    StaticTimer_t * pxTimerBufferRet = NULL;

    /* Setup */
    /* Expectations */
    /* prvInitialiseNewTimer */
    /* prvCheckForValidListAndQueue */
    vListInitialise_ExpectAnyArgs();
    vListInitialise_ExpectAnyArgs();
    xQueueGenericCreateStatic_ExpectAnyArgsAndReturn( NULL );
    /* Back prvInitialiseNewTimer */
    vListInitialiseItem_ExpectAnyArgs();

    /* API Call */
    ret_timer_create = xTimerCreateStatic( "ut_timer_task",
                                           pdMS_TO_TICKS( 1000 ),
                                           pdTRUE,
                                           ( void * ) &pvTimerID,
                                           xCallback_Test,
                                           pxTimerBuffer );

    TEST_ASSERT_EQUAL( pdTRUE, xTimerGetStaticBuffer( ret_timer_create, &pxTimerBufferRet ) );
    TEST_ASSERT_EQUAL( pxTimerBuffer, pxTimerBufferRet );
}

void test_xTimerGetStaticBuffer_dynamic( void )
{
    TimerHandle_t xTimer = NULL;
    UBaseType_t pvTimerID = 0;
    Timer_t pxNewTimer = { 0 };
    StaticTimer_t * pxTimerBufferRet = NULL;

    pvPortMalloc_ExpectAndReturn( sizeof( Timer_t ), &pxNewTimer );

    /* Setup */
    /* Expectations */
    /* prvInitialiseNewTimer */
    /* prvCheckForValidListAndQueue */
    vListInitialise_ExpectAnyArgs();
    vListInitialise_ExpectAnyArgs();
    xQueueGenericCreateStatic_ExpectAnyArgsAndReturn( NULL );
    /* Back prvInitialiseNewTimer */
    vListInitialiseItem_ExpectAnyArgs();


    /* API Call */
    xTimer = xTimerCreate( "ut_timer_task",
                           pdMS_TO_TICKS( 1000 ),
                           pdTRUE,
                           ( void * ) &pvTimerID,
                           xCallback_Test );

    TEST_ASSERT_EQUAL( pdFALSE, xTimerGetStaticBuffer( xTimer, &pxTimerBufferRet ) );
    TEST_ASSERT_EQUAL( NULL, pxTimerBufferRet );
}
