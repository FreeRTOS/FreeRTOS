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
static bool port_yield_within_api_called = false;
static TickType_t saved_last_time = 0;

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
    HOOK_DIAG();
}
/* ==========================  CALLBACK FUNCTIONS =========================== */
static void xCallback_Test( TimerHandle_t xTimer )
{
    HOOK_DIAG();
}

static int32_t end_2_timer = 0;
static void xCallback_Test_2_end( TimerHandle_t xTimer )
{
    HOOK_DIAG();
    static int i = 2;

    if( end_2_timer - 1 <= 0 )
    {
        pthread_exit( &i );
    }

    end_2_timer--;
}

static int32_t end_4_timer = 0;
static void pended_function_4_end( void * arg1,
                                   uint32_t arg2 )
{
    HOOK_DIAG();
    static int i = 4;

    if( end_4_timer - 1 <= 0 )
    {
        pthread_exit( &i );
    }

    end_4_timer--;
}

/* ============================  STATIC FUNCTIONS =========================== */
static void * timer_thread_function( void * args )
{
    void * pvParameters = NULL;

    portTASK_FUNCTION( prvTimerTask, pvParameters );
    ( void ) fool_static2; /* ignore unused variable warning */
    /* API Call */
    prvTimerTask( pvParameters );
    return NULL;
}

/* ==============================  UNITY FIXTURES  ========================== */

void setUp( void )
{
    vFakeAssert_Ignore();
    port_yield_within_api_called = false;
    /* Track calls to malloc / free */
    UnityMalloc_StartTest();
    critical_section_counter = 0;
    end_2_timer = 0;
    end_4_timer = 0;
    stopTimers();
}

/*! called before each testcase */
void tearDown( void )
{
    TEST_ASSERT_EQUAL_INT_MESSAGE( 0, usMallocFreeCalls,
                                   "free is not called the same number of times as malloc,"
                                   "you might have a memory leak!!" );
    usMallocFreeCalls = 0;

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

/**
 * @brief xTimerCreate happy path
 *
 */
void test_xTimerCreateTimerTask_success( void )
{
    BaseType_t ret_xtimer;
    QueueHandle_t queue_handle = ( QueueHandle_t ) 3; /* not zero */

    /* Setup */
    /* Expectations */
    vListInitialise_ExpectAnyArgs();
    vListInitialise_ExpectAnyArgs();
    xQueueGenericCreate_ExpectAnyArgsAndReturn( queue_handle );
    vQueueAddToRegistry_ExpectAnyArgs();
    xTaskCreate_ExpectAnyArgsAndReturn( pdTRUE );
    /* API Call */
    ret_xtimer = xTimerCreateTimerTask();
    /* Validations */
    TEST_ASSERT_TRUE( ret_xtimer );
}


/**
 * @brief xTimerCreate happy path
 *
 */
void test_xTimerCreate_success( void )
{
    uint32_t ulID = 0;
    TimerHandle_t xTimer = NULL;
    Timer_t pxNewTimer;
    QueueHandle_t queue_handle = ( QueueHandle_t ) 3; /* not zero */

    pvPortMalloc_ExpectAndReturn( sizeof( Timer_t ), &pxNewTimer );
    vListInitialise_ExpectAnyArgs();
    vListInitialise_ExpectAnyArgs();
    xQueueGenericCreate_ExpectAnyArgsAndReturn( queue_handle );
    vQueueAddToRegistry_ExpectAnyArgs();
    vListInitialiseItem_ExpectAnyArgs();

    xTimer = xTimerCreate( "ut-timer",
                           pdMS_TO_TICKS( 1000 ),
                           pdTRUE,
                           &ulID,
                           xCallback_Test );

    TEST_ASSERT_NOT_EQUAL( NULL, xTimer );
    TEST_ASSERT_EQUAL_PTR( &pxNewTimer, xTimer );
    TEST_ASSERT_EQUAL( tmrSTATUS_IS_AUTORELOAD, pxNewTimer.ucStatus );
    TEST_ASSERT_EQUAL_STRING( "ut-timer", pxNewTimer.pcTimerName );
    TEST_ASSERT_EQUAL( pdMS_TO_TICKS( 1000 ), pxNewTimer.xTimerPeriodInTicks );
    TEST_ASSERT_EQUAL_PTR( &ulID, pxNewTimer.pvTimerID );
    TEST_ASSERT_EQUAL_PTR( xCallback_Test, pxNewTimer.pxCallbackFunction );
}

void test_xTimerCreate_success_no_auto_reload( void )
{
    uint32_t ulID = 0;
    TimerHandle_t xTimer = NULL;
    Timer_t pxNewTimer;
    QueueHandle_t queue_handle = ( QueueHandle_t ) 3; /* not zero */

    pvPortMalloc_ExpectAndReturn( sizeof( Timer_t ), &pxNewTimer );
    vListInitialise_ExpectAnyArgs();
    vListInitialise_ExpectAnyArgs();
    xQueueGenericCreate_ExpectAnyArgsAndReturn( queue_handle );
    vQueueAddToRegistry_ExpectAnyArgs();
    vListInitialiseItem_ExpectAnyArgs();

    xTimer = xTimerCreate( "ut-timer",
                           pdMS_TO_TICKS( 1000 ),
                           pdFALSE,
                           &ulID,
                           xCallback_Test );

    TEST_ASSERT_EQUAL_PTR( &pxNewTimer, xTimer );
    TEST_ASSERT_EQUAL( 0, pxNewTimer.ucStatus );
}

void test_xTimerCreate_success_twice( void )
{
    uint32_t ulID = 0;
    TimerHandle_t xTimer = NULL;
    Timer_t pxNewTimer;
    QueueHandle_t queue_handle = ( QueueHandle_t ) 3; /* not zero */

    pvPortMalloc_ExpectAndReturn( sizeof( Timer_t ), &pxNewTimer );
    /* prvInitialiseNewTimer */
    /* prvCheckForValidListAndQueue */
    vListInitialise_ExpectAnyArgs();
    vListInitialise_ExpectAnyArgs();
    xQueueGenericCreate_ExpectAnyArgsAndReturn( queue_handle );
    vQueueAddToRegistry_ExpectAnyArgs();
    /* back prvInitialiseNewTimer  */
    vListInitialiseItem_ExpectAnyArgs();

    xTimer = xTimerCreate( "ut-timer",
                           pdMS_TO_TICKS( 1000 ),
                           pdTRUE,
                           &ulID,
                           xCallback_Test );

    TEST_ASSERT_EQUAL_PTR( &pxNewTimer, xTimer );
    TEST_ASSERT_EQUAL_PTR( &pxNewTimer, xTimer );
    TEST_ASSERT_EQUAL( tmrSTATUS_IS_AUTORELOAD, pxNewTimer.ucStatus );
    TEST_ASSERT_EQUAL_STRING( "ut-timer", pxNewTimer.pcTimerName );
    TEST_ASSERT_EQUAL( pdMS_TO_TICKS( 1000 ), pxNewTimer.xTimerPeriodInTicks );
    TEST_ASSERT_EQUAL_PTR( &ulID, pxNewTimer.pvTimerID );
    TEST_ASSERT_EQUAL_PTR( xCallback_Test, pxNewTimer.pxCallbackFunction );

    /* Second call to xTimerCreate */
    pvPortMalloc_ExpectAndReturn( sizeof( Timer_t ), &pxNewTimer );
    vListInitialiseItem_ExpectAnyArgs();
    xTimer = xTimerCreate( "ut-timer",
                           pdMS_TO_TICKS( 1000 ),
                           pdTRUE,
                           &ulID,
                           xCallback_Test );
    TEST_ASSERT_EQUAL_PTR( &pxNewTimer, xTimer );
}

void test_xTimerCreate_fail_timer_allocation( void )
{
    uint32_t ulID = 0;
    TimerHandle_t xTimer = NULL;

    pvPortMalloc_ExpectAndReturn( sizeof( Timer_t ), NULL );

    xTimer = xTimerCreate( "ut-timer",
                           pdMS_TO_TICKS( 1000 ),
                           pdTRUE,
                           &ulID,
                           xCallback_Test );

    TEST_ASSERT_EQUAL( NULL, xTimer );
}
void test_xTimerCreate_fail_queue_allocation( void )
{
    uint32_t ulID = 0;
    Timer_t pxNewTimer;
    TimerHandle_t xTimer = NULL;

    /* Expectations */
    pvPortMalloc_ExpectAndReturn( sizeof( Timer_t ), &pxNewTimer );
    /* prvInitialiseNewTimer */
    /* prvCheckForValidListAndQueue */
    vListInitialise_ExpectAnyArgs();
    vListInitialise_ExpectAnyArgs();
    xQueueGenericCreate_ExpectAnyArgsAndReturn( NULL );
    /* Back prvInitialiseNewTimer */
    vListInitialiseItem_ExpectAnyArgs();

    /* API Call */
    xTimer = xTimerCreate( "ut-timer",
                           pdMS_TO_TICKS( 1000 ),
                           pdTRUE,
                           &ulID,
                           xCallback_Test );
    /* Validations */
    TEST_ASSERT_EQUAL( &pxNewTimer, xTimer );
}

void test_timer_function_success3_command_delete_dynamic( void )
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
    vQueueWaitForMessageRestricted_ExpectAnyArgs();
    xTaskResumeAll_ExpectAndReturn( pdTRUE );
    /* prvProcessReceivedCommands */
    xQueueReceive_ExpectAndReturn( NULL, NULL, tmrNO_DELAY, pdPASS );
    xQueueReceive_IgnoreArg_xQueue();
    xQueueReceive_IgnoreArg_pvBuffer();
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xMessage, sizeof( DaemonTaskMessage_t ) );
    listIS_CONTAINED_WITHIN_ExpectAnyArgsAndReturn( pdFALSE );
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    /* prvSampleTimeNow*/
    xTaskGetTickCount_ExpectAndReturn( saved_last_time ); /* time now / static last_time = 0 */
    vPortFree_Expect( &xTimer );                          /* testcase is testing this clause */
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
    vQueueWaitForMessageRestricted_ExpectAnyArgs();
    xTaskResumeAll_ExpectAndReturn( pdTRUE );
    /* prvProcessExpiredTimer */
    /* prvInsertTimerInActiveList */
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
