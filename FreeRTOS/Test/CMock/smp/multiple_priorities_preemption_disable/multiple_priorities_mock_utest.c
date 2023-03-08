/*
 * FreeRTOS V202012.00
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
/*! @file config_assert_utest.c */

/* C runtime includes. */
#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>
#include <stdio.h>

/* Tasks includes */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"
#include "../global_vars.h"
#include "task.h"

// #include "fake_port.h"
// #include "portmacro.h"

/* Test includes. */
#include "unity.h"
#include "unity_memory.h"
#include "CException.h"


/* Local includes. */
//#include "../smp_utest_common.h"

/* Mock includes. */
#include "mock_timers.h"
#include "mock_list.h"
#include "mock_list_macros.h"
#include "mock_fake_assert.h"
#include "mock_fake_port.h"
#include "mock_local_portable.h"


/* =================================  MACROS  =============================== */

/**
 * @brief CException code for when a configASSERT should be intercepted.
 */
#define configASSERT_E                       0xAA101

/**
 * @brief simulate up to 10 tasks: add more if needed
 * */
#define TCB_ARRAY                       10

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
static int assertionFailed = 1;

/**
 * @brief Flag which denotes if test need to abort on assertion.
 */
static BaseType_t shouldAbortOnAssertion;


/* ===========================  EXTERN VARIABLES  =========================== */
extern void vTaskEnterCritical( void );
extern void vTaskExitCritical( void );
extern void vTaskExitCriticalFromISR( UBaseType_t uxSavedInterruptStatus );

extern volatile UBaseType_t uxDeletedTasksWaitingCleanUp;
extern volatile BaseType_t xSchedulerRunning;
extern volatile UBaseType_t uxSchedulerSuspended;
extern TCB_t * volatile pxCurrentTCBs[ configNUMBER_OF_CORES ];
extern volatile BaseType_t xYieldPendings[ configNUMBER_OF_CORES ];
extern volatile UBaseType_t uxTopReadyPriority;
extern List_t pxReadyTasksLists[ configMAX_PRIORITIES ];
extern UBaseType_t uxTaskNumber;

/* ==========================  STATIC FUNCTIONS  ========================== */
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

void * pvPortMalloc( size_t xSize )
{
    return unity_malloc( xSize );
}

void vPortFree( void * pv )
{
    return unity_free( pv );
}
/* ============================  Unity Fixtures  ============================ */
/*! called before each testcase */
void setUp( void )
{
    vFakeAssert_StubWithCallback( vFakeAssertStub );
}

/*! called after each testcase */
void tearDown( void )
{
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

/** 
 * @brief This test ensures that the  first condition is true while the second
 *        condition is false in the if statement, so we will be performing the
 *        action with portYIELD_CORE, and the task is put in the yielding state
 * 
 * <b>Coverage</b> 
 * @code{c} 
 * prvYieldCore( xCoreID ); 
 *
 * if( ( portCHECK_IF_IN_ISR() == pdTRUE ) && ( xCoreID == portGET_CORE_ID() ) )
 *
 * @endcode 
 *
 * configNMBER_OF_CORES > 1
 * configUSE_TASK_PREEMPTION_DISABLE = 1
 */
void test_prvYieldCore_core_id_ne_current_coreid( void )
{
    TCB_t task;
    TCB_t task2;
    TaskHandle_t  xTaskHandle;

    task.xTaskRunState = 1;   /* running on core 1 */
    task2.xTaskRunState = -2; /* running on core 2 taskTASK_YIELDING  */
    xTaskHandle = &task;
    pxCurrentTCBs[0] = &task;
    pxCurrentTCBs[1] = &task;
    pxCurrentTCBs[2] = &task2;
    xSchedulerRunning  = pdTRUE;

    /* Test Expectations */
    vFakePortEnterCriticalSection_Expect();
    /* Entering prvYieldCore */
    vFakePortCheckIfInISR_ExpectAndReturn( pdTRUE );
    vFakePortGetCoreID_ExpectAndReturn ( 2 );
    vFakePortGetCoreID_ExpectAndReturn ( 2 );
    vFakePortYieldCore_Expect(1);
    /* Leaving prvYieldCore */
    vFakePortExitCriticalSection_Expect();

    /* API call */
    vTaskPreemptionEnable( xTaskHandle );

    /* Test Assertions */
    TEST_ASSERT_EQUAL( pdFALSE, xYieldPendings[2] );
    TEST_ASSERT_EQUAL( -2, pxCurrentTCBs[1]->xTaskRunState );/* yielding state */
    TEST_ASSERT_EQUAL( -2, task.xTaskRunState );             /* yielding state */
}

/** 
 * @brief This test ensures that when the task is already in the yielding state,
 *        nothing is done
 * 
 * <b>Coverage</b> 
 * @code{c} 
 * prvYieldCore( xCoreID ); 
 *
 * if( pxCurrentTCBs[ xCoreID ]->xTaskRunState != taskTASK_YIELDING )
 *
 * @endcode 
 *
 * configNMBER_OF_CORES > 1
 * configUSE_TASK_PREEMPTION_DISABLE = 1
 */
void test_prvYieldCore_runstate_eq_yielding( void )
{
    TCB_t task;
    TCB_t task2;
    TaskHandle_t xTaskHandle;

    task.xTaskRunState = 1;   /* running on core 1 */
    task2.xTaskRunState = -2; /* running on core 2 taskTASK_YIELDING  */
    xTaskHandle = &task;
    pxCurrentTCBs[0] = &task;
    pxCurrentTCBs[1] = &task2;
    pxCurrentTCBs[2] = &task2;
    xSchedulerRunning  = pdTRUE;

    /* Test Expectations */
    vFakePortEnterCriticalSection_Expect();
    /* Entering prvYieldCore */
    vFakePortCheckIfInISR_ExpectAndReturn( pdTRUE );
    vFakePortGetCoreID_ExpectAndReturn ( 2 );
    /* Leaving prvYieldCore */
    vFakePortExitCriticalSection_Expect();

    /* API call */
    vTaskPreemptionEnable( xTaskHandle );

    /* Test Assertions */
    TEST_ASSERT_EQUAL( pdFALSE, xYieldPendings[2] );
    TEST_ASSERT_EQUAL( -2, pxCurrentTCBs[1]->xTaskRunState ); /* yielding */
    TEST_ASSERT_EQUAL( 1, task.xTaskRunState ); /* nothing has changed */
}

/** 
 * @brief This test ensures that if xTask Delete is caled and the scheuler is
 *        not running, the core is not yielded, but it is removed from the
 *        stateList, the eventList and inserted in the taskwaitingtermination
 *        list, the uxdeletedtaskwaiting for cleanup is increased and the
 *        uxtasknumber is increased
 * 
 * <b>Coverage</b> 
 * @code{c} 
 * vTaskDelete( xTaskToDelete); 
 *
 *   if( ( xSchedulerRunning != pdFALSE ) &&
 *               ( taskTASK_IS_RUNNING( pxTCB ) == pdTRUE ) )
 *
 * @endcode 
 *
 * configNMBER_OF_CORES > 1
 * INCLUDE_vTaskDelete = 1
 */
void test_vTaskDelete_scheduler_not_running( void )
{
    TCB_t task;
    TaskHandle_t xTaskToDelete;

    task.xTaskRunState = 1;   /* running on core 1 */
    xTaskToDelete = &task;
    pxCurrentTCBs[0] = &task;

    xSchedulerRunning = pdFALSE;

    uxDeletedTasksWaitingCleanUp = 0;
    uxTaskNumber = 1;

    /* Test Expectations */
    vFakePortEnterCriticalSection_Expect();
    uxListRemove_ExpectAnyArgsAndReturn ( 0 );
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( NULL );

    /* if task != taskTaskNOT_RUNNING */
    vListInsertEnd_ExpectAnyArgs();
    vPortCurrentTaskDying_ExpectAnyArgs();

    vFakePortExitCriticalSection_Expect();


    /* API Call */
    vTaskDelete( xTaskToDelete );

    /* Test Verifications */
    TEST_ASSERT_EQUAL( 1, uxDeletedTasksWaitingCleanUp );
    TEST_ASSERT_EQUAL (2, uxTaskNumber );
}

/** 
 * @brief This test ensures that if xTask Delete is caled and the scheuler is
 *        running while the task runstate is more that the configNUMBER_OF_CORES,
 *        the core is not yielded, but it is removed from the
 *        stateList, the eventList and inserted in the taskwaitingtermination
 *        list, the uxdeletedtaskwaiting for cleanup is not changed
 *        uxtasknumber is increased
 * 
 * <b>Coverage</b> 
 * @code{c} 
 * vTaskDelete( xTaskToDelete); 
 *
 *   if( ( xSchedulerRunning != pdFALSE ) &&
 *               ( taskTASK_IS_RUNNING( pxTCB ) == pdTRUE ) )
 *
 * @endcode 
 *
 * configNMBER_OF_CORES > 1
 * INCLUDE_vTaskDelete = 1
 */
void test_vTaskDelete_( void )
{
    TCB_t  task;
    TaskHandle_t xTaskToDelete;

    task.xTaskRunState = configNUMBER_OF_CORES + 2;   /* running on core 1 */
    xTaskToDelete = &task;
    pxCurrentTCBs[0] = &task;

    xSchedulerRunning = pdTRUE;

    uxDeletedTasksWaitingCleanUp = 0;
    uxTaskNumber = 1;

    /* Test Expectations */
    vFakePortEnterCriticalSection_Expect();
    uxListRemove_ExpectAnyArgsAndReturn ( 0 );
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( NULL );

    /* if task != taskTaskNOT_RUNNING */
    vListInsertEnd_ExpectAnyArgs();
    vPortCurrentTaskDying_ExpectAnyArgs();

    vFakePortExitCriticalSection_Expect();

    /* API Call */
    vTaskDelete( xTaskToDelete );

    /* Test Verifications */
    TEST_ASSERT_EQUAL( 1, uxDeletedTasksWaitingCleanUp );
    TEST_ASSERT_EQUAL (2, uxTaskNumber );
}

