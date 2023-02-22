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
#include "fake_port.h"
#include "task.h"
#include "portmacro.h"

/* Test includes. */
#include "unity.h"
#include "unity_memory.h"
#include "CException.h"
#include "../global_vars.h"
#include "../smp_utest_common.h"

/* Mock includes. */
#include "mock_timers.h"
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
static int assertionFailed = 0;

/**
 * @brief Flag which denotes if test need to abort on assertion.
 */
static BaseType_t shouldAbortOnAssertion;


/* ===========================  EXTERN VARIABLES  =========================== */
extern void vTaskEnterCritical( void );
extern volatile UBaseType_t uxDeletedTasksWaitingCleanUp;
extern volatile BaseType_t xSchedulerRunning;
extern volatile UBaseType_t uxSchedulerSuspended;
extern TCB_t * volatile pxCurrentTCBs[ configNUMBER_OF_CORES ];

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

static void validate_and_clear_assertions( void )
{
    TEST_ASSERT_EQUAL( 1, assertionFailed );
    assertionFailed = 0;
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

void port_release_task_lock_cb( int  num_calls)
{
    pxCurrentTCBs[ 0 ]->xTaskRunState = -1; /* taskTASK_YIELDING */
}

/* ==============================  Test Cases  ============================== */

/** 
 * @brief This test ensures that the code asserts when the TCB's xTaskRunState
 *        is not equal to taskTASK_YIELDING ( -2 )
 * 
 * <b>Coverage</b> 
 * @code{c} 
 * rvCheckForRunStateChange( pxTCB ); 
 * 
 * configASSERT( pxThisTCB->xTaskRunState == taskTASK_YIELDING );
 * @endcode 
*/
void test_prvCheckForRunStateChange_asssert_runstate_ne_task_yield (void )
{
    xSchedulerRunning = pdTRUE;
    uxSchedulerSuspended = 0U;

    TCB_t currentTCB;

    pxCurrentTCBs[ 0 ]                    =  &currentTCB;
    pxCurrentTCBs[ 0 ]->uxCriticalNesting = 0;
    pxCurrentTCBs[ 0 ]->xTaskRunState     = -2; /* taskTASK_YIELDING */

    vFakePortReleaseTaskLock_AddCallback(port_release_task_lock_cb);
    vFakePortDisableInterrupts_ExpectAndReturn( pdTRUE );
    vFakePortGetCoreID_ExpectAndReturn( 0);
    vFakePortGetTaskLock_Expect();
    vFakePortGetISRLock_Expect();
    vFakePortGetCoreID_ExpectAndReturn( 0);
    vFakePortGetCoreID_ExpectAndReturn( 0);
    vFakePortAssertIfISR_Expect();
    vFakePortCheckIfInISR_ExpectAndReturn(pdFALSE);
    vFakePortGetCoreID_ExpectAndReturn( 0);
    vFakePortGetCoreID_ExpectAndReturn( 0);
    vFakePortGetCoreID_ExpectAndReturn( 0);
    vFakePortReleaseISRLock_Expect();
    vFakePortReleaseTaskLock_Expect();

    EXPECT_ASSERT_BREAK( vTaskEnterCritical() );

    validate_and_clear_assertions();

}
