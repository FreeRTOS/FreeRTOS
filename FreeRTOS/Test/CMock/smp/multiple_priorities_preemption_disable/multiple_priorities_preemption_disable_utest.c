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

/* #include "fake_port.h" */
#include "portmacro.h"

/* Test includes. */
#include "unity.h"
#include "unity_memory.h"
#include "CException.h"


/* Local includes. */
/*#include "../smp_utest_common.h" */

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
#define configASSERT_E    0xAA101
#define EXIT_LOOP         0xAA102

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
extern volatile TickType_t xTickCount;
extern volatile TickType_t xNextTaskUnblockTime;
extern TaskHandle_t xIdleTaskHandles[ configNUMBER_OF_CORES ];

/* ===========================  STATIC FUNCTIONS  =========================== */
void vApplicationMinimalIdleHook( void )
{
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
    uxDeletedTasksWaitingCleanUp;
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
