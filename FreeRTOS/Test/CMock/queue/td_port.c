/*
 * FreeRTOS V202112.00
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
/*! @file td_port.c */

#include "queue_utest_common.h"

/* C runtime includes. */
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>

/* Test includes. */
#include "unity.h"
#include "unity_memory.h"

/* Mock includes. */
#include "mock_task.h"
#include "mock_fake_port.h"

/* ============================  GLOBAL VARIABLES =========================== */

bool xInCriticalSection = false;
uint32_t ulNumEnterCriticalSection = 0;
uint32_t ulNumExitCriticalSection = 0;

UBaseType_t uxSavedInterruptStatusGlobal = 0;
uint32_t ulNumCallsSetInterruptMaskFromISR = 0;
uint32_t ulNumCallsClearInterruptMaskFromISR = 0;

/* ==========================  CALLBACK FUNCTIONS =========================== */

static void enterCriticalSectionStub( int cmock_num_calls )
{
    /* check that enterCriticalSectionStub was not called twice in a row */
    TEST_ASSERT_FALSE_MESSAGE( xInCriticalSection, "vFakePortEnterCriticalSection was called twice in a row." );
    xInCriticalSection = true;
    ulNumEnterCriticalSection++;
}

static void exitCriticalSectionStub( int cmock_num_calls )
{
    /* check that exitCriticalSectionStub was not called twice in a row */
    TEST_ASSERT_TRUE_MESSAGE( xInCriticalSection, "vFakePortExitCriticalSection was called twice in a row." );
    xInCriticalSection = false;
    ulNumExitCriticalSection++;
}

static UBaseType_t portSetInterruptMaskFromISRStub( int cmock_num_calls )
{
    ulNumCallsSetInterruptMaskFromISR++;
    uxSavedInterruptStatusGlobal = getLastMonotonicTestValue() + 241235;
    xInCriticalSection = true;
    return uxSavedInterruptStatusGlobal;
}

static void portClearInterruptMaskFromISRStub( UBaseType_t uxSavedInterruptStatus,
                                               int cmock_num_calls )
{
    ulNumCallsClearInterruptMaskFromISR++;
    TEST_ASSERT_EQUAL_MESSAGE( uxSavedInterruptStatusGlobal, uxSavedInterruptStatus,
                               "Saved interrupt state from call to portClearInterruptMaskFromISR does not match last call to portSetInterruptMaskFromISR." );
    xInCriticalSection = false;
    uxSavedInterruptStatusGlobal = 0;
}

/* ============================= Unity Fixtures ============================= */

/* ==========================  Helper functions =========================== */

void td_port_register_stubs( void )
{
    /* Track critical section state */
    xInCriticalSection = false;
    ulNumEnterCriticalSection = 0;
    ulNumExitCriticalSection = 0;

    vFakePortEnterCriticalSection_Stub( &enterCriticalSectionStub );
    vFakePortExitCriticalSection_Stub( &exitCriticalSectionStub );

    uxSavedInterruptStatusGlobal = 0;
    vFakePortClearInterruptMaskFromISR_Stub( &portClearInterruptMaskFromISRStub );
    ulFakePortSetInterruptMaskFromISR_Stub( &portSetInterruptMaskFromISRStub );
}

BaseType_t td_port_isInCriticalSection( void )
{
    return xInCriticalSection;
}

void td_port_teardown_check( void )
{
    TEST_ASSERT_EQUAL_MESSAGE( ulNumEnterCriticalSection,
                               ulNumExitCriticalSection,
                               "Number of calls to vFakePortEnterCriticalSection does not match the number of calls to vFakePortExitCriticalSection." );

    TEST_ASSERT_EQUAL_MESSAGE( 0,
                               uxSavedInterruptStatusGlobal,
                               "uxSavedInterruptStatus was non-zero at the end of the preceeding test case." );
}
