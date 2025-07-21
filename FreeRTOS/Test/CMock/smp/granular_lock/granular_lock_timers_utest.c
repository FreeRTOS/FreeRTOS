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
/*! @file granular_lock_timers_utest.c */

/* C runtime includes. */
#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>

/* Task includes */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"
#include "task.h"
#include "event_groups.h"
#include "queue.h"
#include "semphr.h"
#include "timers.h"

/* Test includes. */
#include "unity.h"
#include "unity_memory.h"
#include "../global_vars.h"
//#include "../smp_utest_common.h"
#include "../granular_lock_utest_common.h"

/* Mock includes. */
#include "mock_fake_assert.h"
#include "mock_fake_port.h"
#include "mock_portmacro.h"

/* ===========================  EXTERN VARIABLES  =========================== */
extern portSPINLOCK_TYPE xTimerTaskSpinlock;
extern portSPINLOCK_TYPE xTimerISRSpinlock;

/* ============================  Unity Fixtures  ============================ */

/*! called before each testcase */
void setUp( void )
{
    /* Use the common setup for the testing. */
    granularLocksSetUp();

    xTimerTaskSpinlock.uxLockCount = 0;
    xTimerTaskSpinlock.xOwnerCore = -1;
    xTimerISRSpinlock.uxLockCount = 0;
    xTimerISRSpinlock.xOwnerCore = -1;

}

/*! called after each testcase */
void tearDown( void )
{
    granularLocksTearDown();
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

void test_granular_locks_timers_critical_section_independence( void )
{
    granular_locks_critical_section_independence( &xTimerTaskSpinlock, &xTimerISRSpinlock);
}

void test_granular_locks_timers_mutual_exclusion( void )
{
    granular_locks_mutual_exclusion( &xTimerTaskSpinlock, &xTimerISRSpinlock );
}

void test_granular_locks_timers_critical_section_nesting( void )
{
    granular_locks_critical_section_nesting( &xTimerTaskSpinlock, &xTimerISRSpinlock );
}

void test_granular_locks_timers_state_protection_deletion( void )
{
    granular_locks_state_protection_deletion( &xTimerTaskSpinlock, &xTimerISRSpinlock );
}

void test_granular_locks_timers_state_protection_suspension( void )
{
    granular_locks_state_protection_suspension( &xTimerTaskSpinlock, &xTimerISRSpinlock );
}

void test_granular_locks_timers_state_protection_deletion_suspension( void )
{
    granular_locks_state_protection_deletion_suspension( &xTimerTaskSpinlock, &xTimerISRSpinlock );
}

void test_granular_locks_timers_state_protection_suspension_deletion( void )
{
    granular_locks_state_protection_suspension_deletion( &xTimerTaskSpinlock, &xTimerISRSpinlock );
}

void test_granular_locks_timers_state_protection_suspension_resumption_test( void ) //=> Currently fails
{
    granular_locks_state_protection_suspension_resumption_test( &xTimerTaskSpinlock, &xTimerISRSpinlock );
}

void test_granular_locks_timers_state_protection_vTaskPlaceOnEventList_blocked_deletion_test( void )
{
    granular_locks_state_protection_vTaskPlaceOnEventList_blocked_deletion_test( &xTimerTaskSpinlock, &xTimerISRSpinlock );
}

void test_granular_locks_timers_state_protection_vTaskPlaceOnEventList_blocked_suspension_test( void )
{
    granular_locks_state_protection_vTaskPlaceOnEventList_blocked_suspension_test( &xTimerTaskSpinlock, &xTimerISRSpinlock );
}

void test_granular_locks_timers_state_protection_vTaskPlaceOnUnorderedEventList_blocked_deletion_test( void )
{
    granular_locks_state_protection_vTaskPlaceOnUnorderedEventList_blocked_deletion( &xTimerTaskSpinlock, &xTimerISRSpinlock );
}

void test_granular_locks_timers_state_protection_vTaskPlaceOnUnorderedEventList_blocked_suspension_test( void )
{
    granular_locks_state_protection_vTaskPlaceOnUnorderedEventList_blocked_suspension_test( &xTimerTaskSpinlock, &xTimerISRSpinlock );
}

void test_granular_locks_timers_state_protection_vTaskPlaceOnEventListRestricted_blocked_deletion_test( void )
{
    granular_locks_state_protection_vTaskPlaceOnEventListRestricted_blocked_deletion_test( &xTimerTaskSpinlock, &xTimerISRSpinlock );
}

void test_granular_locks_timers_state_protection_vTaskPlaceOnEventListRestricted_blocked_suspension_test( void )
{
    granular_locks_state_protection_vTaskPlaceOnEventListRestricted_blocked_suspension_test( &xTimerTaskSpinlock, &xTimerISRSpinlock );
}

void test_granular_locks_timers_state_protection_vTaskPlaceOnEventList_deletion_blocked_test( void )
{
    granular_locks_state_protection_vTaskPlaceOnEventList_deletion_blocked_test( &xTimerTaskSpinlock, &xTimerISRSpinlock );
}

void test_granular_locks_timers_state_protection_vTaskPlaceOnEventList_suspension_blocked_test( void )
{
    granular_locks_state_protection_vTaskPlaceOnEventList_suspension_blocked_test( &xTimerTaskSpinlock, &xTimerISRSpinlock );
}

void test_granular_locks_timers_state_protection_vTaskPlaceOnUnorderedEventList_deletion_blocked_test( void )
{
    granular_locks_state_protection_vTaskPlaceOnUnorderedEventList_deletion_blocked_test( &xTimerTaskSpinlock, &xTimerISRSpinlock );
}

void test_granular_locks_timers_state_protection_vTaskPlaceOnUnorderedEventList_suspension_blocked_test( void )
{
    granular_locks_state_protection_vTaskPlaceOnUnorderedEventList_suspension_blocked_test( &xTimerTaskSpinlock, &xTimerISRSpinlock );
}

void test_granular_locks_timers_state_protection_vTaskPlaceOnEventListRestricted_deletion_blocked_test( void )
{
    granular_locks_state_protection_vTaskPlaceOnEventListRestricted_deletion_blocked_test( &xTimerTaskSpinlock, &xTimerISRSpinlock );
}

void test_granular_locks_timers_state_protection_vTaskPlaceOnEventListRestricted_suspension_blocked_test( void )
{
    granular_locks_state_protection_vTaskPlaceOnEventListRestricted_suspension_blocked_test( &xTimerTaskSpinlock, &xTimerISRSpinlock );
}


