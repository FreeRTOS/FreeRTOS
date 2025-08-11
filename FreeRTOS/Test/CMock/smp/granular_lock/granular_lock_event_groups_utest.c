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
/*! @file granular_lock_event_group_utest.c */

/* C runtime includes. */
#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>

/* Task includes */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"
#include "event_groups.h"

/* Test includes. */
#include "unity.h"
#include "unity_memory.h"
#include "../global_vars.h"
#include "../granular_lock_utest_common.h"
#include "../smp_utest_common.h"

/* Mock includes. */
#include "mock_fake_assert.h"
#include "mock_fake_port.h"
#include "mock_portmacro.h"

/* ===========================  TEST MACROS  =========================== */

#define TEST_EVENT_BIT    ( 0x01U )

/* ===========================  GLOBAL VARIABLES  =========================== */

static EventGroupHandle_t xDynamicEventGroupHandle;
static EventGroupHandle_t xStaticEventGroupHandle;

static StaticEventGroup_t xCreatedEventGroup;

/* ============================  Unity Fixtures  ============================ */

/*! called before each testcase */
void setUp( void )
{
    /* Use the common setup for the testing. */
    granularLocksSetUp();

    /* Data group specific initialization. */
    xDynamicEventGroupHandle = xEventGroupCreate();
    TEST_ASSERT_NOT_EQUAL( NULL, xDynamicEventGroupHandle );

    xStaticEventGroupHandle = xEventGroupCreateStatic( &xCreatedEventGroup );
    TEST_ASSERT_NOT_EQUAL( NULL, xStaticEventGroupHandle );
}

/*! called after each testcase */
void tearDown( void )
{
    granularLocksTearDown();

    vEventGroupDelete( xDynamicEventGroupHandle );
    xDynamicEventGroupHandle = NULL;

    xStaticEventGroupHandle = NULL;
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

/* ==============================  Test Cases event groups ============================== */

void test_granular_locks_dynamic_event_group_xEventGroupSetBits( void )
{
    EventGroup_t * pxEventGroup = ( EventGroup_t * ) xDynamicEventGroupHandle;

    xEventGroupSetBits( xDynamicEventGroupHandle, TEST_EVENT_BIT );

    /* Check the internal data structure that the event bit is set correctly. */
    TEST_ASSERT_EQUAL( pxEventGroup->uxEventBits, TEST_EVENT_BIT );
}

/* ==============================  Test Cases dynamic allocated event groups ============================== */

void test_granular_locks_dynamic_event_group_critical_section_independence( void )
{
    granular_locks_critical_section_independence( &xDynamicEventGroupHandle->xTaskSpinlock, &xDynamicEventGroupHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_event_groups_critical_section_mutual_exclusion( void )
{
    granular_locks_critical_section_mutual_exclusion( &xDynamicEventGroupHandle->xTaskSpinlock, &xDynamicEventGroupHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_event_groups_critical_section_nesting( void )
{
    granular_locks_critical_section_nesting( &xDynamicEventGroupHandle->xTaskSpinlock, &xDynamicEventGroupHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_event_groups_critical_section_state_protection_deletion( void )
{
    granular_locks_critical_section_state_protection_deletion( &xDynamicEventGroupHandle->xTaskSpinlock, &xDynamicEventGroupHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_event_groups_critical_section_state_protection_suspension( void )
{
    granular_locks_critical_section_state_protection_suspension( &xDynamicEventGroupHandle->xTaskSpinlock, &xDynamicEventGroupHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_event_groups_critical_section_state_protection_deletion_suspension( void )
{
    granular_locks_critical_section_state_protection_deletion_suspension( &xDynamicEventGroupHandle->xTaskSpinlock, &xDynamicEventGroupHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_event_groups_critical_section_state_protection_suspension_deletion( void )
{
    granular_locks_critical_section_state_protection_suspension_deletion( &xDynamicEventGroupHandle->xTaskSpinlock, &xDynamicEventGroupHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_event_groups_critical_section_state_protection_suspension_resumption_test( void ) /*=> Currently fails */
{
    granular_locks_critical_section_state_protection_suspension_resumption_test( &xDynamicEventGroupHandle->xTaskSpinlock, &xDynamicEventGroupHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_event_groups_critical_section_state_protection_vTaskPlaceOnEventList_blocked_deletion_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventList_blocked_deletion_test( &xDynamicEventGroupHandle->xTaskSpinlock, &xDynamicEventGroupHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_event_groups_critical_section_state_protection_vTaskPlaceOnEventList_blocked_suspension_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventList_blocked_suspension_test( &xDynamicEventGroupHandle->xTaskSpinlock, &xDynamicEventGroupHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_event_groups_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_blocked_deletion_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_blocked_deletion_test( &xDynamicEventGroupHandle->xTaskSpinlock, &xDynamicEventGroupHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_event_groups_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_blocked_suspension_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_blocked_suspension_test( &xDynamicEventGroupHandle->xTaskSpinlock, &xDynamicEventGroupHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_event_groups_critical_section_state_protection_vTaskPlaceOnEventListRestricted_blocked_deletion_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventListRestricted_blocked_deletion_test( &xDynamicEventGroupHandle->xTaskSpinlock, &xDynamicEventGroupHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_event_groups_critical_section_state_protection_vTaskPlaceOnEventListRestricted_blocked_suspension_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventListRestricted_blocked_suspension_test( &xDynamicEventGroupHandle->xTaskSpinlock, &xDynamicEventGroupHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_event_groups_critical_section_state_protection_vTaskPlaceOnEventList_deletion_blocked_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventList_deletion_blocked_test( &xDynamicEventGroupHandle->xTaskSpinlock, &xDynamicEventGroupHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_event_groups_critical_section_state_protection_vTaskPlaceOnEventList_suspension_blocked_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventList_suspension_blocked_test( &xDynamicEventGroupHandle->xTaskSpinlock, &xDynamicEventGroupHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_event_groups_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_deletion_blocked_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_deletion_blocked_test( &xDynamicEventGroupHandle->xTaskSpinlock, &xDynamicEventGroupHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_event_groups_state_protection_vTaskPlaceOnUnorderedEventList_suspension_blocked_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_suspension_blocked_test( &xDynamicEventGroupHandle->xTaskSpinlock, &xDynamicEventGroupHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_event_groups_critical_section_state_protection_vTaskPlaceOnEventListRestricted_deletion_blocked_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventListRestricted_deletion_blocked_test( &xDynamicEventGroupHandle->xTaskSpinlock, &xDynamicEventGroupHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_event_groups_critical_section_state_protection_vTaskPlaceOnEventListRestricted_suspension_blocked_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventListRestricted_suspension_blocked_test( &xDynamicEventGroupHandle->xTaskSpinlock, &xDynamicEventGroupHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_event_groups_lock_independence( void )
{
    granular_locks_lock_independence( &xDynamicEventGroupHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_event_groups_lock_mutual_exclusion( void )
{
    granular_locks_lock_mutual_exclusion( &xDynamicEventGroupHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_event_groups_lock_state_protection_deletion( void )
{
    granular_locks_lock_state_protection_deletion( &xDynamicEventGroupHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_event_groups_lock_state_protection_suspension( void )
{
    granular_locks_lock_state_protection_suspension( &xDynamicEventGroupHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_event_groups_lock_state_protection_deletion_suspension( void )
{
    granular_locks_lock_state_protection_deletion_suspension( &xDynamicEventGroupHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_event_groups_lock_state_protection_suspension_deletion( void )
{
    granular_locks_lock_state_protection_suspension_deletion( &xDynamicEventGroupHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_event_groups_lock_state_protection_suspension_resumption( void )
{
    granular_locks_lock_state_protection_suspension_resumption_test( &xDynamicEventGroupHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_event_groups_lock_state_protection_vTaskPlaceOnEventList_blocked_deletion( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventList_blocked_deletion_test(
        &xDynamicEventGroupHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_event_groups_lock_state_protection_vTaskPlaceOnEventList_blocked_suspension( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventList_blocked_suspension_test(
        &xDynamicEventGroupHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_event_groups_lock_state_protection_vTaskPlaceOnUnorderedEventList_blocked_deletion( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnUnorderedEventList_blocked_deletion_test(
        &xDynamicEventGroupHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_event_groups_lock_state_protection_vTaskPlaceOnUnorderedEventList_blocked_suspension( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnUnorderedEventList_blocked_suspension_test(
        &xDynamicEventGroupHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_event_groups_lock_state_protection_vTaskPlaceOnEventListRestricted_blocked_deletion( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventListRestricted_blocked_deletion_test(
        &xDynamicEventGroupHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_event_groups_lock_state_protection_vTaskPlaceOnEventListRestricted_blocked_suspension( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventListRestricted_blocked_suspension_test(
        &xDynamicEventGroupHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_event_groups_lock_state_protection_vTaskPlaceOnEventList_deletion_blocked( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventList_deletion_blocked_test(
        &xDynamicEventGroupHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_event_groups_lock_state_protection_vTaskPlaceOnEventList_suspension_blocked( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventList_suspension_blocked_test(
        &xDynamicEventGroupHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_event_groups_lock_state_protection_vTaskPlaceOnUnorderedEventList_deletion_blocked( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnUnorderedEventList_deletion_blocked_test(
        &xDynamicEventGroupHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_event_groups_lock_state_protection_vTaskPlaceOnUnorderedEventList_suspension_blocked( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnUnorderedEventList_suspension_blocked_test(
        &xDynamicEventGroupHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_event_groups_lock_state_protection_vTaskPlaceOnEventListRestricted_deletion_blocked( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventListRestricted_deletion_blocked_test(
        &xDynamicEventGroupHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_event_groups_lock_state_protection_vTaskPlaceOnEventListRestricted_suspension_blocked( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventListRestricted_suspension_blocked_test(
        &xDynamicEventGroupHandle->xTaskSpinlock );
}

/* ==============================  Test Cases static allocated event group ============================== */

void test_granular_locks_static_event_groups_critical_section_independence( void )
{
    granular_locks_critical_section_independence( &xStaticEventGroupHandle->xTaskSpinlock, &xStaticEventGroupHandle->xISRSpinlock );
}

void test_granular_locks_static_event_groups_critical_section_mutual_exclusion( void )
{
    granular_locks_critical_section_mutual_exclusion( &xStaticEventGroupHandle->xTaskSpinlock, &xStaticEventGroupHandle->xISRSpinlock );
}

void test_granular_locks_static_event_groups_critical_section_nesting( void )
{
    granular_locks_critical_section_nesting( &xStaticEventGroupHandle->xTaskSpinlock, &xStaticEventGroupHandle->xISRSpinlock );
}

void test_granular_locks_static_event_groups_critical_section_state_protection_deletion( void )
{
    granular_locks_critical_section_state_protection_deletion( &xStaticEventGroupHandle->xTaskSpinlock, &xStaticEventGroupHandle->xISRSpinlock );
}

void test_granular_locks_static_event_groups_critical_section_state_protection_suspension( void )
{
    granular_locks_critical_section_state_protection_suspension( &xStaticEventGroupHandle->xTaskSpinlock, &xStaticEventGroupHandle->xISRSpinlock );
}

void test_granular_locks_static_event_groups_critical_section_state_protection_deletion_suspension( void )
{
    granular_locks_critical_section_state_protection_deletion_suspension( &xStaticEventGroupHandle->xTaskSpinlock, &xStaticEventGroupHandle->xISRSpinlock );
}

void test_granular_locks_static_event_groups_critical_section_state_protection_suspension_deletion( void )
{
    granular_locks_critical_section_state_protection_suspension_deletion( &xStaticEventGroupHandle->xTaskSpinlock, &xStaticEventGroupHandle->xISRSpinlock );
}

void test_granular_locks_static_event_groups_critical_section_state_protection_suspension_resumption_test( void ) /*=> Currently fails */
{
    granular_locks_critical_section_state_protection_suspension_resumption_test( &xStaticEventGroupHandle->xTaskSpinlock, &xStaticEventGroupHandle->xISRSpinlock );
}

void test_granular_locks_static_event_groups_critical_section_state_protection_vTaskPlaceOnEventList_blocked_deletion_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventList_blocked_deletion_test( &xStaticEventGroupHandle->xTaskSpinlock, &xStaticEventGroupHandle->xISRSpinlock );
}

void test_granular_locks_static_event_groups_critical_section_state_protection_vTaskPlaceOnEventList_blocked_suspension_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventList_blocked_suspension_test( &xStaticEventGroupHandle->xTaskSpinlock, &xStaticEventGroupHandle->xISRSpinlock );
}

void test_granular_locks_static_event_groups_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_blocked_deletion_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_blocked_deletion_test( &xStaticEventGroupHandle->xTaskSpinlock, &xStaticEventGroupHandle->xISRSpinlock );
}

void test_granular_locks_static_event_groups_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_blocked_suspension_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_blocked_suspension_test( &xStaticEventGroupHandle->xTaskSpinlock, &xStaticEventGroupHandle->xISRSpinlock );
}

void test_granular_locks_static_event_groups_critical_section_state_protection_vTaskPlaceOnEventListRestricted_blocked_deletion_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventListRestricted_blocked_deletion_test( &xStaticEventGroupHandle->xTaskSpinlock, &xStaticEventGroupHandle->xISRSpinlock );
}

void test_granular_locks_static_event_groups_critical_section_state_protection_vTaskPlaceOnEventListRestricted_blocked_suspension_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventListRestricted_blocked_suspension_test( &xStaticEventGroupHandle->xTaskSpinlock, &xStaticEventGroupHandle->xISRSpinlock );
}

void test_granular_locks_static_event_groups_critical_section_state_protection_vTaskPlaceOnEventList_deletion_blocked_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventList_deletion_blocked_test( &xStaticEventGroupHandle->xTaskSpinlock, &xStaticEventGroupHandle->xISRSpinlock );
}

void test_granular_locks_static_event_groups_critical_section_state_protection_vTaskPlaceOnEventList_suspension_blocked_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventList_suspension_blocked_test( &xStaticEventGroupHandle->xTaskSpinlock, &xStaticEventGroupHandle->xISRSpinlock );
}

void test_granular_locks_static_event_groups_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_deletion_blocked_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_deletion_blocked_test( &xStaticEventGroupHandle->xTaskSpinlock, &xStaticEventGroupHandle->xISRSpinlock );
}

void test_granular_locks_static_event_groups_state_protection_vTaskPlaceOnUnorderedEventList_suspension_blocked_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_suspension_blocked_test( &xStaticEventGroupHandle->xTaskSpinlock, &xStaticEventGroupHandle->xISRSpinlock );
}

void test_granular_locks_static_event_groups_critical_section_state_protection_vTaskPlaceOnEventListRestricted_deletion_blocked_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventListRestricted_deletion_blocked_test( &xStaticEventGroupHandle->xTaskSpinlock, &xStaticEventGroupHandle->xISRSpinlock );
}

void test_granular_locks_static_event_groups_critical_section_state_protection_vTaskPlaceOnEventListRestricted_suspension_blocked_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventListRestricted_suspension_blocked_test( &xStaticEventGroupHandle->xTaskSpinlock, &xStaticEventGroupHandle->xISRSpinlock );
}

void test_granular_locks_static_event_groups_lock_independence( void )
{
    granular_locks_lock_independence( &xStaticEventGroupHandle->xTaskSpinlock );
}

void test_granular_locks_static_event_groups_lock_mutual_exclusion( void )
{
    granular_locks_lock_mutual_exclusion( &xStaticEventGroupHandle->xTaskSpinlock );
}

void test_granular_locks_static_event_groups_lock_state_protection_deletion( void )
{
    granular_locks_lock_state_protection_deletion( &xStaticEventGroupHandle->xTaskSpinlock );
}

void test_granular_locks_static_event_groups_lock_state_protection_suspension( void )
{
    granular_locks_lock_state_protection_suspension( &xStaticEventGroupHandle->xTaskSpinlock );
}

void test_granular_locks_static_event_groups_lock_state_protection_deletion_suspension( void )
{
    granular_locks_lock_state_protection_deletion_suspension( &xStaticEventGroupHandle->xTaskSpinlock );
}

void test_granular_locks_static_event_groups_lock_state_protection_suspension_deletion( void )
{
    granular_locks_lock_state_protection_suspension_deletion( &xStaticEventGroupHandle->xTaskSpinlock );
}

void test_granular_locks_static_event_groups_lock_state_protection_suspension_resumption( void )
{
    granular_locks_lock_state_protection_suspension_resumption_test( &xStaticEventGroupHandle->xTaskSpinlock );
}

void test_granular_locks_static_event_groups_lock_state_protection_vTaskPlaceOnEventList_blocked_deletion( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventList_blocked_deletion_test(
        &xStaticEventGroupHandle->xTaskSpinlock );
}

void test_granular_locks_static_event_groups_lock_state_protection_vTaskPlaceOnEventList_blocked_suspension( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventList_blocked_suspension_test(
        &xStaticEventGroupHandle->xTaskSpinlock );
}

void test_granular_locks_static_event_groups_lock_state_protection_vTaskPlaceOnUnorderedEventList_blocked_deletion( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnUnorderedEventList_blocked_deletion_test(
        &xStaticEventGroupHandle->xTaskSpinlock );
}

void test_granular_locks_static_event_groups_lock_state_protection_vTaskPlaceOnUnorderedEventList_blocked_suspension( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnUnorderedEventList_blocked_suspension_test(
        &xStaticEventGroupHandle->xTaskSpinlock );
}

void test_granular_locks_static_event_groups_lock_state_protection_vTaskPlaceOnEventListRestricted_blocked_deletion( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventListRestricted_blocked_deletion_test(
        &xStaticEventGroupHandle->xTaskSpinlock );
}

void test_granular_locks_static_event_groups_lock_state_protection_vTaskPlaceOnEventListRestricted_blocked_suspension( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventListRestricted_blocked_suspension_test(
        &xStaticEventGroupHandle->xTaskSpinlock );
}

void test_granular_locks_static_event_groups_lock_state_protection_vTaskPlaceOnEventList_deletion_blocked( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventList_deletion_blocked_test(
        &xStaticEventGroupHandle->xTaskSpinlock );
}

void test_granular_locks_static_event_groups_lock_state_protection_vTaskPlaceOnEventList_suspension_blocked( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventList_suspension_blocked_test(
        &xStaticEventGroupHandle->xTaskSpinlock );
}

void test_granular_locks_static_event_groups_lock_state_protection_vTaskPlaceOnUnorderedEventList_deletion_blocked( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnUnorderedEventList_deletion_blocked_test(
        &xStaticEventGroupHandle->xTaskSpinlock );
}

void test_granular_locks_static_event_groups_lock_state_protection_vTaskPlaceOnUnorderedEventList_suspension_blocked( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnUnorderedEventList_suspension_blocked_test(
        &xStaticEventGroupHandle->xTaskSpinlock );
}

void test_granular_locks_static_event_groups_lock_state_protection_vTaskPlaceOnEventListRestricted_deletion_blocked( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventListRestricted_deletion_blocked_test(
        &xStaticEventGroupHandle->xTaskSpinlock );
}

void test_granular_locks_static_event_groups_lock_state_protection_vTaskPlaceOnEventListRestricted_suspension_blocked( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventListRestricted_suspension_blocked_test(
        &xStaticEventGroupHandle->xTaskSpinlock );
}
