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
/*! @file granular_lock_queue_utest.c */

/* C runtime includes. */
#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>

/* Task includes */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"
#include "queue.h"

/* Test includes. */
#include "unity.h"
#include "unity_memory.h"
#include "../global_vars.h"
#include "../granular_lock_utest_common.h"

/* Mock includes. */
#include "mock_fake_assert.h"
#include "mock_fake_port.h"
#include "mock_portmacro.h"

/* ===========================  TEST MACROS  =========================== */

#define TEST_QUEUE_LENGTH       ( 5 )
#define TEST_QUEUE_ITEM_SIZE    ( sizeof( uint32_t ) )

/* ===========================  GLOBAL VARIABLES  =========================== */

static QueueHandle_t xDynamicQueueHandle = NULL;
static QueueHandle_t xStaticQueueHandle = NULL;

static StaticQueue_t xQueueBuffer;
static uint8_t ucQueueStorage[ TEST_QUEUE_LENGTH * TEST_QUEUE_ITEM_SIZE ];

/* ============================  Unity Fixtures  ============================ */

/*! called before each testcase */
void setUp( void )
{
    /* Use the common setup for the testing. */
    granularLocksSetUp();

    /* Queue specific initialization. */
    xDynamicQueueHandle = xQueueCreate( TEST_QUEUE_LENGTH, TEST_QUEUE_ITEM_SIZE );
    TEST_ASSERT_NOT_EQUAL( NULL, xDynamicQueueHandle );

    xStaticQueueHandle = xQueueCreateStatic( TEST_QUEUE_LENGTH,
                                             TEST_QUEUE_ITEM_SIZE,
                                             ucQueueStorage,
                                             &xQueueBuffer );
    TEST_ASSERT_NOT_EQUAL( NULL, xStaticQueueHandle );
}

/*! called after each testcase */
void tearDown( void )
{
    granularLocksTearDown();

    vQueueDelete( xDynamicQueueHandle );
    xDynamicQueueHandle = NULL;

    xStaticQueueHandle = NULL;
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

/* ==============================  Test Cases dynamic allocated queue ============================== */

void test_granular_locks_dynamic_queue_critical_section_independence( void )
{
    granular_locks_critical_section_independence( &xDynamicQueueHandle->xTaskSpinlock, &xDynamicQueueHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_queue_critical_section_mutual_exclusion( void )
{
    granular_locks_critical_section_mutual_exclusion( &xDynamicQueueHandle->xTaskSpinlock, &xDynamicQueueHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_queue_critical_section_nesting( void )
{
    granular_locks_critical_section_nesting( &xDynamicQueueHandle->xTaskSpinlock, &xDynamicQueueHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_queue_critical_section_state_protection_deletion( void )
{
    granular_locks_critical_section_state_protection_deletion( &xDynamicQueueHandle->xTaskSpinlock, &xDynamicQueueHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_queue_critical_section_state_protection_suspension( void )
{
    granular_locks_critical_section_state_protection_suspension( &xDynamicQueueHandle->xTaskSpinlock, &xDynamicQueueHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_queue_critical_section_state_protection_deletion_suspension( void )
{
    granular_locks_critical_section_state_protection_deletion_suspension( &xDynamicQueueHandle->xTaskSpinlock, &xDynamicQueueHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_queue_critical_section_state_protection_suspension_deletion( void )
{
    granular_locks_critical_section_state_protection_suspension_deletion( &xDynamicQueueHandle->xTaskSpinlock, &xDynamicQueueHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_queue_critical_section_state_protection_suspension_resumption_test( void ) /*=> Currently fails */
{
    granular_locks_critical_section_state_protection_suspension_resumption_test( &xDynamicQueueHandle->xTaskSpinlock, &xDynamicQueueHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_queue_critical_section_state_protection_vTaskPlaceOnEventList_blocked_deletion_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventList_blocked_deletion_test( &xDynamicQueueHandle->xTaskSpinlock, &xDynamicQueueHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_queue_critical_section_state_protection_vTaskPlaceOnEventList_blocked_suspension_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventList_blocked_suspension_test( &xDynamicQueueHandle->xTaskSpinlock, &xDynamicQueueHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_queue_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_blocked_deletion_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_blocked_deletion_test( &xDynamicQueueHandle->xTaskSpinlock, &xDynamicQueueHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_queue_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_blocked_suspension_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_blocked_suspension_test( &xDynamicQueueHandle->xTaskSpinlock, &xDynamicQueueHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_queue_critical_section_state_protection_vTaskPlaceOnEventListRestricted_blocked_deletion_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventListRestricted_blocked_deletion_test( &xDynamicQueueHandle->xTaskSpinlock, &xDynamicQueueHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_queue_critical_section_state_protection_vTaskPlaceOnEventListRestricted_blocked_suspension_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventListRestricted_blocked_suspension_test( &xDynamicQueueHandle->xTaskSpinlock, &xDynamicQueueHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_queue_critical_section_state_protection_vTaskPlaceOnEventList_deletion_blocked_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventList_deletion_blocked_test( &xDynamicQueueHandle->xTaskSpinlock, &xDynamicQueueHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_queue_critical_section_state_protection_vTaskPlaceOnEventList_suspension_blocked_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventList_suspension_blocked_test( &xDynamicQueueHandle->xTaskSpinlock, &xDynamicQueueHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_queue_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_deletion_blocked_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_deletion_blocked_test( &xDynamicQueueHandle->xTaskSpinlock, &xDynamicQueueHandle->xISRSpinlock );
}

void test_granular_locks_queue_state_protection_vTaskPlaceOnUnorderedEventList_suspension_blocked_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_suspension_blocked_test( &xDynamicQueueHandle->xTaskSpinlock, &xDynamicQueueHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_queue_critical_section_state_protection_vTaskPlaceOnEventListRestricted_deletion_blocked_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventListRestricted_deletion_blocked_test( &xDynamicQueueHandle->xTaskSpinlock, &xDynamicQueueHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_queue_critical_section_state_protection_vTaskPlaceOnEventListRestricted_suspension_blocked_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventListRestricted_suspension_blocked_test( &xDynamicQueueHandle->xTaskSpinlock, &xDynamicQueueHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_queue_lock_independence( void )
{
    granular_locks_lock_independence( &xDynamicQueueHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_queue_lock_mutual_exclusion( void )
{
    granular_locks_lock_mutual_exclusion( &xDynamicQueueHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_queue_lock_state_protection_deletion( void )
{
    granular_locks_lock_state_protection_deletion( &xDynamicQueueHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_queue_lock_state_protection_suspension( void )
{
    granular_locks_lock_state_protection_suspension( &xDynamicQueueHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_queue_lock_state_protection_deletion_suspension( void )
{
    granular_locks_lock_state_protection_deletion_suspension( &xDynamicQueueHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_queue_lock_state_protection_suspension_deletion( void )
{
    granular_locks_lock_state_protection_suspension_deletion( &xDynamicQueueHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_queue_lock_state_protection_suspension_resumption( void )
{
    granular_locks_lock_state_protection_suspension_resumption_test( &xDynamicQueueHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_queue_lock_state_protection_vTaskPlaceOnEventList_blocked_deletion( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventList_blocked_deletion_test(
        &xDynamicQueueHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_queue_lock_state_protection_vTaskPlaceOnEventList_blocked_suspension( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventList_blocked_suspension_test(
        &xDynamicQueueHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_queue_lock_state_protection_vTaskPlaceOnUnorderedEventList_blocked_deletion( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnUnorderedEventList_blocked_deletion_test(
        &xDynamicQueueHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_queue_lock_state_protection_vTaskPlaceOnUnorderedEventList_blocked_suspension( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnUnorderedEventList_blocked_suspension_test(
        &xDynamicQueueHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_queue_lock_state_protection_vTaskPlaceOnEventListRestricted_blocked_deletion( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventListRestricted_blocked_deletion_test(
        &xDynamicQueueHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_queue_lock_state_protection_vTaskPlaceOnEventListRestricted_blocked_suspension( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventListRestricted_blocked_suspension_test(
        &xDynamicQueueHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_queue_lock_state_protection_vTaskPlaceOnEventList_deletion_blocked( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventList_deletion_blocked_test(
        &xDynamicQueueHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_queue_lock_state_protection_vTaskPlaceOnEventList_suspension_blocked( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventList_suspension_blocked_test(
        &xDynamicQueueHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_queue_lock_state_protection_vTaskPlaceOnUnorderedEventList_deletion_blocked( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnUnorderedEventList_deletion_blocked_test(
        &xDynamicQueueHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_queue_lock_state_protection_vTaskPlaceOnUnorderedEventList_suspension_blocked( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnUnorderedEventList_suspension_blocked_test(
        &xDynamicQueueHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_queue_lock_state_protection_vTaskPlaceOnEventListRestricted_deletion_blocked( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventListRestricted_deletion_blocked_test(
        &xDynamicQueueHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_queue_lock_state_protection_vTaskPlaceOnEventListRestricted_suspension_blocked( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventListRestricted_suspension_blocked_test(
        &xDynamicQueueHandle->xTaskSpinlock );
}

/* ==============================  Test Cases static allocated queue ============================== */

void test_granular_locks_static_queue_critical_section_independence( void )
{
    granular_locks_critical_section_independence( &xStaticQueueHandle->xTaskSpinlock, &xStaticQueueHandle->xISRSpinlock );
}

void test_granular_locks_static_queue_critical_section_mutual_exclusion( void )
{
    granular_locks_critical_section_mutual_exclusion( &xStaticQueueHandle->xTaskSpinlock, &xStaticQueueHandle->xISRSpinlock );
}

void test_granular_locks_static_queue_critical_section_nesting( void )
{
    granular_locks_critical_section_nesting( &xStaticQueueHandle->xTaskSpinlock, &xStaticQueueHandle->xISRSpinlock );
}

void test_granular_locks_static_queue_critical_section_state_protection_deletion( void )
{
    granular_locks_critical_section_state_protection_deletion( &xStaticQueueHandle->xTaskSpinlock, &xStaticQueueHandle->xISRSpinlock );
}

void test_granular_locks_static_queue_critical_section_state_protection_suspension( void )
{
    granular_locks_critical_section_state_protection_suspension( &xStaticQueueHandle->xTaskSpinlock, &xStaticQueueHandle->xISRSpinlock );
}

void test_granular_locks_static_queue_critical_section_state_protection_deletion_suspension( void )
{
    granular_locks_critical_section_state_protection_deletion_suspension( &xStaticQueueHandle->xTaskSpinlock, &xStaticQueueHandle->xISRSpinlock );
}

void test_granular_locks_static_queue_critical_section_state_protection_suspension_deletion( void )
{
    granular_locks_critical_section_state_protection_suspension_deletion( &xStaticQueueHandle->xTaskSpinlock, &xStaticQueueHandle->xISRSpinlock );
}

void test_granular_locks_static_queue_critical_section_state_protection_suspension_resumption_test( void ) /*=> Currently fails */
{
    granular_locks_critical_section_state_protection_suspension_resumption_test( &xStaticQueueHandle->xTaskSpinlock, &xStaticQueueHandle->xISRSpinlock );
}

void test_granular_locks_static_queue_critical_section_state_protection_vTaskPlaceOnEventList_blocked_deletion_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventList_blocked_deletion_test( &xStaticQueueHandle->xTaskSpinlock, &xStaticQueueHandle->xISRSpinlock );
}

void test_granular_locks_static_queue_critical_section_state_protection_vTaskPlaceOnEventList_blocked_suspension_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventList_blocked_suspension_test( &xStaticQueueHandle->xTaskSpinlock, &xStaticQueueHandle->xISRSpinlock );
}

void test_granular_locks_static_queue_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_blocked_deletion_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_blocked_deletion_test( &xStaticQueueHandle->xTaskSpinlock, &xStaticQueueHandle->xISRSpinlock );
}

void test_granular_locks_static_queue_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_blocked_suspension_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_blocked_suspension_test( &xStaticQueueHandle->xTaskSpinlock, &xStaticQueueHandle->xISRSpinlock );
}

void test_granular_locks_static_queue_critical_section_state_protection_vTaskPlaceOnEventListRestricted_blocked_deletion_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventListRestricted_blocked_deletion_test( &xStaticQueueHandle->xTaskSpinlock, &xStaticQueueHandle->xISRSpinlock );
}

void test_granular_locks_static_queue_critical_section_state_protection_vTaskPlaceOnEventListRestricted_blocked_suspension_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventListRestricted_blocked_suspension_test( &xStaticQueueHandle->xTaskSpinlock, &xStaticQueueHandle->xISRSpinlock );
}

void test_granular_locks_static_queue_critical_section_state_protection_vTaskPlaceOnEventList_deletion_blocked_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventList_deletion_blocked_test( &xStaticQueueHandle->xTaskSpinlock, &xStaticQueueHandle->xISRSpinlock );
}

void test_granular_locks_static_queue_critical_section_state_protection_vTaskPlaceOnEventList_suspension_blocked_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventList_suspension_blocked_test( &xStaticQueueHandle->xTaskSpinlock, &xStaticQueueHandle->xISRSpinlock );
}

void test_granular_locks_static_queue_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_deletion_blocked_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_deletion_blocked_test( &xStaticQueueHandle->xTaskSpinlock, &xStaticQueueHandle->xISRSpinlock );
}

void test_granular_locks_static_queue_state_protection_vTaskPlaceOnUnorderedEventList_suspension_blocked_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_suspension_blocked_test( &xStaticQueueHandle->xTaskSpinlock, &xStaticQueueHandle->xISRSpinlock );
}

void test_granular_locks_static_queue_critical_section_state_protection_vTaskPlaceOnEventListRestricted_deletion_blocked_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventListRestricted_deletion_blocked_test( &xStaticQueueHandle->xTaskSpinlock, &xStaticQueueHandle->xISRSpinlock );
}

void test_granular_locks_static_queue_critical_section_state_protection_vTaskPlaceOnEventListRestricted_suspension_blocked_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventListRestricted_suspension_blocked_test( &xStaticQueueHandle->xTaskSpinlock, &xStaticQueueHandle->xISRSpinlock );
}

void test_granular_locks_static_queue_lock_independence( void )
{
    granular_locks_lock_independence( &xStaticQueueHandle->xTaskSpinlock );
}

void test_granular_locks_static_queue_lock_mutual_exclusion( void )
{
    granular_locks_lock_mutual_exclusion( &xStaticQueueHandle->xTaskSpinlock );
}

void test_granular_locks_static_queue_lock_state_protection_deletion( void )
{
    granular_locks_lock_state_protection_deletion( &xStaticQueueHandle->xTaskSpinlock );
}

void test_granular_locks_static_queue_lock_state_protection_suspension( void )
{
    granular_locks_lock_state_protection_suspension( &xStaticQueueHandle->xTaskSpinlock );
}

void test_granular_locks_static_queue_lock_state_protection_deletion_suspension( void )
{
    granular_locks_lock_state_protection_deletion_suspension( &xStaticQueueHandle->xTaskSpinlock );
}

void test_granular_locks_static_queue_lock_state_protection_suspension_deletion( void )
{
    granular_locks_lock_state_protection_suspension_deletion( &xStaticQueueHandle->xTaskSpinlock );
}

void test_granular_locks_static_queue_lock_state_protection_suspension_resumption( void )
{
    granular_locks_lock_state_protection_suspension_resumption_test( &xStaticQueueHandle->xTaskSpinlock );
}

void test_granular_locks_static_queue_lock_state_protection_vTaskPlaceOnEventList_blocked_deletion( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventList_blocked_deletion_test(
        &xStaticQueueHandle->xTaskSpinlock );
}

void test_granular_locks_static_queue_lock_state_protection_vTaskPlaceOnEventList_blocked_suspension( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventList_blocked_suspension_test(
        &xStaticQueueHandle->xTaskSpinlock );
}

void test_granular_locks_static_queue_lock_state_protection_vTaskPlaceOnUnorderedEventList_blocked_deletion( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnUnorderedEventList_blocked_deletion_test(
        &xStaticQueueHandle->xTaskSpinlock );
}

void test_granular_locks_static_queue_lock_state_protection_vTaskPlaceOnUnorderedEventList_blocked_suspension( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnUnorderedEventList_blocked_suspension_test(
        &xStaticQueueHandle->xTaskSpinlock );
}

void test_granular_locks_static_queue_lock_state_protection_vTaskPlaceOnEventListRestricted_blocked_deletion( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventListRestricted_blocked_deletion_test(
        &xStaticQueueHandle->xTaskSpinlock );
}

void test_granular_locks_static_queue_lock_state_protection_vTaskPlaceOnEventListRestricted_blocked_suspension( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventListRestricted_blocked_suspension_test(
        &xStaticQueueHandle->xTaskSpinlock );
}

void test_granular_locks_static_queue_lock_state_protection_vTaskPlaceOnEventList_deletion_blocked( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventList_deletion_blocked_test(
        &xStaticQueueHandle->xTaskSpinlock );
}

void test_granular_locks_static_queue_lock_state_protection_vTaskPlaceOnEventList_suspension_blocked( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventList_suspension_blocked_test(
        &xStaticQueueHandle->xTaskSpinlock );
}

void test_granular_locks_static_queue_lock_state_protection_vTaskPlaceOnUnorderedEventList_deletion_blocked( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnUnorderedEventList_deletion_blocked_test(
        &xStaticQueueHandle->xTaskSpinlock );
}

void test_granular_locks_static_queue_lock_state_protection_vTaskPlaceOnUnorderedEventList_suspension_blocked( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnUnorderedEventList_suspension_blocked_test(
        &xStaticQueueHandle->xTaskSpinlock );
}

void test_granular_locks_static_queue_lock_state_protection_vTaskPlaceOnEventListRestricted_deletion_blocked( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventListRestricted_deletion_blocked_test(
        &xStaticQueueHandle->xTaskSpinlock );
}

void test_granular_locks_static_queue_lock_state_protection_vTaskPlaceOnEventListRestricted_suspension_blocked( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventListRestricted_suspension_blocked_test(
        &xStaticQueueHandle->xTaskSpinlock );
}
