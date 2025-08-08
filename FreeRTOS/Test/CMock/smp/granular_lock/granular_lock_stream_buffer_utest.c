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
/*! @file granular_lock_stream_buffer_utest.c */

/* C runtime includes. */
#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>

/* Task includes */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"
#include "stream_buffer.h"

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

#define TEST_BUFFER_SIZE_BYTES      ( 50U )
#define TEST_TRIGGER_LEVEL_BYTES    ( 1U )

/* ===========================  GLOBAL VARIABLES  =========================== */

static StreamBufferHandle_t xDynamicStreamBufferHandle;
static StreamBufferHandle_t xStaticStreamBufferHandle;
static StaticStreamBuffer_t xStreamBufferStruct;

static uint8_t pucStreamBufferStorageArea[ TEST_BUFFER_SIZE_BYTES + 1U ];

/* ============================  Unity Fixtures  ============================ */

/*! called before each testcase */
void setUp( void )
{
    /* Use the common setup for the testing. */
    granularLocksSetUp();

    /* stream buffer specific initialization. */
    xDynamicStreamBufferHandle = xStreamBufferCreate( TEST_BUFFER_SIZE_BYTES, TEST_TRIGGER_LEVEL_BYTES );
    TEST_ASSERT_NOT_EQUAL( NULL, xDynamicStreamBufferHandle );

    xStaticStreamBufferHandle = xStreamBufferCreateStatic( TEST_BUFFER_SIZE_BYTES,
                                                           TEST_TRIGGER_LEVEL_BYTES,
                                                           pucStreamBufferStorageArea,
                                                           &xStreamBufferStruct );
    TEST_ASSERT_NOT_EQUAL( NULL, xStaticStreamBufferHandle );
}

/*! called after each testcase */
void tearDown( void )
{
    granularLocksTearDown();

    vStreamBufferDelete( xDynamicStreamBufferHandle );
    xDynamicStreamBufferHandle = NULL;

    xStaticStreamBufferHandle = NULL;
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

/* ==============================  Test Cases dynamic allocated stream buffer ============================== */

void test_granular_locks_dynamic_stream_buffer_critical_section_independence( void )
{
    granular_locks_critical_section_independence( &xDynamicStreamBufferHandle->xTaskSpinlock, &xDynamicStreamBufferHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_stream_buffer_critical_section_mutual_exclusion( void )
{
    granular_locks_critical_section_mutual_exclusion( &xDynamicStreamBufferHandle->xTaskSpinlock, &xDynamicStreamBufferHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_stream_buffer_critical_section_nesting( void )
{
    granular_locks_critical_section_nesting( &xDynamicStreamBufferHandle->xTaskSpinlock, &xDynamicStreamBufferHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_stream_buffer_critical_section_state_protection_deletion( void )
{
    granular_locks_critical_section_state_protection_deletion( &xDynamicStreamBufferHandle->xTaskSpinlock, &xDynamicStreamBufferHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_stream_buffer_critical_section_state_protection_suspension( void )
{
    granular_locks_critical_section_state_protection_suspension( &xDynamicStreamBufferHandle->xTaskSpinlock, &xDynamicStreamBufferHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_stream_buffer_critical_section_state_protection_deletion_suspension( void )
{
    granular_locks_critical_section_state_protection_deletion_suspension( &xDynamicStreamBufferHandle->xTaskSpinlock, &xDynamicStreamBufferHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_stream_buffer_critical_section_state_protection_suspension_deletion( void )
{
    granular_locks_critical_section_state_protection_suspension_deletion( &xDynamicStreamBufferHandle->xTaskSpinlock, &xDynamicStreamBufferHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_stream_buffer_critical_section_state_protection_suspension_resumption_test( void ) /*=> Currently fails */
{
    granular_locks_critical_section_state_protection_suspension_resumption_test( &xDynamicStreamBufferHandle->xTaskSpinlock, &xDynamicStreamBufferHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_stream_buffer_critical_section_state_protection_vTaskPlaceOnEventList_blocked_deletion_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventList_blocked_deletion_test( &xDynamicStreamBufferHandle->xTaskSpinlock, &xDynamicStreamBufferHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_stream_buffer_critical_section_state_protection_vTaskPlaceOnEventList_blocked_suspension_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventList_blocked_suspension_test( &xDynamicStreamBufferHandle->xTaskSpinlock, &xDynamicStreamBufferHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_stream_buffer_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_blocked_deletion_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_blocked_deletion_test( &xDynamicStreamBufferHandle->xTaskSpinlock, &xDynamicStreamBufferHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_stream_buffer_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_blocked_suspension_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_blocked_suspension_test( &xDynamicStreamBufferHandle->xTaskSpinlock, &xDynamicStreamBufferHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_stream_buffer_critical_section_state_protection_vTaskPlaceOnEventListRestricted_blocked_deletion_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventListRestricted_blocked_deletion_test( &xDynamicStreamBufferHandle->xTaskSpinlock, &xDynamicStreamBufferHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_stream_buffer_critical_section_state_protection_vTaskPlaceOnEventListRestricted_blocked_suspension_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventListRestricted_blocked_suspension_test( &xDynamicStreamBufferHandle->xTaskSpinlock, &xDynamicStreamBufferHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_stream_buffer_critical_section_state_protection_vTaskPlaceOnEventList_deletion_blocked_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventList_deletion_blocked_test( &xDynamicStreamBufferHandle->xTaskSpinlock, &xDynamicStreamBufferHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_stream_buffer_critical_section_state_protection_vTaskPlaceOnEventList_suspension_blocked_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventList_suspension_blocked_test( &xDynamicStreamBufferHandle->xTaskSpinlock, &xDynamicStreamBufferHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_stream_buffer_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_deletion_blocked_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_deletion_blocked_test( &xDynamicStreamBufferHandle->xTaskSpinlock, &xDynamicStreamBufferHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_stream_buffer_state_protection_vTaskPlaceOnUnorderedEventList_suspension_blocked_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_suspension_blocked_test( &xDynamicStreamBufferHandle->xTaskSpinlock, &xDynamicStreamBufferHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_stream_buffer_critical_section_state_protection_vTaskPlaceOnEventListRestricted_deletion_blocked_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventListRestricted_deletion_blocked_test( &xDynamicStreamBufferHandle->xTaskSpinlock, &xDynamicStreamBufferHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_stream_buffer_critical_section_state_protection_vTaskPlaceOnEventListRestricted_suspension_blocked_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventListRestricted_suspension_blocked_test( &xDynamicStreamBufferHandle->xTaskSpinlock, &xDynamicStreamBufferHandle->xISRSpinlock );
}

void test_granular_locks_dynamic_stream_buffer_lock_independence( void )
{
    granular_locks_lock_independence( &xDynamicStreamBufferHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_stream_buffer_lock_mutual_exclusion( void )
{
    granular_locks_lock_mutual_exclusion( &xDynamicStreamBufferHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_stream_buffer_lock_state_protection_deletion( void )
{
    granular_locks_lock_state_protection_deletion( &xDynamicStreamBufferHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_stream_buffer_lock_state_protection_suspension( void )
{
    granular_locks_lock_state_protection_suspension( &xDynamicStreamBufferHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_stream_buffer_lock_state_protection_deletion_suspension( void )
{
    granular_locks_lock_state_protection_deletion_suspension( &xDynamicStreamBufferHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_stream_buffer_lock_state_protection_suspension_deletion( void )
{
    granular_locks_lock_state_protection_suspension_deletion( &xDynamicStreamBufferHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_stream_buffer_lock_state_protection_suspension_resumption( void )
{
    granular_locks_lock_state_protection_suspension_resumption_test( &xDynamicStreamBufferHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_stream_buffer_lock_state_protection_vTaskPlaceOnEventList_blocked_deletion( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventList_blocked_deletion_test(
        &xDynamicStreamBufferHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_stream_buffer_lock_state_protection_vTaskPlaceOnEventList_blocked_suspension( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventList_blocked_suspension_test(
        &xDynamicStreamBufferHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_stream_buffer_lock_state_protection_vTaskPlaceOnUnorderedEventList_blocked_deletion( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnUnorderedEventList_blocked_deletion_test(
        &xDynamicStreamBufferHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_stream_buffer_lock_state_protection_vTaskPlaceOnUnorderedEventList_blocked_suspension( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnUnorderedEventList_blocked_suspension_test(
        &xDynamicStreamBufferHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_stream_buffer_lock_state_protection_vTaskPlaceOnEventListRestricted_blocked_deletion( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventListRestricted_blocked_deletion_test(
        &xDynamicStreamBufferHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_stream_buffer_lock_state_protection_vTaskPlaceOnEventListRestricted_blocked_suspension( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventListRestricted_blocked_suspension_test(
        &xDynamicStreamBufferHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_stream_buffer_lock_state_protection_vTaskPlaceOnEventList_deletion_blocked( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventList_deletion_blocked_test(
        &xDynamicStreamBufferHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_stream_buffer_lock_state_protection_vTaskPlaceOnEventList_suspension_blocked( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventList_suspension_blocked_test(
        &xDynamicStreamBufferHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_stream_buffer_lock_state_protection_vTaskPlaceOnUnorderedEventList_deletion_blocked( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnUnorderedEventList_deletion_blocked_test(
        &xDynamicStreamBufferHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_stream_buffer_lock_state_protection_vTaskPlaceOnUnorderedEventList_suspension_blocked( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnUnorderedEventList_suspension_blocked_test(
        &xDynamicStreamBufferHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_stream_buffer_lock_state_protection_vTaskPlaceOnEventListRestricted_deletion_blocked( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventListRestricted_deletion_blocked_test(
        &xDynamicStreamBufferHandle->xTaskSpinlock );
}

void test_granular_locks_dynamic_stream_buffer_lock_state_protection_vTaskPlaceOnEventListRestricted_suspension_blocked( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventListRestricted_suspension_blocked_test(
        &xDynamicStreamBufferHandle->xTaskSpinlock );
}

/* ==============================  Test Cases dynamic allocated stream buffer ============================== */

void test_granular_locks_static_stream_buffer_critical_section_independence( void )
{
    granular_locks_critical_section_independence( &xStaticStreamBufferHandle->xTaskSpinlock, &xStaticStreamBufferHandle->xISRSpinlock );
}

void test_granular_locks_static_stream_buffer_critical_section_mutual_exclusion( void )
{
    granular_locks_critical_section_mutual_exclusion( &xStaticStreamBufferHandle->xTaskSpinlock, &xStaticStreamBufferHandle->xISRSpinlock );
}

void test_granular_locks_static_stream_buffer_critical_section_nesting( void )
{
    granular_locks_critical_section_nesting( &xStaticStreamBufferHandle->xTaskSpinlock, &xStaticStreamBufferHandle->xISRSpinlock );
}

void test_granular_locks_static_stream_buffer_critical_section_state_protection_deletion( void )
{
    granular_locks_critical_section_state_protection_deletion( &xStaticStreamBufferHandle->xTaskSpinlock, &xStaticStreamBufferHandle->xISRSpinlock );
}

void test_granular_locks_static_stream_buffer_critical_section_state_protection_suspension( void )
{
    granular_locks_critical_section_state_protection_suspension( &xStaticStreamBufferHandle->xTaskSpinlock, &xStaticStreamBufferHandle->xISRSpinlock );
}

void test_granular_locks_static_stream_buffer_critical_section_state_protection_deletion_suspension( void )
{
    granular_locks_critical_section_state_protection_deletion_suspension( &xStaticStreamBufferHandle->xTaskSpinlock, &xStaticStreamBufferHandle->xISRSpinlock );
}

void test_granular_locks_static_stream_buffer_critical_section_state_protection_suspension_deletion( void )
{
    granular_locks_critical_section_state_protection_suspension_deletion( &xStaticStreamBufferHandle->xTaskSpinlock, &xStaticStreamBufferHandle->xISRSpinlock );
}

void test_granular_locks_static_stream_buffer_critical_section_state_protection_suspension_resumption_test( void ) /*=> Currently fails */
{
    granular_locks_critical_section_state_protection_suspension_resumption_test( &xStaticStreamBufferHandle->xTaskSpinlock, &xStaticStreamBufferHandle->xISRSpinlock );
}

void test_granular_locks_static_stream_buffer_critical_section_state_protection_vTaskPlaceOnEventList_blocked_deletion_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventList_blocked_deletion_test( &xStaticStreamBufferHandle->xTaskSpinlock, &xStaticStreamBufferHandle->xISRSpinlock );
}

void test_granular_locks_static_stream_buffer_critical_section_state_protection_vTaskPlaceOnEventList_blocked_suspension_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventList_blocked_suspension_test( &xStaticStreamBufferHandle->xTaskSpinlock, &xStaticStreamBufferHandle->xISRSpinlock );
}

void test_granular_locks_static_stream_buffer_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_blocked_deletion_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_blocked_deletion_test( &xStaticStreamBufferHandle->xTaskSpinlock, &xStaticStreamBufferHandle->xISRSpinlock );
}

void test_granular_locks_static_stream_buffer_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_blocked_suspension_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_blocked_suspension_test( &xStaticStreamBufferHandle->xTaskSpinlock, &xStaticStreamBufferHandle->xISRSpinlock );
}

void test_granular_locks_static_stream_buffer_critical_section_state_protection_vTaskPlaceOnEventListRestricted_blocked_deletion_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventListRestricted_blocked_deletion_test( &xStaticStreamBufferHandle->xTaskSpinlock, &xStaticStreamBufferHandle->xISRSpinlock );
}

void test_granular_locks_static_stream_buffer_critical_section_state_protection_vTaskPlaceOnEventListRestricted_blocked_suspension_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventListRestricted_blocked_suspension_test( &xStaticStreamBufferHandle->xTaskSpinlock, &xStaticStreamBufferHandle->xISRSpinlock );
}

void test_granular_locks_static_stream_buffer_critical_section_state_protection_vTaskPlaceOnEventList_deletion_blocked_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventList_deletion_blocked_test( &xStaticStreamBufferHandle->xTaskSpinlock, &xStaticStreamBufferHandle->xISRSpinlock );
}

void test_granular_locks_static_stream_buffer_critical_section_state_protection_vTaskPlaceOnEventList_suspension_blocked_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventList_suspension_blocked_test( &xStaticStreamBufferHandle->xTaskSpinlock, &xStaticStreamBufferHandle->xISRSpinlock );
}

void test_granular_locks_static_stream_buffer_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_deletion_blocked_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_deletion_blocked_test( &xStaticStreamBufferHandle->xTaskSpinlock, &xStaticStreamBufferHandle->xISRSpinlock );
}

void test_granular_locks_static_stream_buffer_state_protection_vTaskPlaceOnUnorderedEventList_suspension_blocked_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_suspension_blocked_test( &xStaticStreamBufferHandle->xTaskSpinlock, &xStaticStreamBufferHandle->xISRSpinlock );
}

void test_granular_locks_static_stream_buffer_critical_section_state_protection_vTaskPlaceOnEventListRestricted_deletion_blocked_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventListRestricted_deletion_blocked_test( &xStaticStreamBufferHandle->xTaskSpinlock, &xStaticStreamBufferHandle->xISRSpinlock );
}

void test_granular_locks_static_stream_buffer_critical_section_state_protection_vTaskPlaceOnEventListRestricted_suspension_blocked_test( void )
{
    granular_locks_critical_section_state_protection_vTaskPlaceOnEventListRestricted_suspension_blocked_test( &xStaticStreamBufferHandle->xTaskSpinlock, &xStaticStreamBufferHandle->xISRSpinlock );
}

void test_granular_locks_static_stream_buffer_lock_independence( void )
{
    granular_locks_lock_independence( &xStaticStreamBufferHandle->xTaskSpinlock );
}

void test_granular_locks_static_stream_buffer_lock_mutual_exclusion( void )
{
    granular_locks_lock_mutual_exclusion( &xStaticStreamBufferHandle->xTaskSpinlock );
}

void test_granular_locks_static_stream_buffer_lock_state_protection_deletion( void )
{
    granular_locks_lock_state_protection_deletion( &xStaticStreamBufferHandle->xTaskSpinlock );
}

void test_granular_locks_static_stream_buffer_lock_state_protection_suspension( void )
{
    granular_locks_lock_state_protection_suspension( &xStaticStreamBufferHandle->xTaskSpinlock );
}

void test_granular_locks_static_stream_buffer_lock_state_protection_deletion_suspension( void )
{
    granular_locks_lock_state_protection_deletion_suspension( &xStaticStreamBufferHandle->xTaskSpinlock );
}

void test_granular_locks_static_stream_buffer_lock_state_protection_suspension_deletion( void )
{
    granular_locks_lock_state_protection_suspension_deletion( &xStaticStreamBufferHandle->xTaskSpinlock );
}

void test_granular_locks_static_stream_buffer_lock_state_protection_suspension_resumption( void )
{
    granular_locks_lock_state_protection_suspension_resumption_test( &xStaticStreamBufferHandle->xTaskSpinlock );
}

void test_granular_locks_static_stream_buffer_lock_state_protection_vTaskPlaceOnEventList_blocked_deletion( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventList_blocked_deletion_test(
        &xStaticStreamBufferHandle->xTaskSpinlock );
}

void test_granular_locks_static_stream_buffer_lock_state_protection_vTaskPlaceOnEventList_blocked_suspension( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventList_blocked_suspension_test(
        &xStaticStreamBufferHandle->xTaskSpinlock );
}

void test_granular_locks_static_stream_buffer_lock_state_protection_vTaskPlaceOnUnorderedEventList_blocked_deletion( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnUnorderedEventList_blocked_deletion_test(
        &xStaticStreamBufferHandle->xTaskSpinlock );
}

void test_granular_locks_static_stream_buffer_lock_state_protection_vTaskPlaceOnUnorderedEventList_blocked_suspension( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnUnorderedEventList_blocked_suspension_test(
        &xStaticStreamBufferHandle->xTaskSpinlock );
}

void test_granular_locks_static_stream_buffer_lock_state_protection_vTaskPlaceOnEventListRestricted_blocked_deletion( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventListRestricted_blocked_deletion_test(
        &xStaticStreamBufferHandle->xTaskSpinlock );
}

void test_granular_locks_static_stream_buffer_lock_state_protection_vTaskPlaceOnEventListRestricted_blocked_suspension( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventListRestricted_blocked_suspension_test(
        &xStaticStreamBufferHandle->xTaskSpinlock );
}

void test_granular_locks_static_stream_buffer_lock_state_protection_vTaskPlaceOnEventList_deletion_blocked( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventList_deletion_blocked_test(
        &xStaticStreamBufferHandle->xTaskSpinlock );
}

void test_granular_locks_static_stream_buffer_lock_state_protection_vTaskPlaceOnEventList_suspension_blocked( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventList_suspension_blocked_test(
        &xStaticStreamBufferHandle->xTaskSpinlock );
}

void test_granular_locks_static_stream_buffer_lock_state_protection_vTaskPlaceOnUnorderedEventList_deletion_blocked( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnUnorderedEventList_deletion_blocked_test(
        &xStaticStreamBufferHandle->xTaskSpinlock );
}

void test_granular_locks_static_stream_buffer_lock_state_protection_vTaskPlaceOnUnorderedEventList_suspension_blocked( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnUnorderedEventList_suspension_blocked_test(
        &xStaticStreamBufferHandle->xTaskSpinlock );
}

void test_granular_locks_static_stream_buffer_lock_state_protection_vTaskPlaceOnEventListRestricted_deletion_blocked( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventListRestricted_deletion_blocked_test(
        &xStaticStreamBufferHandle->xTaskSpinlock );
}

void test_granular_locks_static_stream_buffer_lock_state_protection_vTaskPlaceOnEventListRestricted_suspension_blocked( void )
{
    granular_locks_lock_state_protection_vTaskPlaceOnEventListRestricted_suspension_blocked_test(
        &xStaticStreamBufferHandle->xTaskSpinlock );
}
