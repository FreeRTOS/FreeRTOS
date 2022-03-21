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
/*! @file semaphore_in_set_utest.c */

/* C runtime includes. */
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>

#include "../queue_utest_common.h"

/* Queue includes */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"
#include "semphr.h"
#include "mock_fake_port.h"

/* ============================  GLOBAL VARIABLES =========================== */

/* ==========================  CALLBACK FUNCTIONS =========================== */

/* ============================= Unity Fixtures ============================= */

void setUp( void )
{
    commonSetUp();
}

void tearDown( void )
{
    commonTearDown();
}

void suiteSetUp()
{
    commonSuiteSetUp();
}

int suiteTearDown( int numFailures )
{
    return commonSuiteTearDown( numFailures );
}

/* ==========================  Helper functions =========================== */

/* ==========================  Test Cases =========================== */

/**
 * @brief Test xSemaphoreGiveFromISR with a higher priority task waiting and a null pointer for pxHigherPriorityTaskWoken
 * @details Test xSemaphoreGiveFromISR on a queue that is in a Queue Set with a higher priority task waiting.
 *  Verify that a null pxHigherPriorityTaskWoken is handled correctly.
 * @coverage xQueueGiveFromISR
 */
void test_macro_xSemaphoreGiveFromISR_in_set_high_priority_pending_null_ptr( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateBinary();

    QueueSetHandle_t xQueueSet = xQueueCreateSet( 1 );

    xQueueAddToSet( xSemaphore, xQueueSet );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();

    /* Insert an item into the event list */
    td_task_setFakeTaskPriority( DEFAULT_PRIORITY + 1 );
    td_task_addFakeTaskWaitingToReceiveFromQueue( xQueueSet );

    /* Give the semaphore */
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreGiveFromISR( xSemaphore, NULL ) );

    TEST_ASSERT_EQUAL( pdTRUE, td_task_getYieldPending() );

    SemaphoreHandle_t xSemaphoreTemp = xQueueSelectFromSet( xQueueSet, 0 );

    TEST_ASSERT_EQUAL( B_SEMPHR_AVAILABLE, uxSemaphoreGetCount( xSemaphoreTemp ) );

    vSemaphoreDelete( xSemaphore );
    vQueueDelete( xQueueSet );
}

/**
 * @brief Test xSemaphoreGiveFromISR with a higher priority task waiting on a queue in and Queue Set
 * @details Test xSemaphoreGiveFromISR with a higher priority task waiting and
 *  verifies that xHigherPriorityTaskWoken is set accordingly.
 * @coverage xQueueGiveFromISR
 */
void test_macro_xSemaphoreGiveFromISR_in_set_high_priority_pending( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateBinary();

    QueueSetHandle_t xQueueSet = xQueueCreateSet( 1 );

    xQueueAddToSet( xSemaphore, xQueueSet );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();

    /* Insert an item into the event list */
    td_task_setFakeTaskPriority( DEFAULT_PRIORITY + 1 );
    td_task_addFakeTaskWaitingToReceiveFromQueue( xQueueSet );

    BaseType_t xHigherPriorityTaskWoken = pdFALSE;

    /* Give the semaphore */
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreGiveFromISR( xSemaphore, &xHigherPriorityTaskWoken ) );

    TEST_ASSERT_EQUAL( pdTRUE, xHigherPriorityTaskWoken );

    TEST_ASSERT_EQUAL( pdTRUE, td_task_getYieldPending() );

    SemaphoreHandle_t xSemaphoreTemp = xQueueSelectFromSet( xQueueSet, 0 );

    TEST_ASSERT_EQUAL( B_SEMPHR_AVAILABLE, uxSemaphoreGetCount( xSemaphoreTemp ) );

    vSemaphoreDelete( xSemaphore );
    vQueueDelete( xQueueSet );
}

/**
 * @brief Test xSemaphoreGiveFromISR with a lower priority task waiting on a queue in a Queue Set
 * @details Test xSemaphoreGiveFromISR on a Queeu in a Queue Set with a lower priority task waiting and
 *  verify that xHigherPriorityTaskWoken is not modified.
 * @coverage xQueueGiveFromISR
 */
void test_macro_xSemaphoreGiveFromISR_in_set_low_priority_pending( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateBinary();

    QueueSetHandle_t xQueueSet = xQueueCreateSet( 1 );

    xQueueAddToSet( xSemaphore, xQueueSet );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();

    /* Insert an item into the event list */
    td_task_setFakeTaskPriority( DEFAULT_PRIORITY - 1 );
    td_task_addFakeTaskWaitingToReceiveFromQueue( xQueueSet );

    BaseType_t xHigherPriorityTaskWoken = pdFALSE;

    /* Give the semaphore */
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreGiveFromISR( xSemaphore, &xHigherPriorityTaskWoken ) );

    TEST_ASSERT_EQUAL( pdFALSE, xHigherPriorityTaskWoken );

    TEST_ASSERT_EQUAL( pdFALSE, td_task_getYieldPending() );

    SemaphoreHandle_t xSemaphoreTemp = xQueueSelectFromSet( xQueueSet, 0 );

    TEST_ASSERT_EQUAL( B_SEMPHR_AVAILABLE, uxSemaphoreGetCount( xSemaphoreTemp ) );

    vSemaphoreDelete( xSemaphore );
    vQueueDelete( xQueueSet );
}

/**
 * @brief Test xSemaphoreGiveFromISR on a queue in a Queue Set with no tasks waiting
 * @details Test xSemaphoreGiveFromISR on a Queue in a Queue Set no tasks waiting and verify that xHigherPriorityTaskWoken is not modified.
 * @coverage xQueueGiveFromISR
 */
void test_macro_xSemaphoreGiveFromISR_in_set_no_pending( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateBinary();

    QueueSetHandle_t xQueueSet = xQueueCreateSet( 1 );

    xQueueAddToSet( xSemaphore, xQueueSet );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();

    BaseType_t xHigherPriorityTaskWoken = pdFALSE;

    /* Give the semaphore */
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreGiveFromISR( xSemaphore, &xHigherPriorityTaskWoken ) );

    TEST_ASSERT_EQUAL( pdFALSE, xHigherPriorityTaskWoken );

    SemaphoreHandle_t xSemaphoreTemp = xQueueSelectFromSet( xQueueSet, 0 );

    TEST_ASSERT_EQUAL( B_SEMPHR_AVAILABLE, uxSemaphoreGetCount( xSemaphoreTemp ) );

    vSemaphoreDelete( xSemaphore );
    vQueueDelete( xQueueSet );
}
