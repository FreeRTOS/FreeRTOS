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
/*! @file queue_unlock_utest.c */

/* C runtime includes. */
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>

#include "../queue_utest_common.h"

/* Queue includes */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"
#include "queue.h"
#include "mock_fake_port.h"

/* ============================  GLOBAL VARIABLES =========================== */

#define TICKS_TO_WAIT                10
#define NUM_CALLS_TO_INTERCEPT_TX    TICKS_TO_WAIT / 2
#define NUM_CALLS_TO_INTERCEPT_RX    TICKS_TO_WAIT / 2

/* Share QueueHandle_t / QueueSetHandle_t between a test case and it's callbacks */
static QueueHandle_t xQueueHandleStatic;
static QueueSetHandle_t xQueueSetHandleStatic;

/* ==========================  CALLBACK FUNCTIONS =========================== */

/* ============================= Unity Fixtures ============================= */

void setUp( void )
{
    commonSetUp();
    vFakePortAssertIfInterruptPriorityInvalid_Ignore();
    xQueueHandleStatic = NULL;
    xQueueSetHandleStatic = NULL;
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

/* / ** */
/*  *  @brief Callback for test_macro_xQueueSend_blocking_success which empties it's test queue. */
/*  * / */
/* static BaseType_t xQueueSend_locked_xTaskCheckForTimeOutCB( TimeOut_t* const pxTimeOut, */
/*                                                             TickType_t* const pxTicksToWait, */
/*                                                             int cmock_num_calls ) */
/* { */
/*     BaseType_t xReturnValue = td_task_xTaskCheckForTimeOutStub( pxTimeOut, pxTicksToWait, cmock_num_calls ); */

/*     if(cmock_num_calls == NUM_CALLS_TO_INTERCEPT_TX) */
/*     { */
/*         uint32_t checkVal = INVALID_UINT32; */
/*         QueueHandle_t xQueue = xQueueSelectFromSetFromISR( xQueueSetHandleStatic ); */
/*         TEST_ASSERT_NOT_NULL( xQueue ); */
/*         xQueueReceiveFromISR( xQueue, &checkVal, NULL ); */
/*         TEST_ASSERT_EQUAL( getLastMonotonicTestValue(), checkVal ); */
/*     } */
/*     return xReturnValue; */
/* } */

/* void test_macro_xQueueSend_in_set_blocking_success_locked_no_pending( void ) */
/* { */
/*     QueueSetHandle_t xQueueSet = xQueueCreateSet( 1 ); */

/*     QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) ); */

/*     xQueueAddToSet( xQueue, xQueueSet ); */

/*     / * Export for callbacks * / */
/*     xQueueSetHandleStatic = xQueueSet; */

/*     uint32_t testVal = getNextMonotonicTestValue(); */

/*     TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &testVal, 0 ) ); */

/*     xTaskCheckForTimeOut_Stub( &xQueueSend_locked_xTaskCheckForTimeOutCB  ); */
/*     xTaskResumeAll_Stub( &td_task_xTaskResumeAllStub ); */

/*     uint32_t testVal2 = getLastMonotonicTestValue() + 12345; */

/*     TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &testVal2, TICKS_TO_WAIT ) ); */

/*     (void) xQueueRemoveFromSet( xQueue, xQueueSet ); */
/*     vQueueDelete( xQueueSet ); */
/*     vQueueDelete( xQueue ); */
/* } */

/* static BaseType_t xQueueSend_xTaskResumeAllCallback( int cmock_num_calls ) */
/* { */
/*     BaseType_t xReturnValue = td_task_xTaskResumeAllStub( cmock_num_calls ); */
/*     / * If td_task_xTaskResumeAllStub returns pdTRUE, a higher priority task is pending */
/*        Send from an ISR to block * / */
/*     if( pdTRUE == xReturnValue ) */
/*     { */
/*         if(cmock_num_calls == NUM_CALLS_TO_INTERCEPT_TX) */
/*         { */
/*             uint32_t testVal = getNextMonotonicTestValue(); */
/*             (void) xQueueSendFromISR( xQueueHandleStatic, &testVal, NULL ); */
/*         } */
/*     } */
/*     return xReturnValue; */
/* } */

/* / * @coverage prvUnlockQueue * / */
/* void test_macro_xQueueSend_in_set_blocking_fail_locked_high_prio_pending( void ) */
/* { */
/*     QueueSetHandle_t xQueueSet = xQueueCreateSet( 1 ); */

/*     QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) ); */

/*     xQueueAddToSet( xQueue, xQueueSet ); */

/*     / * Export for callbacks * / */
/*     xQueueHandleStatic = xQueue; */
/*     xQueueSetHandleStatic = xQueueSet; */

/*     uint32_t testVal = getNextMonotonicTestValue(); */

/*     TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &testVal, 0 ) ); */

/*     xTaskCheckForTimeOut_Stub( &xQueueSend_locked_xTaskCheckForTimeOutCB  ); */
/*     xTaskResumeAll_Stub( &xQueueSend_xTaskResumeAllCallback ); */

/*     / * this task is lower priority than the pending task * / */
/*     td_task_setFakeTaskPriority( DEFAULT_PRIORITY + 1 ); */

/*     td_task_addFakeTaskWaitingToSendToQueue( xQueue ); */

/*     uint32_t testVal2 = getLastMonotonicTestValue() + 12345; */

/*     TEST_ASSERT_EQUAL( pdFALSE, xQueueSend( xQueue, &testVal2, TICKS_TO_WAIT ) ); */

/*     (void) xQueueRemoveFromSet( xQueue, xQueueSet ); */
/*     vQueueDelete( xQueueSet ); */
/*     vQueueDelete( xQueue ); */
/* } */


/* void test_macro_xQueueSend_in_set_blocking_success_locked_low_prio_pending( void ) */
/* { */
/*     QueueSetHandle_t xQueueSet = xQueueCreateSet( 1 ); */

/*     QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) ); */

/*     xQueueAddToSet( xQueue, xQueueSet ); */

/*     / * Export for callbacks * / */
/*     xQueueHandleStatic = xQueue; */
/*     xQueueSetHandleStatic = xQueueSet; */

/*     uint32_t testVal = getNextMonotonicTestValue(); */

/*     TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &testVal, 0 ) ); */

/*     xTaskCheckForTimeOut_Stub( &xQueueSend_locked_xTaskCheckForTimeOutCB  ); */
/*     xTaskResumeAll_Stub( &xQueueSend_xTaskResumeAllCallback ); */

/*     / * this task is higher priority than the pending task * / */
/*     td_task_setFakeTaskPriority( DEFAULT_PRIORITY - 1 ); */

/*     td_task_addFakeTaskWaitingToSendToQueue( xQueue ); */

/*     uint32_t testVal2 = getLastMonotonicTestValue() + 12345; */

/*     TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &testVal2, TICKS_TO_WAIT ) ); */

/*     (void) xQueueRemoveFromSet( xQueue, xQueueSet ); */
/*     vQueueDelete( xQueueSet ); */
/*     vQueueDelete( xQueue ); */
/* } */

/**
 *  @brief Callback for test_macro_xQueueReceive_blocking_success_locked_no_pending which adds an item to it's test queue.
 */
static BaseType_t xQueueReceive_xTaskCheckForTimeOutCB( TimeOut_t * const pxTimeOut,
                                                        TickType_t * const pxTicksToWait,
                                                        int cmock_num_calls )
{
    BaseType_t xReturnValue = td_task_xTaskCheckForTimeOutStub( pxTimeOut, pxTicksToWait, cmock_num_calls );

    printf( "In xQueueReceive_xTaskCheckForTimeOutCB %d\n", cmock_num_calls );

    if( cmock_num_calls == NUM_CALLS_TO_INTERCEPT_TX )
    {
        uint32_t testVal = getNextMonotonicTestValue();
        printf( "Calling xQueueSendFromISR\n" );
        TEST_ASSERT_TRUE( xQueueSendFromISR( xQueueHandleStatic, &testVal, NULL ) );
    }

    return xReturnValue;
}

void test_macro_xQueueReceive_in_set_blocking_success_locked_no_pending( void )
{
    QueueSetHandle_t xQueueSetOuter = xQueueCreateSet( 1 );
    QueueSetHandle_t xQueueSetInner = xQueueCreateSet( 1 );

    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    printf( "xQueueSetOuter: %lu, xQueueSetInner: %lu, xQueue: %lu\n", ( unsigned long ) xQueueSetOuter, ( unsigned long ) xQueueSetInner, ( unsigned long ) xQueue );


    TEST_ASSERT_TRUE( xQueueAddToSet( xQueueSetInner, xQueueSetOuter ) );

    TEST_ASSERT_TRUE( xQueueAddToSet( xQueue, xQueueSetInner ) );

    /* Export for callbacks */
    xQueueHandleStatic = xQueue;

    xTaskCheckForTimeOut_Stub( &xQueueReceive_xTaskCheckForTimeOutCB );
    xTaskResumeAll_Stub( &td_task_xTaskResumeAllStub );

    uint32_t checkVal = INVALID_UINT32;

    /* printf("Calling xQueueSelectFromSet from OuterSet\n"); */
    /* QueueSetHandle_t xQueueSetFromSet = xQueueSelectFromSet( xQueueSetOuter, TICKS_TO_WAIT ); */

    /* TEST_ASSERT_EQUAL( xQueueSetInner, xQueueSetFromSet ); */

    QueueHandle_t xQueueFromSet = xQueueSelectFromSet( xQueueSetOuter, TICKS_TO_WAIT );

    TEST_ASSERT_EQUAL( xQueue, xQueueFromSet ); /* TODO: assert equality */

    printf( "Calling xQueueReceive\n" );
    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueueFromSet, &checkVal, 0 ) );

    TEST_ASSERT_EQUAL( getLastMonotonicTestValue(), checkVal );

    ( void ) xQueueRemoveFromSet( xQueueSetInner, xQueueSetOuter );
    vQueueDelete( xQueueSetOuter );
    ( void ) xQueueRemoveFromSet( xQueue, xQueueSetInner );
    vQueueDelete( xQueueSetInner );
    vQueueDelete( xQueue );
}

/* static BaseType_t xQueueReceive_xTaskResumeAllCallback( int cmock_num_calls ) */
/* { */
/*     BaseType_t xReturnValue = td_task_xTaskResumeAllStub( cmock_num_calls ); */
/*     / * If td_task_xTaskResumeAllStub returns pdTRUE, a higher priority task is pending */
/*        Receive from an ISR to block * / */

/*     printf("In xQueueReceive_xTaskResumeAllCallback %d\n", cmock_num_calls); */
/*     if( pdTRUE == xReturnValue ) */
/*     { */
/*         if(cmock_num_calls == NUM_CALLS_TO_INTERCEPT_TX) */
/*         { */
/*             uint32_t checkValue = INVALID_UINT32; */
/*             QueueHandle_t xQueue = xQueueSelectFromSetFromISR( xQueueSetHandleStatic ); */
/*             TEST_ASSERT_TRUE( xQueueReceiveFromISR( xQueue, &checkValue, NULL ) ); */
/*             TEST_ASSERT_EQUAL( getLastMonotonicTestValue(), checkValue ); */
/*         } */
/*     } */
/*     return xReturnValue; */
/* } */


/* void test_macro_xQueueReceive_in_set_blocking_success_locked_high_prio_pending( void ) */
/* { */
/*     QueueSetHandle_t xQueueSet = xQueueCreateSet( 1 ); */

/*     QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) ); */

/*     xQueueAddToSet( xQueue, xQueueSet ); */

/*     / * Export for callbacks * / */
/*     xQueueHandleStatic = xQueue; */
/*     xQueueSetHandleStatic = xQueueSet; */

/*     xTaskCheckForTimeOut_Stub( &xQueueReceive_xTaskCheckForTimeOutCB  ); */
/*     xTaskResumeAll_Stub( &xQueueReceive_xTaskResumeAllCallback ); */

/*     td_task_setFakeTaskPriority( DEFAULT_PRIORITY + 1 ); */

/*     td_task_addFakeTaskWaitingToReceiveFromQueue( xQueueSet ); */

/*     QueueHandle_t xQueueFromSet = xQueueSelectFromSet( xQueueSet, TICKS_TO_WAIT ); */

/*     TEST_ASSERT_EQUAL( NULL, xQueueFromSet ); */

/*     (void) xQueueRemoveFromSet( xQueue, xQueueSet ); */
/*     vQueueDelete( xQueueSet ); */
/*     vQueueDelete( xQueue ); */
/* } */


/* void test_macro_xQueueReceive_in_set_blocking_success_locked_low_prio_pending( void ) */
/* { */
/*     QueueSetHandle_t xQueueSet = xQueueCreateSet( 1 ); */

/*     QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) ); */

/*     xQueueAddToSet( xQueue, xQueueSet ); */

/*     / * Export for callbacks * / */
/*     xQueueHandleStatic = xQueue; */
/*     xQueueSetHandleStatic = xQueueSet; */

/*     xTaskCheckForTimeOut_Stub( &xQueueReceive_xTaskCheckForTimeOutCB  ); */
/*     xTaskResumeAll_Stub( &xQueueReceive_xTaskResumeAllCallback ); */

/*     td_task_setFakeTaskPriority( DEFAULT_PRIORITY - 1 ); */

/*     td_task_addFakeTaskWaitingToReceiveFromQueue( xQueueSet ); */

/*     uint32_t checkVal = INVALID_UINT32; */

/*     QueueHandle_t xQueueFromSet = xQueueSelectFromSet( xQueueSet, TICKS_TO_WAIT ); */

/*     TEST_ASSERT_NOT_NULL( xQueueFromSet ); */

/*     TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueueFromSet, &checkVal, TICKS_TO_WAIT ) ); */

/*     TEST_ASSERT_EQUAL( getLastMonotonicTestValue(), checkVal ); */

/*     (void) xQueueRemoveFromSet( xQueue, xQueueSet ); */
/*     vQueueDelete( xQueueSet ); */
/*     vQueueDelete( xQueue ); */
/* } */
