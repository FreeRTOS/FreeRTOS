/*
 * FreeRTOS V202111.00
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
/*! @file td_task.c */

#include "queue_utest_common.h"

/* Test includes. */
#include "unity.h"

/* Mock includes. */
#include "mock_task.h"
#include "mock_fake_port.h"


/* ============================  GLOBAL VARIABLES =========================== */
static BaseType_t xSchedulerState = taskSCHEDULER_RUNNING;
static ListItem_t taskListItem;
static ListItem_t fakeTaskListItem;
static TickType_t xTickCount = 0;
static BaseType_t xYieldPending = pdFALSE;
static BaseType_t xYieldCount = 0;
static BaseType_t xPortYieldCount = 0;
static BaseType_t xPortYieldFromISRCount = 0;
static BaseType_t xPortYieldWithinAPICount = 0;
static BaseType_t xTaskMissedYieldCount = 0;
static BaseType_t xYieldFromTaskResumeAllCount = 0;

/* ==========================  CALLBACK FUNCTIONS =========================== */

static BaseType_t xTaskGetSchedulerStateStub( int num_calls )
{
    return xSchedulerState;
}

static void vTaskSuspendAllStub( int cmock_num_calls )
{
    TEST_ASSERT_EQUAL_MESSAGE( taskSCHEDULER_RUNNING, xSchedulerState, "vTaskSuspendAll called with scheduler suspended." );
    xSchedulerState = taskSCHEDULER_SUSPENDED;
}

void td_task_vTaskSuspendAllStubNoCheck( int cmock_num_calls )
{
    xSchedulerState = taskSCHEDULER_SUSPENDED;
}

static void vTaskMissedYieldStub( int cmock_num_calls )
{
    TEST_ASSERT_TRUE_MESSAGE( ( td_task_getFakeTaskPriority() >= DEFAULT_PRIORITY ), "A Missed Yield should only occur when a higher priority task is pending." );
    xTaskMissedYieldCount++;
    xYieldPending = pdTRUE;
}

BaseType_t td_task_xTaskResumeAllStub( int cmock_num_calls )
{
    BaseType_t xDidYield = pdFALSE;

    TEST_ASSERT_EQUAL_MESSAGE( taskSCHEDULER_SUSPENDED, xSchedulerState, "xTaskResumeAll called with scheduler running." );

    xSchedulerState = taskSCHEDULER_RUNNING;

    if( ( td_task_getFakeTaskPriority() >= DEFAULT_PRIORITY ) &&
        ( listLIST_ITEM_CONTAINER( &fakeTaskListItem ) != NULL ) )
    {
        xYieldPending = pdTRUE;
    }

    if( xYieldPending )
    {
        #if ( configUSE_PREEMPTION == 1 )
            xDidYield = pdTRUE;
            xYieldCount++;
            xYieldFromTaskResumeAllCount++;
            xYieldPending = pdFALSE;
        #endif
    }

    /* Remove task from blocked list */
    if( listLIST_ITEM_CONTAINER( &taskListItem ) )
    {
        uxListRemove( &taskListItem );
    }

    return xDidYield;
}

static void vPortYieldStub( int cmock_num_calls )
{
    xYieldCount++;
    xPortYieldCount++;
    xYieldPending = pdFALSE;
}

static void vPortYieldFromISRStub( int cmock_num_calls )
{
    xYieldCount++;
    xPortYieldFromISRCount++;
    xYieldPending = pdFALSE;
}

void td_task_vPortYieldWithinAPIStub( int cmock_num_calls )
{
    xYieldCount++;
    xPortYieldWithinAPICount++;
    xYieldPending = pdFALSE;
}

/* Timeout handling callbacks */
static void vTaskInternalSetTimeOutStateStub( TimeOut_t * const pxTimeOut,
                                              int cmock_num_calls )
{
    pxTimeOut->xOverflowCount = 0;
    pxTimeOut->xTimeOnEntering = xTickCount;
}

BaseType_t td_task_xTaskCheckForTimeOutStub( TimeOut_t * const pxTimeOut,
                                             TickType_t * const pxTicksToWait,
                                             int cmock_num_calls )
{
    BaseType_t xReturnValue = pdFALSE;

    xTickCount++;

    if( ( xTickCount - pxTimeOut->xTimeOnEntering ) > *pxTicksToWait )
    {
        xReturnValue = pdTRUE;
    }

    return xReturnValue;
}

/* Sorted Event list related */
static BaseType_t xTaskRemoveFromEventListStub( const List_t * const pxEventList,
                                                int cmock_num_calls )
{
    BaseType_t xReturnValue = pdFALSE;

    /* check that xTaskRemoveFromEventList was called from within a critical section */
    TEST_ASSERT_TRUE_MESSAGE( td_port_isInCriticalSection(), "xTaskRemoveFromEventList was called outside of a critical section." );

    ListItem_t * pxItem = listGET_HEAD_ENTRY( pxEventList );

    TickType_t xItemPriority = ( configMAX_PRIORITIES - listGET_LIST_ITEM_VALUE( pxItem ) );

    ( void ) uxListRemove( pxItem );

    xReturnValue = ( xItemPriority > DEFAULT_PRIORITY );

    xYieldPending |= xReturnValue;

    return( xReturnValue );
}



static void vTaskPlaceOnEventListStub( List_t * const pxEventList,
                                       const TickType_t xTicksToWait,
                                       int cmock_num_calls )
{
    if( listLIST_ITEM_CONTAINER( &taskListItem ) )
    {
        uxListRemove( &taskListItem );
    }

    listSET_LIST_ITEM_VALUE( &taskListItem, ( configMAX_PRIORITIES - DEFAULT_PRIORITY ) );

    vListInsert( pxEventList, &taskListItem );
}

/* ============================= Unity Fixtures ============================= */


/* ==========================  Helper functions ============================= */


void td_task_register_stubs( void )
{
    /* Initialize local static variables */
    xSchedulerState = taskSCHEDULER_RUNNING;
    xTickCount = 0;
    vListInitialiseItem( &taskListItem );
    listSET_LIST_ITEM_VALUE( &taskListItem, configMAX_PRIORITIES - DEFAULT_PRIORITY );
    vListInitialiseItem( &fakeTaskListItem );
    listSET_LIST_ITEM_VALUE( &fakeTaskListItem, configMAX_PRIORITIES - DEFAULT_PRIORITY );
    xYieldPending = pdFALSE;
    xYieldCount = 0;
    xPortYieldCount = 0;
    xPortYieldFromISRCount = 0;
    xPortYieldWithinAPICount = 0;
    xTaskMissedYieldCount = 0;
    xYieldFromTaskResumeAllCount = 0;

    /* Setup stubs */
    vFakePortYield_Stub( &vPortYieldStub );
    vFakePortYieldFromISR_Stub( &vPortYieldFromISRStub );
    vFakePortYieldWithinAPI_Stub( &td_task_vPortYieldWithinAPIStub );

    xTaskGetSchedulerState_Stub( &xTaskGetSchedulerStateStub );
    vTaskSuspendAll_Stub( &vTaskSuspendAllStub );
    vTaskMissedYield_Stub( &vTaskMissedYieldStub );
    xTaskResumeAll_Stub( &td_task_xTaskResumeAllStub );

    vTaskInternalSetTimeOutState_Stub( &vTaskInternalSetTimeOutStateStub );
    xTaskCheckForTimeOut_Stub( &td_task_xTaskCheckForTimeOutStub );

    xTaskRemoveFromEventList_Stub( &xTaskRemoveFromEventListStub );
    vTaskPlaceOnEventList_Stub( &vTaskPlaceOnEventListStub );
}

void td_task_setSchedulerState( BaseType_t state )
{
    xSchedulerState = state;
}

void td_task_teardown_check( void )
{
    /* Assertions to run at the end of the test case */
    TEST_ASSERT_EQUAL_MESSAGE( taskSCHEDULER_RUNNING, xSchedulerState, "Test case ended with the scheduler suspended." );

    TEST_ASSERT_EQUAL_MESSAGE( 0, xYieldCount, "Test case ended with xYieldCount > 0" );
    TEST_ASSERT_EQUAL_MESSAGE( 0, xPortYieldCount, "Test case ended with xPortYieldCount > 0" );
    TEST_ASSERT_EQUAL_MESSAGE( 0, xPortYieldFromISRCount, "Test case ended with xPortYieldFromISRCount > 0" );
    TEST_ASSERT_EQUAL_MESSAGE( 0, xPortYieldWithinAPICount, "Test case ended with xPortYieldWithinAPICount > 0" );
    TEST_ASSERT_EQUAL_MESSAGE( 0, xYieldFromTaskResumeAllCount, "Test case ended with xYieldFromTaskResumeAllCount > 0" );
    TEST_ASSERT_EQUAL_MESSAGE( 0, xTaskMissedYieldCount, "Test case ended with xTaskMissedYieldCount > 0" );
    TEST_ASSERT_EQUAL_MESSAGE( pdFALSE, xYieldPending, "Test case ended with xYieldPending != pdFALSE" );
}

void td_task_setFakeTaskPriority( TickType_t priority )
{
    fakeTaskListItem.xItemValue = ( configMAX_PRIORITIES - priority );
    List_t * pxContainer = listLIST_ITEM_CONTAINER( &fakeTaskListItem );

    if( pxContainer != NULL )
    {
        uxListRemove( &fakeTaskListItem );
        vListInsert( pxContainer, &fakeTaskListItem );
    }
}

void td_task_addFakeTaskWaitingToSendToQueue( QueueHandle_t xQueue )
{
    StaticQueue_t * pxQueue = ( StaticQueue_t * ) xQueue;
    List_t * pxTasksWaitingToSend = ( List_t * ) &( pxQueue->xDummy3[ 0 ] );

    if( listLIST_ITEM_CONTAINER( &fakeTaskListItem ) )
    {
        uxListRemove( &fakeTaskListItem );
    }

    fakeTaskListItem.pvOwner = NULL;

    vListInsert( pxTasksWaitingToSend, &fakeTaskListItem );
}

void td_task_addFakeTaskWaitingToReceiveFromQueue( QueueHandle_t xQueue )
{
    StaticQueue_t * pxQueue = ( StaticQueue_t * ) xQueue;
    List_t * pxTasksWaitingToReceive = ( List_t * ) &( pxQueue->xDummy3[ 1 ] );

    if( listLIST_ITEM_CONTAINER( &fakeTaskListItem ) )
    {
        uxListRemove( &fakeTaskListItem );
    }

    fakeTaskListItem.pvOwner = NULL;

    vListInsert( pxTasksWaitingToReceive, &fakeTaskListItem );
}

TickType_t td_task_getFakeTaskPriority( void )
{
    return( configMAX_PRIORITIES - fakeTaskListItem.xItemValue );
}

BaseType_t td_task_getYieldCount( void )
{
    BaseType_t xReturnValue = xYieldCount;

    xYieldCount = 0;
    return xReturnValue;
}

BaseType_t td_task_getCount_vPortYield( void )
{
    BaseType_t xReturnValue = xPortYieldCount;

    xPortYieldCount = 0;
    return xReturnValue;
}

BaseType_t td_task_getCount_vPortYieldFromISR( void )
{
    BaseType_t xReturnValue = xPortYieldFromISRCount;

    xPortYieldFromISRCount = 0;
    return xReturnValue;
}

BaseType_t td_task_getCount_vPortYieldWithinAPI( void )
{
    BaseType_t xReturnValue = xPortYieldWithinAPICount;

    xPortYieldWithinAPICount = 0;
    return xReturnValue;
}

BaseType_t td_task_getCount_vTaskMissedYield( void )
{
    BaseType_t xReturnValue = xTaskMissedYieldCount;

    xTaskMissedYieldCount = 0;
    return xReturnValue;
}

BaseType_t td_task_getCount_YieldFromTaskResumeAll( void )
{
    BaseType_t xReturnValue = xYieldFromTaskResumeAllCount;

    xYieldFromTaskResumeAllCount = 0;
    return xReturnValue;
}

BaseType_t td_task_getYieldPending( void )
{
    BaseType_t xReturnValue = xYieldPending;

    xYieldPending = pdFALSE;
    return xReturnValue;
}
