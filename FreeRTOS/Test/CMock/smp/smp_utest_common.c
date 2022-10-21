/*
 * FreeRTOS V202112.00
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
/*! @file smp_utest_common.c */

#include "smp_utest_common.h"

/* C runtime includes. */
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>

/* Test includes */
#include "task.h"
#include "global_vars.h"

/* Unity includes. */
#include "unity.h"
#include "unity_memory.h"

/* Mock includes. */
#include "mock_fake_assert.h"
#include "mock_fake_port.h"
#include "mock_timers.h"

/* ===========================  EXTERN VARIABLES  =========================== */

extern List_t pxReadyTasksLists[ configMAX_PRIORITIES ];
extern List_t xDelayedTaskList1;
extern List_t xDelayedTaskList2;
extern volatile UBaseType_t uxDeletedTasksWaitingCleanUp;
extern volatile UBaseType_t uxCurrentNumberOfTasks;
extern volatile TickType_t xTickCount;
extern volatile UBaseType_t uxTopReadyPriority;
extern volatile BaseType_t xSchedulerRunning;
extern volatile TickType_t xPendedTicks;
extern volatile BaseType_t xNumOfOverflows;
extern volatile TickType_t xNextTaskUnblockTime;
extern UBaseType_t uxTaskNumber;
extern TaskHandle_t xIdleTaskHandles[configNUM_CORES];
extern volatile UBaseType_t uxSchedulerSuspended;
extern volatile UBaseType_t uxDeletedTasksWaitingCleanUp;
extern List_t * volatile pxDelayedTaskList;
extern volatile TCB_t *  pxCurrentTCBs[ configNUM_CORES ];

/* ==========================  CALLBACK FUNCTIONS  ========================== */

void * pvPortMalloc( size_t xSize )
{
    return unity_malloc( xSize );
}

void vPortFree( void * pv )
{
    return unity_free( pv );
}

StackType_t * pxPortInitialiseStack( StackType_t * pxTopOfStack,
                                             TaskFunction_t pxCode,
                                             void * pvParameters )
{
    return pxTopOfStack;
}

BaseType_t xPortStartScheduler( void )
{
    uint8_t i;

    /* Initialize each core with a task */
    for (i = 0; i < configNUM_CORES; i++) {
        vTaskSwitchContextForCore(i);
    }

    return pdTRUE;
}

void vPortEndScheduler( void )
{
    return;
}

void vFakePortYieldCoreStubCallback( int xCoreID, int cmock_num_calls )
{
    vTaskSwitchContextForCore( xCoreID );
}

void vFakePortYieldStubCallback( int cmock_num_calls )
{
    uint8_t i;

    for (i = 0; i < configNUM_CORES; i++) {
        vTaskSwitchContextForCore(i);
    }
}

/* ============================= Unity Fixtures ============================= */

void commonSetUp( void )
{

    vFakePortYieldCore_StubWithCallback( vFakePortYieldCoreStubCallback) ;
    vFakePortYield_StubWithCallback( vFakePortYieldStubCallback );

    vFakeAssert_Ignore();
    vFakePortEnterCriticalSection_Ignore();
    vFakePortExitCriticalSection_Ignore();

    vFakePortGetTaskLock_Ignore();
    vFakePortGetISRLock_Ignore();
    vFakePortDisableInterrupts_IgnoreAndReturn(1);
    vFakePortGetCoreID_IgnoreAndReturn(0);
    vFakePortRestoreInterrupts_Ignore();
    xTimerCreateTimerTask_IgnoreAndReturn(1);
    vFakePortReleaseISRLock_Ignore();
    vFakePortReleaseTaskLock_Ignore();
    vFakePortCheckIfInISR_IgnoreAndReturn(0);
    vPortCurrentTaskDying_Ignore();
    portSetupTCB_CB_Ignore();
    ulFakePortSetInterruptMask_IgnoreAndReturn(0);
    vFakePortClearInterruptMask_Ignore();

    memset( &pxReadyTasksLists, 0x00, configMAX_PRIORITIES * sizeof( List_t ) );
    memset( &xDelayedTaskList1, 0x00, sizeof( List_t ) );
    memset( &xDelayedTaskList2, 0x00, sizeof( List_t ) );
    memset( &xIdleTaskHandles, 0x00, (configNUM_CORES * sizeof( TaskHandle_t )) );
    memset( &pxCurrentTCBs, 0x00, (configNUM_CORES * sizeof( TCB_t * )) );

    uxDeletedTasksWaitingCleanUp = 0;
    uxCurrentNumberOfTasks = ( UBaseType_t ) 0U;
    xTickCount = ( TickType_t ) 500; /* configINITIAL_TICK_COUNT */
    uxTopReadyPriority = tskIDLE_PRIORITY;
    xSchedulerRunning = pdFALSE;
    xPendedTicks = ( TickType_t ) 0U;
    xNumOfOverflows = ( BaseType_t ) 0;
    uxTaskNumber = ( UBaseType_t ) 0U;
    xNextTaskUnblockTime = ( TickType_t ) 0U;
    uxSchedulerSuspended = ( UBaseType_t ) 0;
    uxDeletedTasksWaitingCleanUp = 0;
    pxDelayedTaskList = NULL;
}

void commonTearDown( void )
{

}

/* ==========================  Helper functions =========================== */

void vSmpTestTask( void *pvParameters )
{
}

void verifySmpTask( TaskHandle_t * xTaskHandle, eTaskState eCurrentState, TaskRunning_t xTaskRunState)
{
    TaskStatus_t xTaskDetails;

    vTaskGetInfo(*xTaskHandle, &xTaskDetails, pdTRUE, eInvalid );
    TEST_ASSERT_EQUAL_INT_MESSAGE( xTaskRunState, xTaskDetails.xHandle->xTaskRunState, "Task Verification Failed: Incorrect xTaskRunState" );
    TEST_ASSERT_EQUAL_INT_MESSAGE( eCurrentState, xTaskDetails.eCurrentState, "Task Verification Failed: Incorrect eCurrentState" );
}

void verifyIdleTask( BaseType_t index, TaskRunning_t xTaskRunState)
{
    TaskStatus_t xTaskDetails;
    int ret;

    vTaskGetInfo(xIdleTaskHandles[index], &xTaskDetails, pdTRUE, eInvalid );
    ret = strncmp( xTaskDetails.xHandle->pcTaskName, "IDLE", 4 );
    TEST_ASSERT_EQUAL_INT_MESSAGE( 0, ret, "Idle Task Verification Failed: Incorrect task name" );
    TEST_ASSERT_EQUAL_INT_MESSAGE( pdTRUE, xTaskDetails.xHandle->xIsIdle, "Idle Task Verification Failed: Incorrect xIsIdle" );
    TEST_ASSERT_EQUAL_INT_MESSAGE( xTaskRunState, xTaskDetails.xHandle->xTaskRunState, "Idle Task Verification Failed: Incorrect xTaskRunState" );
    TEST_ASSERT_EQUAL_INT_MESSAGE( eRunning, xTaskDetails.eCurrentState, "Idle Task Verification Failed: Incorrect eCurrentState" );
}
