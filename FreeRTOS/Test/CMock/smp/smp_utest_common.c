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
extern TaskHandle_t xIdleTaskHandles[ configNUMBER_OF_CORES ];
extern volatile UBaseType_t uxSchedulerSuspended;
extern volatile UBaseType_t uxDeletedTasksWaitingCleanUp;
extern List_t * volatile pxDelayedTaskList;
extern volatile TCB_t * pxCurrentTCBs[ configNUMBER_OF_CORES ];
extern volatile BaseType_t xYieldPendings[ configNUMBER_OF_CORES ];

static BaseType_t xCoreYields[ configNUMBER_OF_CORES ] = { 0 };

/* portGET_CORE_ID() returns the xCurrentCoreId. The task choose order is dependent on
 * which core calls the FreeRTOS APIs. Setup xCurrentCoreId is required before calling
 * FreeRTOS APIs. The default core is 0. */
static BaseType_t xCurrentCoreId = 0;

/* Each core maintains it's lock count. However, only one core has lock count value > 0.
 * In real world case, this value is read when interrupt disabled while increased when
 * lock is acquired. */
static BaseType_t xIsrLockCount[ configNUMBER_OF_CORES ] = { 0 };
static BaseType_t xTaskLockCount[ configNUMBER_OF_CORES ] = { 0 };

/* ==========================  EXTERN FUNCTIONS  ========================== */

extern void vTaskEnterCritical( void );
extern void vTaskExitCritical( void );
extern UBaseType_t vTaskEnterCriticalFromISR( void );
extern void vTaskExitCriticalFromISR( UBaseType_t uxSavedInterruptStatus );

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
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        vTaskSwitchContext( i );
    }

    return pdTRUE;
}

void vPortEndScheduler( void )
{
}

void vFakePortYieldCoreStubCallback( int xCoreID,
                                     int cmock_num_calls )
{
    BaseType_t xCoreInCritical = pdFALSE;
    BaseType_t xPreviousCoreId = xCurrentCoreId;
    int i;

    /* Check if the lock is acquired by any core. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        if( ( xIsrLockCount[ i ] > 0 ) || ( xTaskLockCount[ i ] > 0 ) )
        {
            xCoreInCritical = pdTRUE;
            break;
        }
    }

    if( xCoreInCritical == pdTRUE )
    {
        /* If a is in the critical section, pend the core yield until the
         * task spinlock is released. */
        xCoreYields[ xCoreID ] = pdTRUE;
    }
    else
    {
        /* No task is in the critical section. We can yield this core. */
        xCurrentCoreId = xCoreID;
        vTaskSwitchContext( xCurrentCoreId );
        xCurrentCoreId = xPreviousCoreId;
    }
}

void vFakePortYieldCoreAsyncStubCallback( int xCoreID,
                                          int cmock_num_calls )
{
    ( void ) cmock_num_calls;

    xCoreYields[ xCoreID ] = pdTRUE;
}

void vFakePortYieldStubCallback( int cmock_num_calls )
{
    vTaskSwitchContext( xCurrentCoreId );
}

void vFakePortEnterCriticalSectionCallback( int cmock_num_calls )
{
    vTaskEnterCritical();
}

/* vTaskExitCritical release the lock then check if this task is requested to yield.
 * The mock implementation assumes all the cores can be requested to yield immediately.
 * If the core is requested to yield, it will yield in the following order.
 * 1. core ID in accsending order if the core is requested to yield and is not xCurrentCoreId.
 * 2. core ID which is requested to yield and the core ID equals xCurrentCoreId.
 * core i : Core ID requested to yield in critical section in acesending order.
 * ....
 * core xCurrentCoreId : Core ID equals to xCurrentCoreId and is requested to yield in critical section. */
void vFakePortExitCriticalSectionCallback( int cmock_num_calls )
{
    vTaskExitCritical();
}

void vSetCurrentCore( BaseType_t xCoreID )
{
    xCurrentCoreId = xCoreID;
}

void vCheckAndExecuteAsyncCoreYield( BaseType_t xCoreID )
{
    BaseType_t xCoreInCritical = pdFALSE;
    BaseType_t xPreviousCoreId = xCurrentCoreId;
    int i;

    if( xCoreYields[ xCoreID ] != pdFALSE )
    {
        /* Check if the lock is acquired by any core. */
        for( i = 0; i < configNUMBER_OF_CORES; i++ )
        {
            if( ( xIsrLockCount[ i ] > 0 ) || ( xTaskLockCount[ i ] > 0 ) )
            {
                xCoreInCritical = pdTRUE;
                break;
            }
        }

        if( xCoreInCritical != pdTRUE )
        {
            /* No task is in the critical section. We can yield this core. */
            xCurrentCoreId = xCoreID;
            vTaskSwitchContext( xCurrentCoreId );
            xCurrentCoreId = xPreviousCoreId;
        }
    }
}

static void vYieldCores( void )
{
    BaseType_t i;
    BaseType_t xPreviousCoreId = xCurrentCoreId;

    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        if( xCoreYields[ i ] == pdTRUE )
        {
            xCurrentCoreId = i;
            xCoreYields[ i ] = pdFALSE;
            vTaskSwitchContext( i );
        }
    }

    xCurrentCoreId = xPreviousCoreId;
}

unsigned int vFakePortGetCoreIDCallback( int cmock_num_calls )
{
    return ( unsigned int ) xCurrentCoreId;
}

void vFakePortGetISRLockCallback( int cmock_num_calls )
{
    int i;

    ( void ) cmock_num_calls;

    /* Ensure that no other core is in the critical section. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        if( i != xCurrentCoreId )
        {
            TEST_ASSERT_MESSAGE( xIsrLockCount[ i ] == 0, "vFakePortGetISRLock xIsrLockCount[ i ] > 0" );
            TEST_ASSERT_MESSAGE( xTaskLockCount[ i ] == 0, "vFakePortGetISRLock xTaskLockCount[ i ] > 0" );
        }
    }

    xIsrLockCount[ xCurrentCoreId ]++;
}

void vFakePortReleaseISRLockCallback( int cmock_num_calls )
{
    ( void ) cmock_num_calls;

    TEST_ASSERT_MESSAGE( xIsrLockCount[ xCurrentCoreId ] > 0, "xIsrLockCount[ xCurrentCoreId ] <= 0" );
    xIsrLockCount[ xCurrentCoreId ]--;
}

void vFakePortGetTaskLockCallback( int cmock_num_calls )
{
    int i;

    ( void ) cmock_num_calls;

    /* Ensure that no other core is in the critical section. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        if( i != xCurrentCoreId )
        {
            TEST_ASSERT_MESSAGE( xIsrLockCount[ i ] == 0, "vFakePortGetTaskLock xIsrLockCount[ i ] > 0" );
            TEST_ASSERT_MESSAGE( xTaskLockCount[ i ] == 0, "vFakePortGetTaskLock xTaskLockCount[ i ] > 0" );
        }
    }

    xTaskLockCount[ xCurrentCoreId ]++;
}

void vFakePortReleaseTaskLockCallback( int cmock_num_calls )
{
    ( void ) cmock_num_calls;

    TEST_ASSERT_MESSAGE( xTaskLockCount[ xCurrentCoreId ] > 0, "xTaskLockCount[ xCurrentCoreId ] <= 0" );
    xTaskLockCount[ xCurrentCoreId ]--;

    /* When releasing the ISR lock, check if any core is waiting to yield. */
    if( xTaskLockCount[ xCurrentCoreId ] == 0 )
    {
        vYieldCores();
    }
}

void vFakePortReleaseTaskLockAsyncCallback( int cmock_num_calls )
{
    ( void ) cmock_num_calls;

    TEST_ASSERT_MESSAGE( xTaskLockCount[ xCurrentCoreId ] > 0, "xTaskLockCount[ xCurrentCoreId ] <= 0" );
    xTaskLockCount[ xCurrentCoreId ]--;
}

portBASE_TYPE vFakePortEnterCriticalFromISRCallback( int cmock_num_calls )
{
    portBASE_TYPE xSavedInterruptState;

    xSavedInterruptState = vTaskEnterCriticalFromISR();
    return xSavedInterruptState;
}

void vFakePortExitCriticalFromISRCallback( portBASE_TYPE xSavedInterruptState,
                                           int cmock_num_calls )
{
    vTaskExitCriticalFromISR( xSavedInterruptState );
    /* Simulate yield cores when leaving the critical section. */
    vYieldCores();
}

void vFakePortExitCriticalFromISRAsyncCallback( portBASE_TYPE xSavedInterruptState,
                                                int cmock_num_calls )
{
    vTaskExitCriticalFromISR( xSavedInterruptState );
}

/* ============================= Unity Fixtures ============================= */

void commonSetUp( void )
{
    vFakePortYieldCore_StubWithCallback( vFakePortYieldCoreStubCallback );
    vFakePortYield_StubWithCallback( vFakePortYieldStubCallback );

    vFakePortEnterCriticalSection_StubWithCallback( vFakePortEnterCriticalSectionCallback );
    vFakePortExitCriticalSection_StubWithCallback( vFakePortExitCriticalSectionCallback );

    vFakePortEnterCriticalFromISR_StubWithCallback( vFakePortEnterCriticalFromISRCallback );
    vFakePortExitCriticalFromISR_StubWithCallback( vFakePortExitCriticalFromISRCallback );

    vFakePortGetCoreID_StubWithCallback( vFakePortGetCoreIDCallback );

    vFakePortGetISRLock_StubWithCallback( vFakePortGetISRLockCallback );
    vFakePortGetTaskLock_StubWithCallback( vFakePortGetTaskLockCallback );
    vFakePortReleaseISRLock_StubWithCallback( vFakePortReleaseISRLockCallback );
    vFakePortReleaseTaskLock_StubWithCallback( vFakePortReleaseTaskLockCallback );

    vFakeAssert_Ignore();
    vFakePortAssertIfISR_Ignore();
    vFakePortEnableInterrupts_Ignore();

    ulFakePortSetInterruptMaskFromISR_IgnoreAndReturn( 0 );
    vFakePortClearInterruptMaskFromISR_Ignore();

    vFakePortDisableInterrupts_IgnoreAndReturn( 1 );
    vFakePortRestoreInterrupts_Ignore();
    xTimerCreateTimerTask_IgnoreAndReturn( 1 );
    vFakePortCheckIfInISR_IgnoreAndReturn( 0 );
    vPortCurrentTaskDying_Ignore();
    portSetupTCB_CB_Ignore();
    ulFakePortSetInterruptMask_IgnoreAndReturn( 0 );
    vFakePortClearInterruptMask_Ignore();

    memset( &pxReadyTasksLists, 0x00, configMAX_PRIORITIES * sizeof( List_t ) );
    memset( &xDelayedTaskList1, 0x00, sizeof( List_t ) );
    memset( &xDelayedTaskList2, 0x00, sizeof( List_t ) );
    memset( &xIdleTaskHandles, 0x00, ( configNUMBER_OF_CORES * sizeof( TaskHandle_t ) ) );
    memset( &pxCurrentTCBs, 0x00, ( configNUMBER_OF_CORES * sizeof( TCB_t * ) ) );
    memset( ( void * ) &xYieldPendings, 0x00, ( configNUMBER_OF_CORES * sizeof( BaseType_t ) ) );

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

    xCurrentCoreId = 0;
    memset( xTaskLockCount, 0x00, sizeof( xTaskLockCount ) );
    memset( xIsrLockCount, 0x00, sizeof( xIsrLockCount ) );
}

void commonAsyncCoreYieldSetup( void )
{
    vFakePortYieldCore_StubWithCallback( vFakePortYieldCoreAsyncStubCallback );
    vFakePortExitCriticalFromISR_StubWithCallback( vFakePortExitCriticalFromISRAsyncCallback );
    vFakePortReleaseTaskLock_StubWithCallback( vFakePortReleaseTaskLockAsyncCallback );
}

void commonTearDown( void )
{
}

/* ==========================  Helper functions =========================== */

void vSmpTestTask( void * pvParameters )
{
}

void verifySmpTask( TaskHandle_t * xTaskHandle,
                    eTaskState eCurrentState,
                    TaskRunning_t xTaskRunState )
{
    TaskStatus_t xTaskDetails;

    vTaskGetInfo( *xTaskHandle, &xTaskDetails, pdTRUE, eInvalid );
    TEST_ASSERT_EQUAL_INT_MESSAGE( xTaskRunState, xTaskDetails.xHandle->xTaskRunState, "Task Verification Failed: Incorrect xTaskRunState" );
    TEST_ASSERT_EQUAL_INT_MESSAGE( eCurrentState, xTaskDetails.eCurrentState, "Task Verification Failed: Incorrect eCurrentState" );
}

void verifyIdleTask( BaseType_t index,
                     TaskRunning_t xTaskRunState )
{
    TaskStatus_t xTaskDetails;
    int ret;

    vTaskGetInfo( xIdleTaskHandles[ index ], &xTaskDetails, pdTRUE, eInvalid );
    #ifdef configIDLE_TASK_NAME
        ret = strncmp( xTaskDetails.xHandle->pcTaskName, configIDLE_TASK_NAME, strlen( configIDLE_TASK_NAME ) );
    #else
        ret = strncmp( xTaskDetails.xHandle->pcTaskName, "IDLE", 4 );
    #endif
    TEST_ASSERT_EQUAL_INT_MESSAGE( 0, ret, "Idle Task Verification Failed: Incorrect task name" );
    TEST_ASSERT_EQUAL_INT_MESSAGE( pdTRUE, xTaskDetails.xHandle->uxTaskAttributes, "Idle Task Verification Failed: Incorrect xIsIdle" );
    TEST_ASSERT_EQUAL_INT_MESSAGE( xTaskRunState, xTaskDetails.xHandle->xTaskRunState, "Idle Task Verification Failed: Incorrect xTaskRunState" );
    TEST_ASSERT_EQUAL_INT_MESSAGE( eRunning, xTaskDetails.eCurrentState, "Idle Task Verification Failed: Incorrect eCurrentState" );
}

/* Helper function to simulate calling xTaskIncrementTick in critical section. */
void xTaskIncrementTick_helper( void )
{
    BaseType_t xSwitchRequired;
    UBaseType_t uxSavedInterruptState;

    /* xTaskIncrementTick is called in ISR context. Use taskENTER/EXIT_CRITICAL_FROM_ISR
     * here. */
    uxSavedInterruptState = taskENTER_CRITICAL_FROM_ISR();

    xSwitchRequired = xTaskIncrementTick();

    /* Simulate context switch on the core which calls xTaskIncrementTick. */
    if( xSwitchRequired == pdTRUE )
    {
        portYIELD_CORE( configTICK_CORE );
    }

    taskEXIT_CRITICAL_FROM_ISR( uxSavedInterruptState );
}

void vCreateStaticTestTask( TaskHandle_t xTaskHandle,
                            UBaseType_t uxPriority,
                            BaseType_t xTaskRunState,
                            BaseType_t xTaskIsIdle )
{
    TCB_t * pxTaskTCB = ( TCB_t * ) xTaskHandle;

    pxTaskTCB->xStateListItem.pvOwner = pxTaskTCB;
    pxTaskTCB->uxPriority = uxPriority;

    /* Also assign pxCurrentTCBs to the created task. */
    if( ( xTaskRunState >= 0 ) && ( xTaskRunState < configNUMBER_OF_CORES ) )
    {
        pxCurrentTCBs[ xTaskRunState ] = pxTaskTCB;
    }

    pxTaskTCB->xTaskRunState = xTaskRunState;

    /* Set idle task attribute. */
    if( xTaskIsIdle == pdTRUE )
    {
        pxTaskTCB->uxTaskAttributes = taskATTRIBUTE_IS_IDLE;
    }
    else
    {
        pxTaskTCB->uxTaskAttributes = 0;
    }

    /* Increase the uxCurrentNumberOfTasks. */
    uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;
}

#if ( configUSE_CORE_AFFINITY == 1 )
    void vCreateStaticTestTaskAffinity( TaskHandle_t xTaskHandle,
                                        UBaseType_t uxCoreAffinityMask,
                                        UBaseType_t uxPriority,
                                        BaseType_t xTaskRunState,
                                        BaseType_t xTaskIsIdle )
    {
        TCB_t * pxTaskTCB = ( TCB_t * ) xTaskHandle;

        vCreateStaticTestTask( xTaskHandle, uxPriority, xTaskRunState, xTaskIsIdle );
        pxTaskTCB->uxCoreAffinityMask = uxCoreAffinityMask;
    }
#endif /* if ( configUSE_CORE_AFFINITY == 1 ) */
