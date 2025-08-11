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
/*! @file granular_lock_utest_common.c */

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

/* Test includes. */
#include "unity.h"
#include "unity_memory.h"
#include "../global_vars.h"
#include "smp_utest_common.h"

/* Mock includes. */
#include "mock_fake_assert.h"
#include "mock_fake_port.h"
#include "mock_portmacro.h"
#include "mock_timers.h"


/* ===========================  TYPE DEFINITIONS  =========================== */

typedef enum eStateChangeType
{
    STATE_CHANGE_DELETE,
    STATE_CHANGE_SUSPEND,
    STATE_CHANGE_DELETE_SUSPEND,
    STATE_CHANGE_SUSPEND_DELETE,
    STATE_CHANGE_SUSPEND_RESUME
} eStateChangeType_t;

typedef enum eEventListOperation
{
    PLACE_ON_EVENT_LIST,
    PLACE_ON_UNORDERED_EVENT_LIST,
    PLACE_ON_EVENT_LIST_RESTRICTED
} eEventListOperation_t;

typedef enum eStateChangeOperation
{
    OPERATION_DELETE,
    OPERATION_SUSPEND
} eStateChangeOperation_t;

/* ===========================  EXTERN VARIABLES  =========================== */
extern portSPINLOCK_TYPE xTaskSpinlock;
extern portSPINLOCK_TYPE xISRSpinlock;

/* ===========================  GLOBAL VARIABLES  =========================== */

static TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES ] = { NULL };
uint32_t xPortCriticalNestingCount[ configNUMBER_OF_CORES ] = { 0U };

static BaseType_t xCoreYields[ configNUMBER_OF_CORES ] = { 0 };

static UBaseType_t xInterruptMaskCount[ configNUMBER_OF_CORES ] = { 0U };
static BaseType_t xInterruptDisableStatus[ configNUMBER_OF_CORES ] = { 0U };

static List_t xTasksWaitingToSend;

static portSPINLOCK_TYPE xPortTaskSpinlock = portINIT_SPINLOCK_STATIC;
static portSPINLOCK_TYPE xPortISRSpinlock = portINIT_SPINLOCK_STATIC;

BaseType_t xReturnOnSpin = pdFALSE;

/* ============================  Application hook function  ============================ */

#if ( configSUPPORT_STATIC_ALLOCATION == 1 )

    static void prvApplicationGetTimerTaskMemory( StaticTask_t ** ppxTimerTaskTCBBuffer,
                                                  StackType_t ** ppxTimerTaskStackBuffer,
                                                  configSTACK_DEPTH_TYPE * puxTimerTaskStackSize,
                                                  int cmock_num_calls )
    {
        static StaticTask_t xTimerTaskTCB;
        static StackType_t uxTimerTaskStack[ configTIMER_TASK_STACK_DEPTH ];

        ( void ) cmock_num_calls;

        *ppxTimerTaskTCBBuffer = &( xTimerTaskTCB );
        *ppxTimerTaskStackBuffer = &( uxTimerTaskStack[ 0 ] );
        *puxTimerTaskStackSize = configTIMER_TASK_STACK_DEPTH;
    }

    void vApplicationGetIdleTaskMemory( StaticTask_t ** ppxIdleTaskTCBBuffer,
                                        StackType_t ** ppxIdleTaskStackBuffer,
                                        configSTACK_DEPTH_TYPE * puxIdleTaskStackSize )
    {
        static StaticTask_t xIdleTaskTCB;
        static StackType_t uxIdleTaskStack[ configMINIMAL_STACK_SIZE ];

        *ppxIdleTaskTCBBuffer = &( xIdleTaskTCB );
        *ppxIdleTaskStackBuffer = &( uxIdleTaskStack[ 0 ] );
        *puxIdleTaskStackSize = configMINIMAL_STACK_SIZE;
    }

    void vApplicationGetPassiveIdleTaskMemory( StaticTask_t ** ppxIdleTaskTCBBuffer,
                                               StackType_t ** ppxIdleTaskStackBuffer,
                                               configSTACK_DEPTH_TYPE * puxIdleTaskStackSize,
                                               BaseType_t xPassiveIdleTaskIndex )
    {
        static StaticTask_t xIdleTaskTCBs[ configNUMBER_OF_CORES - 1 ];
        static StackType_t uxIdleTaskStacks[ configNUMBER_OF_CORES - 1 ][ configMINIMAL_STACK_SIZE ];

        *ppxIdleTaskTCBBuffer = &( xIdleTaskTCBs[ xPassiveIdleTaskIndex ] );
        *ppxIdleTaskStackBuffer = &( uxIdleTaskStacks[ xPassiveIdleTaskIndex ][ 0 ] );
        *puxIdleTaskStackSize = configMINIMAL_STACK_SIZE;
    }

#endif /* if ( configSUPPORT_STATIC_ALLOCATION == 1 ) */

/* ============================  Callback Functions  ============================ */
static void vFakePortEnterCriticalSection_callback( int cmock_num_calls )
{
    taskDATA_GROUP_ENTER_CRITICAL( &xPortTaskSpinlock, &xPortISRSpinlock );
}

static void vFakePortExitCriticalSection_callback( int cmock_num_calls )
{
    taskDATA_GROUP_EXIT_CRITICAL( &xPortTaskSpinlock, &xPortISRSpinlock );
}

static void vFakePortInitSpinlock_callback( portSPINLOCK_TYPE * pxSpinlock,
                                            int cmock_num_calls )
{
    TEST_ASSERT_NOT_EQUAL( NULL, pxSpinlock );

    pxSpinlock->uxLockCount = 0;
    pxSpinlock->xOwnerCore = -1;
}

static void vYieldCores( void )
{
    BaseType_t i;
    BaseType_t xPreviousCoreId = portGET_CORE_ID();

    if( ( xTaskSpinlock.uxLockCount == 0U ) && ( xISRSpinlock.uxLockCount == 0U ) )
    {
        for( i = 0; i < configNUMBER_OF_CORES; i++ )
        {
            if( ( xCoreYields[ i ] == pdTRUE ) &&
                ( xInterruptMaskCount[ i ] == 0 ) &&
                ( xInterruptDisableStatus[ i ] == pdFALSE ) )
            {
                vSetCurrentCore( i );
                xCoreYields[ i ] = pdFALSE;
                vTaskSwitchContext( i );
            }
        }

        vSetCurrentCore( xPreviousCoreId );
    }
}

static void vFakePortReleaseSpinlock_callback( BaseType_t xCoreID,
                                               portSPINLOCK_TYPE * pxSpinlock,
                                               int cmock_num_calls )
{
    TEST_ASSERT_NOT_EQUAL( NULL, pxSpinlock );
    TEST_ASSERT_NOT_EQUAL( 0, pxSpinlock->uxLockCount );
    TEST_ASSERT_EQUAL( xCoreID, pxSpinlock->xOwnerCore );

    pxSpinlock->uxLockCount = pxSpinlock->uxLockCount - 1U;

    if( pxSpinlock->uxLockCount == 0U )
    {
        pxSpinlock->xOwnerCore = -1;
    }

    /* Check if and pending core yield. */
    vYieldCores();
}

static void vFakePortReleaseSpinlock_failure_callback( BaseType_t xCoreID,
                                                       portSPINLOCK_TYPE * pxSpinlock,
                                                       int cmock_num_calls )
{
    TEST_ASSERT_NOT_EQUAL( NULL, pxSpinlock );
    TEST_ASSERT_NOT_EQUAL( 0, pxSpinlock->uxLockCount );
    /* Catch failure & do not release lock */
    TEST_ASSERT_NOT_EQUAL( xCoreID, pxSpinlock->xOwnerCore );
}

static void vFakePortGetSpinlock_callback( BaseType_t xCoreID,
                                           portSPINLOCK_TYPE * pxSpinlock,
                                           int cmock_num_calls )
{
    TEST_ASSERT_NOT_EQUAL( NULL, pxSpinlock );

    if( pxSpinlock->uxLockCount == 0 )
    {
        pxSpinlock->uxLockCount = pxSpinlock->uxLockCount + 1U;
        pxSpinlock->xOwnerCore = xCoreID;
    }
    else
    {
        TEST_ASSERT_EQUAL( xCoreID, pxSpinlock->xOwnerCore );
        pxSpinlock->uxLockCount = pxSpinlock->uxLockCount + 1U;
    }
}

static void vFakePortGetSpinlock_failure_callback( BaseType_t xCoreID,
                                                   portSPINLOCK_TYPE * pxSpinlock,
                                                   int cmock_num_calls )
{
    TEST_ASSERT_NOT_EQUAL( NULL, pxSpinlock );

    if( pxSpinlock->uxLockCount == 0 )
    {
        pxSpinlock->uxLockCount = pxSpinlock->uxLockCount + 1U;
        pxSpinlock->xOwnerCore = xCoreID;
    }
    else
    {
        /* Catch failure and do not increment */
        TEST_ASSERT_NOT_EQUAL( xCoreID, pxSpinlock->xOwnerCore );
        xReturnOnSpin = pdTRUE;
    }
}

static void vFakePortYieldCore_callback( int xCoreID,
                                         int cmock_num_calls )
{
    BaseType_t xCoreInCritical = pdFALSE;
    BaseType_t xPreviousCoreId;

    /* Check if the lock is acquired by any core. */
    if( ( xTaskSpinlock.uxLockCount != 0U ) || ( xISRSpinlock.uxLockCount != 0U ) )
    {
        xCoreInCritical = pdTRUE;
    }

    if( xCoreInCritical == pdTRUE )
    {
        /* If a task is in the critical section, pend the core yield until the
         * spinlock is released. */
        xCoreYields[ xCoreID ] = pdTRUE;
    }
    else
    {
        /* No task is in the critical section. We can yield this core. */
        xPreviousCoreId = portGET_CORE_ID();
        vSetCurrentCore( xCoreID );
        vTaskSwitchContext( xCoreID );
        vSetCurrentCore( xPreviousCoreId );
    }
}

static UBaseType_t ulFakePortSetInterruptMaskFromISR_callback( int cmock_num_calls )
{
    ( void ) cmock_num_calls;
    xInterruptMaskCount[ portGET_CORE_ID() ]++;
    return xInterruptMaskCount[ portGET_CORE_ID() ];
}

static void vFakePortClearInterruptMaskFromISR_callback( UBaseType_t uxNewMaskValue,
                                                         int cmock_num_calls )
{
    ( void ) uxNewMaskValue;
    ( void ) cmock_num_calls;
    TEST_ASSERT_EQUAL( uxNewMaskValue, xInterruptMaskCount[ portGET_CORE_ID() ] );
    TEST_ASSERT_NOT_EQUAL( 0, xInterruptMaskCount[ portGET_CORE_ID() ] );
    xInterruptMaskCount[ portGET_CORE_ID() ]--;

    /* Check if and pending core yield. */
    vYieldCores();
}

static UBaseType_t ulFakePortSetInterruptMask_callback( int cmock_num_calls )
{
    ( void ) cmock_num_calls;
    xInterruptMaskCount[ portGET_CORE_ID() ]++;
    return xInterruptMaskCount[ portGET_CORE_ID() ];
}

static void vFakePortClearInterruptMask_callback( UBaseType_t uxNewMaskValue,
                                                  int cmock_num_calls )
{
    ( void ) uxNewMaskValue;
    ( void ) cmock_num_calls;
    TEST_ASSERT_EQUAL( uxNewMaskValue, xInterruptMaskCount[ portGET_CORE_ID() ] );
    TEST_ASSERT_NOT_EQUAL( 0, xInterruptMaskCount[ portGET_CORE_ID() ] );
    xInterruptMaskCount[ portGET_CORE_ID() ]--;

    /* Check if and pending core yield. */
    vYieldCores();
}

static uint32_t vFakePortDisableInterrupts_callback( int cmock_num_calls )
{
    xInterruptDisableStatus[ portGET_CORE_ID() ] = pdTRUE;
    return 0;
}

static void vFakePortEnableInterrupts_callback( int cmock_num_calls )
{
    xInterruptDisableStatus[ portGET_CORE_ID() ] = pdFALSE;

    /* Check if and pending core yield. */
    vYieldCores();
}

/* ============================  Unity Fixtures  ============================ */

void granularLocksSetUp( void )
{
    commonSetUp();
    vListInitialise( &xTasksWaitingToSend );

    xTaskSpinlock.uxLockCount = 0;
    xTaskSpinlock.xOwnerCore = -1;
    xISRSpinlock.uxLockCount = 0;
    xISRSpinlock.xOwnerCore = -1;

    xReturnOnSpin = pdFALSE;

    uint32_t i;

    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xPortCriticalNestingCount[ i ] = 0;
        xTaskHandles[ i ] = NULL;
    }

    /* Specify the granular lock specific implementation. */
    vFakePortInitSpinlock_Stub( vFakePortInitSpinlock_callback );
    vFakePortReleaseSpinlock_Stub( vFakePortReleaseSpinlock_callback );
    vFakePortGetSpinlock_Stub( vFakePortGetSpinlock_callback );
    vFakePortYieldCore_Stub( vFakePortYieldCore_callback );

    /* User data group use portENTER/EXIT_CRITICAL now. */
    vFakePortEnterCriticalSection_StubWithCallback( vFakePortEnterCriticalSection_callback );
    vFakePortExitCriticalSection_StubWithCallback( vFakePortExitCriticalSection_callback );
    portINIT_SPINLOCK( &xPortTaskSpinlock );
    portINIT_SPINLOCK( &xPortISRSpinlock );

    /* Interrupt masks. */
    memset( xInterruptMaskCount, 0, sizeof( UBaseType_t ) * configNUMBER_OF_CORES );
    ulFakePortSetInterruptMaskFromISR_StopIgnore();
    ulFakePortSetInterruptMaskFromISR_Stub( ulFakePortSetInterruptMaskFromISR_callback );
    vFakePortClearInterruptMaskFromISR_StopIgnore();
    vFakePortClearInterruptMaskFromISR_Stub( vFakePortClearInterruptMaskFromISR_callback );

    ulFakePortSetInterruptMask_StopIgnore();
    ulFakePortSetInterruptMask_Stub( ulFakePortSetInterruptMask_callback );
    vFakePortClearInterruptMask_StopIgnore();
    vFakePortClearInterruptMask_Stub( vFakePortClearInterruptMask_callback );

    memset( xInterruptDisableStatus, 0, sizeof( BaseType_t ) * configNUMBER_OF_CORES );
    vFakePortDisableInterrupts_StopIgnore();
    vFakePortDisableInterrupts_Stub( vFakePortDisableInterrupts_callback );
    vFakePortEnableInterrupts_StopIgnore();
    vFakePortEnableInterrupts_Stub( vFakePortEnableInterrupts_callback );

    #if ( configSUPPORT_STATIC_ALLOCATION == 1 )
        /* Setup timer task memory callback. */
        vApplicationGetTimerTaskMemory_StubWithCallback( prvApplicationGetTimerTaskMemory );
    #endif
}

void granularLocksTearDown( void )
{
    /* Revert the callback function. */
    vFakePortGetSpinlock_Stub( vFakePortGetSpinlock_callback );

    commonTearDown();
}

/* ==============================  Test Cases  ============================== */

/* ==============================  granular lock independence  ============================== */
static void granular_locks_independence( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                         portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    xTaskCreate( vSmpTestTask, "Granular Lock Task 1", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 0 ] );
    xTaskCreate( vSmpTestTask, "Granular Lock Task 2", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 1 ] );

    vTaskStartScheduler();

    /* Core 0 actions */
    vSetCurrentCore( 0 );

    if( pxDataGroupISRSpinlock != NULL )
    {
        taskDATA_GROUP_ENTER_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );
    }
    else
    {
        taskDATA_GROUP_LOCK( pxDataGroupTaskSpinlock );
    }

    TEST_ASSERT_EQUAL( 1, pxDataGroupTaskSpinlock->uxLockCount );
    TEST_ASSERT_EQUAL( 0, pxDataGroupTaskSpinlock->xOwnerCore );

    if( pxDataGroupISRSpinlock != NULL )
    {
        TEST_ASSERT_EQUAL( 1, pxDataGroupISRSpinlock->uxLockCount );
        TEST_ASSERT_EQUAL( 0, pxDataGroupISRSpinlock->xOwnerCore );
    }

    /* Core 1 actions */
    vSetCurrentCore( 1 );

    /* Core 1 should be able to acquire kernel data group lock. */
    if( pxDataGroupISRSpinlock != NULL )
    {
        taskENTER_CRITICAL();
    }
    else
    {
        vTaskSuspendAll();
    }

    TEST_ASSERT_EQUAL( 1, pxDataGroupTaskSpinlock->uxLockCount );
    TEST_ASSERT_EQUAL( 0, pxDataGroupTaskSpinlock->xOwnerCore );

    if( pxDataGroupISRSpinlock != NULL )
    {
        TEST_ASSERT_EQUAL( 1, pxDataGroupISRSpinlock->uxLockCount );
        TEST_ASSERT_EQUAL( 0, pxDataGroupISRSpinlock->xOwnerCore );
    }

    /* Core 1 release the kerenl data group lock. */
    if( pxDataGroupISRSpinlock != NULL )
    {
        taskEXIT_CRITICAL();
    }
    else
    {
        ( void ) xTaskResumeAll();
    }

    /* Switch back to core 0 after test. */
    vSetCurrentCore( 0 );
}

void granular_locks_critical_section_independence( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                                   portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    granular_locks_independence( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );
}

void granular_locks_lock_independence( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock )
{
    granular_locks_independence( pxDataGroupTaskSpinlock, NULL );
}

/* ==============================  granular lock mutual exclustion  ============================== */

static void granular_locks_mutual_exclusion( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                             portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    xTaskCreate( vSmpTestTask, "Granular Lock Task 1", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 0 ] );
    xTaskCreate( vSmpTestTask, "Granular Lock Task 2", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 1 ] );

    vTaskStartScheduler();

    /* Core 0 actions */
    vSetCurrentCore( 0 );

    if( pxDataGroupISRSpinlock != NULL )
    {
        taskDATA_GROUP_ENTER_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );
    }
    else
    {
        taskDATA_GROUP_LOCK( pxDataGroupTaskSpinlock );
    }

    TEST_ASSERT_EQUAL( 1, pxDataGroupTaskSpinlock->uxLockCount );
    TEST_ASSERT_EQUAL( 0, pxDataGroupTaskSpinlock->xOwnerCore );

    if( pxDataGroupISRSpinlock != NULL )
    {
        TEST_ASSERT_EQUAL( 1, pxDataGroupISRSpinlock->uxLockCount );
        TEST_ASSERT_EQUAL( 0, pxDataGroupISRSpinlock->xOwnerCore );
    }

    /* Core 1 attempts to enter critical section or lock */
    vSetCurrentCore( 1 );
    vFakePortGetSpinlock_Stub( vFakePortGetSpinlock_failure_callback );

    if( pxDataGroupISRSpinlock != NULL )
    {
        taskDATA_GROUP_ENTER_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );
    }
    else
    {
        taskDATA_GROUP_LOCK( pxDataGroupTaskSpinlock );
    }

    /* Lock state hasn't changed */
    TEST_ASSERT_EQUAL( 1, pxDataGroupTaskSpinlock->uxLockCount );
    TEST_ASSERT_EQUAL( 0, pxDataGroupTaskSpinlock->xOwnerCore );

    if( pxDataGroupISRSpinlock != NULL )
    {
        TEST_ASSERT_EQUAL( 1, pxDataGroupISRSpinlock->uxLockCount );
        TEST_ASSERT_EQUAL( 0, pxDataGroupISRSpinlock->xOwnerCore );
    }

    /* Switch back to core 0 after test. */
    vSetCurrentCore( 0 );
}

/* Wrapper functions for backward compatibility */
void granular_locks_critical_section_mutual_exclusion( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                                       portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    granular_locks_mutual_exclusion( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );
}

void granular_locks_lock_mutual_exclusion( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock )
{
    granular_locks_mutual_exclusion( pxDataGroupTaskSpinlock, NULL );
}

/* ==============================  granular lock nesting  ============================== */
static void granular_locks_nesting( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                    portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    xTaskCreate( vSmpTestTask, "Granular Lock Task 1", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 0 ] );
    xTaskCreate( vSmpTestTask, "Granular Lock Task 2", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 1 ] );

    vTaskStartScheduler();

    /* Core 0 enters user critical section */
    vSetCurrentCore( 0 );
    taskENTER_CRITICAL();

    /* Core 0 also enters data group critical section or lock */
    if( pxDataGroupISRSpinlock != NULL )
    {
        taskDATA_GROUP_ENTER_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );
    }
    else
    {
        taskDATA_GROUP_LOCK( pxDataGroupTaskSpinlock );
    }

    TEST_ASSERT_EQUAL( 2, xPortCriticalNestingCount[ 0 ] );
    TEST_ASSERT_EQUAL( 1, pxDataGroupTaskSpinlock->uxLockCount );
    TEST_ASSERT_EQUAL( 0, pxDataGroupTaskSpinlock->xOwnerCore );

    if( pxDataGroupISRSpinlock != NULL )
    {
        TEST_ASSERT_EQUAL( 1, pxDataGroupISRSpinlock->uxLockCount );
        TEST_ASSERT_EQUAL( 0, pxDataGroupISRSpinlock->xOwnerCore );
    }

    /* Core 1 attempts to acquire the data group spinlocks */
    vSetCurrentCore( 1 );
    vFakePortGetSpinlock_Stub( vFakePortGetSpinlock_failure_callback );

    if( pxDataGroupISRSpinlock != NULL )
    {
        taskDATA_GROUP_ENTER_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );
    }
    else
    {
        taskDATA_GROUP_LOCK( pxDataGroupTaskSpinlock );
    }

    /* The failure callback set the return on spin flag to indicate failure. */
    TEST_ASSERT_EQUAL( pdTRUE, xReturnOnSpin );
    /* The data group lock owner is still core 0. */
    TEST_ASSERT_EQUAL( 1, pxDataGroupTaskSpinlock->uxLockCount );
    TEST_ASSERT_EQUAL( 0, pxDataGroupTaskSpinlock->xOwnerCore );

    if( pxDataGroupISRSpinlock != NULL )
    {
        TEST_ASSERT_EQUAL( 1, pxDataGroupISRSpinlock->uxLockCount );
        TEST_ASSERT_EQUAL( 0, pxDataGroupISRSpinlock->xOwnerCore );
    }

    vSetCurrentCore( 0 );
    vFakePortGetSpinlock_Stub( vFakePortGetSpinlock_callback );

    if( pxDataGroupISRSpinlock != NULL )
    {
        taskDATA_GROUP_EXIT_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );
    }
    else
    {
        taskDATA_GROUP_UNLOCK( pxDataGroupTaskSpinlock );
    }

    taskEXIT_CRITICAL();

    TEST_ASSERT_EQUAL( 0, pxDataGroupTaskSpinlock->uxLockCount );
    TEST_ASSERT_EQUAL( -1, pxDataGroupTaskSpinlock->xOwnerCore );

    if( pxDataGroupISRSpinlock != NULL )
    {
        TEST_ASSERT_EQUAL( 0, pxDataGroupISRSpinlock->uxLockCount );
        TEST_ASSERT_EQUAL( -1, pxDataGroupISRSpinlock->xOwnerCore );
    }
}

void granular_locks_critical_section_nesting( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                              portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    granular_locks_nesting( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );
}

void granular_locks_lock_nesting( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock )
{
    granular_locks_nesting( pxDataGroupTaskSpinlock, NULL );
}

/* ==============================  granular lock nesting  ============================== */

static void test_state_protection_basic( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                         portSPINLOCK_TYPE * pxDataGroupISRSpinlock,
                                         eStateChangeType_t eChangeType )
{
    /* Create tasks */
    xTaskCreate( vSmpTestTask, "Task 1", configMINIMAL_STACK_SIZE, NULL,
                 configMAX_PRIORITIES - 1, &xTaskHandles[ 0 ] );
    xTaskCreate( vSmpTestTask, "Task 2", configMINIMAL_STACK_SIZE, NULL,
                 configMAX_PRIORITIES - 1, &xTaskHandles[ 1 ] );

    vTaskStartScheduler();

    /* Verify initial state */
    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );
    verifySmpTask( &xTaskHandles[ 1 ], eRunning, 1 );

    /* Core 0 enters critical section */
    vSetCurrentCore( 0 );

    if( pxDataGroupISRSpinlock != NULL )
    {
        taskDATA_GROUP_ENTER_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );
    }
    else
    {
        taskDATA_GROUP_LOCK( pxDataGroupTaskSpinlock );
    }

    /* Core 1 attempts state changes */
    vSetCurrentCore( 1 );

    switch( eChangeType )
    {
        case STATE_CHANGE_DELETE:
            vTaskDelete( xTaskHandles[ 0 ] );
            break;

        case STATE_CHANGE_SUSPEND:
            vTaskSuspend( xTaskHandles[ 0 ] );
            break;

        case STATE_CHANGE_DELETE_SUSPEND:
            vTaskDelete( xTaskHandles[ 0 ] );
            vTaskSuspend( xTaskHandles[ 0 ] );
            break;

        case STATE_CHANGE_SUSPEND_DELETE:
            vTaskSuspend( xTaskHandles[ 0 ] );
            vTaskDelete( xTaskHandles[ 0 ] );
            break;

        case STATE_CHANGE_SUSPEND_RESUME:
            vTaskSuspend( xTaskHandles[ 0 ] );
            vTaskResume( xTaskHandles[ 0 ] );
            break;
    }

    /* Verify still running */
    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );

    /* Core 0 exits critical section */
    vSetCurrentCore( 0 );

    if( pxDataGroupISRSpinlock != NULL )
    {
        taskDATA_GROUP_EXIT_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );
    }
    else
    {
        taskDATA_GROUP_UNLOCK( pxDataGroupTaskSpinlock );
    }

    /* Verify final state */
    eTaskState expectedState;

    switch( eChangeType )
    {
        case STATE_CHANGE_DELETE:
        case STATE_CHANGE_DELETE_SUSPEND:
        case STATE_CHANGE_SUSPEND_DELETE:
            expectedState = eDeleted;
            break;

        case STATE_CHANGE_SUSPEND:
            expectedState = eSuspended;
            break;

        case STATE_CHANGE_SUSPEND_RESUME:
            expectedState = eRunning;
            break;

        default:
            expectedState = eRunning;
    }

    verifySmpTask( &xTaskHandles[ 0 ], expectedState, -1 );
}

/* Critical Section versions */
void granular_locks_critical_section_state_protection_deletion( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                                                portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    test_state_protection_basic( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock,
                                 STATE_CHANGE_DELETE );
}

void granular_locks_critical_section_state_protection_suspension( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                                                  portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    test_state_protection_basic( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock,
                                 STATE_CHANGE_SUSPEND );
}

void granular_locks_critical_section_state_protection_deletion_suspension( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                                                           portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    test_state_protection_basic( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock,
                                 STATE_CHANGE_DELETE_SUSPEND );
}

void granular_locks_critical_section_state_protection_suspension_deletion( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                                                           portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    test_state_protection_basic( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock,
                                 STATE_CHANGE_SUSPEND_DELETE );
}

void granular_locks_critical_section_state_protection_suspension_resumption_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                                                                  portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    test_state_protection_basic( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock,
                                 STATE_CHANGE_SUSPEND_RESUME );
}

/* Lock versions */
void granular_locks_lock_state_protection_deletion( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock )
{
    test_state_protection_basic( pxDataGroupTaskSpinlock, NULL,
                                 STATE_CHANGE_DELETE );
}

void granular_locks_lock_state_protection_suspension( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock )
{
    test_state_protection_basic( pxDataGroupTaskSpinlock, NULL,
                                 STATE_CHANGE_SUSPEND );
}

void granular_locks_lock_state_protection_deletion_suspension( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock )
{
    test_state_protection_basic( pxDataGroupTaskSpinlock, NULL,
                                 STATE_CHANGE_DELETE_SUSPEND );
}

void granular_locks_lock_state_protection_suspension_deletion( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock )
{
    test_state_protection_basic( pxDataGroupTaskSpinlock, NULL,
                                 STATE_CHANGE_SUSPEND_DELETE );
}

void granular_locks_lock_state_protection_suspension_resumption_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock )
{
    test_state_protection_basic( pxDataGroupTaskSpinlock, NULL,
                                 STATE_CHANGE_SUSPEND_RESUME );
}

/* ==============================  granular lock task state protect  ============================== */

static void test_state_protection( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                   portSPINLOCK_TYPE * pxDataGroupISRSpinlock,
                                   eEventListOperation_t eListOp,
                                   eStateChangeOperation_t eStateOp,
                                   BaseType_t xStateChangeFirst )
{
    /* Create tasks */
    xTaskCreate( vSmpTestTask, "Task 1", configMINIMAL_STACK_SIZE, NULL,
                 configMAX_PRIORITIES - 1, &xTaskHandles[ 0 ] );
    xTaskCreate( vSmpTestTask, "Task 2", configMINIMAL_STACK_SIZE, NULL,
                 configMAX_PRIORITIES - 1, &xTaskHandles[ 1 ] );

    vTaskStartScheduler();

    /* Verify initial state */
    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );
    verifySmpTask( &xTaskHandles[ 1 ], eRunning, 1 );

    /* Core 0 enters critical section */
    vSetCurrentCore( 0 );

    if( pxDataGroupISRSpinlock != NULL )
    {
        taskDATA_GROUP_ENTER_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );
    }
    else
    {
        taskDATA_GROUP_LOCK( pxDataGroupTaskSpinlock );
    }

    if( !xStateChangeFirst )
    {
        /* Place task on event list */
        switch( eListOp )
        {
            case PLACE_ON_EVENT_LIST:
                vTaskPlaceOnEventList( &xTasksWaitingToSend, 0 );
                break;

            case PLACE_ON_UNORDERED_EVENT_LIST:
                vTaskPlaceOnUnorderedEventList( &xTasksWaitingToSend, 0, 0 );
                break;

            case PLACE_ON_EVENT_LIST_RESTRICTED:
                vTaskPlaceOnEventListRestricted( &xTasksWaitingToSend, 0, pdFALSE );
                break;
        }
    }

    /* Core 1 attempts state change */
    vSetCurrentCore( 1 );

    if( eStateOp == OPERATION_DELETE )
    {
        vTaskDelete( xTaskHandles[ 0 ] );
    }
    else
    {
        vTaskSuspend( xTaskHandles[ 0 ] );
    }

    if( xStateChangeFirst )
    {
        vSetCurrentCore( 0 );

        /* Place task on event list */
        switch( eListOp )
        {
            case PLACE_ON_EVENT_LIST:
                vTaskPlaceOnEventList( &xTasksWaitingToSend, 0 );
                break;

            case PLACE_ON_UNORDERED_EVENT_LIST:
                vTaskPlaceOnUnorderedEventList( &xTasksWaitingToSend, 0, 0 );
                break;

            case PLACE_ON_EVENT_LIST_RESTRICTED:
                vTaskPlaceOnEventListRestricted( &xTasksWaitingToSend, 0, pdFALSE );
                break;
        }
    }

    /* Verify intermediate state */
    verifySmpTask( &xTaskHandles[ 0 ], eBlocked, 0 );

    /* Core 0 exits critical section */
    vSetCurrentCore( 0 );

    if( pxDataGroupISRSpinlock != NULL )
    {
        taskDATA_GROUP_EXIT_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );
    }
    else
    {
        taskDATA_GROUP_UNLOCK( pxDataGroupTaskSpinlock );
    }

    /* Verify final state */
    verifySmpTask( &xTaskHandles[ 0 ],
                   ( eStateOp == OPERATION_DELETE ) ? eDeleted : eSuspended,
                   -1 );
}

void granular_locks_critical_section_state_protection_vTaskPlaceOnEventList_blocked_deletion_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                                                                                   portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    test_state_protection( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock,
                           PLACE_ON_EVENT_LIST,
                           OPERATION_DELETE,
                           pdFALSE );
}

void granular_locks_critical_section_state_protection_vTaskPlaceOnEventList_blocked_suspension_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                                                                                     portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    test_state_protection( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock,
                           PLACE_ON_EVENT_LIST,
                           OPERATION_SUSPEND,
                           pdFALSE );
}

void granular_locks_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_blocked_deletion_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                                                                                            portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    test_state_protection( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock,
                           PLACE_ON_UNORDERED_EVENT_LIST,
                           OPERATION_DELETE,
                           pdFALSE );
}

void granular_locks_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_blocked_suspension_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                                                                                              portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    test_state_protection( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock,
                           PLACE_ON_UNORDERED_EVENT_LIST,
                           OPERATION_SUSPEND,
                           pdFALSE );
}

void granular_locks_critical_section_state_protection_vTaskPlaceOnEventListRestricted_blocked_deletion_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                                                                                             portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    test_state_protection( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock,
                           PLACE_ON_EVENT_LIST_RESTRICTED,
                           OPERATION_DELETE,
                           pdFALSE );
}

void granular_locks_critical_section_state_protection_vTaskPlaceOnEventListRestricted_blocked_suspension_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                                                                                               portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    test_state_protection( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock,
                           PLACE_ON_EVENT_LIST_RESTRICTED,
                           OPERATION_SUSPEND,
                           pdFALSE );
}

void granular_locks_critical_section_state_protection_vTaskPlaceOnEventList_deletion_blocked_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                                                                                   portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    test_state_protection( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock,
                           PLACE_ON_EVENT_LIST,
                           OPERATION_DELETE,
                           pdTRUE );
}

void granular_locks_critical_section_state_protection_vTaskPlaceOnEventList_suspension_blocked_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                                                                                     portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    test_state_protection( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock,
                           PLACE_ON_EVENT_LIST,
                           OPERATION_SUSPEND,
                           pdTRUE );
}

void granular_locks_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_deletion_blocked_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                                                                                            portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    test_state_protection( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock,
                           PLACE_ON_UNORDERED_EVENT_LIST,
                           OPERATION_DELETE,
                           pdTRUE );
}

void granular_locks_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_suspension_blocked_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                                                                                              portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    test_state_protection( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock,
                           PLACE_ON_UNORDERED_EVENT_LIST,
                           OPERATION_SUSPEND,
                           pdTRUE );
}

void granular_locks_critical_section_state_protection_vTaskPlaceOnEventListRestricted_deletion_blocked_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                                                                                             portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    test_state_protection( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock,
                           PLACE_ON_EVENT_LIST_RESTRICTED,
                           OPERATION_DELETE,
                           pdTRUE );
}

void granular_locks_critical_section_state_protection_vTaskPlaceOnEventListRestricted_suspension_blocked_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                                                                                               portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    test_state_protection( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock,
                           PLACE_ON_EVENT_LIST_RESTRICTED,
                           OPERATION_SUSPEND,
                           pdTRUE );
}

void granular_locks_lock_state_protection_vTaskPlaceOnEventList_blocked_deletion_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock )
{
    test_state_protection( pxDataGroupTaskSpinlock, NULL,
                           PLACE_ON_EVENT_LIST,
                           OPERATION_DELETE,
                           pdFALSE );
}

void granular_locks_lock_state_protection_vTaskPlaceOnEventList_blocked_suspension_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock )
{
    test_state_protection( pxDataGroupTaskSpinlock, NULL,
                           PLACE_ON_EVENT_LIST,
                           OPERATION_SUSPEND,
                           pdFALSE );
}

void granular_locks_lock_state_protection_vTaskPlaceOnUnorderedEventList_blocked_deletion_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock )
{
    test_state_protection( pxDataGroupTaskSpinlock, NULL,
                           PLACE_ON_UNORDERED_EVENT_LIST,
                           OPERATION_DELETE,
                           pdFALSE );
}

void granular_locks_lock_state_protection_vTaskPlaceOnUnorderedEventList_blocked_suspension_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock )
{
    test_state_protection( pxDataGroupTaskSpinlock, NULL,
                           PLACE_ON_UNORDERED_EVENT_LIST,
                           OPERATION_SUSPEND,
                           pdFALSE );
}

void granular_locks_lock_state_protection_vTaskPlaceOnEventListRestricted_blocked_deletion_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock )
{
    test_state_protection( pxDataGroupTaskSpinlock, NULL,
                           PLACE_ON_EVENT_LIST_RESTRICTED,
                           OPERATION_DELETE,
                           pdFALSE );
}

void granular_locks_lock_state_protection_vTaskPlaceOnEventListRestricted_blocked_suspension_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock )
{
    test_state_protection( pxDataGroupTaskSpinlock, NULL,
                           PLACE_ON_EVENT_LIST_RESTRICTED,
                           OPERATION_SUSPEND,
                           pdFALSE );
}

void granular_locks_lock_state_protection_vTaskPlaceOnEventList_deletion_blocked_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock )
{
    test_state_protection( pxDataGroupTaskSpinlock, NULL,
                           PLACE_ON_EVENT_LIST,
                           OPERATION_DELETE,
                           pdTRUE );
}

void granular_locks_lock_state_protection_vTaskPlaceOnEventList_suspension_blocked_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock )
{
    test_state_protection( pxDataGroupTaskSpinlock, NULL,
                           PLACE_ON_EVENT_LIST,
                           OPERATION_SUSPEND,
                           pdTRUE );
}

void granular_locks_lock_state_protection_vTaskPlaceOnUnorderedEventList_deletion_blocked_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock )
{
    test_state_protection( pxDataGroupTaskSpinlock, NULL,
                           PLACE_ON_UNORDERED_EVENT_LIST,
                           OPERATION_DELETE,
                           pdTRUE );
}

void granular_locks_lock_state_protection_vTaskPlaceOnUnorderedEventList_suspension_blocked_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock )
{
    test_state_protection( pxDataGroupTaskSpinlock, NULL,
                           PLACE_ON_UNORDERED_EVENT_LIST,
                           OPERATION_SUSPEND,
                           pdTRUE );
}

void granular_locks_lock_state_protection_vTaskPlaceOnEventListRestricted_deletion_blocked_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock )
{
    test_state_protection( pxDataGroupTaskSpinlock, NULL,
                           PLACE_ON_EVENT_LIST_RESTRICTED,
                           OPERATION_DELETE,
                           pdTRUE );
}

void granular_locks_lock_state_protection_vTaskPlaceOnEventListRestricted_suspension_blocked_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock )
{
    test_state_protection( pxDataGroupTaskSpinlock, NULL,
                           PLACE_ON_EVENT_LIST_RESTRICTED,
                           OPERATION_SUSPEND,
                           pdTRUE );
}

/* ==============================  Locking Test Cases  ============================== */
