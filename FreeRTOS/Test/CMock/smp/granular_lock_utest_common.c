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

/* ============================  Callback Functions  ============================ */
static void vFakePortEnterCriticalSection_callback( int cmock_num_calls )
{
    vTaskEnterCritical();
}

static void vFakePortExitCriticalSection_callback( int cmock_num_calls )
{
    vTaskExitCritical();
}

static void vFakePortInitSpinlock_callback( portSPINLOCK_TYPE *pxSpinlock, int cmock_num_calls )
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

static void vFakePortReleaseSpinlock_callback( BaseType_t xCoreID, portSPINLOCK_TYPE *pxSpinlock, int cmock_num_calls )
{
    TEST_ASSERT_NOT_EQUAL( NULL, pxSpinlock );
    TEST_ASSERT_NOT_EQUAL( -1, pxSpinlock->xOwnerCore );
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

static void vFakePortReleaseSpinlock_failure_callback( BaseType_t xCoreID, portSPINLOCK_TYPE *pxSpinlock, int cmock_num_calls )
{
    TEST_ASSERT_NOT_EQUAL( NULL, pxSpinlock );
    TEST_ASSERT_NOT_EQUAL( -1, pxSpinlock->xOwnerCore );
    TEST_ASSERT_NOT_EQUAL( 0, pxSpinlock->uxLockCount );
    /* Catch failure & do not release lock */
    TEST_ASSERT_NOT_EQUAL( xCoreID, pxSpinlock->xOwnerCore );
}

static void vFakePortGetSpinlock_callback( BaseType_t xCoreID, portSPINLOCK_TYPE *pxSpinlock, int cmock_num_calls )
{
    TEST_ASSERT_NOT_EQUAL( NULL, pxSpinlock );
    
    if( pxSpinlock->uxLockCount == 0 )
    {
        TEST_ASSERT_EQUAL( -1, pxSpinlock->xOwnerCore );
        pxSpinlock->uxLockCount = pxSpinlock->uxLockCount + 1U;
        pxSpinlock->xOwnerCore = xCoreID;
    }
    else
    {
        TEST_ASSERT_EQUAL( xCoreID, pxSpinlock->xOwnerCore );
        pxSpinlock->uxLockCount = pxSpinlock->uxLockCount + 1U;
    }
}

static void vFakePortGetSpinlock_failure_callback( BaseType_t xCoreID, portSPINLOCK_TYPE *pxSpinlock, int cmock_num_calls )
{
    TEST_ASSERT_NOT_EQUAL( NULL, pxSpinlock );
    
    if( pxSpinlock->uxLockCount == 0 )
    {
        // TEST_ASSERT_EQUAL( -1, pxSpinlock->xOwnerCore );
        pxSpinlock->uxLockCount = pxSpinlock->uxLockCount + 1U;
        pxSpinlock->xOwnerCore = xCoreID;
    }
    else
    {
        /* Catch failure and do not increment */
        TEST_ASSERT_NOT_EQUAL( xCoreID, pxSpinlock->xOwnerCore );
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
    ( void )cmock_num_calls;
    xInterruptMaskCount[ portGET_CORE_ID() ]++;
    return xInterruptMaskCount[ portGET_CORE_ID() ];
}

static void vFakePortClearInterruptMaskFromISR_callback( UBaseType_t uxNewMaskValue, int cmock_num_calls )
{
    ( void )uxNewMaskValue;
    ( void )cmock_num_calls;
    TEST_ASSERT_EQUAL( uxNewMaskValue, xInterruptMaskCount[ portGET_CORE_ID() ] );
    TEST_ASSERT_NOT_EQUAL( 0, xInterruptMaskCount[ portGET_CORE_ID() ] );
    xInterruptMaskCount[ portGET_CORE_ID() ]--;

    /* Check if and pending core yield. */
    vYieldCores();
}

static UBaseType_t ulFakePortSetInterruptMask_callback( int cmock_num_calls )
{
    ( void )cmock_num_calls;
    xInterruptMaskCount[ portGET_CORE_ID() ]++;
    return xInterruptMaskCount[ portGET_CORE_ID() ];
}

static void vFakePortClearInterruptMask_callback( UBaseType_t uxNewMaskValue, int cmock_num_calls )
{
    ( void )uxNewMaskValue;
    ( void )cmock_num_calls;
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

    uint32_t i;
    for ( i = 0; i < configNUMBER_OF_CORES; i++ ){
        xPortCriticalNestingCount[ i ] = 0;
        xTaskHandles[ i ] = NULL;
    }

    /* Specify the granular lock specific implementation. */
    vFakePortInitSpinlock_Stub( vFakePortInitSpinlock_callback );
    vFakePortReleaseSpinlock_Stub( vFakePortReleaseSpinlock_callback );
    vFakePortGetSpinlock_Stub( vFakePortGetSpinlock_callback );
    vFakePortYieldCore_Stub( vFakePortYieldCore_callback );

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
}

void granularLocksTearDown( void )
{
    commonTearDown();
}

/* ==============================  Test Cases  ============================== */

void granular_locks_critical_section_independence( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock, portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{    
    xTaskCreate( vSmpTestTask, "Granular Lock Task 1", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 0 ] );
    xTaskCreate( vSmpTestTask, "Granular Lock Task 2", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 1 ] );

    vTaskStartScheduler();

    /* Core 0 enters timer critical section */
    vSetCurrentCore( 0 );
    taskDATA_GROUP_ENTER_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );

    TEST_ASSERT_EQUAL( 1, pxDataGroupTaskSpinlock->uxLockCount );
    TEST_ASSERT_EQUAL( 0, pxDataGroupTaskSpinlock->xOwnerCore );
    TEST_ASSERT_EQUAL( 1, pxDataGroupISRSpinlock->uxLockCount );
    TEST_ASSERT_EQUAL( 0, pxDataGroupISRSpinlock->xOwnerCore );

    /* Core 1 enters user critical section */
    vSetCurrentCore( 1 );
    taskENTER_CRITICAL();

    TEST_ASSERT_EQUAL( 1, pxDataGroupTaskSpinlock->uxLockCount );
    TEST_ASSERT_EQUAL( 0, pxDataGroupTaskSpinlock->xOwnerCore );
    TEST_ASSERT_EQUAL( 1, pxDataGroupISRSpinlock->uxLockCount );
    TEST_ASSERT_EQUAL( 0, pxDataGroupISRSpinlock->xOwnerCore );
}

void granular_locks_mutual_exclusion( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock, portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    xTaskCreate( vSmpTestTask, "Granular Lock Task 1", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 0 ] );
    xTaskCreate( vSmpTestTask, "Granular Lock Task 2", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 1 ] );

    vTaskStartScheduler();

    /* Core 0 enters timer critical section */
    vSetCurrentCore( 0 );
    taskDATA_GROUP_ENTER_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );

    TEST_ASSERT_EQUAL( 1, pxDataGroupTaskSpinlock->uxLockCount );
    TEST_ASSERT_EQUAL( 0, pxDataGroupTaskSpinlock->xOwnerCore );
    TEST_ASSERT_EQUAL( 1, pxDataGroupISRSpinlock->uxLockCount );
    TEST_ASSERT_EQUAL( 0, pxDataGroupISRSpinlock->xOwnerCore );

    /* Core 1 attempts to enter timer critical section */
    vSetCurrentCore( 1 );
    vFakePortGetSpinlock_Stub( vFakePortGetSpinlock_failure_callback );
    
    taskDATA_GROUP_ENTER_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );

    /* Lock state hasn't changed */
    TEST_ASSERT_EQUAL( 1, pxDataGroupTaskSpinlock->uxLockCount );
    TEST_ASSERT_EQUAL( 0, pxDataGroupTaskSpinlock->xOwnerCore );
    TEST_ASSERT_EQUAL( 1, pxDataGroupISRSpinlock->uxLockCount );
    TEST_ASSERT_EQUAL( 0, pxDataGroupISRSpinlock->xOwnerCore );
}

void granular_locks_critical_section_nesting( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock, portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    xTaskCreate( vSmpTestTask, "Granular Lock Task 1", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 0 ] );
    xTaskCreate( vSmpTestTask, "Granular Lock Task 2", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 1 ] );

    vTaskStartScheduler();

    /* Core 0 enters user critical section */
    vSetCurrentCore( 0 );
    taskENTER_CRITICAL();

    /* Core 0 also enters timer critical section */
    taskDATA_GROUP_ENTER_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );

    TEST_ASSERT_EQUAL( 2, xPortCriticalNestingCount[ 0 ] );
    TEST_ASSERT_EQUAL( 1, pxDataGroupTaskSpinlock->uxLockCount );
    TEST_ASSERT_EQUAL( 0, pxDataGroupTaskSpinlock->xOwnerCore );
    TEST_ASSERT_EQUAL( 1, pxDataGroupISRSpinlock->uxLockCount );
    TEST_ASSERT_EQUAL( 0, pxDataGroupISRSpinlock->xOwnerCore );

    vSetCurrentCore( 1 );
    vFakePortReleaseSpinlock_Stub( vFakePortReleaseSpinlock_failure_callback );
    /* Core 1 attempts to release timer spinlocks */
    taskDATA_GROUP_EXIT_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );

    vFakePortReleaseSpinlock_Stub( vFakePortReleaseSpinlock_callback );
    vSetCurrentCore( 0 );
    taskDATA_GROUP_EXIT_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );
    taskEXIT_CRITICAL();

    TEST_ASSERT_EQUAL( 0, xPortCriticalNestingCount[ 1 ] );
    TEST_ASSERT_EQUAL( 0, pxDataGroupTaskSpinlock->uxLockCount );
    TEST_ASSERT_EQUAL( -1, pxDataGroupTaskSpinlock->xOwnerCore );
    TEST_ASSERT_EQUAL( 0, pxDataGroupISRSpinlock->uxLockCount );
    TEST_ASSERT_EQUAL( -1, pxDataGroupISRSpinlock->xOwnerCore );

}

void granular_locks_state_protection_deletion( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock, portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    xTaskCreate( vSmpTestTask, "Granular Lock Task 1", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 0 ] );
    xTaskCreate( vSmpTestTask, "Granular Lock Task 2", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 1 ] );

    vTaskStartScheduler();

    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );
    verifySmpTask( &xTaskHandles[ 1 ], eRunning, 1 );

    /* Core 0 enters timer critical section */
    vSetCurrentCore( 0 );
    taskDATA_GROUP_ENTER_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );

    /* Core 1 attempts to delete task running on Core 0 */
    vSetCurrentCore( 1 );
    vTaskDelete( xTaskHandles[ 0 ] );

    /* Not Yet Deleted */
    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );

    vSetCurrentCore( 0 );
    taskDATA_GROUP_EXIT_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );

    /* Now Deleted */
    verifySmpTask( &xTaskHandles[ 0 ], eDeleted, -1 );
}

void granular_locks_state_protection_suspension( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock, portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    xTaskCreate( vSmpTestTask, "Granular Lock Task 1", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 0 ] );
    xTaskCreate( vSmpTestTask, "Granular Lock Task 2", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 1 ] );

    vTaskStartScheduler();

    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );
    verifySmpTask( &xTaskHandles[ 1 ], eRunning, 1 );

    /* Core 0 enters timer critical section */
    vSetCurrentCore( 0 );
    taskDATA_GROUP_ENTER_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );

    /* Core 1 attempts to suspend task running on Core 0 */
    vSetCurrentCore( 1 );
    vTaskSuspend( xTaskHandles[ 0 ] );

    /* Not Yet Suspended */
    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );

    vSetCurrentCore( 0 );
    taskDATA_GROUP_EXIT_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );

    /* Now Suspended */
    verifySmpTask( &xTaskHandles[ 0 ], eSuspended, -1 );
}

void granular_locks_state_protection_deletion_suspension( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock, portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    xTaskCreate( vSmpTestTask, "Granular Lock Task 1", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 0 ] );
    xTaskCreate( vSmpTestTask, "Granular Lock Task 2", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 1 ] );

    vTaskStartScheduler();

    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );
    verifySmpTask( &xTaskHandles[ 1 ], eRunning, 1 );

    /* Core 0 enters timer critical section */
    vSetCurrentCore( 0 );
    taskDATA_GROUP_ENTER_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );

    /* Core 1 attempts to delete & then suspend task running on Core 0 */
    vSetCurrentCore( 1 );
    vTaskDelete( xTaskHandles[ 0 ] );
    vTaskSuspend( xTaskHandles[ 0 ] );
    
    /* Still running */
    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );

    vSetCurrentCore( 0 );
    taskDATA_GROUP_EXIT_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );

    /* Now Deleted */
    verifySmpTask( &xTaskHandles[ 0 ], eDeleted, -1 );
}

void granular_locks_state_protection_suspension_deletion( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock, portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    xTaskCreate( vSmpTestTask, "Granular Lock Task 1", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 0 ] );
    xTaskCreate( vSmpTestTask, "Granular Lock Task 2", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 1 ] );

    vTaskStartScheduler();

    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );
    verifySmpTask( &xTaskHandles[ 1 ], eRunning, 1 );

    /* Core 0 enters timer critical section */
    vSetCurrentCore( 0 );
    taskDATA_GROUP_ENTER_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );

    /* Core 1 attempts to suspend & then delete task running on Core 0 */
    vSetCurrentCore( 1 );
    vTaskSuspend( xTaskHandles[ 0 ] );
    vTaskDelete( xTaskHandles[ 0 ] );
    
    /* Still running */
    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );

    vSetCurrentCore( 0 );
    taskDATA_GROUP_EXIT_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );

    /* Now Deleted */
    verifySmpTask( &xTaskHandles[ 0 ], eDeleted, -1 );
}


void granular_locks_state_protection_suspension_resumption_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock, portSPINLOCK_TYPE * pxDataGroupISRSpinlock ) //=> Currently fails
{
    xTaskCreate( vSmpTestTask, "Granular Lock Task 1", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 0 ] );
    xTaskCreate( vSmpTestTask, "Granular Lock Task 2", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 1 ] );

    vTaskStartScheduler();

    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );
    verifySmpTask( &xTaskHandles[ 1 ], eRunning, 1 );

    /* Core 0 enters timer critical section */
    vSetCurrentCore( 0 );
    taskDATA_GROUP_ENTER_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );

    /* Core 1 attempts to suspend & then resume task running on Core 0 */
    vSetCurrentCore( 1 );
    vTaskSuspend( xTaskHandles[ 0 ] );
    vTaskResume( xTaskHandles[ 0 ] );
    
    /* Still running on Core 0 */
    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );

    vSetCurrentCore( 0 );
    taskDATA_GROUP_EXIT_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );

    /* Since we had resumed the task on Core 0 is still running */
    verifySmpTask( &xTaskHandles[ 0 ], eRunning, -1 );
}

void granular_locks_state_protection_vTaskPlaceOnEventList_blocked_deletion_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock, portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    xTaskCreate( vSmpTestTask, "Granular Lock Task 1", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 0 ] );
    xTaskCreate( vSmpTestTask, "Granular Lock Task 2", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 1 ] );

    vTaskStartScheduler();

    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );
    verifySmpTask( &xTaskHandles[ 1 ], eRunning, 1 );

    /* Core 0 enters timer critical section */
    vSetCurrentCore( 0 );
    taskDATA_GROUP_ENTER_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );

    vTaskPlaceOnEventList( &xTasksWaitingToSend, 0);

    /* Core 1 attempts to delete task running on Core 0 */
    vSetCurrentCore( 1 );
    vTaskDelete( xTaskHandles[ 0 ] );

    /* Still blocked and run state 1 on Core 0, deletion deferred */
    verifySmpTask( &xTaskHandles[ 0 ], eBlocked, 0 );

    /* Core 0 exits timer critical section */
    vSetCurrentCore( 0 );
    taskDATA_GROUP_EXIT_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );

    /* Now deleted */
    verifySmpTask( &xTaskHandles[ 0 ], eDeleted, -1 );
}

void granular_locks_state_protection_vTaskPlaceOnEventList_blocked_suspension_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock, portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    xTaskCreate( vSmpTestTask, "Granular Lock Task 1", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 0 ] );
    xTaskCreate( vSmpTestTask, "Granular Lock Task 2", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 1 ] );

    vTaskStartScheduler();

    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );
    verifySmpTask( &xTaskHandles[ 1 ], eRunning, 1 );

    /* Core 0 enters timer critical section */
    vSetCurrentCore( 0 );
    taskDATA_GROUP_ENTER_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );

    vSetCurrentCore( 0 );
    vTaskPlaceOnEventList( &xTasksWaitingToSend, 0);

    /* Core 1 attempts to suspend task running on Core 0 */
    vSetCurrentCore( 1 );
    vTaskSuspend( xTaskHandles[ 0 ] );

    /* Still blocked and run state 1 on Core 0, suspension deferred */
    verifySmpTask( &xTaskHandles[ 0 ], eBlocked, 0);

    /* Core 0 exits timer critical section */
    vSetCurrentCore( 0 );
    taskDATA_GROUP_EXIT_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );

    /* Now suspended */
    verifySmpTask( &xTaskHandles[ 0 ], eSuspended, -1 );
}

void granular_locks_state_protection_vTaskPlaceOnUnorderedEventList_blocked_deletion( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock, portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    xTaskCreate( vSmpTestTask, "Granular Lock Task 1", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 0 ] );
    xTaskCreate( vSmpTestTask, "Granular Lock Task 2", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 1 ] );

    vTaskStartScheduler();

    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );
    verifySmpTask( &xTaskHandles[ 1 ], eRunning, 1 );

    /* Core 0 enters timer critical section */
    vSetCurrentCore( 0 );
    taskDATA_GROUP_ENTER_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );

    vTaskPlaceOnUnorderedEventList( &xTasksWaitingToSend, 0,0);

    /* Core 1 attempts to delete task running on Core 0 */
    vSetCurrentCore( 1 );
    vTaskDelete( xTaskHandles[ 0 ] );

    /* Still blocked and run state 1 on Core 0, deletion deferred */
    verifySmpTask( &xTaskHandles[ 0 ], eBlocked, 0 );

    /* Core 0 exits timer critical section */
    vSetCurrentCore( 0 );
    taskDATA_GROUP_EXIT_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );

    /* Now deleted */
    verifySmpTask( &xTaskHandles[ 0 ], eDeleted, -1 );
}

void granular_locks_state_protection_vTaskPlaceOnUnorderedEventList_blocked_suspension_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock, portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    xTaskCreate( vSmpTestTask, "Granular Lock Task 1", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 0 ] );
    xTaskCreate( vSmpTestTask, "Granular Lock Task 2", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 1 ] );

    vTaskStartScheduler();

    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );
    verifySmpTask( &xTaskHandles[ 1 ], eRunning, 1 );

    /* Core 0 enters timer critical section */
    vSetCurrentCore( 0 );
    taskDATA_GROUP_ENTER_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );

    vTaskPlaceOnUnorderedEventList( &xTasksWaitingToSend, 0, 0);

    /* Core 1 attempts to suspend task running on Core 0 */
    vSetCurrentCore( 1 );
    vTaskSuspend( xTaskHandles[ 0 ] );

    /* Still blocked and run state 1 on Core 0, suspension deferred */
    verifySmpTask( &xTaskHandles[ 0 ], eBlocked, 0 );

    /* Core 0 exits timer critical section */
    vSetCurrentCore( 0 );
    taskDATA_GROUP_EXIT_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );

    /* Now suspended */
    verifySmpTask( &xTaskHandles[ 0 ], eSuspended, -1 );
}

void granular_locks_state_protection_vTaskPlaceOnEventListRestricted_blocked_deletion_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock, portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    xTaskCreate( vSmpTestTask, "Granular Lock Task 1", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 0 ] );
    xTaskCreate( vSmpTestTask, "Granular Lock Task 2", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 1 ] );

    vTaskStartScheduler();

    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );
    verifySmpTask( &xTaskHandles[ 1 ], eRunning, 1 );

    /* Core 0 enters timer critical section */
    vSetCurrentCore( 0 );
    taskDATA_GROUP_ENTER_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );

    vTaskPlaceOnEventListRestricted( &xTasksWaitingToSend, 0, pdFALSE);

    /* Core 1 attempts to delete task running on Core 0 */
    vSetCurrentCore( 1 );
    vTaskDelete( xTaskHandles[ 0 ] );

    /* Still blocked and run state 1 on Core 0, deletion deferred */
    verifySmpTask( &xTaskHandles[ 0 ], eBlocked, 0 );

    /* Core 0 exits timer critical section */
    vSetCurrentCore( 0 );
    taskDATA_GROUP_EXIT_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );

    /* Now deleted */
    verifySmpTask( &xTaskHandles[ 0 ], eDeleted, -1 );
}

void granular_locks_state_protection_vTaskPlaceOnEventListRestricted_blocked_suspension_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock, portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    xTaskCreate( vSmpTestTask, "Granular Lock Task 1", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 0 ] );
    xTaskCreate( vSmpTestTask, "Granular Lock Task 2", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 1 ] );

    vTaskStartScheduler();

    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );
    verifySmpTask( &xTaskHandles[ 1 ], eRunning, 1 );

    /* Core 0 enters timer critical section */
    vSetCurrentCore( 0 );
    taskDATA_GROUP_ENTER_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );

    vTaskPlaceOnEventListRestricted( &xTasksWaitingToSend, 0, pdFALSE);

    /* Core 1 attempts to suspend task running on Core 0 */
    vSetCurrentCore( 1 );
    vTaskSuspend( xTaskHandles[ 0 ] );

    /* Still blocked and run state 1 on Core 0, suspension deferred */
    verifySmpTask( &xTaskHandles[ 0 ], eBlocked, 0 );

    /* Core 0 exits timer critical section */
    vSetCurrentCore( 0 );
    taskDATA_GROUP_EXIT_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );

    /* Now suspended */
    verifySmpTask( &xTaskHandles[ 0 ], eSuspended, -1 );
}

void granular_locks_state_protection_vTaskPlaceOnEventList_deletion_blocked_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock, portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    xTaskCreate( vSmpTestTask, "Granular Lock Task 1", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 0 ] );
    xTaskCreate( vSmpTestTask, "Granular Lock Task 2", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 1 ] );

    vTaskStartScheduler();

    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );
    verifySmpTask( &xTaskHandles[ 1 ], eRunning, 1 );

    /* Core 0 enters timer critical section */
    vSetCurrentCore( 0 );
    taskDATA_GROUP_ENTER_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );

    /* Core 1 attempts to suspend task running on Core 0 */
    vSetCurrentCore( 1 );
    vTaskDelete( xTaskHandles[ 0 ] );

    vSetCurrentCore( 0 );
    /* Task running on Core 0 enters blocked state */
    vTaskPlaceOnEventList( &xTasksWaitingToSend, 0);

    /* Still blocked and run state 1 on Core 0, deletion deferred */
    verifySmpTask( &xTaskHandles[ 0 ], eBlocked, 0 );

    /* Core 0 exits timer critical section */
    vSetCurrentCore( 0 );
    taskDATA_GROUP_EXIT_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );

    /* Now deleted */
    verifySmpTask( &xTaskHandles[ 0 ], eDeleted, -1 );
}

void granular_locks_state_protection_vTaskPlaceOnEventList_suspension_blocked_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock, portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    xTaskCreate( vSmpTestTask, "Granular Lock Task 1", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 0 ] );
    xTaskCreate( vSmpTestTask, "Granular Lock Task 2", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 1 ] );

    vTaskStartScheduler();

    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );
    verifySmpTask( &xTaskHandles[ 1 ], eRunning, 1 );

    /* Core 0 enters timer critical section */
    vSetCurrentCore( 0 );
    taskDATA_GROUP_ENTER_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );

    /* Core 1 attempts to suspend task running on Core 0 */
    vSetCurrentCore( 1 );
    vTaskSuspend( xTaskHandles[ 0 ] );

    vSetCurrentCore( 0 );
    /* Task running on Core 0 enters blocked state */
    vTaskPlaceOnEventList( &xTasksWaitingToSend, 0);

    /* Still blocked and run state 1 on Core 0, suspension deferred */
    verifySmpTask( &xTaskHandles[ 0 ], eBlocked, 0 );

    /* Core 0 exits timer critical section */
    vSetCurrentCore( 0 );
    taskDATA_GROUP_EXIT_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );

    /* Now deleted */
    verifySmpTask( &xTaskHandles[ 0 ], eSuspended, -1 );
}

void granular_locks_state_protection_vTaskPlaceOnUnorderedEventList_deletion_blocked_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock, portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    xTaskCreate( vSmpTestTask, "Granular Lock Task 1", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 0 ] );
    xTaskCreate( vSmpTestTask, "Granular Lock Task 2", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 1 ] );

    vTaskStartScheduler();

    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );
    verifySmpTask( &xTaskHandles[ 1 ], eRunning, 1 );

    /* Core 0 enters timer critical section */
    vSetCurrentCore( 0 );
    taskDATA_GROUP_ENTER_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );

    /* Core 1 attempts to suspend task running on Core 0 */
    vSetCurrentCore( 1 );
    vTaskDelete( xTaskHandles[ 0 ] );

    vSetCurrentCore( 0 );
    /* Task running on Core 0 enters blocked state */
    vTaskPlaceOnUnorderedEventList( &xTasksWaitingToSend, 0, 0);

    /* Still blocked and run state 1 on Core 0, deletion deferred */
    verifySmpTask( &xTaskHandles[ 0 ], eBlocked, 0 );

    /* Core 0 exits timer critical section */
    vSetCurrentCore( 0 );
    taskDATA_GROUP_EXIT_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );

    /* Now deleted */
    verifySmpTask( &xTaskHandles[ 0 ], eDeleted, -1 );
}

void granular_locks_state_protection_vTaskPlaceOnUnorderedEventList_suspension_blocked_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock, portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    xTaskCreate( vSmpTestTask, "Granular Lock Task 1", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 0 ] );
    xTaskCreate( vSmpTestTask, "Granular Lock Task 2", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 1 ] );

    vTaskStartScheduler();

    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );
    verifySmpTask( &xTaskHandles[ 1 ], eRunning, 1 );

    /* Core 0 enters timer critical section */
    vSetCurrentCore( 0 );
    taskDATA_GROUP_ENTER_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );

    /* Core 1 attempts to suspend task running on Core 0 */
    vSetCurrentCore( 1 );
    vTaskSuspend( xTaskHandles[ 0 ] );

    vSetCurrentCore( 0 );
    /* Task running on Core 0 enters blocked state */
    vTaskPlaceOnUnorderedEventList( &xTasksWaitingToSend, 0, 0);

    /* Still blocked and run state 1 on Core 0, suspension deferred */
    verifySmpTask( &xTaskHandles[ 0 ], eBlocked, 0 );

    /* Core 0 exits timer critical section */
    vSetCurrentCore( 0 );
    taskDATA_GROUP_EXIT_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );

    /* Now deleted */
    verifySmpTask( &xTaskHandles[ 0 ], eSuspended, -1 );
}

void granular_locks_state_protection_vTaskPlaceOnEventListRestricted_deletion_blocked_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock, portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    xTaskCreate( vSmpTestTask, "Granular Lock Task 1", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 0 ] );
    xTaskCreate( vSmpTestTask, "Granular Lock Task 2", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 1 ] );

    vTaskStartScheduler();

    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );
    verifySmpTask( &xTaskHandles[ 1 ], eRunning, 1 );

    /* Core 0 enters timer critical section */
    vSetCurrentCore( 0 );
    taskDATA_GROUP_ENTER_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );

    /* Core 1 attempts to suspend task running on Core 0 */
    vSetCurrentCore( 1 );
    vTaskDelete( xTaskHandles[ 0 ] );

    vSetCurrentCore( 0 );
    /* Task running on Core 0 enters blocked state */
    vTaskPlaceOnEventListRestricted( &xTasksWaitingToSend, 0, pdFALSE);

    /* Still blocked and run state 1 on Core 0, deletion deferred */
    verifySmpTask( &xTaskHandles[ 0 ], eBlocked, 0 );

    /* Core 0 exits timer critical section */
    vSetCurrentCore( 0 );
    taskDATA_GROUP_EXIT_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );

    /* Now deleted */
    verifySmpTask( &xTaskHandles[ 0 ], eDeleted, -1 );
}

void granular_locks_state_protection_vTaskPlaceOnEventListRestricted_suspension_blocked_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock, portSPINLOCK_TYPE * pxDataGroupISRSpinlock )
{
    xTaskCreate( vSmpTestTask, "Granular Lock Task 1", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 0 ] );
    xTaskCreate( vSmpTestTask, "Granular Lock Task 2", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xTaskHandles[ 1 ] );

    vTaskStartScheduler();

    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );
    verifySmpTask( &xTaskHandles[ 1 ], eRunning, 1 );

    /* Core 0 enters timer critical section */
    vSetCurrentCore( 0 );
    taskDATA_GROUP_ENTER_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );

    /* Core 1 attempts to suspend task running on Core 0 */
    vSetCurrentCore( 1 );
    vTaskSuspend( xTaskHandles[ 0 ] );

    vSetCurrentCore( 0 );
    /* Task running on Core 0 enters blocked state */
    vTaskPlaceOnEventListRestricted( &xTasksWaitingToSend, 0, pdFALSE);

    /* Still blocked and run state 1 on Core 0, suspension deferred */
    verifySmpTask( &xTaskHandles[ 0 ], eBlocked, 0 );

    /* Core 0 exits timer critical section */
    vSetCurrentCore( 0 );
    taskDATA_GROUP_EXIT_CRITICAL( pxDataGroupTaskSpinlock, pxDataGroupISRSpinlock );

    /* Now deleted */
    verifySmpTask( &xTaskHandles[ 0 ], eSuspended, -1 );
}