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
/*! @file granular_lock_timers_utest.c */

/* C runtime includes. */
#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>

/* Task includes */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"
#include "event_groups.h"
#include "queue.h"
#include "semphr.h"

/* Test includes. */
#include "unity.h"
#include "unity_memory.h"
#include "../global_vars.h"
#include "../smp_utest_common.h"

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

/* ============================  Callback Functions  ============================ */
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

static void vFakePortGetSpinlock_callback( BaseType_t xCoreID, portSPINLOCK_TYPE *pxSpinlock, int cmock_num_calls )
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
        TEST_ASSERT_EQUAL( xCoreID, pxSpinlock->xOwnerCore );
        pxSpinlock->uxLockCount = pxSpinlock->uxLockCount + 1U;
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

/*! called before each testcase */
void setUp( void )
{
    /* Use the common setup for the testing. */
    commonSetUp();

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

/*! called after each testcase */
void tearDown( void )
{
    commonTearDown();
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

/* ==============================  Test Cases  ============================== */

void test_granular_locks_timers_smoke(void)
{
    uint32_t i;
    
    /* Create configNUMBER_OF_CORES - 1 tasks of equal priority */
    for( i = 1; i < configNUMBER_OF_CORES; i++ ){
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );
    }

    vTaskStartScheduler();

    /* Timer task at core 0 */

    /* Verify all configNUMBER_OF_CORES tasks are in the running state */
    for( i = 1; i < configNUMBER_OF_CORES ; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }
}
