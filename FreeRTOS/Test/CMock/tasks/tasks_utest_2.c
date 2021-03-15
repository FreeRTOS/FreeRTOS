/*
 * FreeRTOS V202012.00
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
/*! @file tasks_utest_2.c */

/* Tasks includes */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"
#include "task.h"

#include "mock_list.h"
#include "mock_list_macros.h"
#include "mock_timers.h"
#include "mock_portable.h"

/* Test includes. */
#include "unity.h"
#include "global_vars.h"

/* C runtime includes. */
#include <stdbool.h>
#include <string.h>


/* ===========================  EXTERN VARIABLES  =========================== */
extern TCB_t * volatile pxCurrentTCB;
extern List_t pxReadyTasksLists[ configMAX_PRIORITIES ];
extern List_t xDelayedTaskList1;
extern List_t xDelayedTaskList2;
extern List_t * volatile pxDelayedTaskList;
extern List_t * volatile pxOverflowDelayedTaskList;
extern List_t xPendingReadyList;
/* INCLUDE_vTaskDelete */
extern List_t xTasksWaitingTermination;
extern volatile UBaseType_t uxDeletedTasksWaitingCleanUp;
extern List_t xSuspendedTaskList;

extern volatile UBaseType_t uxCurrentNumberOfTasks;
extern volatile TickType_t xTickCount;
extern volatile UBaseType_t uxTopReadyPriority;
extern volatile BaseType_t xSchedulerRunning;
extern volatile TickType_t xPendedTicks;
extern volatile BaseType_t xYieldPending;
extern volatile BaseType_t xNumOfOverflows;
extern UBaseType_t uxTaskNumber;
extern volatile TickType_t xNextTaskUnblockTime;
extern TaskHandle_t xIdleTaskHandle;
extern volatile UBaseType_t uxSchedulerSuspended;

/* ===========================  GLOBAL VARIABLES  =========================== */
static StaticTask_t xIdleTaskTCB;
static StackType_t uxIdleTaskStack[ configMINIMAL_STACK_SIZE ];


/* ============================  HOOK FUNCTIONS  ============================ */
static void dummy_operation()
{
}

void port_allocate_secure_context( BaseType_t stackSize )
{
    HOOK_DIAG();
    port_allocate_secure_context_called = true;
}

void vApplicationIdleHook( void )
{
    HOOK_DIAG();
    vApplicationIdleHook_called = true;
}

void vApplicationMallocFailedHook( void )
{
    vApplicationMallocFailedHook_called = true;
    HOOK_DIAG();
}


void vApplicationGetIdleTaskMemory( StaticTask_t ** ppxIdleTaskTCBBuffer,
                                    StackType_t ** ppxIdleTaskStackBuffer,
                                    uint32_t * pulIdleTaskStackSize )
{
    HOOK_DIAG();
    if( getIddleTaskMemoryValid == true )
    {
        /* Pass out a pointer to the StaticTask_t structure in which the Idle task's
         * state will be stored. */
        *ppxIdleTaskTCBBuffer = &xIdleTaskTCB;

        /* Pass out the array that will be used as the Idle task's stack. */
        *ppxIdleTaskStackBuffer = uxIdleTaskStack;

        /* Pass out the size of the array pointed to by *ppxIdleTaskStackBuffer.
         * Note that, as the array is necessarily of type StackType_t,
         * configMINIMAL_STACK_SIZE is specified in words, not bytes. */
        *pulIdleTaskStackSize = configMINIMAL_STACK_SIZE;
    }
    else
    {
        *ppxIdleTaskTCBBuffer = NULL;
        *ppxIdleTaskStackBuffer = NULL;
        *pulIdleTaskStackSize = 0;
    }

    getIddleTaskMemoryCalled = true;
}

void vConfigureTimerForRunTimeStats( void )
{
    HOOK_DIAG();
}
long unsigned int ulGetRunTimeCounterValue( void )
{
    HOOK_DIAG();
    return 3;
}

void vApplicationTickHook()
{
    HOOK_DIAG();
    vApplicationTickHook_Called = true;
}

void vPortCurrentTaskDying( void * pvTaskToDelete,
                            volatile BaseType_t * pxPendYield )
{
    HOOK_DIAG();
    vTaskDeletePreCalled = true;
}

void vPortEnterCritical( void )
{
    HOOK_DIAG();
    critical_section_counter++;
}

void vPortExitCritical( void )
{
    HOOK_DIAG();
    critical_section_counter--;
}

void port_yield_cb()
{
    HOOK_DIAG();
    port_yield_called = true;
    py_operation();
}

void portSetupTCB_CB( void * tcb )
{
    HOOK_DIAG();
    port_setup_tcb_called = true;
}

void portClear_Interrupt_Mask(UBaseType_t bt)
{
    HOOK_DIAG();
    portClear_Interrupt_called = true;
}

UBaseType_t portSet_Interrupt_Mask( void )
{
    HOOK_DIAG();
    portSet_Interrupt_called = true;
    return 1;
}

void portAssert_if_int_prio_invalid(void)
{
    port_invalid_interrupt_called = true;
}

void vApplicationStackOverflowHook(TaskHandle_t xTask, char* stack)
{
    vApplicationStackOverflowHook_called = true;
}

/* ============================  Unity Fixtures  ============================ */
/*! called before each testcase */
void setUp( void )
{
    pxCurrentTCB = NULL;
    memset( &tcb, 0x00, sizeof( TCB_t ) );
    ptcb = NULL;
    memset( &pxReadyTasksLists, 0x00, configMAX_PRIORITIES * sizeof( List_t ) );
    memset( &xDelayedTaskList1, 0x00, sizeof( List_t ) );
    memset( &xDelayedTaskList2, 0x00, sizeof( List_t ) );
    /*
    pxDelayedTaskList = NULL;
    pxOverflowDelayedTaskList = NULL;
    */
    memset( &xPendingReadyList, 0x00, sizeof( List_t ) );

    memset( &xTasksWaitingTermination, 0x00, sizeof( List_t ) );
    uxDeletedTasksWaitingCleanUp = 0;
    memset( &xSuspendedTaskList, 0x00, sizeof( List_t ) );

    uxCurrentNumberOfTasks = ( UBaseType_t ) 0U;
    xTickCount = ( TickType_t ) 500; /* configINITIAL_TICK_COUNT */
    uxTopReadyPriority = tskIDLE_PRIORITY;
    xSchedulerRunning = pdFALSE;
    xPendedTicks = ( TickType_t ) 0U;
    xYieldPending = pdFALSE;
    xNumOfOverflows = ( BaseType_t ) 0;
    uxTaskNumber = ( UBaseType_t ) 0U;
    xNextTaskUnblockTime = ( TickType_t ) 0U;
    xIdleTaskHandle = NULL;
    uxSchedulerSuspended = ( UBaseType_t ) 0;
  //  ulTaskSwitchedInTime = 0UL;
    //ulTotalRunTime = 0UL;

    vApplicationTickHook_Called  = false;
    vTaskDeletePreCalled = false;
    getIddleTaskMemoryCalled = false;
    is_first_task = true;
    created_tasks = 0;
    port_yield_called  = false;
    port_setup_tcb_called = false;
    portClear_Interrupt_called = false;
    portSet_Interrupt_called = false;
    port_invalid_interrupt_called = false;
    vApplicationStackOverflowHook_called = false;
    py_operation = dummy_operation;
}

/*! called after each testcase */
void tearDown( void )
{
    TEST_ASSERT_EQUAL( 0, critical_section_counter );
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

/* ===========================  Static Functions  =========================== */



/* ==============================  Test Cases  ============================== */

/*!
 * @brief
 */
void test_dummy( void )
{
    TEST_PASS();
}
