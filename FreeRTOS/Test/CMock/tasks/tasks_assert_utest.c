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
/*! @file tasks_assert_utest.c */

/* ===============================  INCLUDES  =============================== */
/* Tasks includes */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"
#include "fake_port.h"
#include "task.h"

/* C runtime includes. */
#include <stdlib.h>
#include <stdbool.h>

/* Test includes. */
#include "unity.h"
#include "unity_memory.h"
#include "CException.h"
#include "global_vars.h"

/* Mock includes. */
#include "mock_fake_assert.h"
#include "mock_portable.h"

/* =================================  MACROS  =============================== */

/**
 * @brief CException code for when a configASSERT should be intercepted.
 */
#define configASSERT_E                       0xAA101
/**
 * @brief Expect a configASSERT from the function called.
 *  Break out of the called function when this occurs.
 * @details Use this macro when the call passed in as a parameter is expected
 * to cause invalid memory access.
 */
#define EXPECT_ASSERT_BREAK( call )                 \
    do                                              \
    {                                               \
        shouldAbortOnAssertion = true;              \
        CEXCEPTION_T e = CEXCEPTION_NONE;           \
        Try                                         \
        {                                           \
            call;                                   \
            TEST_FAIL();                            \
        }                                           \
        Catch( e )                                  \
        {                                           \
            TEST_ASSERT_EQUAL( configASSERT_E, e ); \
        }                                           \
    } while( 0 )

/* ============================  GLOBAL VARIABLES =========================== */
/**
 * @brief Global counter for the number of assertions in code.
 */
static int assertionFailed = 0;

/**
 * @brief Flag which denotes if test need to abort on assertion.
 */
static BaseType_t shouldAbortOnAssertion;

/**
 * @brief counts entries to critical sections then subtracts from the variable
 *        when exiting, value should be zero at the end
 */
static uint32_t critical_section_counter = 0;

static bool port_yield_within_api_called = false;
static port_yield_operation py_operation;
static bool port_disable_interrupts_called = false;
static bool port_enable_interrupts_called = false;
static bool port_yield_called = false;
static bool port_setup_tcb_called = false;
static bool portClear_Interrupt_called = false;
static bool portSet_Interrupt_called = false;
static bool portClear_Interrupt_from_isr_called = false;
static bool portSet_Interrupt_from_isr_called = false;
static bool port_invalid_interrupt_called = false;
static bool vApplicationStackOverflowHook_called = false;
static bool getIddleTaskMemoryValid = false;
static StaticTask_t xIdleTaskTCB;
static StackType_t uxIdleTaskStack[ configMINIMAL_STACK_SIZE ];
static bool getIddleTaskMemory_called = false;
static bool vTaskDeletePre_called = false;
static bool vApplicationIdleHook_called = false;
static bool vApplicationTickHook_called = false;

/* ==========================  CALLBACK FUNCTIONS  ========================== */
static void vFakeAssertStub( bool x,
                             char * file,
                             int line,
                             int cmock_num_calls )
{
    if( !x )
    {
        assertionFailed++;

        if( shouldAbortOnAssertion == pdTRUE )
        {
            Throw( configASSERT_E );
        }
    }
}

/* ==========================  STATIC FUNCTIONS  ============================ */
static void validate_and_clear_assertions( void )
{
    TEST_ASSERT_EQUAL( 1, assertionFailed );
    assertionFailed = 0;
}



/* ========================  HOOK FUNCTIONS  =================================*/
void vApplicationTickHook()
{
    HOOK_DIAG();
    vApplicationTickHook_called = true;
}

void vApplicationIdleHook( void )
{
    HOOK_DIAG();
    vApplicationIdleHook_called = true;
}

void vConfigureTimerForRunTimeStats( void )
{
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

    getIddleTaskMemory_called = true;
}

void vPortCurrentTaskDying( void * pvTaskToDelete,
                            volatile BaseType_t * pxPendYield )
{
    HOOK_DIAG();
    vTaskDeletePre_called = true;
}

void vFakePortEnterCriticalSection( void )
{
    HOOK_DIAG();
    critical_section_counter++;
}

void vFakePortExitCriticalSection( void )
{
    HOOK_DIAG();
    critical_section_counter--;
}

void vFakePortYieldWithinAPI()
{
    HOOK_DIAG();
    port_yield_within_api_called = true;
    py_operation();
}

void vFakePortYieldFromISR()
{
    HOOK_DIAG();
}

uint32_t vFakePortDisableInterrupts()
{
    port_disable_interrupts_called = true;
    HOOK_DIAG();
    return 0;
}

void vFakePortEnableInterrupts()
{
    port_enable_interrupts_called = true;
    HOOK_DIAG();
}

void vFakePortYield()
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

void vFakePortClearInterruptMask( UBaseType_t bt )
{
    HOOK_DIAG();
    portClear_Interrupt_called = true;
}

UBaseType_t ulFakePortSetInterruptMask( void )
{
    HOOK_DIAG();
    portSet_Interrupt_called = true;
    return 1;
}

void vFakePortClearInterruptMaskFromISR( UBaseType_t bt )
{
    HOOK_DIAG();
    portClear_Interrupt_from_isr_called = true;
}

UBaseType_t ulFakePortSetInterruptMaskFromISR( void )
{
    HOOK_DIAG();
    portSet_Interrupt_from_isr_called = true;
    return 1;
}

void vFakePortAssertIfInterruptPriorityInvalid( void )
{
    HOOK_DIAG();
    port_invalid_interrupt_called = true;
}

void vApplicationStackOverflowHook( TaskHandle_t xTask,
                                    char * stack )
{
    HOOK_DIAG();
    vApplicationStackOverflowHook_called = true;
}

unsigned int vFakePortGetCoreID( void )
{
    HOOK_DIAG();
    return 0;
}

void vFakePortReleaseTaskLock (void )
{
    HOOK_DIAG();
}

void vFakePortGetTaskLock( void )
{
    HOOK_DIAG();
}

void vFakePortGetISRLock( void )
{
    HOOK_DIAG();
}

void vFakePortReleaseISRLock( void )
{
    HOOK_DIAG();
}

/* ===========================  UNITY FIXTURES  ============================= */
/*! called before each test case */
void setUp( void )
{
    assertionFailed = 0;
    shouldAbortOnAssertion = pdTRUE;
    vFakeAssert_StubWithCallback( vFakeAssertStub );
}

/*! called after each test case */
void tearDown( void )
{
    TEST_ASSERT_EQUAL_MESSAGE( 0, assertionFailed, "Assertion check failed in code." );

    mock_fake_assert_Verify();
    mock_fake_assert_Destroy();
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

/* ========================  TEST CASES ===================================== */
/*!
 * @brief This function ensures that the code asserts if the handle name is
 *        greater than configMAX_TASK_NAME_LEN
 */
void test_xTaskGetHandle_assert_large_handle_name( void )
{
    int bigSize = configMAX_TASK_NAME_LEN  + 5;
    char handleName[ bigSize ];
    int i ;

    for( i = 0; i < bigSize; ++i )
    {
        handleName[i] = 'a';
    }
    handleName[ bigSize - 1 ] = '\0';

    EXPECT_ASSERT_BREAK( ( void ) xTaskGetHandle( handleName ) );
    validate_and_clear_assertions();
}

/*!
 * @brief this function ensures that the code asserts if the value of
 *        uxSchedulerSuspended is 1
 */
void test_xTaskResumeAll_assert_scheduler_not_started( void )
{
    vTaskSuspendAll();

    EXPECT_ASSERT_BREAK( ( void ) xTaskResumeAll( ) );

    validate_and_clear_assertions();
}

void test_vTaskGenericNotifyGiveFromISR_assert_xTaskNotify_NULL( void )
{
    BaseType_t pxHigherPriorityTaskWoken;

    EXPECT_ASSERT_BREAK( vTaskGenericNotifyGiveFromISR( NULL,
                                                        1,
                                                        &pxHigherPriorityTaskWoken) );

    validate_and_clear_assertions();
}

void test_vTaskGenericNotifyGiveFromISR_assert_uxIndexToNotify_out_of_bound( void )
{
    BaseType_t pxHigherPriorityTaskWoken;

    TaskHandle_t xTaskToNotify = (TaskHandle_t )0x1234;

    EXPECT_ASSERT_BREAK( vTaskGenericNotifyGiveFromISR( xTaskToNotify,
                                                        configTASK_NOTIFICATION_ARRAY_ENTRIES + 1,
                                                        &pxHigherPriorityTaskWoken) );

    validate_and_clear_assertions();
}
