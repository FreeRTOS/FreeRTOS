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
/*! @file tasks_utest.c */

/* C runtime includes. */
#include <stdlib.h>
#include <stdbool.h>

/* Tasks includes */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"
#include "task.h"

/* Test includes. */
#include "unity.h"

/* ===========================  DEFINES CONSTANTS  ========================== */

/* ===========================  GLOBAL VARIABLES  =========================== */


/* ============================  Unity Fixtures  ============================ */
/*! called before each testcase */
void setUp( void )
{
}

/*! called after each testcase */
void tearDown( void )
{
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

void vPortEnterCritical( void )
{
}

void vPortExitCritical( void )
{
}

void vPortCurrentTaskDying( void * pvTaskToDelete,
                            volatile BaseType_t * pxPendYield )
{
}

void vApplicationIdleHook( void )
{
}

void vApplicationMallocFailedHook( void )
{
}

void vApplicationGetIdleTaskMemory( StaticTask_t ** a,
                                    StackType_t ** b,
                                    uint32_t * c )
{
}
void vConfigureTimerForRunTimeStats( void )
{
}
long unsigned int ulGetRunTimeCounterValue( void )
{
    return 3;
}
void vApplicationTickHook()
{
}

void  port_yield_cb()
{
}

void portSetupTCB_CB( void * tcb )
{
}

void portClear_Interrupt_Mask(UBaseType_t bt)
{
}

UBaseType_t portSet_Interrupt_Mask( void )
{
    return 1;
}

void portAssert_if_int_prio_invalid(void)
{
}

/*!
 * @brief
 */
void test_dummy( void )
{
    TEST_PASS();
}
