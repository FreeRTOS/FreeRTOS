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
/*! @file smp_utest_common.h */

#ifndef SMP_UTEST_COMMON_H
#define SMP_UTEST_COMMON_H

/* C runtime includes. */
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>

/* Test includes. */
#include "unity.h"
#include "unity_memory.h"

/* FreeRTOS includes */
#include "FreeRTOS.h"
#include "task.h"
#include "global_vars.h"

/* ==========================  CALLBACK FUNCTIONS =========================== */

/**
 * @brief defines malloc() for this test and redirects it to unity_malloc
 * @param xSize size of memory block to be allocated
 * @return pointer to the allocated memory on success.
 * @return NULL if the memory could not be allocated.
 */
void * pvPortMalloc( size_t xSize );

/**
 * @brief defines free() for this test and redirects it to unity_free
 * @param pv pointer to the block to be freed
 */
void vPortFree( void * pv );

/* ==========================  Helper functions =========================== */

/**
 * @brief Common test case setup function for SMP tests.
 */
void commonSetUp( void );

/**
 * @brief Common test case asyncrhonous core yield setup function for SMP tests.
 * This API should be called after commonSetUp().
 */
void commonAsyncCoreYieldSetup( void );

/**
 * @brief Common test case teardown function for SMP tests.
 */
void commonTearDown( void );

/**
 * @brief Verify task current and run states
 */
void verifySmpTask( TaskHandle_t * xTaskHandle,
                    eTaskState eCurrentState,
                    TaskRunning_t xTaskRunState );

/**
 * @brief Verify the Idle task is executing on a specific core
 */
void verifyIdleTask( BaseType_t index,
                     TaskRunning_t xTaskRunState );

/**
 * @brief Dummy task for test execution
 */
void vSmpTestTask( void * pvParameters );

/**
 * @brief Helper function to simulate calling xTaskIncrementTick in critical section.
 */
void xTaskIncrementTick_helper( void );

/**
 * @brief Set the core ID returned by portGET_CORE_ID()
 */
void vSetCurrentCore( BaseType_t xCoreID );

/**
 * @brief Check and execut asynchronous core yield request.
 */
void vCheckAndExecuteAsyncCoreYield( BaseType_t xCoreID );

/**
 * @brief Helper function to create static test task.
 */
void vCreateStaticTestTask( TaskHandle_t xTaskHandle,
                            UBaseType_t uxPriority,
                            BaseType_t xTaskRunState,
                            BaseType_t xTaskIsIdle );

#if ( configUSE_CORE_AFFINITY == 1 )
    void vCreateStaticTestTaskAffinity( TaskHandle_t xTaskHandle,
                                        UBaseType_t uxCoreAffinityMask,
                                        UBaseType_t uxPriority,
                                        BaseType_t xTaskRunState,
                                        BaseType_t xTaskIsIdle );
#endif


#endif /* SMP_UTEST_COMMON_H */
