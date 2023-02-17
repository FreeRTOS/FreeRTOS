/*
 * FreeRTOS Kernel <DEVELOPMENT BRANCH>
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
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

/**
 * @file tasks_delete.c
 * @brief When a n RTOS object is deleted, the associated resources shall be freed.
 *
 * Procedure:
 *   - Create task A
 *   - Task A delete itself
 *   - Check if memory freed
 *   - Create task B
 *   - Delete task B in test runner task
 *   - Check if memory freed
 * Expected:
 *   - Have same remaining memory before creating task and after deleting task
 */

/* Kernel includes. */
#include "FreeRTOS.h" /* Must come first. */
#include "task.h"     /* RTOS task related API prototypes. */

#include "bsl.h"
#include "unity.h" /* unit testing support functions */

/*-----------------------------------------------------------*/

#define mainTASK_A_PRIORITY             ( tskIDLE_PRIORITY + 2 )

#define mainTASK_B_PRIORITY             ( tskIDLE_PRIORITY + 2 )

#define mainSOFTWARE_TIMER_PERIOD_MS    pdMS_TO_TICKS( 10 )

/*-----------------------------------------------------------*/

#if configNUMBER_OF_CORES <= 1
    #error Require two cores be configured for FreeRTOS
#endif /* if configNUMBER_OF_CORES <= 1 */

#if configRUN_MULTIPLE_PRIORITIES != 0
    #error configRUN_MULTIPLE_PRIORITIES shoud be 0 in this test case. Please check if testConfig.h is included.
#endif /* if configRUN_MULTIPLE_PRIORITIES != 0 */

#if configUSE_CORE_AFFINITY != 0
    #error configUSE_CORE_AFFINITY shoud be 0 in this test case. Please check if testConfig.h is included.
#endif /* if configUSE_CORE_AFFINITY != 0 */

/*-----------------------------------------------------------*/

/* Function declaration. */
static void vPrvTaskA( void * pvParameters );
static void vPrvTaskB( void * pvParameters );
static void fr07_memoryFreedTaskSelfDeleted();
static void fr07_memoryFreedTaskRemoteDeleted();

/*-----------------------------------------------------------*/

TaskHandle_t xTaskBHandler;

static volatile BaseType_t xTaskAState = 0;

static volatile BaseType_t xTaskBState = 0;

static uint32_t ulOriginalFreeHeapSize;

/*-----------------------------------------------------------*/

static void vPrvTaskA( void * pvParameters )
{
    xTaskAState++;

    vTaskDelete( NULL );
}

/*-----------------------------------------------------------*/

static void vPrvTaskB( void * pvParameters )
{
    xTaskBState++;

    /* idle the task */
    for( ; ; )
    {
        vTaskDelay( mainSOFTWARE_TIMER_PERIOD_MS );
    }
}

/*-----------------------------------------------------------*/

static void fr07_memoryFreedTaskSelfDeleted()
{
    uint32_t ulAttempt;
    uint32_t ulFreeHeapSize = 0;

    ulOriginalFreeHeapSize = xPortGetFreeHeapSize();

    /* Task A does delete itself when it runs. */
    xTaskCreate( vPrvTaskA, "TaskA", configMINIMAL_STACK_SIZE, NULL,
                 mainTASK_A_PRIORITY, NULL );

    while( xTaskAState <= 0 )
    {
        vTaskDelay( mainSOFTWARE_TIMER_PERIOD_MS );
    }

    /* Need to wait for task A to delete itself and FreeRTOS kernel to recycle memory. */
    for( ulAttempt = 1; ulAttempt < 100; ulAttempt++ )
    {
        /* Reserve for idle task to delete the entire task. */
        vTaskDelay( mainSOFTWARE_TIMER_PERIOD_MS );
        ulFreeHeapSize = xPortGetFreeHeapSize();

        if( ulFreeHeapSize == ulOriginalFreeHeapSize )
        {
            break;
        }
    }

    TEST_ASSERT_TRUE( ulFreeHeapSize == ulOriginalFreeHeapSize );
}

/*-----------------------------------------------------------*/

static void fr07_memoryFreedTaskRemoteDeleted()
{
    uint32_t ulAttempt;
    uint32_t ulFreeHeapSize = 0;

    ulOriginalFreeHeapSize = xPortGetFreeHeapSize();

    xTaskCreate( vPrvTaskB, "TaskB", configMINIMAL_STACK_SIZE, NULL,
                 mainTASK_B_PRIORITY, &xTaskBHandler );

    while( xTaskBState <= 0 )
    {
        vTaskDelay( mainSOFTWARE_TIMER_PERIOD_MS );
    }

    vTaskDelete( xTaskBHandler );

    /* Need to wait for FreeRTOS kernel to recycle memory. */
    for( ulAttempt = 1; ulAttempt < 100; ulAttempt++ )
    {
        /* Reserve for idle task to delete the entire task. */
        vTaskDelay( mainSOFTWARE_TIMER_PERIOD_MS );
        ulFreeHeapSize = xPortGetFreeHeapSize();

        if( ulFreeHeapSize == ulOriginalFreeHeapSize )
        {
            break;
        }
    }

    TEST_ASSERT_TRUE( ulFreeHeapSize == ulOriginalFreeHeapSize );
}

/*-----------------------------------------------------------*/

/**
 * @brief A start entry for test runner to run FR10.
 */
void vTestRunner( void )
{
    UNITY_BEGIN();

    RUN_TEST( fr07_memoryFreedTaskSelfDeleted );
    RUN_TEST( fr07_memoryFreedTaskRemoteDeleted );

    UNITY_END();
}

/*-----------------------------------------------------------*/
