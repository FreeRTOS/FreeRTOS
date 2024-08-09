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

/* Standard includes. */
#include <stdint.h>

/* FreeRTOS includes. */
#include "FreeRTOSConfig.h"
#include "FreeRTOS.h"
#include "task.h"
#include "portmacro.h"

/* HalCoGen includes. */
#include "sci.h"

/* Demo include */
#include "demo_tasks.h"

/* ----------------------------------------------------------------------------------- */

/** @brief TCB used by Register Test Task One. */
static StaticTask_t xRegTestOneTaskTCB;

/** @brief Stack used by Register Test Task One. */
static StackType_t uxRegTestOneTaskStack[ configMINIMAL_STACK_SIZE / 2U ];

/** @brief TCB used by Register Test Two Task. */
static StaticTask_t xRegTestTwoTaskTCB;

/** @brief Stack used by Register Test Task Two. */
static StackType_t uxRegTestTwoTaskStack[ configMINIMAL_STACK_SIZE / 2U ];

/* Parameters that are passed into the register check tasks solely for the
 * purpose of ensuring parameters are passed into tasks correctly. */
#define mainREG_TEST_TASK_1_PARAMETER    ( ( void * ) 0x12345678 )
#define mainREG_TEST_TASK_2_PARAMETER    ( ( void * ) 0x87654321 )

/* ----------------------------------------------------------------------------------- */

/** @brief Array to track the number of loops the register test tasks have run.
 *
 * Register Test One will use loopCount[0];
 * Register Test Two Will use loopCount[1];
 */
uint32_t loopCounter[ 0x8 ];

/** @brief Statically allocated task handle for the first register task. */
static TaskHandle_t xRegisterTaskOneHandle;

/** @brief Statically allocated task handle for the second register task. */
static TaskHandle_t xRegisterTaskTwoHandle;

/* ----------------------------------------------------------------------------------- */

/** @brief Entry point for the Register Test 1 Task.
 * @param pvParameters A test value to ensure the task's arguments are correctly set.
 * @note This task runs in a loop to ensure that all General and Floating Point Registers
 * don't change. Any change in value in the registers can only occur due to an improper
 * context save or load.
 */
static void prvRegTestTaskEntry1( void * pvParameters )
{
    /** Although the Register Test task is written in assembly, its entry point
     * is written in C for convenience of checking the task parameter is being
     * passed in correctly. */
    if( pvParameters == mainREG_TEST_TASK_1_PARAMETER )
    {
        /* Start the part of the test that is written in assembler. */
        vRegTest1Implementation();
    }
    else
    {
        /** The following line will only execute if the task parameter is found to
         * be incorrect. The check task will detect that the regtest loop counter
         * is not being incremented and flag an error. */
        vTaskDelete( NULL );
    }
}

/* ----------------------------------------------------------------------------------- */

/** @brief Entry point for the Register Test 2 Task.
 * @param pvParameters A test value to ensure the task's arguments are correctly set.
 * @note This task runs in a loop to ensure that all General and Floating Point Registers
 * don't change. Any change in value in the registers can only occur due to an improper
 * context save or load.
 */
static void prvRegTestTaskEntry2( void * pvParameters )
{
    /** Although the Register Test task is written in assembly, its entry point
     * is written in C for convenience of checking the task parameter is being
     * passed in correctly. */
    if( pvParameters == mainREG_TEST_TASK_2_PARAMETER )
    {
        /* Start the part of the test that is written in assembler. */
        vRegTest2Implementation();
    }
    else
    {
        /* The following line will only execute if the task parameter is found to
         * be incorrect. The check task will detect that the regtest loop counter
         * is not being incremented and flag an error. */
        vTaskDelete( NULL );
    }
}

/* ----------------------------------------------------------------------------------- */

BaseType_t xCreateRegisterTestTasks( void )
{
    BaseType_t xReturn = pdFAIL;

    /* Create the register check tasks, as described at the top of this file. */

    /* Create the first register test task. */
    xRegisterTaskOneHandle = xTaskCreateStatic( prvRegTestTaskEntry1,
                                                "RegTestOne",
                                                configMINIMAL_STACK_SIZE / 0x2,
                                                mainREG_TEST_TASK_1_PARAMETER,
                                                demoREG_TASK_1_PRIORITY,
                                                uxRegTestOneTaskStack,
                                                &xRegTestOneTaskTCB );

    if( xRegisterTaskOneHandle != NULL )
    {
        sci_print( "Created the Register Test 1 Task\r\n" );

        /* Create the second register test task. */
        xRegisterTaskTwoHandle = xTaskCreateStatic( prvRegTestTaskEntry2,
                                                    "RegTestTwo",
                                                    configMINIMAL_STACK_SIZE / 0x2,
                                                    mainREG_TEST_TASK_2_PARAMETER,
                                                    demoREG_TASK_2_PRIORITY,
                                                    uxRegTestTwoTaskStack,
                                                    &xRegTestTwoTaskTCB );

        if( xRegisterTaskTwoHandle != NULL )
        {
            sci_print( "Created the Register Test 2 Task\r\n" );
            xReturn = pdPASS;
        }
        else
        {
            sci_print( "Failed to create the Register Test 2 Task\r\n" );
        }
    }
    else
    {
        sci_print( "Failed to create the Register Test 1 Task\r\n" );
    }

    return xReturn;
}
