/*
 * FreeRTOS V202212.00
 * Copyright (C) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

/** @brief TCB used by Register Test Task One */
PRIVILEGED_DATA static StaticTask_t xRegTestOneTaskTCB;

/** @brief Small MPU Region Aligned Stack used by Register Test Task One */
PRIVILEGED_DATA static StackType_t uxRegTestOneTaskStack[ configMINIMAL_STACK_SIZE / 2U ]
    __attribute__( ( aligned( configMINIMAL_STACK_SIZE * 0x2U ) ) );

/** @brief TCB used by Register Test Two Task */
PRIVILEGED_DATA static StaticTask_t xRegTestTwoTaskTCB;

/** @brief Small MPU Region Aligned Stack used by Register Test Task Two */
static StackType_t uxRegTestTwoTaskStack[ configMINIMAL_STACK_SIZE / 2U ]
    __attribute__( ( aligned( configMINIMAL_STACK_SIZE * 0x2U ) ) );

/* Parameters that are passed into the register check tasks solely for the
 * purpose of ensuring parameters are passed into tasks correctly. */
#define mainREG_TEST_TASK_1_PARAMETER ( ( void * ) 0x12345678 )
#define mainREG_TEST_TASK_2_PARAMETER ( ( void * ) 0x87654321 )

/* ----------------------------------------------------------------------------------- */

/** @brief Array to track the number of loops the register test tasks have run.
 *
 * @note Smallest valid MPU region size for Armv7-R is 32 bytes.
 * Register Test One will use loopCount[0];
 * Register Test Two Will use loopCount[1];
 */
uint32_t loopCounter[ 0x8 ] __attribute__( ( aligned( 0x20 ) ) );

/* ----------------------------------------------------------------------------------- */

/** @brief Entry point for the Privileged Register Test Task.
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

/** @brief Entry point for the Unprivileged Register Test Task.
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
    TaskParameters_t  xRegTestOneTaskParameters =  {
        /* The function that implements the task. */
        .pvTaskCode = prvRegTestTaskEntry1,
        /* The name of the task. */
        .pcName = "RegTestOne",
        /* Size of stack to allocate for the task - in words not bytes!. */
        .usStackDepth = configMINIMAL_STACK_SIZE / 0x2,
        /* Parameter passed into the task. */
        .pvParameters = mainREG_TEST_TASK_1_PARAMETER,
        /* Priority of the task. */
        .uxPriority = demoREG_PRIVILEGED_TASK_PRIORITY | portPRIVILEGE_BIT,
        .puxStackBuffer = uxRegTestOneTaskStack,
        .pxTaskBuffer = &xRegTestOneTaskTCB,
        .xRegions = {
                    /* MPU Region 0 */
                    { loopCounter,
                      0x20,
                      portMPU_REGION_PRIV_RW_USER_RW_NOEXEC | portMPU_REGION_NORMAL_OIWTNOWA_SHARED,
                    },
                    /* MPU Region 1 */
                    { 0, 0, 0 },
                    /* MPU Region 2 */
                    { 0, 0, 0 },
                    /* MPU Region 3 */
                    { 0, 0, 0 },
                    /* MPU Region 4 */
                    { 0, 0, 0 },
                    /* MPU Region 5 */
                    { 0, 0, 0 },
                    /* MPU Region 6 */
                    { 0, 0, 0 },
#if( configTOTAL_MPU_REGIONS == 16 )
                        /* MPU Region 7 */
                        { 0, 0, 0 },
                        /* MPU Region 8 */
                        { 0, 0, 0 },
                        /* MPU Region 9 */
                        { 0, 0, 0 },
                        /* MPU Region 10 */
                        { 0, 0, 0 },
#endif
                    /* Final MPU Region */
                    { 0, 0, 0 },
        }
    };

    TaskParameters_t xRegTestTwoTaskParameters = {
         /* The function that implements the task. */
        .pvTaskCode = prvRegTestTaskEntry2,
        /* The name of the task. */
        .pcName = "RegTestTwo",
        /* Size of stack to allocate for the task - in words not bytes!. */
        .usStackDepth = configMINIMAL_STACK_SIZE / 0x2,
        /* Parameter passed into the task. */
        .pvParameters = mainREG_TEST_TASK_2_PARAMETER,
        /* Priority of the task. */
        .uxPriority = demoREG_UNPRIVILEGED_TASK_PRIORITY,
        .puxStackBuffer = uxRegTestTwoTaskStack,
        .pxTaskBuffer = &xRegTestTwoTaskTCB,
        .xRegions = {
                     /* MPU Region 0 */
                     { loopCounter,
                       0x20,
                       portMPU_REGION_PRIV_RW_USER_RW_NOEXEC | portMPU_REGION_NORMAL_OIWTNOWA_SHARED,
                     },
                    /* MPU Region 1 */
                    { 0, 0, 0 },
                    /* MPU Region 2 */
                    { 0, 0, 0 },
                    /* MPU Region 3 */
                    { 0, 0, 0 },
                    /* MPU Region 4 */
                    { 0, 0, 0 },
                    /* MPU Region 5 */
                    { 0, 0, 0 },
                    /* MPU Region 6 */
                    { 0, 0, 0 },
#if( configTOTAL_MPU_REGIONS == 16 )
                    /* MPU Region 7 */
                    { 0, 0, 0 },
                    /* MPU Region 8 */
                    { 0, 0, 0 },
                    /* MPU Region 9 */
                    { 0, 0, 0 },
                    /* MPU Region 10 */
                    { 0, 0, 0 },
#endif
                    /* Final MPU Region */
                    { 0, 0, 0 },
        }
    };

    /* Create the first register test task as a privileged task */
    xReturn = xTaskCreateRestrictedStatic( &( xRegTestOneTaskParameters ), NULL );
    if( pdPASS == xReturn )
    {
        /* Create the second register test task as an unprivileged task */
        xReturn = xTaskCreateRestrictedStatic( &( xRegTestTwoTaskParameters ), NULL );
        if( pdPASS == xReturn )
        {
            sci_print( "Created the Unprivileged Regsiter Test Task\r\n" );
        }
        else
        {
            sci_print( "Failed to create the Unprivileged Regsiter Test Task\r\n" );
        }
    }
    else
    {
        sci_print( "Failed to create the Privileged Regsiter Test Task\r\n" );
    }

    return xReturn;
}
