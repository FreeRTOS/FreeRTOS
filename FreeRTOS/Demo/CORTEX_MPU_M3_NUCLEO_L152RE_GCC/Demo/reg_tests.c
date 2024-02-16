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

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Reg test includes. */
#include "reg_tests.h"

/* Hardware includes. */
#include "main.h"

/*
 * Functions that implement reg test tasks.
 */
static void prvRegTest1Task( void * pvParameters );
static void prvRegTest2Task( void * pvParameters );
static void prvRegTest3Task( void * pvParameters );
static void prvRegTest4Task( void * pvParameters );

/*
 * Check task periodically checks that reg tests tasks
 * are running fine.
 */
static void prvCheckTask( void * pvParameters );

/*
 * Functions implemented in assembly.
 */
extern void vRegTest1Asm( void ) __attribute__( ( naked ) );
extern void vRegTest2Asm( void ) __attribute__( ( naked ) );
extern void vRegTest3Asm( void ) __attribute__( ( naked ) );
extern void vRegTest4Asm( void ) __attribute__( ( naked ) );
/*-----------------------------------------------------------*/

/*
 * Priority of the check task.
 */
#define CHECK_TASK_PRIORITY                 ( configMAX_PRIORITIES - 1 )

/*
 * Frequency of check task.
 */
#define NO_ERROR_CHECK_TASK_PERIOD          ( pdMS_TO_TICKS( 5000UL ) )
#define ERROR_CHECK_TASK_PERIOD             ( pdMS_TO_TICKS( 200UL ) )

/*
 * Parameters passed to reg test tasks.
 */
#define REG_TEST_TASK_1_PARAMETER           ( ( void * ) 0x12345678 )
#define REG_TEST_TASK_2_PARAMETER           ( ( void * ) 0x87654321 )
#define REG_TEST_TASK_3_PARAMETER           ( ( void * ) 0x12348765 )
#define REG_TEST_TASK_4_PARAMETER           ( ( void * ) 0x43215678 )
/*-----------------------------------------------------------*/

/*
 * The following variables are used to communicate the status of the register
 * test tasks to the check task. If the variables keep incrementing, then the
 * register test tasks have not discovered any errors. If a variable stops
 * incrementing, then an error has been found.
 */
volatile unsigned long ulRegTest1LoopCounter = 0UL, ulRegTest2LoopCounter = 0UL;
volatile unsigned long ulRegTest3LoopCounter = 0UL, ulRegTest4LoopCounter = 0UL;

/**
 * Counter to keep a count of how may times the check task loop has detected
 * error.
 */
volatile unsigned long ulCheckTaskLoops = 0UL;
/*-----------------------------------------------------------*/

void vStartRegTests( void )
{
static StackType_t xRegTest1TaskStack[ configMINIMAL_STACK_SIZE ] __attribute__( ( aligned( configMINIMAL_STACK_SIZE * sizeof( StackType_t ) ) ) );
static StackType_t xRegTest2TaskStack[ configMINIMAL_STACK_SIZE ] __attribute__( ( aligned( configMINIMAL_STACK_SIZE * sizeof( StackType_t ) ) ) );
static StackType_t xRegTest3TaskStack[ configMINIMAL_STACK_SIZE ] __attribute__( ( aligned( configMINIMAL_STACK_SIZE * sizeof( StackType_t ) ) ) );
static StackType_t xRegTest4TaskStack[ configMINIMAL_STACK_SIZE ] __attribute__( ( aligned( configMINIMAL_STACK_SIZE * sizeof( StackType_t ) ) ) );
static StackType_t xCheckTaskStack[ configMINIMAL_STACK_SIZE ] __attribute__( ( aligned( configMINIMAL_STACK_SIZE * sizeof( StackType_t ) ) ) );

TaskParameters_t xRegTest1TaskParameters =
{
    .pvTaskCode      = prvRegTest1Task,
    .pcName          = "RegTest1",
    .usStackDepth    = configMINIMAL_STACK_SIZE,
    .pvParameters    = REG_TEST_TASK_1_PARAMETER,
    .uxPriority      = tskIDLE_PRIORITY | portPRIVILEGE_BIT,
    .puxStackBuffer  = xRegTest1TaskStack,
    .xRegions        =    {
                            { 0, 0, 0 },
                            { 0, 0, 0 },
                            { 0, 0, 0 }
                        }
};
TaskParameters_t xRegTest2TaskParameters =
{
    .pvTaskCode      = prvRegTest2Task,
    .pcName          = "RegTest2",
    .usStackDepth    = configMINIMAL_STACK_SIZE,
    .pvParameters    = REG_TEST_TASK_2_PARAMETER,
    .uxPriority      = tskIDLE_PRIORITY | portPRIVILEGE_BIT,
    .puxStackBuffer  = xRegTest2TaskStack,
    .xRegions        =    {
                            { 0, 0, 0 },
                            { 0, 0, 0 },
                            { 0, 0, 0 }
                        }
};
TaskParameters_t xRegTest3TaskParameters =
{
    .pvTaskCode      = prvRegTest3Task,
    .pcName          = "RegTest3",
    .usStackDepth    = configMINIMAL_STACK_SIZE,
    .pvParameters    = REG_TEST_TASK_3_PARAMETER,
    .uxPriority      = tskIDLE_PRIORITY | portPRIVILEGE_BIT,
    .puxStackBuffer  = xRegTest3TaskStack,
    .xRegions        =    {
                            { 0, 0, 0 },
                            { 0, 0, 0 },
                            { 0, 0, 0 }
                        }
};
TaskParameters_t xRegTest4TaskParameters =
{
    .pvTaskCode      = prvRegTest4Task,
    .pcName          = "RegTest4",
    .usStackDepth    = configMINIMAL_STACK_SIZE,
    .pvParameters    = REG_TEST_TASK_4_PARAMETER,
    .uxPriority      = tskIDLE_PRIORITY | portPRIVILEGE_BIT,
    .puxStackBuffer  = xRegTest4TaskStack,
    .xRegions        =    {
                            { 0, 0, 0 },
                            { 0, 0, 0 },
                            { 0, 0, 0 }
                        }
};

TaskParameters_t xCheckTaskParameters =
{
    .pvTaskCode      = prvCheckTask,
    .pcName          = "Check",
    .usStackDepth    = configMINIMAL_STACK_SIZE,
    .pvParameters    = NULL,
    .uxPriority      = ( CHECK_TASK_PRIORITY | portPRIVILEGE_BIT ),
    .puxStackBuffer  = xCheckTaskStack,
    .xRegions        =    {
                            { 0, 0, 0 },
                            { 0, 0, 0 },
                            { 0, 0, 0 }
                        }
};

    xTaskCreateRestricted( &( xRegTest1TaskParameters ), NULL );
    xTaskCreateRestricted( &( xRegTest2TaskParameters ), NULL );
    xTaskCreateRestricted( &( xRegTest3TaskParameters ), NULL );
    xTaskCreateRestricted( &( xRegTest4TaskParameters ), NULL );
    xTaskCreateRestricted( &( xCheckTaskParameters ), NULL );
}
/*-----------------------------------------------------------*/

static void prvRegTest1Task( void * pvParameters )
{
    /* Although the reg tests are written in assembly, its entry
     * point is written in C for convenience of checking that the
     * task parameter is being passed in correctly. */
    if( pvParameters == REG_TEST_TASK_1_PARAMETER )
    {
        /* Start the part of the test that is written in assembler. */
        vRegTest1Asm();
    }

    /* The following line will only execute if the task parameter
     * is found to be incorrect. The check task will detect that
     * the reg test loop counter is not being incremented and flag
     * an error. */
    vTaskDelete( NULL );
}
/*-----------------------------------------------------------*/

static void prvRegTest2Task( void * pvParameters )
{
    /* Although the reg tests are written in assembly, its entry
     * point is written in C for convenience of checking that the
     * task parameter is being passed in correctly. */
    if( pvParameters == REG_TEST_TASK_2_PARAMETER )
    {
        /* Start the part of the test that is written in assembler. */
        vRegTest2Asm();
    }

    /* The following line will only execute if the task parameter
     * is found to be incorrect. The check task will detect that
     * the reg test loop counter is not being incremented and flag
     * an error. */
    vTaskDelete( NULL );
}
/*-----------------------------------------------------------*/

static void prvRegTest3Task( void * pvParameters )
{
    /* Although the reg tests are written in assembly, its entry
     * point is written in C for convenience of checking that the
     * task parameter is being passed in correctly. */
    if( pvParameters == REG_TEST_TASK_3_PARAMETER )
    {
        /* Start the part of the test that is written in assembler. */
        vRegTest3Asm();
    }

    /* The following line will only execute if the task parameter
     * is found to be incorrect. The check task will detect that
     * the reg test loop counter is not being incremented and flag
     * an error. */
    vTaskDelete( NULL );
}
/*-----------------------------------------------------------*/

static void prvRegTest4Task( void * pvParameters )
{
    /* Although the reg tests are written in assembly, its entry
     * point is written in C for convenience of checking that the
     * task parameter is being passed in correctly. */
    if( pvParameters == REG_TEST_TASK_4_PARAMETER )
    {
        /* Start the part of the test that is written in assembler. */
        vRegTest4Asm();
    }

    /* The following line will only execute if the task parameter
     * is found to be incorrect. The check task will detect that
     * the reg test loop counter is not being incremented and flag
     * an error. */
    vTaskDelete( NULL );
}
/*-----------------------------------------------------------*/

static void prvCheckTask( void * pvParameters )
{
TickType_t xDelayPeriod = NO_ERROR_CHECK_TASK_PERIOD;
TickType_t xLastExecutionTime;
unsigned long ulErrorFound = pdFALSE;
static unsigned long ulLastRegTest1Value = 0, ulLastRegTest2Value = 0;
static unsigned long ulLastRegTest3Value = 0, ulLastRegTest4Value = 0;

    /* Just to stop compiler warnings. */
    ( void ) pvParameters;

    /* Initialize xLastExecutionTime so the first call to vTaskDelayUntil()
     * works correctly. */
    xLastExecutionTime = xTaskGetTickCount();

    /* Cycle for ever, delaying then checking all the other tasks are still
     * operating without error.  The onboard LED is toggled on each iteration.
     * If an error is detected then the delay period is decreased from
     * mainNO_ERROR_CHECK_TASK_PERIOD to mainERROR_CHECK_TASK_PERIOD.  This has
     * the effect of increasing the rate at which the onboard LED toggles, and
     * in so doing gives visual feedback of the system status. */
    for( ;; )
    {
        /* Delay until it is time to execute again. */
        vTaskDelayUntil( &xLastExecutionTime, xDelayPeriod );

        /* Check that the register test 1 task is still running. */
        if( ulLastRegTest1Value == ulRegTest1LoopCounter )
        {
            ulErrorFound |= 1UL << 0UL;
        }
        ulLastRegTest1Value = ulRegTest1LoopCounter;

        /* Check that the register test 2 task is still running. */
        if( ulLastRegTest2Value == ulRegTest2LoopCounter )
        {
            ulErrorFound |= 1UL << 1UL;
        }
        ulLastRegTest2Value = ulRegTest2LoopCounter;

        /* Check that the register test 3 task is still running. */
        if( ulLastRegTest3Value == ulRegTest3LoopCounter )
        {
            ulErrorFound |= 1UL << 2UL;
        }
        ulLastRegTest3Value = ulRegTest3LoopCounter;

        /* Check that the register test 4 task is still running. */
        if( ulLastRegTest4Value == ulRegTest4LoopCounter )
        {
            ulErrorFound |= 1UL << 3UL;
        }
        ulLastRegTest4Value = ulRegTest4LoopCounter;


        /* Toggle the Green LED to give an indication of the system status.
         * If the LED toggles every NO_ERROR_CHECK_TASK_PERIOD milliseconds
         * then everything is ok. A faster toggle indicates an error. */
        HAL_GPIO_TogglePin( LD2_GPIO_Port, LD2_Pin );

        if( ulErrorFound != pdFALSE )
        {
            /* An error has been detected in one of the tasks - flash the LED
             * at a higher frequency to give visible feedback that something has
             * gone wrong. */
            xDelayPeriod = ERROR_CHECK_TASK_PERIOD;

            /* Increment error detection count. */
            ulCheckTaskLoops++;
        }
    }
}
/*-----------------------------------------------------------*/
