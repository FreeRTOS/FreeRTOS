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
#include "reg_test_asm.h"
#if( configENABLE_TRUSTZONE == 1 )
    #include "secure_reg_test_asm.h"
#endif

/* Device includes. */
#include "NuMicro.h"

/*
 * Functions that implement reg test tasks.
 */
static void prvRegTest1_Task( void * pvParameters );
static void prvRegTest2_Task( void * pvParameters );
#if( configENABLE_TRUSTZONE == 1 )
    static void prvRegTest_Secure_Task( void * pvParameters );
    static void prvRegTest_NonSecureCallback_Task( void * pvParameters );
#endif
/*
 * Check task periodically checks that reg tests tasks
 * are running fine.
 */
static void prvCheckTask( void * pvParameters );
/*-----------------------------------------------------------*/

/*
 * On board LEDs.
 */
#if( configENABLE_TRUSTZONE == 1 )
    #define YELLOW_LED  PA11_NS
    #define GREEN_LED   PA10_NS
#else
    #define YELLOW_LED  PA11
    #define GREEN_LED   PA10
#endif

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
#define REG_TEST_1_TASK_PARAMETER                   ( ( void * ) 0x12345678 )
#define REG_TEST_2_TASK_PARAMETER                   ( ( void * ) 0x87654321 )
#define REG_TEST_SECURE_TASK_PARAMETER              ( ( void * ) 0x1234ABCD )
#define REG_TEST_NON_SECURE_CALLBACK_TASK_PARAMETER ( ( void * ) 0xABCD1234 )
/*-----------------------------------------------------------*/

/*
 * The following variables are used to communicate the status of the register
 * test tasks to the check task. If the variables keep incrementing, then the
 * register test tasks have not discovered any errors. If a variable stops
 * incrementing, then an error has been found.
 */
volatile unsigned long ulRegTest1LoopCounter = 0UL, ulRegTest2LoopCounter = 0UL;
#if( configENABLE_TRUSTZONE == 1 )
    volatile unsigned long ulRegTestSecureLoopCounter = 0UL;
    volatile unsigned long ulRegTestNonSecureCallbackLoopCounter = 0UL;
#endif

/**
 * Counter to keep a count of how may times the check task loop has detected
 * error.
 */
volatile unsigned long ulCheckTaskLoops = 0UL;
/*-----------------------------------------------------------*/

void vStartRegTests( void )
{
static StackType_t xRegTest1TaskStack[ configMINIMAL_STACK_SIZE ] __attribute__( ( aligned( 32 ) ) );
static StackType_t xRegTest2TaskStack[ configMINIMAL_STACK_SIZE ] __attribute__( ( aligned( 32 ) ) );
static StackType_t xCheckTaskStack[ configMINIMAL_STACK_SIZE ] __attribute__( ( aligned( 32 ) ) );
#if( configENABLE_TRUSTZONE == 1 )
    static StackType_t xRegTestSecureTaskStack[ configMINIMAL_STACK_SIZE ] __attribute__( ( aligned( 32 ) ) );
    static StackType_t xRegTestNonSecureCallbackTaskStack[ configMINIMAL_STACK_SIZE ] __attribute__( ( aligned( 32 ) ) );
#endif

TaskParameters_t xRegTest1TaskParameters =
{
    .pvTaskCode      = prvRegTest1_Task,
    .pcName          = "RegTest1",
    .usStackDepth    = configMINIMAL_STACK_SIZE,
    .pvParameters    = REG_TEST_1_TASK_PARAMETER,
    .uxPriority      = tskIDLE_PRIORITY | portPRIVILEGE_BIT,
    .puxStackBuffer  = xRegTest1TaskStack,
    .xRegions        =  {
                            { 0, 0, 0 },
                            { 0, 0, 0 },
                            { 0, 0, 0 }
                        }
};
TaskParameters_t xRegTest2TaskParameters =
{
    .pvTaskCode      = prvRegTest2_Task,
    .pcName          = "RegTest2",
    .usStackDepth    = configMINIMAL_STACK_SIZE,
    .pvParameters    = REG_TEST_2_TASK_PARAMETER,
    .uxPriority      = tskIDLE_PRIORITY | portPRIVILEGE_BIT,
    .puxStackBuffer  = xRegTest2TaskStack,
    .xRegions        =  {
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
    .xRegions        =  {
                            { 0, 0, 0 },
                            { 0, 0, 0 },
                            { 0, 0, 0 }
                        }
};

#if( configENABLE_TRUSTZONE == 1 )
    TaskParameters_t xRegTestSecureTaskParameters =
    {
        .pvTaskCode      = prvRegTest_Secure_Task,
        .pcName          = "RegTestSecure",
        .usStackDepth    = configMINIMAL_STACK_SIZE,
        .pvParameters    = REG_TEST_SECURE_TASK_PARAMETER,
        .uxPriority      = tskIDLE_PRIORITY | portPRIVILEGE_BIT,
        .puxStackBuffer  = xRegTestSecureTaskStack,
        .xRegions        =  {
                                { 0, 0, 0 },
                                { 0, 0, 0 },
                                { 0, 0, 0 }
                            }
    };
    TaskParameters_t xRegTestNonSecureCallbackTaskParameters =
    {
        .pvTaskCode      = prvRegTest_NonSecureCallback_Task,
        .pcName          = "RegTestNonSecureCallback",
        .usStackDepth    = configMINIMAL_STACK_SIZE,
        .pvParameters    = REG_TEST_NON_SECURE_CALLBACK_TASK_PARAMETER,
        .uxPriority      = tskIDLE_PRIORITY | portPRIVILEGE_BIT,
        .puxStackBuffer  = xRegTestNonSecureCallbackTaskStack,
        .xRegions        =  {
                                { 0, 0, 0 },
                                { 0, 0, 0 },
                                { 0, 0, 0 }
                            }
    };
#endif /* configENABLE_TRUSTZONE */

    /* Configure pins in output mode to drive external LEDs. */
    #if( configENABLE_TRUSTZONE == 1 )
        GPIO_SetMode( PA_NS, BIT10 | BIT11, GPIO_MODE_OUTPUT );
    #else
        GPIO_SetMode( PA, BIT10 | BIT11, GPIO_MODE_OUTPUT );
    #endif

    /* Start with both LEDs off. */
    YELLOW_LED = 1;
    GREEN_LED = 1;

    xTaskCreateRestricted( &( xRegTest1TaskParameters ), NULL );
    xTaskCreateRestricted( &( xRegTest2TaskParameters ), NULL );
    xTaskCreateRestricted( &( xCheckTaskParameters ), NULL );
    #if( configENABLE_TRUSTZONE == 1 )
        xTaskCreateRestricted( &( xRegTestSecureTaskParameters ), NULL );
        xTaskCreateRestricted( &( xRegTestNonSecureCallbackTaskParameters ), NULL );
    #endif
}
/*-----------------------------------------------------------*/

static void prvRegTest1_Task( void * pvParameters )
{
    /* Although the reg tests are written in assembly, its entry
     * point is written in C for convenience of checking that the
     * task parameter is being passed in correctly. */
    if( pvParameters == REG_TEST_1_TASK_PARAMETER )
    {
        /* Start the part of the test that is written in assembler. */
        vRegTest1Asm_NonSecure();
    }

    /* The following line will only execute if the task parameter
     * is found to be incorrect. The check task will detect that
     * the reg test loop counter is not being incremented and flag
     * an error. */
    vTaskDelete( NULL );
}
/*-----------------------------------------------------------*/

static void prvRegTest2_Task( void * pvParameters )
{
    /* Although the reg tests are written in assembly, its entry
     * point is written in C for convenience of checking that the
     * task parameter is being passed in correctly. */
    if( pvParameters == REG_TEST_2_TASK_PARAMETER )
    {
        /* Start the part of the test that is written in assembler. */
        vRegTest2Asm_NonSecure();
    }

    /* The following line will only execute if the task parameter
     * is found to be incorrect. The check task will detect that
     * the reg test loop counter is not being incremented and flag
     * an error. */
    vTaskDelete( NULL );
}
/*-----------------------------------------------------------*/

#if( configENABLE_TRUSTZONE == 1 )

static void prvRegTest_Secure_Task( void * pvParameters )
{
    /* This task is going to call secure side functions. */
    portALLOCATE_SECURE_CONTEXT( configMINIMAL_SECURE_STACK_SIZE );

    /* Although the reg tests are written in assembly, its entry
     * point is written in C for convenience of checking that the
     * task parameter is being passed in correctly. */
    if( pvParameters == REG_TEST_SECURE_TASK_PARAMETER )
    {
        for( ;; )
        {
            /* Call the secure side function. This function populates registers
             * with known values, then forces a context switch while on the
             * secure side and then verifies that the contents of the registers
             * are intact. This ensure that the context restoring mechanism
             * works properly when the interrupted task was in the middle of a
             * call to a secure side function. */
            vRegTestAsm_Secure();

            ulRegTestSecureLoopCounter += 1;
        }
    }

    /* The following line will only execute if the task parameter
     * is found to be incorrect. The check task will detect that
     * the reg test loop counter is not being incremented and flag
     * an error. */
    vTaskDelete( NULL );
}

#endif
/*-----------------------------------------------------------*/

#if( configENABLE_TRUSTZONE == 1 )

static void prvRegTest_NonSecureCallback_Task( void * pvParameters )
{
    /* This task is going to call secure side functions. */
    portALLOCATE_SECURE_CONTEXT( configMINIMAL_SECURE_STACK_SIZE );

    /* Although the reg tests are written in assembly, its entry
     * point is written in C for convenience of checking that the
     * task parameter is being passed in correctly. */
    if( pvParameters == REG_TEST_NON_SECURE_CALLBACK_TASK_PARAMETER )
    {
        for( ;; )
        {
            /* Call the secure side function. This function calls the provided
             * non-secure callback which in-turn populates registers with
             * known values, then forces a context switch while on the
             * non-secure side and then verifies that the contents of the
             * registers are intact. This ensure that the context restoring
             * mechanism works properly when the interrupted task was in the
             * middle of a non-secure callback from the secure side. */
            vRegTest_NonSecureCallback( vRegTestAsm_NonSecureCallback );

            ulRegTestNonSecureCallbackLoopCounter += 1;
        }
    }

    /* The following line will only execute if the task parameter
     * is found to be incorrect. The check task will detect that
     * the reg test loop counter is not being incremented and flag
     * an error. */
    vTaskDelete( NULL );
}

#endif
/*-----------------------------------------------------------*/

static void prvCheckTask( void * pvParameters )
{
TickType_t xDelayPeriod = NO_ERROR_CHECK_TASK_PERIOD;
TickType_t xLastExecutionTime;
unsigned long ulErrorFound = pdFALSE;
static unsigned long ulLastRegTest1Value = 0, ulLastRegTest2Value = 0;
#if( configENABLE_TRUSTZONE == 1 )
    static unsigned long ulLastRegTestSecureValue = 0, ulLastRegTestNonSecureCallbackValue = 0;
#endif

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

        #if( configENABLE_TRUSTZONE == 1 )
        {
            /* Check that the register test secure task is still running. */
            if( ulLastRegTestSecureValue == ulRegTestSecureLoopCounter )
            {
                ulErrorFound |= 1UL << 2UL;
            }
            ulLastRegTestSecureValue = ulRegTestSecureLoopCounter;

            /* Check that the register test non-secure callback task is
            * still running. */
            if( ulLastRegTestNonSecureCallbackValue == ulRegTestNonSecureCallbackLoopCounter )
            {
                ulErrorFound |= 1UL << 3UL;
            }
            ulLastRegTestNonSecureCallbackValue = ulRegTestNonSecureCallbackLoopCounter;
        }
        #endif /* configENABLE_TRUSTZONE */

        /* Toggle the green LED to give an indication of the system status.
         * If the LED toggles every NO_ERROR_CHECK_TASK_PERIOD milliseconds
         * then everything is ok. A faster toggle indicates an error. */
        GPIO_TOGGLE( GREEN_LED );

        if( ulErrorFound != pdFALSE )
        {
            /* An error has been detected in one of the tasks. */
            xDelayPeriod = ERROR_CHECK_TASK_PERIOD;

            /* Turn on Yellow LED to indicate error. */
            YELLOW_LED = 0;
            printf( "ERROR detected!\r\n" );

            /* Increment error detection count. */
            ulCheckTaskLoops++;
        }
        else
        {
            printf( "No errors.\r\n" );
        }
    }
}
/*-----------------------------------------------------------*/
