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
    #include "nsc_printf.h"
#else
    #include "fsl_debug_console.h"
#endif

/*
 * Functions that implement reg test tasks.
 */
static void prvRegTest1_Task( void * pvParameters );
static void prvRegTest2_Task( void * pvParameters );
static void prvRegTest3_Task( void * pvParameters );
static void prvRegTest4_Task( void * pvParameters );
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
#define REG_TEST_3_TASK_PARAMETER                   ( ( void * ) 0x12348765 )
#define REG_TEST_4_TASK_PARAMETER                   ( ( void * ) 0x43215678 )
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
volatile unsigned long ulRegTest3LoopCounter = 0UL, ulRegTest4LoopCounter = 0UL;
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
static StackType_t xRegTest3TaskStack[ configMINIMAL_STACK_SIZE ] __attribute__( ( aligned( 32 ) ) );
static StackType_t xRegTest4TaskStack[ configMINIMAL_STACK_SIZE ] __attribute__( ( aligned( 32 ) ) );
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
TaskParameters_t xRegTest3TaskParameters =
{
    .pvTaskCode      = prvRegTest3_Task,
    .pcName          = "RegTest3",
    .usStackDepth    = configMINIMAL_STACK_SIZE,
    .pvParameters    = REG_TEST_3_TASK_PARAMETER,
    .uxPriority      = tskIDLE_PRIORITY | portPRIVILEGE_BIT,
    .puxStackBuffer  = xRegTest3TaskStack,
    .xRegions        =  {
                            { 0, 0, 0 },
                            { 0, 0, 0 },
                            { 0, 0, 0 }
                        }
};
TaskParameters_t xRegTest4TaskParameters =
{
    .pvTaskCode      = prvRegTest4_Task,
    .pcName          = "RegTest4",
    .usStackDepth    = configMINIMAL_STACK_SIZE,
    .pvParameters    = REG_TEST_4_TASK_PARAMETER,
    .uxPriority      = tskIDLE_PRIORITY | portPRIVILEGE_BIT,
    .puxStackBuffer  = xRegTest4TaskStack,
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

    xTaskCreateRestricted( &( xRegTest1TaskParameters ), NULL );
    xTaskCreateRestricted( &( xRegTest2TaskParameters ), NULL );
    xTaskCreateRestricted( &( xRegTest3TaskParameters ), NULL );
    xTaskCreateRestricted( &( xRegTest4TaskParameters ), NULL );
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

static void prvRegTest3_Task( void * pvParameters )
{
    /* Although the reg tests are written in assembly, its entry
     * point is written in C for convenience of checking that the
     * task parameter is being passed in correctly. */
    if( pvParameters == REG_TEST_3_TASK_PARAMETER )
    {
        /* Start the part of the test that is written in assembler. */
        vRegTest3Asm_NonSecure();
    }

    /* The following line will only execute if the task parameter
     * is found to be incorrect. The check task will detect that
     * the reg test loop counter is not being incremented and flag
     * an error. */
    vTaskDelete( NULL );
}
/*-----------------------------------------------------------*/

static void prvRegTest4_Task( void * pvParameters )
{
    /* Although the reg tests are written in assembly, its entry
     * point is written in C for convenience of checking that the
     * task parameter is being passed in correctly. */
    if( pvParameters == REG_TEST_4_TASK_PARAMETER )
    {
        /* Start the part of the test that is written in assembler. */
        vRegTest4Asm_NonSecure();
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

#endif /* configENABLE_TRUSTZONE */
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

#endif /* configENABLE_TRUSTZONE */
/*-----------------------------------------------------------*/

static void prvCheckTask( void * pvParameters )
{
TickType_t xDelayPeriod = NO_ERROR_CHECK_TASK_PERIOD;
TickType_t xLastExecutionTime;
unsigned long ulErrorFound = pdFALSE;
static unsigned long ulLastRegTest1Value = 0, ulLastRegTest2Value = 0;
static unsigned long ulLastRegTest3Value = 0, ulLastRegTest4Value = 0;

#if( configENABLE_TRUSTZONE == 1 )
    static unsigned long ulLastRegTestSecureValue = 0, ulLastRegTestNonSecureCallbackValue = 0;

    /* This task is going to call secure side functions for
     * printing messages. */
    portALLOCATE_SECURE_CONTEXT( configMINIMAL_SECURE_STACK_SIZE );
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

        #if( configENABLE_TRUSTZONE == 1 )
        {
            /* Check that the register test secure task is still running. */
            if( ulLastRegTestSecureValue == ulRegTestSecureLoopCounter )
            {
                ulErrorFound |= 1UL << 4UL;
            }
            ulLastRegTestSecureValue = ulRegTestSecureLoopCounter;

            /* Check that the register test non-secure callback task is
             * still running. */
            if( ulLastRegTestNonSecureCallbackValue == ulRegTestNonSecureCallbackLoopCounter )
            {
                ulErrorFound |= 1UL << 5UL;
            }
            ulLastRegTestNonSecureCallbackValue = ulRegTestNonSecureCallbackLoopCounter;
        }
        #endif /* configENABLE_TRUSTZONE */

        if( ulErrorFound != pdFALSE )
        {
            /* An error has been detected in one of the tasks. */
            xDelayPeriod = ERROR_CHECK_TASK_PERIOD;

            #if( configENABLE_TRUSTZONE == 1 )
                NSC_Printf( "ERROR detected!\r\n" );
            #else
                PRINTF( "ERROR detected!\r\n" );
            #endif

            /* Increment error detection count. */
            ulCheckTaskLoops++;
        }
        else
        {
            #if( configENABLE_TRUSTZONE == 1 )
                NSC_Printf( "No errors.\r\n" );
            #else
                PRINTF( "No errors.\r\n" );
            #endif
        }
    }
}
/*-----------------------------------------------------------*/
