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
 * https://aws.amazon.com/freertos
 *
 */

/*
 * Creates eight tasks, each of which loops continuously performing a floating
 * point calculation.
 *
 * All the tasks run at the idle priority and never block or yield.  This causes
 * all eight tasks to time slice with the idle task.  Running at the idle
 * priority means that these tasks will get pre-empted any time another task is
 * ready to run or a time slice occurs.  More often than not the pre-emption
 * will occur mid calculation, creating a good test of the schedulers context
 * switch mechanism - a calculation producing an unexpected result could be a
 * symptom of a corruption in the context of a task.
 */

/* Standard includes. */
#include <stdlib.h>
#include <math.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo program include files. */
#include "flop.h"

#ifndef mathSTACK_SIZE
    #define mathSTACK_SIZE     configMINIMAL_STACK_SIZE
#endif

#define mathNUMBER_OF_TASKS    ( 4 )

/* Four tasks, each of which performs a different floating point calculation.
 * Each of the four is created twice. */
static portTASK_FUNCTION_PROTO( vCompetingMathTask1, pvParameters );
static portTASK_FUNCTION_PROTO( vCompetingMathTask2, pvParameters );
static portTASK_FUNCTION_PROTO( vCompetingMathTask3, pvParameters );
static portTASK_FUNCTION_PROTO( vCompetingMathTask4, pvParameters );

/* These variables are used to check that all the tasks are still running.  If a
 * task gets a calculation wrong it will stop setting its check variable. */
static uint16_t usTaskCheck[ mathNUMBER_OF_TASKS ] = { ( uint16_t ) 0 };

/*-----------------------------------------------------------*/

void vStartMathTasks( UBaseType_t uxPriority )
{
    xTaskCreate( vCompetingMathTask1, "Math1", mathSTACK_SIZE, ( void * ) &( usTaskCheck[ 0 ] ), uxPriority, NULL );
    xTaskCreate( vCompetingMathTask2, "Math2", mathSTACK_SIZE, ( void * ) &( usTaskCheck[ 1 ] ), uxPriority, NULL );
    xTaskCreate( vCompetingMathTask3, "Math3", mathSTACK_SIZE, ( void * ) &( usTaskCheck[ 2 ] ), uxPriority, NULL );
    xTaskCreate( vCompetingMathTask4, "Math4", mathSTACK_SIZE, ( void * ) &( usTaskCheck[ 3 ] ), uxPriority, NULL );
}
/*-----------------------------------------------------------*/

static portTASK_FUNCTION( vCompetingMathTask1, pvParameters )
{
    volatile portDOUBLE d1, d2, d3, d4;
    volatile uint16_t * pusTaskCheckVariable;
    volatile portDOUBLE dAnswer;
    short sError = pdFALSE;

    /* Some ports require that tasks that use a hardware floating point unit
     * tell the kernel that they require a floating point context before any
     * floating point instructions are executed. */
    portTASK_USES_FLOATING_POINT();

    d1 = 123.4567;
    d2 = 2345.6789;
    d3 = -918.222;

    dAnswer = ( d1 + d2 ) * d3;

    /* The variable this task increments to show it is still running is passed in
     * as the parameter. */
    pusTaskCheckVariable = ( volatile uint16_t * ) pvParameters;

    /* Keep performing a calculation and checking the result against a constant. */
    for( ; ; )
    {
        d1 = 123.4567;
        d2 = 2345.6789;
        d3 = -918.222;

        d4 = ( d1 + d2 ) * d3;

        #if configUSE_PREEMPTION == 0
            taskYIELD();
        #endif

        /* If the calculation does not match the expected constant, stop the
         * increment of the check variable. */
        if( fabs( d4 - dAnswer ) > 0.001 )
        {
            sError = pdTRUE;
        }

        if( sError == pdFALSE )
        {
            /* If the calculation has always been correct then set set the check
             * variable.  The check variable will get set to pdFALSE each time
             * xAreMathsTaskStillRunning() is executed. */
            ( *pusTaskCheckVariable ) = pdTRUE;
        }

        #if configUSE_PREEMPTION == 0
            taskYIELD();
        #endif
    }
}
/*-----------------------------------------------------------*/

static portTASK_FUNCTION( vCompetingMathTask2, pvParameters )
{
    volatile portDOUBLE d1, d2, d3, d4;
    volatile uint16_t * pusTaskCheckVariable;
    volatile portDOUBLE dAnswer;
    short sError = pdFALSE;

    /* Some ports require that tasks that use a hardware floating point unit
     * tell the kernel that they require a floating point context before any
     * floating point instructions are executed. */
    portTASK_USES_FLOATING_POINT();

    d1 = -389.38;
    d2 = 32498.2;
    d3 = -2.0001;

    dAnswer = ( d1 / d2 ) * d3;


    /* The variable this task increments to show it is still running is passed in
     * as the parameter. */
    pusTaskCheckVariable = ( volatile uint16_t * ) pvParameters;

    /* Keep performing a calculation and checking the result against a constant. */
    for( ; ; )
    {
        d1 = -389.38;
        d2 = 32498.2;
        d3 = -2.0001;

        d4 = ( d1 / d2 ) * d3;

        #if configUSE_PREEMPTION == 0
            taskYIELD();
        #endif

        /* If the calculation does not match the expected constant, stop the
         * increment of the check variable. */
        if( fabs( d4 - dAnswer ) > 0.001 )
        {
            sError = pdTRUE;
        }

        if( sError == pdFALSE )
        {
            /* If the calculation has always been correct then set set the check
             * variable.  The check variable will get set to pdFALSE each time
             * xAreMathsTaskStillRunning() is executed. */
            ( *pusTaskCheckVariable ) = pdTRUE;
        }

        #if configUSE_PREEMPTION == 0
            taskYIELD();
        #endif
    }
}
/*-----------------------------------------------------------*/

static portTASK_FUNCTION( vCompetingMathTask3, pvParameters )
{
    volatile portDOUBLE * pdArray, dTotal1, dTotal2, dDifference;
    volatile uint16_t * pusTaskCheckVariable;
    const size_t xArraySize = 10;
    size_t xPosition;
    short sError = pdFALSE;

    /* Some ports require that tasks that use a hardware floating point unit
     * tell the kernel that they require a floating point context before any
     * floating point instructions are executed. */
    portTASK_USES_FLOATING_POINT();

    /* The variable this task increments to show it is still running is passed in
     * as the parameter. */
    pusTaskCheckVariable = ( volatile uint16_t * ) pvParameters;

    pdArray = ( portDOUBLE * ) pvPortMalloc( xArraySize * sizeof( portDOUBLE ) );

    /* Keep filling an array, keeping a running total of the values placed in the
     * array.  Then run through the array adding up all the values.  If the two totals
     * do not match, stop the check variable from incrementing. */
    for( ; ; )
    {
        dTotal1 = 0.0;
        dTotal2 = 0.0;

        for( xPosition = 0; xPosition < xArraySize; xPosition++ )
        {
            pdArray[ xPosition ] = ( portDOUBLE ) xPosition + 5.5;
            dTotal1 += ( portDOUBLE ) xPosition + 5.5;
        }

        #if configUSE_PREEMPTION == 0
            taskYIELD();
        #endif

        for( xPosition = 0; xPosition < xArraySize; xPosition++ )
        {
            dTotal2 += pdArray[ xPosition ];
        }

        dDifference = dTotal1 - dTotal2;

        if( fabs( dDifference ) > 0.001 )
        {
            sError = pdTRUE;
        }

        #if configUSE_PREEMPTION == 0
            taskYIELD();
        #endif

        if( sError == pdFALSE )
        {
            /* If the calculation has always been correct then set set the check
             * variable.  The check variable will get set to pdFALSE each time
             * xAreMathsTaskStillRunning() is executed. */
            ( *pusTaskCheckVariable ) = pdTRUE;
        }
    }
}
/*-----------------------------------------------------------*/

static portTASK_FUNCTION( vCompetingMathTask4, pvParameters )
{
    volatile portDOUBLE * pdArray, dTotal1, dTotal2, dDifference;
    volatile uint16_t * pusTaskCheckVariable;
    const size_t xArraySize = 10;
    size_t xPosition;
    short sError = pdFALSE;

    /* Some ports require that tasks that use a hardware floating point unit
     * tell the kernel that they require a floating point context before any
     * floating point instructions are executed. */
    portTASK_USES_FLOATING_POINT();

    /* The variable this task increments to show it is still running is passed in
     * as the parameter. */
    pusTaskCheckVariable = ( volatile uint16_t * ) pvParameters;

    pdArray = ( portDOUBLE * ) pvPortMalloc( xArraySize * sizeof( portDOUBLE ) );

    /* Keep filling an array, keeping a running total of the values placed in the
     * array.  Then run through the array adding up all the values.  If the two totals
     * do not match, stop the check variable from incrementing. */
    for( ; ; )
    {
        dTotal1 = 0.0;
        dTotal2 = 0.0;

        for( xPosition = 0; xPosition < xArraySize; xPosition++ )
        {
            pdArray[ xPosition ] = ( portDOUBLE ) xPosition * 12.123;
            dTotal1 += ( portDOUBLE ) xPosition * 12.123;
        }

        #if configUSE_PREEMPTION == 0
            taskYIELD();
        #endif

        for( xPosition = 0; xPosition < xArraySize; xPosition++ )
        {
            dTotal2 += pdArray[ xPosition ];
        }

        dDifference = dTotal1 - dTotal2;

        if( fabs( dDifference ) > 0.001 )
        {
            sError = pdTRUE;
        }

        #if configUSE_PREEMPTION == 0
            taskYIELD();
        #endif

        if( sError == pdFALSE )
        {
            /* If the calculation has always been correct then set set the check
             * variable.  The check variable will get set to pdFALSE each time
             * xAreMathsTaskStillRunning() is executed. */
            ( *pusTaskCheckVariable ) = pdTRUE;
        }
    }
}
/*-----------------------------------------------------------*/

/* This is called to check that all the created tasks are still running. */
BaseType_t xAreMathsTaskStillRunning( void )
{
    BaseType_t xReturn = pdPASS, xTask;

    /* Check the maths tasks are still running by ensuring their check variables
     * have been set to pdPASS. */
    for( xTask = 0; xTask < mathNUMBER_OF_TASKS; xTask++ )
    {
        if( usTaskCheck[ xTask ] != pdTRUE )
        {
            /* The check has not been set so the associated task has either
             * stalled or detected an error. */
            xReturn = pdFAIL;
        }
        else
        {
            /* Reset the variable so it can be checked again the next time this
             * function is executed. */
            usTaskCheck[ xTask ] = pdFALSE;
        }
    }

    return xReturn;
}
