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
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

/*
 * Changes from V1.2.3
 *
 + The created tasks now include calls to tskYIELD(), allowing them to be used
 +    with the cooperative scheduler.
 */

/**
 * This does the same as flop. c, but uses variables of type long instead of
 * type double.
 *
 * As with flop. c, the tasks created in this file are a good test of the
 * scheduler context switch mechanism.  The processor has to access 32bit
 * variables in two or four chunks (depending on the processor).  The low
 * priority of these tasks means there is a high probability that a context
 * switch will occur mid calculation.  See the flop. c documentation for
 * more information.
 *
 * \page IntegerC integer.c
 * \ingroup DemoFiles
 * <HR>
 */

/*
 * Changes from V1.2.1
 *
 + The constants used in the calculations are larger to ensure the
 +    optimiser does not truncate them to 16 bits.
 */

#include <stdlib.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "print.h"

/* Demo program include files. */
#include "integer.h"

#define intgSTACK_SIZE         ( ( unsigned short ) 256 )
#define intgNUMBER_OF_TASKS    ( 8 )

/* Four tasks, each of which performs a different calculation on four byte
 * variables.  Each of the four is created twice. */
static void vCompeteingIntMathTask1( void * pvParameters );
static void vCompeteingIntMathTask2( void * pvParameters );
static void vCompeteingIntMathTask3( void * pvParameters );
static void vCompeteingIntMathTask4( void * pvParameters );

/* These variables are used to check that all the tasks are still running.  If a
* task gets a calculation wrong it will stop incrementing its check variable. */
static volatile unsigned short usTaskCheck[ intgNUMBER_OF_TASKS ] = { ( unsigned short ) 0 };
/*-----------------------------------------------------------*/

void vStartIntegerMathTasks( unsigned portBASE_TYPE uxPriority )
{
    xTaskCreate( vCompeteingIntMathTask1, "IntMath1", intgSTACK_SIZE, ( void * ) &( usTaskCheck[ 0 ] ), uxPriority, NULL );
    xTaskCreate( vCompeteingIntMathTask2, "IntMath2", intgSTACK_SIZE, ( void * ) &( usTaskCheck[ 1 ] ), uxPriority, NULL );
    xTaskCreate( vCompeteingIntMathTask3, "IntMath3", intgSTACK_SIZE, ( void * ) &( usTaskCheck[ 2 ] ), uxPriority, NULL );
    xTaskCreate( vCompeteingIntMathTask4, "IntMath4", intgSTACK_SIZE, ( void * ) &( usTaskCheck[ 3 ] ), uxPriority, NULL );
    xTaskCreate( vCompeteingIntMathTask1, "IntMath5", intgSTACK_SIZE, ( void * ) &( usTaskCheck[ 4 ] ), uxPriority, NULL );
    xTaskCreate( vCompeteingIntMathTask2, "IntMath6", intgSTACK_SIZE, ( void * ) &( usTaskCheck[ 5 ] ), uxPriority, NULL );
    xTaskCreate( vCompeteingIntMathTask3, "IntMath7", intgSTACK_SIZE, ( void * ) &( usTaskCheck[ 6 ] ), uxPriority, NULL );
    xTaskCreate( vCompeteingIntMathTask4, "IntMath8", intgSTACK_SIZE, ( void * ) &( usTaskCheck[ 7 ] ), uxPriority, NULL );
}
/*-----------------------------------------------------------*/

static void vCompeteingIntMathTask1( void * pvParameters )
{
    long l1, l2, l3, l4;
    short sError = pdFALSE;
    volatile unsigned short * pusTaskCheckVariable;
    const long lAnswer = ( ( long ) 74565L + ( long ) 1234567L ) * ( long ) -918L;
    const char * const pcTaskStartMsg = "Integer math task 1 started.\r\n";
    const char * const pcTaskFailMsg = "Integer math task 1 failed.\r\n";

    /* Queue a message for printing to say the task has started. */
    vPrintDisplayMessage( &pcTaskStartMsg );

    /* The variable this task increments to show it is still running is passed in
     * as the parameter. */
    pusTaskCheckVariable = ( unsigned short * ) pvParameters;

    /* Keep performing a calculation and checking the result against a constant. */
    for( ; ; )
    {
        l1 = ( long ) 74565L;
        l2 = ( long ) 1234567L;
        l3 = ( long ) -918L;

        l4 = ( l1 + l2 ) * l3;

        taskYIELD();

        /* If the calculation does not match the expected constant, stop the
         * increment of the check variable. */
        if( l4 != lAnswer )
        {
            vPrintDisplayMessage( &pcTaskFailMsg );
            sError = pdTRUE;
        }

        if( sError == pdFALSE )
        {
            /* If the calculation has always been correct, increment the check
             * variable so we know	this task is still running okay. */
            ( *pusTaskCheckVariable )++;
        }
    }
}
/*-----------------------------------------------------------*/

static void vCompeteingIntMathTask2( void * pvParameters )
{
    long l1, l2, l3, l4;
    short sError = pdFALSE;
    volatile unsigned short * pusTaskCheckVariable;
    const long lAnswer = ( ( long ) -389000L / ( long ) 329999L ) * ( long ) -89L;
    const char * const pcTaskStartMsg = "Integer math task 2 started.\r\n";
    const char * const pcTaskFailMsg = "Integer math task 2 failed.\r\n";

    /* Queue a message for printing to say the task has started. */
    vPrintDisplayMessage( &pcTaskStartMsg );

    /* The variable this task increments to show it is still running is passed in
     * as the parameter. */
    pusTaskCheckVariable = ( unsigned short * ) pvParameters;

    /* Keep performing a calculation and checking the result against a constant. */
    for( ; ; )
    {
        l1 = -389000L;
        l2 = 329999L;
        l3 = -89L;

        l4 = ( l1 / l2 ) * l3;

        taskYIELD();

        /* If the calculation does not match the expected constant, stop the
         * increment of the check variable. */
        if( l4 != lAnswer )
        {
            vPrintDisplayMessage( &pcTaskFailMsg );
            sError = pdTRUE;
        }

        if( sError == pdFALSE )
        {
            /* If the calculation has always been correct, increment the check
             * variable so we know this task is still running okay. */
            ( *pusTaskCheckVariable )++;
        }
    }
}
/*-----------------------------------------------------------*/

static void vCompeteingIntMathTask3( void * pvParameters )
{
    long * plArray, lTotal1, lTotal2;
    short sError = pdFALSE;
    volatile unsigned short * pusTaskCheckVariable;
    const unsigned short usArraySize = ( unsigned short ) 250;
    unsigned short usPosition;
    const char * const pcTaskStartMsg = "Integer math task 3 started.\r\n";
    const char * const pcTaskFailMsg = "Integer math task 3 failed.\r\n";

    /* Queue a message for printing to say the task has started. */
    vPrintDisplayMessage( &pcTaskStartMsg );

    /* The variable this task increments to show it is still running is passed in
     * as the parameter. */
    pusTaskCheckVariable = ( unsigned short * ) pvParameters;

    /* Create the array we are going to use for our check calculation. */
    plArray = ( long * ) pvPortMalloc( ( size_t ) 250 * sizeof( long ) );

    /* Keep filling the array, keeping a running total of the values placed in the
     * array.  Then run through the array adding up all the values.  If the two totals
     * do not match, stop the check variable from incrementing. */
    for( ; ; )
    {
        lTotal1 = ( long ) 0;
        lTotal2 = ( long ) 0;

        for( usPosition = 0; usPosition < usArraySize; usPosition++ )
        {
            plArray[ usPosition ] = ( long ) usPosition + ( long ) 5;
            lTotal1 += ( long ) usPosition + ( long ) 5;
        }

        taskYIELD();

        for( usPosition = 0; usPosition < usArraySize; usPosition++ )
        {
            lTotal2 += plArray[ usPosition ];
        }

        if( lTotal1 != lTotal2 )
        {
            vPrintDisplayMessage( &pcTaskFailMsg );
            sError = pdTRUE;
        }

        taskYIELD();

        if( sError == pdFALSE )
        {
            /* If the calculation has always been correct, increment the check
             * variable so we know	this task is still running okay. */
            ( *pusTaskCheckVariable )++;
        }
    }
}
/*-----------------------------------------------------------*/

static void vCompeteingIntMathTask4( void * pvParameters )
{
    long * plArray, lTotal1, lTotal2;
    short sError = pdFALSE;
    volatile unsigned short * pusTaskCheckVariable;
    const unsigned short usArraySize = 250;
    unsigned short usPosition;
    const char * const pcTaskStartMsg = "Integer math task 4 started.\r\n";
    const char * const pcTaskFailMsg = "Integer math task 4 failed.\r\n";

    /* Queue a message for printing to say the task has started. */
    vPrintDisplayMessage( &pcTaskStartMsg );

    /* The variable this task increments to show it is still running is passed in
     * as the parameter. */
    pusTaskCheckVariable = ( unsigned short * ) pvParameters;

    /* Create the array we are going to use for our check calculation. */
    plArray = ( long * ) pvPortMalloc( ( size_t ) 250 * sizeof( long ) );

    /* Keep filling the array, keeping a running total of the values placed in the
     * array.  Then run through the array adding up all the values.  If the two totals
     * do not match, stop the check variable from incrementing. */
    for( ; ; )
    {
        lTotal1 = ( long ) 0;
        lTotal2 = ( long ) 0;

        for( usPosition = 0; usPosition < usArraySize; usPosition++ )
        {
            plArray[ usPosition ] = ( long ) usPosition * ( long ) 12;
            lTotal1 += ( long ) usPosition * ( long ) 12;
        }

        taskYIELD();

        for( usPosition = 0; usPosition < usArraySize; usPosition++ )
        {
            lTotal2 += plArray[ usPosition ];
        }

        if( lTotal1 != lTotal2 )
        {
            vPrintDisplayMessage( &pcTaskFailMsg );
            sError = pdTRUE;
        }

        taskYIELD();

        if( sError == pdFALSE )
        {
            /* If the calculation has always been correct, increment the check
             * variable so we know	this task is still running okay. */
            ( *pusTaskCheckVariable )++;
        }
    }
}
/*-----------------------------------------------------------*/

/* This is called to check that all the created tasks are still running. */
portBASE_TYPE xAreIntegerMathsTaskStillRunning( void )
{
/* Keep a history of the check variables so we know if they have been incremented
 * since the last call. */
    static unsigned short usLastTaskCheck[ intgNUMBER_OF_TASKS ] = { ( unsigned short ) 0 };
    portBASE_TYPE xReturn = pdTRUE, xTask;

    /* Check the maths tasks are still running by ensuring their check variables
     * are still incrementing. */
    for( xTask = 0; xTask < intgNUMBER_OF_TASKS; xTask++ )
    {
        if( usTaskCheck[ xTask ] == usLastTaskCheck[ xTask ] )
        {
            /* The check has not incremented so an error exists. */
            xReturn = pdFALSE;
        }

        usLastTaskCheck[ xTask ] = usTaskCheck[ xTask ];
    }

    return xReturn;
}
