/*
 * FreeRTOS Kernel V10.2.1
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * Creates eight tasks, each of which loops continuously performing a
 * floating point calculation.
 *
 * All the tasks run at the idle priority and never block or yield.  This causes
 * all eight tasks to time slice with the idle task.  Running at the idle priority
 * means that these tasks will get pre-empted any time another task is ready to run
 * or a time slice occurs.  More often than not the pre-emption will occur mid
 * calculation, creating a good test of the schedulers context switch mechanism - a
 * calculation producing an unexpected result could be a symptom of a corruption in
 * the context of a task.
 */

#include <stdlib.h>
#include <math.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo program include files. */
#include "flop_mz.h"

#define mathSTACK_SIZE		(configMINIMAL_STACK_SIZE + 100)
#define mathNUMBER_OF_TASKS  ( 8 )

/* Four tasks, each of which performs a different floating point calculation.
Each of the four is created twice. */
static portTASK_FUNCTION_PROTO( vCompetingMathTask1, pvParameters );
static portTASK_FUNCTION_PROTO( vCompetingMathTask2, pvParameters );
static portTASK_FUNCTION_PROTO( vCompetingMathTask3, pvParameters );
static portTASK_FUNCTION_PROTO( vCompetingMathTask4, pvParameters );

/* These variables are used to check that all the tasks are still running.  If a
task gets a calculation wrong it will
stop incrementing its check variable. */
static volatile unsigned long ulTaskCheck[ mathNUMBER_OF_TASKS ] = { 0 };

/*-----------------------------------------------------------*/

void vStartMathTasks( unsigned portBASE_TYPE uxPriority )
{
	xTaskCreate( vCompetingMathTask1, "Math1", mathSTACK_SIZE, ( void * ) &( ulTaskCheck[ 0 ] ), uxPriority, NULL );
	xTaskCreate( vCompetingMathTask2, "Math2", mathSTACK_SIZE, ( void * ) &( ulTaskCheck[ 1 ] ), uxPriority, NULL );
	xTaskCreate( vCompetingMathTask3, "Math3", mathSTACK_SIZE, ( void * ) &( ulTaskCheck[ 2 ] ), uxPriority, NULL );
	xTaskCreate( vCompetingMathTask4, "Math4", mathSTACK_SIZE, ( void * ) &( ulTaskCheck[ 3 ] ), uxPriority, NULL );
	xTaskCreate( vCompetingMathTask1, "Math5", mathSTACK_SIZE, ( void * ) &( ulTaskCheck[ 4 ] ), uxPriority, NULL );
	xTaskCreate( vCompetingMathTask2, "Math6", mathSTACK_SIZE, ( void * ) &( ulTaskCheck[ 5 ] ), uxPriority, NULL );
	xTaskCreate( vCompetingMathTask3, "Math7", mathSTACK_SIZE, ( void * ) &( ulTaskCheck[ 6 ] ), uxPriority, NULL );
	xTaskCreate( vCompetingMathTask4, "Math8", mathSTACK_SIZE, ( void * ) &( ulTaskCheck[ 7 ] ), uxPriority, NULL );
}
/*-----------------------------------------------------------*/

static portTASK_FUNCTION( vCompetingMathTask1, pvParameters )
{
volatile portDOUBLE d1, d2, d3, d4;
volatile unsigned long *pulTaskCheckVariable;
volatile portDOUBLE dAnswer;
short sError = pdFALSE;


	/* Must be called before any hardware floating point operations are
	performed to let the RTOS portable layer know that this task requires
	a floating point context. */
	portTASK_USES_FLOATING_POINT();

	d1 = 123.4567;
	d2 = 2345.6789;
	d3 = -918.222;

	dAnswer = ( d1 + d2 ) * d3;

	/* The variable this task increments to show it is still running is passed in
	as the parameter. */
	pulTaskCheckVariable = ( unsigned long * ) pvParameters;
    
	/* Keep performing a calculation and checking the result against a constant. */
	for(;;)
	{
		d1 = 123.4567;
		d2 = 2345.6789;
		d3 = -918.222;

		d4 = ( d1 + d2 ) * d3;

		#if configUSE_PREEMPTION == 0
			taskYIELD();
		#endif

		/* If the calculation does not match the expected constant, stop the
		increment of the check variable. */
		if( fabs( d4 - dAnswer ) > 0.001 )
		{
			sError = pdTRUE;
		}

		if( sError == pdFALSE )
		{
			/* If the calculation has always been correct, increment the check
			variable so we know this task is still running okay. */
			( *pulTaskCheckVariable )++;
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
volatile unsigned long *pulTaskCheckVariable;
volatile portDOUBLE dAnswer;
short sError = pdFALSE;

	/* Must be called before any hardware floating point operations are
	performed to let the RTOS portable layer know that this task requires
	a floating point context. */
	portTASK_USES_FLOATING_POINT();

	d1 = -389.38;
	d2 = 32498.2;
	d3 = -2.0001;

	dAnswer = ( d1 / d2 ) * d3;


	/* The variable this task increments to show it is still running is passed in
	as the parameter. */
	pulTaskCheckVariable = ( unsigned long * ) pvParameters;

	/* Keep performing a calculation and checking the result against a constant. */
	for( ;; )
	{
		d1 = -389.38;
		d2 = 32498.2;
		d3 = -2.0001;

		d4 = ( d1 / d2 ) * d3;

		#if configUSE_PREEMPTION == 0
			taskYIELD();
		#endif

		/* If the calculation does not match the expected constant, stop the
		increment of the check variable. */
		if( fabs( d4 - dAnswer ) > 0.001 )
		{
			sError = pdTRUE;
		}

		if( sError == pdFALSE )
		{
			/* If the calculation has always been correct, increment the check
			variable so we know
			this task is still running okay. */
			( *pulTaskCheckVariable )++;
		}

		#if configUSE_PREEMPTION == 0
			taskYIELD();
		#endif
	}
}
/*-----------------------------------------------------------*/

static portTASK_FUNCTION( vCompetingMathTask3, pvParameters )
{
volatile portDOUBLE *pdArray, dTotal1, dTotal2, dDifference;
volatile unsigned long *pulTaskCheckVariable;
const size_t xArraySize = 10;
size_t xPosition;
short sError = pdFALSE;

	/* Must be called before any hardware floating point operations are
	performed to let the RTOS portable layer know that this task requires
	a floating point context. */
	portTASK_USES_FLOATING_POINT();

	/* The variable this task increments to show it is still running is passed in
	as the parameter. */
	pulTaskCheckVariable = ( unsigned long * ) pvParameters;

	pdArray = ( portDOUBLE * ) pvPortMalloc( xArraySize * sizeof( portDOUBLE ) );

	/* Keep filling an array, keeping a running total of the values placed in the
	array.  Then run through the array adding up all the values.  If the two totals
	do not match, stop the check variable from incrementing. */
	for( ;; )
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
			/* If the calculation has always been correct, increment the check
			variable so we know	this task is still running okay. */
			( *pulTaskCheckVariable )++;
		}
	}
}
/*-----------------------------------------------------------*/

static portTASK_FUNCTION( vCompetingMathTask4, pvParameters )
{
volatile portDOUBLE *pdArray, dTotal1, dTotal2, dDifference;
volatile unsigned long *pulTaskCheckVariable;
const size_t xArraySize = 10;
size_t xPosition;
short sError = pdFALSE;

	/* Must be called before any hardware floating point operations are
	performed to let the RTOS portable layer know that this task requires
	a floating point context. */
	portTASK_USES_FLOATING_POINT();

	/* The variable this task increments to show it is still running is passed in
	as the parameter. */
	pulTaskCheckVariable = ( unsigned long * ) pvParameters;

	pdArray = ( portDOUBLE * ) pvPortMalloc( xArraySize * sizeof( portDOUBLE ) );

	/* Keep filling an array, keeping a running total of the values placed in the
	array.  Then run through the array adding up all the values.  If the two totals
	do not match, stop the check variable from incrementing. */
	for( ;; )
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
			/* If the calculation has always been correct, increment the check
			variable so we know	this task is still running okay. */
			( *pulTaskCheckVariable )++;
		}
	}
}
/*-----------------------------------------------------------*/

/* This is called to check that all the created tasks are still running. */
portBASE_TYPE xAreMathsTaskStillRunning( void )
{
/* Keep a history of the check variables so we know if they have been incremented
since the last call. */
static unsigned long ulLastTaskCheck[ mathNUMBER_OF_TASKS ] = { ( unsigned short ) 0 };
portBASE_TYPE xReturn = pdTRUE, xTask;

	/* Check the maths tasks are still running by ensuring their check variables
	are still incrementing. */
	for( xTask = 0; xTask < mathNUMBER_OF_TASKS; xTask++ )
	{
		if( ulTaskCheck[ xTask ] == ulLastTaskCheck[ xTask ] )
		{
			/* The check has not incremented so an error exists. */
			xReturn = pdFALSE;
		}

		ulLastTaskCheck[ xTask ] = ulTaskCheck[ xTask ];
	}

	return xReturn;
}



