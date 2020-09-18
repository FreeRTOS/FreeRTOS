/*
 * FreeRTOS Kernel V10.4.1
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
 * Creates eight tasks, each of which loops continuously performing a floating 
 * point calculation and in so doing test the floating point context switching.
 * This file also demonstrates the use of the xPortUsesFloatingPoint() function
 * which informs the kernel that the task requires its floating point context
 * saved on each switch.
 *
 * All the tasks run at the idle priority and never block or yield.  This causes 
 * all eight tasks to time slice with the idle task.  Running at the idle 
 * priority means that these tasks will get pre-empted any time another task is 
 * ready to run or a time slice occurs.  More often than not the pre-emption 
 * will occur mid calculation, creating a good test of the schedulers context 
 * switch mechanism - a calculation producing an unexpected result could be a 
 * symptom of a corruption in the context of a task.
 */

#include <stdlib.h>
#include <math.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo program include files. */
#include "flop.h"

#define mathSTACK_SIZE		configMINIMAL_STACK_SIZE
#define mathNUMBER_OF_TASKS  ( 8 )

/* Four tasks, each of which performs a different floating point calculation.  
Each of the four is created twice. */
static void vCompetingMathTask1( void *pvParameters );
static void vCompetingMathTask2( void *pvParameters );
static void vCompetingMathTask3( void *pvParameters );
static void vCompetingMathTask4( void *pvParameters );

/* These variables are used to check that all the tasks are still running.  If a 
task gets a calculation wrong it will stop incrementing its check variable,
otherwise the check variable will get incremented on each iteration of the 
tasks execution. */
static volatile unsigned short usTaskCheck[ mathNUMBER_OF_TASKS ] = { ( unsigned short ) 0 };

/*-----------------------------------------------------------*/

void vStartMathTasks( unsigned portBASE_TYPE uxPriority )
{
TaskHandle_t xCreatedTask;

	/* Create one of the floating point tasks... */
	xTaskCreate( vCompetingMathTask1, "Math1", mathSTACK_SIZE, ( void * ) &( usTaskCheck[ 0 ] ), uxPriority, &xCreatedTask );
	
	/* ... then enable floating point support for the created task so its flop
	flop registers are maintained in a consistent state. */
	xPortUsesFloatingPoint( xCreatedTask );

	xTaskCreate( vCompetingMathTask2, "Math2", mathSTACK_SIZE, ( void * ) &( usTaskCheck[ 1 ] ), uxPriority, &xCreatedTask );
	xPortUsesFloatingPoint( xCreatedTask );
	
	xTaskCreate( vCompetingMathTask3, "Math3", mathSTACK_SIZE, ( void * ) &( usTaskCheck[ 2 ] ), uxPriority, &xCreatedTask );
	xPortUsesFloatingPoint( xCreatedTask );
	
	xTaskCreate( vCompetingMathTask4, "Math4", mathSTACK_SIZE, ( void * ) &( usTaskCheck[ 3 ] ), uxPriority, &xCreatedTask );
	xPortUsesFloatingPoint( xCreatedTask );
	
	xTaskCreate( vCompetingMathTask1, "Math5", mathSTACK_SIZE, ( void * ) &( usTaskCheck[ 4 ] ), uxPriority, &xCreatedTask );
	xPortUsesFloatingPoint( xCreatedTask );
	
	xTaskCreate( vCompetingMathTask2, "Math6", mathSTACK_SIZE, ( void * ) &( usTaskCheck[ 5 ] ), uxPriority, &xCreatedTask );
	xPortUsesFloatingPoint( xCreatedTask );
	
	xTaskCreate( vCompetingMathTask3, "Math7", mathSTACK_SIZE, ( void * ) &( usTaskCheck[ 6 ] ), uxPriority, &xCreatedTask );
	xPortUsesFloatingPoint( xCreatedTask );
	
	xTaskCreate( vCompetingMathTask4, "Math8", mathSTACK_SIZE, ( void * ) &( usTaskCheck[ 7 ] ), uxPriority, &xCreatedTask );
	xPortUsesFloatingPoint( xCreatedTask );
}
/*-----------------------------------------------------------*/

static void vCompetingMathTask1( void *pvParameters )
{
volatile double d1, d2, d3, d4;
volatile unsigned short *pusTaskCheckVariable;
volatile double dAnswer;
short sError = pdFALSE;

	d1 = 123.4567;
	d2 = 2345.6789;
	d3 = -918.222;

	/* Calculate the expected answer. */
	dAnswer = ( d1 + d2 ) * d3;

	/* The variable this task increments to show it is still running is passed in 
	as the parameter. */
	pusTaskCheckVariable = ( unsigned short * ) pvParameters;

	/* Keep performing a calculation and checking the result against a constant. */
	for(;;)
	{
		/* Perform the calculation. */
		d1 = 123.4567;
		d2 = 2345.6789;
		d3 = -918.222;

		d4 = ( d1 + d2 ) * d3;

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
			( *pusTaskCheckVariable )++;
		}
	}
}
/*-----------------------------------------------------------*/

static void vCompetingMathTask2( void *pvParameters )
{
volatile double d1, d2, d3, d4;
volatile unsigned short *pusTaskCheckVariable;
volatile double dAnswer;
short sError = pdFALSE;

	d1 = -389.38;
	d2 = 32498.2;
	d3 = -2.0001;

	/* Calculate the expected answer. */
	dAnswer = ( d1 / d2 ) * d3;


	/* The variable this task increments to show it is still running is passed in 
	as the parameter. */
	pusTaskCheckVariable = ( unsigned short * ) pvParameters;

	/* Keep performing a calculation and checking the result against a constant. */
	for( ;; )
	{
		/* Perform the calculation. */
		d1 = -389.38;
		d2 = 32498.2;
		d3 = -2.0001;

		d4 = ( d1 / d2 ) * d3;

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
			( *pusTaskCheckVariable )++;
		}
	}
}
/*-----------------------------------------------------------*/

static void vCompetingMathTask3( void *pvParameters )
{
volatile double *pdArray, dTotal1, dTotal2, dDifference;
volatile unsigned short *pusTaskCheckVariable;
const size_t xArraySize = 10;
size_t xPosition;
short sError = pdFALSE;

	/* The variable this task increments to show it is still running is passed 
	in as the parameter. */
	pusTaskCheckVariable = ( unsigned short * ) pvParameters;

	/* Allocate memory for use as an array. */
	pdArray = ( double * ) pvPortMalloc( xArraySize * sizeof( double ) );

	/* Keep filling an array, keeping a running total of the values placed in 
	the array.  Then run through the array adding up all the values.  If the two 
	totals do not match, stop the check variable from incrementing. */
	for( ;; )
	{
		dTotal1 = 0.0;
		dTotal2 = 0.0;

		for( xPosition = 0; xPosition < xArraySize; xPosition++ )
		{
			pdArray[ xPosition ] = ( double ) xPosition + 5.5;
			dTotal1 += ( double ) xPosition + 5.5;	
		}

		for( xPosition = 0; xPosition < xArraySize; xPosition++ )
		{
			dTotal2 += pdArray[ xPosition ];
		}

		dDifference = dTotal1 - dTotal2;
		if( fabs( dDifference ) > 0.001 )
		{
			sError = pdTRUE;
		}

		if( sError == pdFALSE )
		{
			/* If the calculation has always been correct, increment the check 
			variable so we know	this task is still running okay. */
			( *pusTaskCheckVariable )++;
		}
	}
}
/*-----------------------------------------------------------*/

static void vCompetingMathTask4( void *pvParameters )
{
volatile double *pdArray, dTotal1, dTotal2, dDifference;
volatile unsigned short *pusTaskCheckVariable;
const size_t xArraySize = 10;
size_t xPosition;
short sError = pdFALSE;

	/* The variable this task increments to show it is still running is passed in 
	as the parameter. */
	pusTaskCheckVariable = ( unsigned short * ) pvParameters;

	/* Allocate RAM for use as an array. */
	pdArray = ( double * ) pvPortMalloc( xArraySize * sizeof( double ) );

	/* Keep filling an array, keeping a running total of the values placed in the 
	array.  Then run through the array adding up all the values.  If the two totals 
	do not match, stop the check variable from incrementing. */
	for( ;; )
	{
		dTotal1 = 0.0;
		dTotal2 = 0.0;

		for( xPosition = 0; xPosition < xArraySize; xPosition++ )
		{
			pdArray[ xPosition ] = ( double ) xPosition * 12.123;
			dTotal1 += ( double ) xPosition * 12.123;	
		}

		for( xPosition = 0; xPosition < xArraySize; xPosition++ )
		{
			dTotal2 += pdArray[ xPosition ];
		}

		dDifference = dTotal1 - dTotal2;
		if( fabs( dDifference ) > 0.001 )
		{
			sError = pdTRUE;
		}

		if( sError == pdFALSE )
		{
			/* If the calculation has always been correct, increment the check 
			variable so we know	this task is still running okay. */
			( *pusTaskCheckVariable )++;
		}
	}
}				 
/*-----------------------------------------------------------*/

/* This is called to check that all the created tasks are still running. */
portBASE_TYPE xAreMathsTaskStillRunning( void )
{
/* Keep a history of the check variables so we know if they have been 
incremented since the last call. */
static unsigned short usLastTaskCheck[ mathNUMBER_OF_TASKS ] = { ( unsigned short ) 0 };
portBASE_TYPE xReturn = pdTRUE, xTask;

	/* Check the maths tasks are still running by ensuring their check variables 
	are still incrementing. */
	for( xTask = 0; xTask < mathNUMBER_OF_TASKS; xTask++ )
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



