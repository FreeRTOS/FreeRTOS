/*
    FreeRTOS V7.5.2 - Copyright (C) 2013 Real Time Engineers Ltd.

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that has become a de facto standard.             *
     *                                                                       *
     *    Help yourself get started quickly and support the FreeRTOS         *
     *    project by purchasing a FreeRTOS tutorial book, reference          *
     *    manual, or both from: http://www.FreeRTOS.org/Documentation        *
     *                                                                       *
     *    Thank you!                                                         *
     *                                                                       *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    >>! NOTE: The modification to the GPL is included to allow you to distribute
    >>! a combined work that includes FreeRTOS without being obliged to provide
    >>! the source code for proprietary components outside of the FreeRTOS
    >>! kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available from the following
    link: http://www.freertos.org/a00114.html

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org - Documentation, books, training, latest versions,
    license and Real Time Engineers Ltd. contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

/*
 * Creates eight tasks, each of which loops continuously performing a floating 
 * point calculation - using single precision variables.
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
#include "flop.h"

#define mathSTACK_SIZE		configMINIMAL_STACK_SIZE
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
static volatile unsigned short usTaskCheck[ mathNUMBER_OF_TASKS ] = { ( unsigned short ) 0 };

/*-----------------------------------------------------------*/

void vStartMathTasks( unsigned portBASE_TYPE uxPriority )
{
	xTaskCreate( vCompetingMathTask1, ( signed char * ) "Math1", mathSTACK_SIZE, ( void * ) &( usTaskCheck[ 0 ] ), uxPriority, NULL );
	xTaskCreate( vCompetingMathTask2, ( signed char * ) "Math2", mathSTACK_SIZE, ( void * ) &( usTaskCheck[ 1 ] ), uxPriority, NULL );
	xTaskCreate( vCompetingMathTask3, ( signed char * ) "Math3", mathSTACK_SIZE, ( void * ) &( usTaskCheck[ 2 ] ), uxPriority, NULL );
	xTaskCreate( vCompetingMathTask4, ( signed char * ) "Math4", mathSTACK_SIZE, ( void * ) &( usTaskCheck[ 3 ] ), uxPriority, NULL );
	xTaskCreate( vCompetingMathTask1, ( signed char * ) "Math5", mathSTACK_SIZE, ( void * ) &( usTaskCheck[ 4 ] ), uxPriority, NULL );
	xTaskCreate( vCompetingMathTask2, ( signed char * ) "Math6", mathSTACK_SIZE, ( void * ) &( usTaskCheck[ 5 ] ), uxPriority, NULL );
	xTaskCreate( vCompetingMathTask3, ( signed char * ) "Math7", mathSTACK_SIZE, ( void * ) &( usTaskCheck[ 6 ] ), uxPriority, NULL );
	xTaskCreate( vCompetingMathTask4, ( signed char * ) "Math8", mathSTACK_SIZE, ( void * ) &( usTaskCheck[ 7 ] ), uxPriority, NULL );
}
/*-----------------------------------------------------------*/

static portTASK_FUNCTION( vCompetingMathTask1, pvParameters )
{
volatile float f1, f2, f3, f4;
volatile unsigned short *pusTaskCheckVariable;
volatile float fAnswer;
short sError = pdFALSE;

	f1 = 123.4567F;
	f2 = 2345.6789F;
	f3 = -918.222F;

	fAnswer = ( f1 + f2 ) * f3;

	/* The variable this task increments to show it is still running is passed in 
	as the parameter. */
	pusTaskCheckVariable = ( unsigned short * ) pvParameters;

	/* Keep performing a calculation and checking the result against a constant. */
	for(;;)
	{
		f1 = 123.4567F;
		f2 = 2345.6789F;
		f3 = -918.222F;

		f4 = ( f1 + f2 ) * f3;

		#if configUSE_PREEMPTION == 0
			taskYIELD();
		#endif

		/* If the calculation does not match the expected constant, stop the 
		increment of the check variable. */
		if( fabs( f4 - fAnswer ) > 0.001F )
		{
			sError = pdTRUE;
		}

		if( sError == pdFALSE )
		{
			/* If the calculation has always been correct, increment the check 
			variable so we know this task is still running okay. */
			( *pusTaskCheckVariable )++;
		}

		#if configUSE_PREEMPTION == 0
			taskYIELD();
		#endif

	}
}
/*-----------------------------------------------------------*/

static portTASK_FUNCTION( vCompetingMathTask2, pvParameters )
{
volatile float f1, f2, f3, f4;
volatile unsigned short *pusTaskCheckVariable;
volatile float fAnswer;
short sError = pdFALSE;

	f1 = -389.38F;
	f2 = 32498.2F;
	f3 = -2.0001F;

	fAnswer = ( f1 / f2 ) * f3;


	/* The variable this task increments to show it is still running is passed in 
	as the parameter. */
	pusTaskCheckVariable = ( unsigned short * ) pvParameters;

	/* Keep performing a calculation and checking the result against a constant. */
	for( ;; )
	{
		f1 = -389.38F;
		f2 = 32498.2F;
		f3 = -2.0001F;

		f4 = ( f1 / f2 ) * f3;

		#if configUSE_PREEMPTION == 0
			taskYIELD();
		#endif
		
		/* If the calculation does not match the expected constant, stop the 
		increment of the check variable. */
		if( fabs( f4 - fAnswer ) > 0.001F )
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

		#if configUSE_PREEMPTION == 0
			taskYIELD();
		#endif
	}
}
/*-----------------------------------------------------------*/

static portTASK_FUNCTION( vCompetingMathTask3, pvParameters )
{
volatile float *pfArray, fTotal1, fTotal2, fDifference, fPosition;
volatile unsigned short *pusTaskCheckVariable;
const size_t xArraySize = 10;
size_t xPosition;
short sError = pdFALSE;

	/* The variable this task increments to show it is still running is passed in 
	as the parameter. */
	pusTaskCheckVariable = ( unsigned short * ) pvParameters;

	pfArray = ( float * ) pvPortMalloc( xArraySize * sizeof( float ) );

	/* Keep filling an array, keeping a running total of the values placed in the 
	array.  Then run through the array adding up all the values.  If the two totals 
	do not match, stop the check variable from incrementing. */
	for( ;; )
	{
		fTotal1 = 0.0F;
		fTotal2 = 0.0F;
		fPosition = 0.0F;
		
		for( xPosition = 0; xPosition < xArraySize; xPosition++ )
		{
			pfArray[ xPosition ] = fPosition + 5.5F;
			fTotal1 += fPosition + 5.5F;	
		}

		#if configUSE_PREEMPTION == 0
			taskYIELD();
		#endif

		for( xPosition = 0; xPosition < xArraySize; xPosition++ )
		{
			fTotal2 += pfArray[ xPosition ];
		}

		fDifference = fTotal1 - fTotal2;
		if( fabs( fDifference ) > 0.001F )
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
			( *pusTaskCheckVariable )++;
		}
	}
}
/*-----------------------------------------------------------*/

static portTASK_FUNCTION( vCompetingMathTask4, pvParameters )
{
volatile float *pfArray, fTotal1, fTotal2, fDifference, fPosition;
volatile unsigned short *pusTaskCheckVariable;
const size_t xArraySize = 10;
size_t xPosition;
short sError = pdFALSE;

	/* The variable this task increments to show it is still running is passed in 
	as the parameter. */
	pusTaskCheckVariable = ( unsigned short * ) pvParameters;

	pfArray = ( float * ) pvPortMalloc( xArraySize * sizeof( float ) );

	/* Keep filling an array, keeping a running total of the values placed in the 
	array.  Then run through the array adding up all the values.  If the two totals 
	do not match, stop the check variable from incrementing. */
	for( ;; )
	{
		fTotal1 = 0.0F;
		fTotal2 = 0.0F;
		fPosition = 0.0F;

		for( xPosition = 0; xPosition < xArraySize; xPosition++ )
		{
			pfArray[ xPosition ] = fPosition * 12.123F;
			fTotal1 += fPosition * 12.123F;	
		}

		#if configUSE_PREEMPTION == 0
			taskYIELD();
		#endif

		for( xPosition = 0; xPosition < xArraySize; xPosition++ )
		{
			fTotal2 += pfArray[ xPosition ];
		}

		fDifference = fTotal1 - fTotal2;
		if( fabs( fDifference ) > 0.001F )
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
			( *pusTaskCheckVariable )++;
		}
	}
}				 
/*-----------------------------------------------------------*/

/* This is called to check that all the created tasks are still running. */
portBASE_TYPE xAreMathsTaskStillRunning( void )
{
/* Keep a history of the check variables so we know if they have been incremented 
since the last call. */
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



