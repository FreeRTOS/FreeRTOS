/*
    FreeRTOS V8.0.0:rc1 - Copyright (C) 2014 Real Time Engineers Ltd. 
    All rights reserved

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
 *
 * This file demonstrates the use of the task tag and traceTASK_SWITCHED_IN and
 * traceTASK_SWITCHED_OUT macros to save and restore the floating point context.
 */

#include <stdlib.h>
#include <math.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo program include files. */
#include "flop.h"

/* Misc. definitions. */
#define mathSTACK_SIZE		configMINIMAL_STACK_SIZE
#define mathNUMBER_OF_TASKS  ( 8 )

/* Four tasks, each of which performs a different floating point calculation.  
Each of the four is created twice. */
static portTASK_FUNCTION_PROTO( vCompetingMathTask1, pvParameters );
static portTASK_FUNCTION_PROTO( vCompetingMathTask2, pvParameters );
static portTASK_FUNCTION_PROTO( vCompetingMathTask3, pvParameters );
static portTASK_FUNCTION_PROTO( vCompetingMathTask4, pvParameters );

/* These variables are used to check that all the tasks are still running.  If a 
task gets a calculation wrong it will stop incrementing its check variable. */
static volatile unsigned short usTaskCheck[ mathNUMBER_OF_TASKS ] = { ( unsigned short ) 0 };

/* Buffers into which the flop registers will be saved.  There is a buffer for 
each task created within this file.  Zeroing out this array is the normal and
safe option as this will cause the task to start with all zeros in its flop
context. */
static portDOUBLE dFlopRegisters[ mathNUMBER_OF_TASKS ][ portNO_FLOP_REGISTERS_TO_SAVE ];

/*-----------------------------------------------------------*/

void vStartMathTasks( unsigned portBASE_TYPE uxPriority )
{
TaskHandle_t xTaskJustCreated;
portBASE_TYPE x, y;

	/* Place known values into the buffers into which the flop registers are 
	to be saved.  This is for debug purposes only, it is not normally
	required.  The last position in each array is left at zero as the status
	register will be loaded from there. 
	
	It is intended that these values can be viewed being loaded into the
	flop registers when a task is started - however the Insight debugger
	does not seem to want to show the flop register values. */
	for( x = 0; x < mathNUMBER_OF_TASKS; x++ )
	{
		for( y = 0; y < ( portNO_FLOP_REGISTERS_TO_SAVE - 1 ); y++ )
		{
			dFlopRegisters[ x ][ y ] = ( x + 1 );
		}
	}

	/* Create the first task - passing it the address of the check variable
	that it is going to increment.  This check variable is used as an 
	indication that the task is still running. */
	xTaskCreate( vCompetingMathTask1, "Math1", mathSTACK_SIZE, ( void * ) &( usTaskCheck[ 0 ] ), uxPriority, &xTaskJustCreated );

	/* The task	tag value is a value that can be associated with a task, but 
	is not used by the scheduler itself.  Its use is down to the application so
	it makes a convenient place in this case to store the pointer to the buffer
	into which the flop context of the task will be stored.  The first created
	task uses dFlopRegisters[ 0 ], the second dFlopRegisters[ 1 ], etc. */
	vTaskSetApplicationTaskTag( xTaskJustCreated, ( void * ) &( dFlopRegisters[ 0 ][ 0 ] ) );

	/* Create another 7 tasks, allocating a buffer for each. */
	xTaskCreate( vCompetingMathTask2, "Math2", mathSTACK_SIZE, ( void * ) &( usTaskCheck[ 1 ] ), uxPriority, &xTaskJustCreated  );
	vTaskSetApplicationTaskTag( xTaskJustCreated, ( void * ) &( dFlopRegisters[ 1 ][ 0 ] ) );

	xTaskCreate( vCompetingMathTask3, "Math3", mathSTACK_SIZE, ( void * ) &( usTaskCheck[ 2 ] ), uxPriority, &xTaskJustCreated  );
	vTaskSetApplicationTaskTag( xTaskJustCreated, ( void * ) &( dFlopRegisters[ 2 ][ 0 ] ) );

	xTaskCreate( vCompetingMathTask4, "Math4", mathSTACK_SIZE, ( void * ) &( usTaskCheck[ 3 ] ), uxPriority, &xTaskJustCreated  );
	vTaskSetApplicationTaskTag( xTaskJustCreated, ( void * ) &( dFlopRegisters[ 3 ][ 0 ] ) );

	xTaskCreate( vCompetingMathTask1, "Math5", mathSTACK_SIZE, ( void * ) &( usTaskCheck[ 4 ] ), uxPriority, &xTaskJustCreated  );
	vTaskSetApplicationTaskTag( xTaskJustCreated, ( void * ) &( dFlopRegisters[ 4 ][ 0 ] ) );

	xTaskCreate( vCompetingMathTask2, "Math6", mathSTACK_SIZE, ( void * ) &( usTaskCheck[ 5 ] ), uxPriority, &xTaskJustCreated  );
	vTaskSetApplicationTaskTag( xTaskJustCreated, ( void * ) &( dFlopRegisters[ 5 ][ 0 ] ) );

	xTaskCreate( vCompetingMathTask3, "Math7", mathSTACK_SIZE, ( void * ) &( usTaskCheck[ 6 ] ), uxPriority, &xTaskJustCreated  );
	vTaskSetApplicationTaskTag( xTaskJustCreated, ( void * ) &( dFlopRegisters[ 6 ][ 0 ] ) );

	xTaskCreate( vCompetingMathTask4, "Math8", mathSTACK_SIZE, ( void * ) &( usTaskCheck[ 7 ] ), uxPriority, &xTaskJustCreated  );
	vTaskSetApplicationTaskTag( xTaskJustCreated, ( void * ) &( dFlopRegisters[ 7 ][ 0 ] ) );
}
/*-----------------------------------------------------------*/

static portTASK_FUNCTION( vCompetingMathTask1, pvParameters )
{
volatile portDOUBLE df1, df2, df3, df4;
volatile unsigned short *pusTaskCheckVariable;
volatile portDOUBLE dAnswer;
short sError = pdFALSE;

	df1 = 123.4567;
	df2 = 2345.6789;
	df3 = -918.222;

	dAnswer = ( df1 + df2 ) * df3;

	/* The variable this task increments to show it is still running is passed in 
	as the parameter. */
	pusTaskCheckVariable = ( unsigned short * ) pvParameters;

	/* Keep performing a calculation and checking the result against a constant. */
	for(;;)
	{
		df1 = 123.4567;
		df2 = 2345.6789;
		df3 = -918.222;

		df4 = ( df1 + df2 ) * df3;

		#if configUSE_PREEMPTION == 0
			taskYIELD();
		#endif

		/* If the calculation does not match the expected constant, stop the 
		increment of the check variable. */
		if( fabs( df4 - dAnswer ) > 0.001 )
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
volatile portDOUBLE df1, df2, df3, df4;
volatile unsigned short *pusTaskCheckVariable;
volatile portDOUBLE dAnswer;
short sError = pdFALSE;

	df1 = -389.38;
	df2 = 32498.2;
	df3 = -2.0001;

	dAnswer = ( df1 / df2 ) * df3;


	/* The variable this task increments to show it is still running is passed in 
	as the parameter. */
	pusTaskCheckVariable = ( unsigned short * ) pvParameters;

	/* Keep performing a calculation and checking the result against a constant. */
	for( ;; )
	{
		df1 = -389.38;
		df2 = 32498.2;
		df3 = -2.0001;

		df4 = ( df1 / df2 ) * df3;

		#if configUSE_PREEMPTION == 0
			taskYIELD();
		#endif
		
		/* If the calculation does not match the expected constant, stop the 
		increment of the check variable. */
		if( fabs( df4 - dAnswer ) > 0.001 )
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
volatile portDOUBLE *pdArray, dTotal1, dTotal2, dDifference;
volatile unsigned short *pusTaskCheckVariable;
const size_t xArraySize = 10;
size_t xPosition;
short sError = pdFALSE;

	/* The variable this task increments to show it is still running is passed in 
	as the parameter. */
	pusTaskCheckVariable = ( unsigned short * ) pvParameters;

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
			( *pusTaskCheckVariable )++;
		}
	}
}
/*-----------------------------------------------------------*/

static portTASK_FUNCTION( vCompetingMathTask4, pvParameters )
{
volatile portDOUBLE *pdArray, dTotal1, dTotal2, dDifference;
volatile unsigned short *pusTaskCheckVariable;
const size_t xArraySize = 10;
size_t xPosition;
short sError = pdFALSE;

	/* The variable this task increments to show it is still running is passed in 
	as the parameter. */
	pusTaskCheckVariable = ( unsigned short * ) pvParameters;

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



