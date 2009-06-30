/*
	FreeRTOS.org V5.3.1 - Copyright (C) 2003-2009 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify it
	under the terms of the GNU General Public License (version 2) as published
	by the Free Software Foundation and modified by the FreeRTOS exception.
	**NOTE** The exception to the GPL is included to allow you to distribute a
	combined work that includes FreeRTOS.org without being obliged to provide
	the source code for any proprietary components.  Alternative commercial
	license and support terms are also available upon request.  See the 
	licensing section of http://www.FreeRTOS.org for full details.

	FreeRTOS.org is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
	more details.

	You should have received a copy of the GNU General Public License along
	with FreeRTOS.org; if not, write to the Free Software Foundation, Inc., 59
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.


	***************************************************************************
	*                                                                         *
	* Get the FreeRTOS eBook!  See http://www.FreeRTOS.org/Documentation      *
	*                                                                         *
	* This is a concise, step by step, 'hands on' guide that describes both   *
	* general multitasking concepts and FreeRTOS specifics. It presents and   *
	* explains numerous examples that are written using the FreeRTOS API.     *
	* Full source code for all the examples is provided in an accompanying    *
	* .zip file.                                                              *
	*                                                                         *
	***************************************************************************

	1 tab == 4 spaces!

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

	http://www.FreeRTOS.org - Documentation, latest information, license and
	contact details.

	http://www.SafeRTOS.com - A version that is certified for use in safety
	critical systems.

	http://www.OpenRTOS.com - Commercial support, development, porting,
	licensing and training services.
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
static volatile unsigned portSHORT usTaskCheck[ mathNUMBER_OF_TASKS ] = { ( unsigned portSHORT ) 0 };

/* Buffers into which the flop registers will be saved.  There is a buffer for 
each task created within this file.  Zeroing out this array is the normal and
safe option as this will cause the task to start with all zeros in its flop
context. */
static unsigned portLONG ulFlopRegisters[ mathNUMBER_OF_TASKS ][ portNO_FLOP_REGISTERS_TO_SAVE ];

/*-----------------------------------------------------------*/

void vStartMathTasks( unsigned portBASE_TYPE uxPriority )
{
xTaskHandle xTaskJustCreated;
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
			ulFlopRegisters[ x ][ y ] = ( x + 1 );
		}
	}

	/* Create the first task - passing it the address of the check variable
	that it is going to increment.  This check variable is used as an 
	indication that the task is still running. */
	xTaskCreate( vCompetingMathTask1, ( signed portCHAR * ) "Math1", mathSTACK_SIZE, ( void * ) &( usTaskCheck[ 0 ] ), uxPriority, &xTaskJustCreated );

	/* The task	tag value is a value that can be associated with a task, but 
	is not used by the scheduler itself.  Its use is down to the application so
	it makes a convenient place in this case to store the pointer to the buffer
	into which the flop context of the task will be stored.  The first created
	task uses ulFlopRegisters[ 0 ], the second ulFlopRegisters[ 1 ], etc. */
	vTaskSetApplicationTaskTag( xTaskJustCreated, ( void * ) &( ulFlopRegisters[ 0 ][ 0 ] ) );

	/* Create another 7 tasks, allocating a buffer for each. */
	xTaskCreate( vCompetingMathTask2, ( signed portCHAR * ) "Math2", mathSTACK_SIZE, ( void * ) &( usTaskCheck[ 1 ] ), uxPriority, &xTaskJustCreated  );
	vTaskSetApplicationTaskTag( xTaskJustCreated, ( void * ) &( ulFlopRegisters[ 1 ][ 0 ] ) );

	xTaskCreate( vCompetingMathTask3, ( signed portCHAR * ) "Math3", mathSTACK_SIZE, ( void * ) &( usTaskCheck[ 2 ] ), uxPriority, &xTaskJustCreated  );
	vTaskSetApplicationTaskTag( xTaskJustCreated, ( void * ) &( ulFlopRegisters[ 2 ][ 0 ] ) );

	xTaskCreate( vCompetingMathTask4, ( signed portCHAR * ) "Math4", mathSTACK_SIZE, ( void * ) &( usTaskCheck[ 3 ] ), uxPriority, &xTaskJustCreated  );
	vTaskSetApplicationTaskTag( xTaskJustCreated, ( void * ) &( ulFlopRegisters[ 3 ][ 0 ] ) );

	xTaskCreate( vCompetingMathTask1, ( signed portCHAR * ) "Math5", mathSTACK_SIZE, ( void * ) &( usTaskCheck[ 4 ] ), uxPriority, &xTaskJustCreated  );
	vTaskSetApplicationTaskTag( xTaskJustCreated, ( void * ) &( ulFlopRegisters[ 4 ][ 0 ] ) );

	xTaskCreate( vCompetingMathTask2, ( signed portCHAR * ) "Math6", mathSTACK_SIZE, ( void * ) &( usTaskCheck[ 5 ] ), uxPriority, &xTaskJustCreated  );
	vTaskSetApplicationTaskTag( xTaskJustCreated, ( void * ) &( ulFlopRegisters[ 5 ][ 0 ] ) );

	xTaskCreate( vCompetingMathTask3, ( signed portCHAR * ) "Math7", mathSTACK_SIZE, ( void * ) &( usTaskCheck[ 6 ] ), uxPriority, &xTaskJustCreated  );
	vTaskSetApplicationTaskTag( xTaskJustCreated, ( void * ) &( ulFlopRegisters[ 6 ][ 0 ] ) );

	xTaskCreate( vCompetingMathTask4, ( signed portCHAR * ) "Math8", mathSTACK_SIZE, ( void * ) &( usTaskCheck[ 7 ] ), uxPriority, &xTaskJustCreated  );
	vTaskSetApplicationTaskTag( xTaskJustCreated, ( void * ) &( ulFlopRegisters[ 7 ][ 0 ] ) );
}
/*-----------------------------------------------------------*/

static portTASK_FUNCTION( vCompetingMathTask1, pvParameters )
{
volatile portFLOAT ff1, ff2, ff3, ff4;
volatile unsigned portSHORT *pusTaskCheckVariable;
volatile portFLOAT fAnswer;
portSHORT sError = pdFALSE;

	ff1 = 123.4567F;
	ff2 = 2345.6789F;
	ff3 = -918.222F;

	fAnswer = ( ff1 + ff2 ) * ff3;

	/* The variable this task increments to show it is still running is passed in 
	as the parameter. */
	pusTaskCheckVariable = ( unsigned portSHORT * ) pvParameters;

	/* Keep performing a calculation and checking the result against a constant. */
	for(;;)
	{
		ff1 = 123.4567F;
		ff2 = 2345.6789F;
		ff3 = -918.222F;

		ff4 = ( ff1 + ff2 ) * ff3;

		#if configUSE_PREEMPTION == 0
			taskYIELD();
		#endif

		/* If the calculation does not match the expected constant, stop the 
		increment of the check variable. */
		if( fabs( ff4 - fAnswer ) > 0.001F )
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
volatile portFLOAT ff1, ff2, ff3, ff4;
volatile unsigned portSHORT *pusTaskCheckVariable;
volatile portFLOAT fAnswer;
portSHORT sError = pdFALSE;

	ff1 = -389.38F;
	ff2 = 32498.2F;
	ff3 = -2.0001F;

	fAnswer = ( ff1 / ff2 ) * ff3;


	/* The variable this task increments to show it is still running is passed in 
	as the parameter. */
	pusTaskCheckVariable = ( unsigned portSHORT * ) pvParameters;

	/* Keep performing a calculation and checking the result against a constant. */
	for( ;; )
	{
		ff1 = -389.38F;
		ff2 = 32498.2F;
		ff3 = -2.0001F;

		ff4 = ( ff1 / ff2 ) * ff3;

		#if configUSE_PREEMPTION == 0
			taskYIELD();
		#endif
		
		/* If the calculation does not match the expected constant, stop the 
		increment of the check variable. */
		if( fabs( ff4 - fAnswer ) > 0.001F )
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
volatile portFLOAT *pfArray, fTotal1, fTotal2, fDifference;
volatile unsigned portSHORT *pusTaskCheckVariable;
const size_t xArraySize = 10;
size_t xPosition;
portSHORT sError = pdFALSE;

	/* The variable this task increments to show it is still running is passed in 
	as the parameter. */
	pusTaskCheckVariable = ( unsigned portSHORT * ) pvParameters;

	pfArray = ( portFLOAT * ) pvPortMalloc( xArraySize * sizeof( portFLOAT ) );

	/* Keep filling an array, keeping a running total of the values placed in the 
	array.  Then run through the array adding up all the values.  If the two totals 
	do not match, stop the check variable from incrementing. */
	for( ;; )
	{
		fTotal1 = 0.0F;
		fTotal2 = 0.0F;

		for( xPosition = 0; xPosition < xArraySize; xPosition++ )
		{
			pfArray[ xPosition ] = ( portFLOAT ) xPosition + 5.5F;
			fTotal1 += ( portFLOAT ) xPosition + 5.5F;	
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
volatile portFLOAT *pfArray, fTotal1, fTotal2, fDifference;
volatile unsigned portSHORT *pusTaskCheckVariable;
const size_t xArraySize = 10;
size_t xPosition;
portSHORT sError = pdFALSE;

	/* The variable this task increments to show it is still running is passed in 
	as the parameter. */
	pusTaskCheckVariable = ( unsigned portSHORT * ) pvParameters;

	pfArray = ( portFLOAT * ) pvPortMalloc( xArraySize * sizeof( portFLOAT ) );

	/* Keep filling an array, keeping a running total of the values placed in the 
	array.  Then run through the array adding up all the values.  If the two totals 
	do not match, stop the check variable from incrementing. */
	for( ;; )
	{
		fTotal1 = 0.0F;
		fTotal2 = 0.0F;

		for( xPosition = 0; xPosition < xArraySize; xPosition++ )
		{
			pfArray[ xPosition ] = ( portFLOAT ) xPosition * 12.123F;
			fTotal1 += ( portFLOAT ) xPosition * 12.123F;	
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
static unsigned portSHORT usLastTaskCheck[ mathNUMBER_OF_TASKS ] = { ( unsigned portSHORT ) 0 };
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



