/*
	FreeRTOS.org V5.1.2 - Copyright (C) 2003-2009 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation; either version 2 of the License, or
	(at your option) any later version.

	FreeRTOS.org is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with FreeRTOS.org; if not, write to the Free Software
	Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

	A special exception to the GPL can be applied should you wish to distribute
	a combined work that includes FreeRTOS.org, without being obliged to provide
	the source code for any proprietary components.  See the licensing section 
	of http://www.FreeRTOS.org for full details of how and when the exception
	can be applied.

    ***************************************************************************
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
    ***************************************************************************

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
Changes from V1.2.3
	
	+ The created tasks now include calls to tskYIELD(), allowing them to be used
	  with the cooperative scheduler.
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
Changes from V1.2.1

	+ The constants used in the calculations are larger to ensure the
	  optimiser does not truncate them to 16 bits.
*/

#include <stdlib.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "print.h"

/* Demo program include files. */
#include "integer.h"

#define intgSTACK_SIZE		( ( unsigned portSHORT ) 256 )
#define intgNUMBER_OF_TASKS  ( 8 )

/* Four tasks, each of which performs a different calculation on four byte 
variables.  Each of the four is created twice. */
static void vCompeteingIntMathTask1( void *pvParameters );
static void vCompeteingIntMathTask2( void *pvParameters );
static void vCompeteingIntMathTask3( void *pvParameters );
static void vCompeteingIntMathTask4( void *pvParameters );

/* These variables are used to check that all the tasks are still running.  If a 
task gets a calculation wrong it will stop incrementing its check variable. */
static volatile unsigned portSHORT usTaskCheck[ intgNUMBER_OF_TASKS ] = { ( unsigned portSHORT ) 0 };
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

static void vCompeteingIntMathTask1( void *pvParameters )
{
portLONG l1, l2, l3, l4;
portSHORT sError = pdFALSE;
volatile unsigned portSHORT *pusTaskCheckVariable;
const portLONG lAnswer = ( ( portLONG ) 74565L + ( portLONG ) 1234567L ) * ( portLONG ) -918L;
const portCHAR * const pcTaskStartMsg = "Integer math task 1 started.\r\n";
const portCHAR * const pcTaskFailMsg = "Integer math task 1 failed.\r\n";

	/* Queue a message for printing to say the task has started. */
	vPrintDisplayMessage( &pcTaskStartMsg );

	/* The variable this task increments to show it is still running is passed in
	as the parameter. */
	pusTaskCheckVariable = ( unsigned portSHORT * ) pvParameters;

	/* Keep performing a calculation and checking the result against a constant. */
	for(;;)
	{
		l1 = ( portLONG ) 74565L;
		l2 = ( portLONG ) 1234567L;
		l3 = ( portLONG ) -918L;

		l4 = ( l1 + l2 ) * l3;

		taskYIELD();

		/* If the calculation does not match the expected constant, stop the
		increment of the check variable. */
		if( l4 != lAnswer )
		{
			vPrintDisplayMessage( &pcTaskFailMsg );
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

static void vCompeteingIntMathTask2( void *pvParameters )
{
portLONG l1, l2, l3, l4;
portSHORT sError = pdFALSE;
volatile unsigned portSHORT *pusTaskCheckVariable;
const portLONG lAnswer = ( ( portLONG ) -389000L / ( portLONG ) 329999L ) * ( portLONG ) -89L;
const portCHAR * const pcTaskStartMsg = "Integer math task 2 started.\r\n";
const portCHAR * const pcTaskFailMsg = "Integer math task 2 failed.\r\n";

	/* Queue a message for printing to say the task has started. */
	vPrintDisplayMessage( &pcTaskStartMsg );

	/* The variable this task increments to show it is still running is passed in
	as the parameter. */
	pusTaskCheckVariable = ( unsigned portSHORT * ) pvParameters;

	/* Keep performing a calculation and checking the result against a constant. */
	for( ;; )
	{
		l1 = -389000L;
		l2 = 329999L;
		l3 = -89L;

		l4 = ( l1 / l2 ) * l3;

		taskYIELD();

		/* If the calculation does not match the expected constant, stop the
		increment of the check variable. */
		if( l4 != lAnswer )
		{
			vPrintDisplayMessage( &pcTaskFailMsg );
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

static void vCompeteingIntMathTask3( void *pvParameters )
{
portLONG *plArray, lTotal1, lTotal2;
portSHORT sError = pdFALSE;
volatile unsigned portSHORT *pusTaskCheckVariable;
const unsigned portSHORT usArraySize = ( unsigned portSHORT ) 250;
unsigned portSHORT usPosition;
const portCHAR * const pcTaskStartMsg = "Integer math task 3 started.\r\n";
const portCHAR * const pcTaskFailMsg = "Integer math task 3 failed.\r\n";

	/* Queue a message for printing to say the task has started. */
	vPrintDisplayMessage( &pcTaskStartMsg );

	/* The variable this task increments to show it is still running is passed in
	as the parameter. */
	pusTaskCheckVariable = ( unsigned portSHORT * ) pvParameters;

	/* Create the array we are going to use for our check calculation. */
	plArray = ( portLONG * ) pvPortMalloc( ( size_t ) 250 * sizeof( portLONG ) );

	/* Keep filling the array, keeping a running total of the values placed in the
	array.  Then run through the array adding up all the values.  If the two totals
	do not match, stop the check variable from incrementing. */
	for( ;; )
	{
		lTotal1 = ( portLONG ) 0;
		lTotal2 = ( portLONG ) 0;

		for( usPosition = 0; usPosition < usArraySize; usPosition++ )
		{
			plArray[ usPosition ] = ( portLONG ) usPosition + ( portLONG ) 5;
			lTotal1 += ( portLONG ) usPosition + ( portLONG ) 5;
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
			variable so we know	this task is still running okay. */
			( *pusTaskCheckVariable )++;
		}
	}
}
/*-----------------------------------------------------------*/

static void vCompeteingIntMathTask4( void *pvParameters )
{
portLONG *plArray, lTotal1, lTotal2;
portSHORT sError = pdFALSE;
volatile unsigned portSHORT *pusTaskCheckVariable;
const unsigned portSHORT usArraySize = 250;
unsigned portSHORT usPosition;
const portCHAR * const pcTaskStartMsg = "Integer math task 4 started.\r\n";
const portCHAR * const pcTaskFailMsg = "Integer math task 4 failed.\r\n";

	/* Queue a message for printing to say the task has started. */
	vPrintDisplayMessage( &pcTaskStartMsg );

	/* The variable this task increments to show it is still running is passed in
	as the parameter. */
	pusTaskCheckVariable = ( unsigned portSHORT * ) pvParameters;

	/* Create the array we are going to use for our check calculation. */
	plArray = ( portLONG * ) pvPortMalloc( ( size_t ) 250 * sizeof( portLONG ) );

	/* Keep filling the array, keeping a running total of the values placed in the 
	array.  Then run through the array adding up all the values.  If the two totals 
	do not match, stop the check variable from incrementing. */
	for( ;; )
	{
		lTotal1 = ( portLONG ) 0;
		lTotal2 = ( portLONG ) 0;

		for( usPosition = 0; usPosition < usArraySize; usPosition++ )
		{
			plArray[ usPosition ] = ( portLONG ) usPosition * ( portLONG ) 12;
			lTotal1 += ( portLONG ) usPosition * ( portLONG ) 12;	
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
			variable so we know	this task is still running okay. */
			( *pusTaskCheckVariable )++;
		}
	}
}
/*-----------------------------------------------------------*/

/* This is called to check that all the created tasks are still running. */
portBASE_TYPE xAreIntegerMathsTaskStillRunning( void )
{
/* Keep a history of the check variables so we know if they have been incremented 
since the last call. */
static unsigned portSHORT usLastTaskCheck[ intgNUMBER_OF_TASKS ] = { ( unsigned portSHORT ) 0 };
portBASE_TYPE xReturn = pdTRUE, xTask;

	/* Check the maths tasks are still running by ensuring their check variables 
	are still incrementing. */
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
