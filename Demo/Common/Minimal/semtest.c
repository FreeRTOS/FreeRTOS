/*
	FreeRTOS.org V4.2.0 - Copyright (C) 2003-2007 Richard Barry.

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
	See http://www.FreeRTOS.org for documentation, latest information, license 
	and contact details.  Please ensure to read the configuration and relevant 
	port sections of the online documentation.
	***************************************************************************
*/

/*
 * Creates two sets of two tasks.  The tasks within a set share a variable, access 
 * to which is guarded by a semaphore.
 * 
 * Each task starts by attempting to obtain the semaphore.  On obtaining a 
 * semaphore a task checks to ensure that the guarded variable has an expected 
 * value.  It then clears the variable to zero before counting it back up to the 
 * expected value in increments of 1.  After each increment the variable is checked 
 * to ensure it contains the value to which it was just set. When the starting 
 * value is again reached the task releases the semaphore giving the other task in 
 * the set a chance to do exactly the same thing.  The starting value is high 
 * enough to ensure that a tick is likely to occur during the incrementing loop.
 *
 * An error is flagged if at any time during the process a shared variable is 
 * found to have a value other than that expected.  Such an occurrence would 
 * suggest an error in the mutual exclusion mechanism by which access to the 
 * variable is restricted.
 *
 * The first set of two tasks poll their semaphore.  The second set use blocking 
 * calls.
 *
 */


#include <stdlib.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* Demo app include files. */
#include "semtest.h"

/* The value to which the shared variables are counted. */
#define semtstBLOCKING_EXPECTED_VALUE		( ( unsigned portLONG ) 0xfff )
#define semtstNON_BLOCKING_EXPECTED_VALUE	( ( unsigned portLONG ) 0xff  )

#define semtstSTACK_SIZE			configMINIMAL_STACK_SIZE

#define semtstNUM_TASKS				( 4 )

#define semtstDELAY_FACTOR			( ( portTickType ) 10 )

/* The task function as described at the top of the file. */
static portTASK_FUNCTION_PROTO( prvSemaphoreTest, pvParameters );

/* Structure used to pass parameters to each task. */
typedef struct SEMAPHORE_PARAMETERS
{
	xSemaphoreHandle xSemaphore;
	volatile unsigned portLONG *pulSharedVariable;
	portTickType xBlockTime;
} xSemaphoreParameters;

/* Variables used to check that all the tasks are still running without errors. */
static volatile portSHORT sCheckVariables[ semtstNUM_TASKS ] = { 0 };
static volatile portSHORT sNextCheckVariable = 0;

/*-----------------------------------------------------------*/

void vStartSemaphoreTasks( unsigned portBASE_TYPE uxPriority )
{
xSemaphoreParameters *pxFirstSemaphoreParameters, *pxSecondSemaphoreParameters;
const portTickType xBlockTime = ( portTickType ) 100;

	/* Create the structure used to pass parameters to the first two tasks. */
	pxFirstSemaphoreParameters = ( xSemaphoreParameters * ) pvPortMalloc( sizeof( xSemaphoreParameters ) );

	if( pxFirstSemaphoreParameters != NULL )
	{
		/* Create the semaphore used by the first two tasks. */
		vSemaphoreCreateBinary( pxFirstSemaphoreParameters->xSemaphore );

		if( pxFirstSemaphoreParameters->xSemaphore != NULL )
		{
			/* Create the variable which is to be shared by the first two tasks. */
			pxFirstSemaphoreParameters->pulSharedVariable = ( unsigned portLONG * ) pvPortMalloc( sizeof( unsigned portLONG ) );

			/* Initialise the share variable to the value the tasks expect. */
			*( pxFirstSemaphoreParameters->pulSharedVariable ) = semtstNON_BLOCKING_EXPECTED_VALUE;

			/* The first two tasks do not block on semaphore calls. */
			pxFirstSemaphoreParameters->xBlockTime = ( portTickType ) 0;

			/* Spawn the first two tasks.  As they poll they operate at the idle priority. */
			xTaskCreate( prvSemaphoreTest, ( signed portCHAR * ) "PolSEM1", semtstSTACK_SIZE, ( void * ) pxFirstSemaphoreParameters, tskIDLE_PRIORITY, ( xTaskHandle * ) NULL );
			xTaskCreate( prvSemaphoreTest, ( signed portCHAR * ) "PolSEM2", semtstSTACK_SIZE, ( void * ) pxFirstSemaphoreParameters, tskIDLE_PRIORITY, ( xTaskHandle * ) NULL );
		}
	}

	/* Do exactly the same to create the second set of tasks, only this time 
	provide a block time for the semaphore calls. */
	pxSecondSemaphoreParameters = ( xSemaphoreParameters * ) pvPortMalloc( sizeof( xSemaphoreParameters ) );
	if( pxSecondSemaphoreParameters != NULL )
	{
		vSemaphoreCreateBinary( pxSecondSemaphoreParameters->xSemaphore );

		if( pxSecondSemaphoreParameters->xSemaphore != NULL )
		{
			pxSecondSemaphoreParameters->pulSharedVariable = ( unsigned portLONG * ) pvPortMalloc( sizeof( unsigned portLONG ) );
			*( pxSecondSemaphoreParameters->pulSharedVariable ) = semtstBLOCKING_EXPECTED_VALUE;
			pxSecondSemaphoreParameters->xBlockTime = xBlockTime / portTICK_RATE_MS;

			xTaskCreate( prvSemaphoreTest, ( signed portCHAR * ) "BlkSEM1", semtstSTACK_SIZE, ( void * ) pxSecondSemaphoreParameters, uxPriority, ( xTaskHandle * ) NULL );
			xTaskCreate( prvSemaphoreTest, ( signed portCHAR * ) "BlkSEM2", semtstSTACK_SIZE, ( void * ) pxSecondSemaphoreParameters, uxPriority, ( xTaskHandle * ) NULL );
		}
	}
}
/*-----------------------------------------------------------*/

static portTASK_FUNCTION( prvSemaphoreTest, pvParameters )
{
xSemaphoreParameters *pxParameters;
volatile unsigned portLONG *pulSharedVariable, ulExpectedValue;
unsigned portLONG ulCounter;
portSHORT sError = pdFALSE, sCheckVariableToUse;

	/* See which check variable to use.  sNextCheckVariable is not semaphore 
	protected! */
	portENTER_CRITICAL();
		sCheckVariableToUse = sNextCheckVariable;
		sNextCheckVariable++;
	portEXIT_CRITICAL();

	/* A structure is passed in as the parameter.  This contains the shared 
	variable being guarded. */
	pxParameters = ( xSemaphoreParameters * ) pvParameters;
	pulSharedVariable = pxParameters->pulSharedVariable;

	/* If we are blocking we use a much higher count to ensure loads of context
	switches occur during the count. */
	if( pxParameters->xBlockTime > ( portTickType ) 0 )
	{
		ulExpectedValue = semtstBLOCKING_EXPECTED_VALUE;
	}
	else
	{
		ulExpectedValue = semtstNON_BLOCKING_EXPECTED_VALUE;
	}

	for( ;; )
	{
		/* Try to obtain the semaphore. */
		if( xSemaphoreTake( pxParameters->xSemaphore, pxParameters->xBlockTime ) == pdPASS )
		{
			/* We have the semaphore and so expect any other tasks using the
			shared variable to have left it in the state we expect to find
			it. */
			if( *pulSharedVariable != ulExpectedValue )
			{
				sError = pdTRUE;
			}
			
			/* Clear the variable, then count it back up to the expected value
			before releasing the semaphore.  Would expect a context switch or
			two during this time. */
			for( ulCounter = ( unsigned portLONG ) 0; ulCounter <= ulExpectedValue; ulCounter++ )
			{
				*pulSharedVariable = ulCounter;
				if( *pulSharedVariable != ulCounter )
				{
					sError = pdTRUE;
				}
			}

			/* Release the semaphore, and if no errors have occurred increment the check
			variable. */
			if(	xSemaphoreGive( pxParameters->xSemaphore ) == pdFALSE )
			{
				sError = pdTRUE;
			}

			if( sError == pdFALSE )
			{
				if( sCheckVariableToUse < semtstNUM_TASKS )
				{
					( sCheckVariables[ sCheckVariableToUse ] )++;
				}
			}

			/* If we have a block time then we are running at a priority higher
			than the idle priority.  This task takes a long time to complete
			a cycle	(deliberately so to test the guarding) so will be starving
			out lower priority tasks.  Block for some time to allow give lower
			priority tasks some processor time. */
			vTaskDelay( pxParameters->xBlockTime * semtstDELAY_FACTOR );
		}
		else
		{
			if( pxParameters->xBlockTime == ( portTickType ) 0 )
			{
				/* We have not got the semaphore yet, so no point using the
				processor.  We are not blocking when attempting to obtain the
				semaphore. */
				taskYIELD();
			}
		}
	}
}
/*-----------------------------------------------------------*/

/* This is called to check that all the created tasks are still running. */
portBASE_TYPE xAreSemaphoreTasksStillRunning( void )
{
static portSHORT sLastCheckVariables[ semtstNUM_TASKS ] = { 0 };
portBASE_TYPE xTask, xReturn = pdTRUE;

	for( xTask = 0; xTask < semtstNUM_TASKS; xTask++ )
	{
		if( sLastCheckVariables[ xTask ] == sCheckVariables[ xTask ] )
		{
			xReturn = pdFALSE;
		}

		sLastCheckVariables[ xTask ] = sCheckVariables[ xTask ];
	}

	return xReturn;
}


