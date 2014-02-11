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
 * Tests the floating point context save and restore mechanism.
 *
 * Two tasks are created - each of which is allocated a buffer of 
 * portNO_FLOP_REGISTERS_TO_SAVE 32bit variables into which the flop context
 * of the task is saved when the task is switched out, and from which the
 * flop context of the task is restored when the task is switch in.  Prior to 
 * the tasks being created each position in the two buffers is filled with a 
 * unique value - this way the flop context of each task is different.
 *
 * The two test tasks never block so are always in either the Running or
 * Ready state.  They execute at the lowest priority so will get pre-empted
 * regularly, although the yield frequently so will not get much execution
 * time.  The lack of execution time is not a problem as its only the 
 * switching in and out that is being tested.
 *
 * Whenever a task is moved from the Ready to the Running state its flop 
 * context will be loaded from the buffer, but while the task is in the
 * Running state the buffer is not used and can contain any value - in this
 * case and for test purposes the task itself clears the buffer to zero.  
 * The next time the task is moved out of the Running state into the
 * Ready state the flop context will once more get saved to the buffer - 
 * overwriting the zeros.
 *
 * Therefore whenever the task is not in the Running state its buffer contains
 * the most recent values of its floating point registers - the zeroing out
 * of the buffer while the task was executing being used to ensure the values 
 * the buffer contains are not stale.
 *
 * When neither test task is in the Running state the buffers should contain
 * the unique values allocated before the tasks were created.  If so then
 * the floating point context has been maintained.  This check is performed
 * by the 'check' task (defined in main.c) by calling 
 * xAreFlopRegisterTestsStillRunning().
 *
 * The test tasks also increment a value each time they execute.
 * xAreFlopRegisterTestsStillRunning() also checks that this value has changed
 * since it last ran to ensure the test tasks are still getting processing time.
 */

/* Standard includes files. */
#include <string.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"

/*-----------------------------------------------------------*/

#define flopNUMBER_OF_TASKS		2
#define flopSTART_VALUE ( 0x1 )

/*-----------------------------------------------------------*/

/* The two test tasks as described at the top of this file. */
static void vFlopTest1( void *pvParameters );
static void vFlopTest2( void *pvParameters );

/*-----------------------------------------------------------*/

/* Buffers into which the flop registers will be saved.  There is a buffer for 
both tasks. */
static volatile unsigned long ulFlopRegisters[ flopNUMBER_OF_TASKS ][ portNO_FLOP_REGISTERS_TO_SAVE ];

/* Variables that are incremented by the tasks to indicate that they are still
running. */
static volatile unsigned long ulFlop1CycleCount = 0, ulFlop2CycleCount = 0;

/*-----------------------------------------------------------*/

void vStartFlopRegTests( void )
{
TaskHandle_t xTaskJustCreated;
unsigned portBASE_TYPE x, y, z = flopSTART_VALUE;

	/* Fill the arrays into which the flop registers are to be saved with 
	known values.  These are the values that will be written to the flop
	registers when the tasks start, and as the tasks do not perform any
	flop operations the values should never change.  Each position in the
	buffer contains a different value so the flop context of each task
	will be different. */
	for( x = 0; x < flopNUMBER_OF_TASKS; x++ )
	{
		for( y = 0; y < ( portNO_FLOP_REGISTERS_TO_SAVE - 1); y++ )
		{
			ulFlopRegisters[ x ][ y ] = z;
			z++;
		}
	}


	/* Create the first task. */
	xTaskCreate( vFlopTest1, "flop1", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, &xTaskJustCreated );

	/* The task	tag value is a value that can be associated with a task, but 
	is not used by the scheduler itself.  Its use is down to the application so
	it makes a convenient place in this case to store the pointer to the buffer
	into which the flop context of the task will be stored.  The first created
	task uses ulFlopRegisters[ 0 ], the second ulFlopRegisters[ 1 ]. */
	vTaskSetApplicationTaskTag( xTaskJustCreated, ( void * ) &( ulFlopRegisters[ 0 ][ 0 ] ) );

	/* Do the same for the second task. */
	xTaskCreate( vFlopTest2, "flop2", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, &xTaskJustCreated );
	vTaskSetApplicationTaskTag( xTaskJustCreated, ( void * ) &( ulFlopRegisters[ 1 ][ 0 ] ) );
}
/*-----------------------------------------------------------*/

static void vFlopTest1( void *pvParameters )
{
	/* Just to remove compiler warning. */
	( void ) pvParameters;

	for( ;; )
	{
		/* The values from the buffer should have now been written to the flop
		registers.  Clear the buffer to ensure the same values then get written
		back the next time the task runs.  Being preempted during this memset
		could cause the test to fail, hence the critical section. */
		portENTER_CRITICAL();
			memset( ( void * ) ulFlopRegisters[ 0 ], 0x00, ( portNO_FLOP_REGISTERS_TO_SAVE * sizeof( unsigned portBASE_TYPE ) ) );
		portEXIT_CRITICAL();

		/* We don't have to do anything other than indicate that we are 
		still running. */
		ulFlop1CycleCount++;
		taskYIELD();
	}
}
/*-----------------------------------------------------------*/

static void vFlopTest2( void *pvParameters )
{
	/* Just to remove compiler warning. */
	( void ) pvParameters;

	for( ;; )
	{
		/* The values from the buffer should have now been written to the flop
		registers.  Clear the buffer to ensure the same values then get written
		back the next time the task runs. */
		portENTER_CRITICAL();
			memset( ( void * ) ulFlopRegisters[ 1 ], 0x00, ( portNO_FLOP_REGISTERS_TO_SAVE * sizeof( unsigned portBASE_TYPE ) ) );
		portEXIT_CRITICAL();

		/* We don't have to do anything other than indicate that we are 
		still running. */
		ulFlop2CycleCount++;
		taskYIELD();
	}
}
/*-----------------------------------------------------------*/

portBASE_TYPE xAreFlopRegisterTestsStillRunning( void )
{
portBASE_TYPE xReturn = pdPASS;
unsigned portBASE_TYPE x, y, z = flopSTART_VALUE;
static unsigned long ulLastFlop1CycleCount = 0, ulLastFlop2CycleCount = 0;

	/* Called from the 'check' task.
	
	The flop tasks cannot be currently running, check their saved registers
	are as expected.  The tests tasks do not perform any flop operations so
	their registers should be as per their initial setting. */
	for( x = 0; x < flopNUMBER_OF_TASKS; x++ )
	{
		for( y = 0; y < ( portNO_FLOP_REGISTERS_TO_SAVE - 1 ); y++ )
		{
			if( ulFlopRegisters[ x ][ y ] != z )
			{
				xReturn = pdFAIL;
				break;
			}

			z++;
		}
	}

	/* Check both tasks have actually been swapped in and out since this function
	last executed. */
	if( ulFlop1CycleCount == ulLastFlop1CycleCount )
	{
		xReturn = pdFAIL;
	}

	if( ulFlop2CycleCount == ulLastFlop2CycleCount )
	{
		xReturn = pdFAIL;
	}

	ulLastFlop1CycleCount = ulFlop1CycleCount;
	ulLastFlop2CycleCount = ulFlop2CycleCount;

	return xReturn;
}

