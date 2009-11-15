/*
    FreeRTOS V6.0.1 - Copyright (C) 2009 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS eBook                                  *
    *                                                                         *
    *        "Using the FreeRTOS Real Time Kernel - a Practical Guide"        *
    *                  http://www.FreeRTOS.org/Documentation                  *
    *                                                                         *
    * A pdf reference manual is also available.  Both are usually delivered   *
    * to your inbox within 20 minutes to two hours when purchased between 8am *
    * and 8pm GMT (although please allow up to 24 hours in case of            *
    * exceptional circumstances).  Thank you for your support!                *
    *                                                                         *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    ***NOTE*** The exception to the GPL is included to allow you to distribute
    a combined work that includes FreeRTOS without being obliged to provide the
    source code for proprietary components outside of the FreeRTOS kernel.
    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public 
    License and the FreeRTOS license exception along with FreeRTOS; if not it 
    can be viewed here: http://www.freertos.org/a00114.html and also obtained 
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!

    http://www.FreeRTOS.org - Documentation, latest information, license and
    contact details.

    http://www.SafeRTOS.com - A version that is certified for use in safety
    critical systems.

    http://www.OpenRTOS.com - Commercial support, development, porting,
    licensing and training services.
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
xTaskHandle xTaskJustCreated;
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
	xTaskCreate( vFlopTest1, ( signed char * ) "flop1", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, &xTaskJustCreated );

	/* The task	tag value is a value that can be associated with a task, but 
	is not used by the scheduler itself.  Its use is down to the application so
	it makes a convenient place in this case to store the pointer to the buffer
	into which the flop context of the task will be stored.  The first created
	task uses ulFlopRegisters[ 0 ], the second ulFlopRegisters[ 1 ]. */
	vTaskSetApplicationTaskTag( xTaskJustCreated, ( void * ) &( ulFlopRegisters[ 0 ][ 0 ] ) );

	/* Do the same for the second task. */
	xTaskCreate( vFlopTest2, ( signed char * ) "flop2", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, &xTaskJustCreated );
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

