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
 * Creates all the demo application tasks, then starts the scheduler.  The WEB
 * documentation provides more details of the standard demo application tasks.
 * In addition to the standard demo tasks, the following tasks are defined
 * within this file:
 * 
 * "Register test" tasks - These tasks first set all the general purpose 
 * registers to a known value (with each register containing a different value)
 * then test each general purpose register to ensure it still contains the
 * set value.  There are two register test tasks, with different values being
 * used by each.  The register test tasks will be preempted frequently due to
 * their low priority.  Setting then testing the value of each register in this
 * manner ensures the context of the tasks is being correctly saved and then
 * restored as the preemptive context switches occur.  An error is flagged
 * should any register be found to contain an unexpected value.  In addition
 * the register test tasks maintain a count of the number of times they cycle, 
 * so an error can also be flagged should the cycle count not increment as
 * expected (indicating the the tasks are not executing at all).
 *
 * "Check" task -  This only executes every three seconds but has the highest 
 * priority so is guaranteed to get processor time.  Its main function is to 
 * check that all the other tasks are still operational.  Each task maintains a 
 * unique count that is incremented each time the task successfully completes 
 * its function.  Should any error occur within such a task the count is 
 * permanently halted.  The check task inspects the count of each task to 
 * ensure it has changed since the last time the check task executed.  If all 
 * the count variables have changed all the tasks are still executing error 
 * free, and the check task toggles the onboard LED.  Should any task contain 
 * an error at any time check task cycle frequency is increased to 500ms, 
 * causing the LED toggle rate to increase from 3 seconds to 500ms and in so
 * doing providing visual feedback that an error has occurred.
 *
 */

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "croutine.h"

/* Demo application includes. */
#include "BlockQ.h"
#include "crflash.h"
#include "blocktim.h"
#include "integer.h"
#include "comtest2.h"
#include "partest.h"

/* Demo task priorities. */
#define mainBLOCK_Q_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainCHECK_TASK_PRIORITY				( tskIDLE_PRIORITY + 3 )
#define mainCOM_TEST_PRIORITY				( 2 )

/* Delay between check task cycles when an error has/has not been detected. */
#define mainNO_ERROR_DELAY					( ( portTickType ) 3000 / portTICK_RATE_MS )
#define mainERROR_DELAY						( ( portTickType ) 500 / portTICK_RATE_MS )

/* The number of flash co-routines to create. */
#define mainNUM_FLASH_COROUTINES			( 3 )

/* Baud rate used by the comtest tasks. */
#define mainCOM_TEST_BAUD_RATE				( 19200 )

/* The LED used by the comtest tasks.  mainCOM_TEST_LED + 1 is also used.
See the comtest.c file for more information. */
#define mainCOM_TEST_LED					( 4 )

/* The LED used by the check task. */
#define mainCHECK_LED						( 7 )

/*-----------------------------------------------------------*/

/*
 * The register test tasks as described at the top of this file. 
 */ 
void xRegisterTest1( void *pvParameters );
void xRegisterTest2( void *pvParameters );

/*
 * The check task as described at the top of this file.
 */
static void vCheckTask( void *pvParameters );

/*
 * Setup the processor ready for the demo.
 */
static void prvSetupHardware( void );

/*-----------------------------------------------------------*/

/* Variables used to detect errors within the register test tasks. */
static volatile unsigned portSHORT usTest1CycleCounter = 0, usTest2CycleCounter = 0;
static unsigned portSHORT usPreviousTest1Count = 0, usPreviousTest2Count = 0;

/* Set to pdTRUE should an error be detected in any of the standard demo tasks
or tasks defined within this file. */
static unsigned portSHORT usErrorDetected = pdFALSE;

/*-----------------------------------------------------------*/

/*
 * Create the demo tasks then start the scheduler.
 */
int main( void )
{
	/* Configure any hardware required for this demo. */
	prvSetupHardware();

	/* Create the standard demo tasks. */
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );	
	vStartIntegerMathTasks( tskIDLE_PRIORITY );
	vStartFlashCoRoutines( mainNUM_FLASH_COROUTINES );
	vAltStartComTestTasks( mainCOM_TEST_PRIORITY, mainCOM_TEST_BAUD_RATE, mainCOM_TEST_LED );
	vCreateBlockTimeTasks();

	/* Create the test tasks defined within this file. */
	xTaskCreate( xRegisterTest1, "Reg1", configMINIMAL_STACK_SIZE, ( void * ) &usTest1CycleCounter, tskIDLE_PRIORITY, NULL );
	xTaskCreate( xRegisterTest2, "Reg2", configMINIMAL_STACK_SIZE, ( void * ) &usTest2CycleCounter, tskIDLE_PRIORITY, NULL );
	xTaskCreate( vCheckTask, "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

	/* Finally start the scheduler. */
	vTaskStartScheduler();

	/* Will only reach here if there is insufficient heap available to start
	the scheduler. */
	return 0;
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	vParTestInitialise();
}
/*-----------------------------------------------------------*/

static void vCheckTask( void *pvParameters )
{
portTickType xLastExecutionTime;

/* Start with the no error delay.  The long delay will cause the LED to flash
slowly. */
portTickType xDelay = mainNO_ERROR_DELAY;

	/* Initialise xLastExecutionTime so the first call to vTaskDelayUntil()
	works correctly. */
	xLastExecutionTime = xTaskGetTickCount();

	for( ;; )
	{
		/* Wait until it is time for the next cycle. */
		vTaskDelayUntil( &xLastExecutionTime, xDelay );

		/* Has an error been found in any of the standard demo tasks? */

		if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
		{
			usErrorDetected = pdTRUE;
		}
	
		if( xAreComTestTasksStillRunning() != pdTRUE )
		{
			usErrorDetected = pdTRUE;
		}

		if( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
		{
			usErrorDetected = pdTRUE;
		}

		if( xAreBlockingQueuesStillRunning() != pdTRUE )
		{
			usErrorDetected = pdTRUE;
		}


		/* Are the register test tasks still cycling? */

		if( usTest1CycleCounter == usPreviousTest1Count )
		{
			usErrorDetected = pdTRUE;
		}

		if( usTest2CycleCounter == usPreviousTest2Count )
		{
			usErrorDetected = pdTRUE;
		}

		usPreviousTest2Count = usTest2CycleCounter;
		usPreviousTest1Count = usTest1CycleCounter;

		
		/* If an error has been detected in any task then the delay will be
		reduced to increase the cycle rate of this task.  This has the effect
		of causing the LED to flash much faster giving a visual indication of
		the error condition. */
		if( usErrorDetected != pdFALSE )
		{
			xDelay = mainERROR_DELAY;
		}

		/* Finally, toggle the LED before returning to delay to wait for the
		next cycle. */
		vParTestToggleLED( mainCHECK_LED );
	}
}
/*-----------------------------------------------------------*/

void xRegisterTest1( void *pvParameters )
{
/* This static so as not to use the frame pointer.   They are volatile
also to avoid it being stored in a register that we clobber during the test. */
static unsigned portSHORT * volatile pusParameter;

	/* The variable incremented by this task is passed in as the parameter
	even though it is defined within this file.  This is just to test the
	parameter passing mechanism. */
	pusParameter = pvParameters;

	for( ;; )
	{
		/* Increment the variable to show this task is still cycling. */
		( *pusParameter )++;

		/* Set the w registers to known values, then check that each register
		contains the expected value.  See the explanation at the top of this
		file for more information. */
		asm volatile( 	"mov.w	#0x0101, W0		\n"		\
						"mov.w	#0x0102, W1		\n"		\
						"mov.w	#0x0103, W2		\n"		\
						"mov.w	#0x0104, W3		\n"		\
						"mov.w	#0x0105, W4		\n"		\
						"mov.w	#0x0106, W5		\n"		\
						"mov.w	#0x0107, W6		\n"		\
						"mov.w	#0x0108, W7		\n"		\
						"mov.w	#0x0109, W8		\n"		\
						"mov.w	#0x010a, W9		\n"		\
						"mov.w	#0x010b, W10	\n"		\
						"mov.w	#0x010c, W11	\n"		\
						"mov.w	#0x010d, W12	\n"		\
						"mov.w	#0x010e, W13	\n"		\
						"mov.w	#0x010f, W14	\n"		\
						"sub	#0x0101, W0		\n"		\
						"cp0.w	W0				\n" 	\
						"bra	NZ, ERROR_TEST1 \n"		\
						"sub	#0x0102, W1		\n"		\
						"cp0.w	W1				\n" 	\
						"bra	NZ, ERROR_TEST1 \n"		\
						"sub	#0x0103, W2		\n"		\
						"cp0.w	W2				\n" 	\
						"bra	NZ, ERROR_TEST1 \n"		\
						"sub	#0x0104, W3		\n"		\
						"cp0.w	W3				\n" 	\
						"bra	NZ, ERROR_TEST1 \n"		\
						"sub	#0x0105, W4		\n"		\
						"cp0.w	W4				\n" 	\
						"bra	NZ, ERROR_TEST1 \n"		\
						"sub	#0x0106, W5		\n"		\
						"cp0.w	W5				\n" 	\
						"bra	NZ, ERROR_TEST1 \n"		\
						"sub	#0x0107, W6		\n"		\
						"cp0.w	W6				\n" 	\
						"bra	NZ, ERROR_TEST1 \n"		\
						"sub	#0x0108, W7		\n"		\
						"cp0.w	W7				\n" 	\
						"bra	NZ, ERROR_TEST1 \n"		\
						"sub	#0x0109, W8		\n"		\
						"cp0.w	W8				\n" 	\
						"bra	NZ, ERROR_TEST1 \n"		\
						"sub	#0x010a, W9		\n"		\
						"cp0.w	W9				\n" 	\
						"bra	NZ, ERROR_TEST1 \n"		\
						"sub	#0x010b, W10	\n"		\
						"cp0.w	W10				\n" 	\
						"bra	NZ, ERROR_TEST1 \n"		\
						"sub	#0x010c, W11	\n"		\
						"cp0.w	W11				\n" 	\
						"bra	NZ, ERROR_TEST1 \n"		\
						"sub	#0x010d, W12	\n"		\
						"cp0.w	W12				\n" 	\
						"bra	NZ, ERROR_TEST1 \n"		\
						"sub	#0x010e, W13	\n"		\
						"cp0.w	W13				\n" 	\
						"bra	NZ, ERROR_TEST1 \n"		\
						"sub	#0x010f, W14	\n"		\
						"cp0.w	W14				\n" 	\
						"bra	NZ, ERROR_TEST1 \n"		\
						"bra	NO_ERROR1		\n" 	\
						"ERROR_TEST1:			\n"		\
						"mov.w	#1, W0			\n"		\
						"mov.w	W0, _usErrorDetected\n"	\
						"NO_ERROR1:				\n" );
	}
}
/*-----------------------------------------------------------*/

void xRegisterTest2( void *pvParameters )
{
/* This static so as not to use the frame pointer.   They are volatile
also to avoid it being stored in a register that we clobber during the test. */
static unsigned portSHORT * volatile pusParameter;

	/* The variable incremented by this task is passed in as the parameter
	even though it is defined within this file.  This is just to test the
	parameter passing mechanism. */
	pusParameter = pvParameters;

	for( ;; )
	{
		/* Increment the variable to show this task is still cycling. */
		( *pusParameter )++;

		/* Set the w registers to known values, then check that each register
		contains the expected value.  See the explanation at the top of this
		file for more information. */
		asm volatile( 	"mov.w	#0x0100, W0		\n"		\
						"mov.w	#0x0101, W1		\n"		\
						"mov.w	#0x0102, W2		\n"		\
						"mov.w	#0x0103, W3		\n"		\
						"mov.w	#0x0104, W4		\n"		\
						"mov.w	#0x0105, W5		\n"		\
						"mov.w	#0x0106, W6		\n"		\
						"mov.w	#0x0107, W7		\n"		\
						"mov.w	#0x0108, W8		\n"		\
						"mov.w	#0x0109, W9		\n"		\
						"mov.w	#0x010a, W10	\n"		\
						"mov.w	#0x010b, W11	\n"		\
						"mov.w	#0x010c, W12	\n"		\
						"mov.w	#0x010d, W13	\n"		\
						"mov.w	#0x010e, W14	\n"		\
						"sub	#0x0100, W0		\n"		\
						"cp0.w	W0				\n" 	\
						"bra	NZ, ERROR_TEST2 \n"		\
						"sub	#0x0101, W1		\n"		\
						"cp0.w	W1				\n" 	\
						"bra	NZ, ERROR_TEST2 \n"		\
						"sub	#0x0102, W2		\n"		\
						"cp0.w	W2				\n" 	\
						"bra	NZ, ERROR_TEST2 \n"		\
						"sub	#0x0103, W3		\n"		\
						"cp0.w	W3				\n" 	\
						"bra	NZ, ERROR_TEST2 \n"		\
						"sub	#0x0104, W4		\n"		\
						"cp0.w	W4				\n" 	\
						"bra	NZ, ERROR_TEST2 \n"		\
						"sub	#0x0105, W5		\n"		\
						"cp0.w	W5				\n" 	\
						"bra	NZ, ERROR_TEST2 \n"		\
						"sub	#0x0106, W6		\n"		\
						"cp0.w	W6				\n" 	\
						"bra	NZ, ERROR_TEST2 \n"		\
						"sub	#0x0107, W7		\n"		\
						"cp0.w	W7				\n" 	\
						"bra	NZ, ERROR_TEST2 \n"		\
						"sub	#0x0108, W8		\n"		\
						"cp0.w	W8				\n" 	\
						"bra	NZ, ERROR_TEST2 \n"		\
						"sub	#0x0109, W9		\n"		\
						"cp0.w	W9				\n" 	\
						"bra	NZ, ERROR_TEST2 \n"		\
						"sub	#0x010a, W10	\n"		\
						"cp0.w	W10				\n" 	\
						"bra	NZ, ERROR_TEST2 \n"		\
						"sub	#0x010b, W11	\n"		\
						"cp0.w	W11				\n" 	\
						"bra	NZ, ERROR_TEST2 \n"		\
						"sub	#0x010c, W12	\n"		\
						"cp0.w	W12				\n" 	\
						"bra	NZ, ERROR_TEST2 \n"		\
						"sub	#0x010d, W13	\n"		\
						"cp0.w	W13				\n" 	\
						"bra	NZ, ERROR_TEST2 \n"		\
						"sub	#0x010e, W14	\n"		\
						"cp0.w	W14				\n" 	\
						"bra	NZ, ERROR_TEST2 \n"		\
						"bra	NO_ERROR2		\n" 	\
						"ERROR_TEST2:			\n"		\
						"mov.w	#1, W0			\n"		\
						"mov.w	W0, _usErrorDetected\n"	\
						"NO_ERROR2:				\n" );
	}
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
	/* Schedule the co-routines from within the idle task hook. */
	vCoRoutineSchedule();
}
/*-----------------------------------------------------------*/
