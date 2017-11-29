/*
 * FreeRTOS Kernel V10.0.0
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. If you wish to use our Amazon
 * FreeRTOS name, please do so in a fair use way that does not cause confusion.
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
	NOTE : Tasks run in system mode and the scheduler runs in Supervisor mode.
	The processor MUST be in supervisor mode when vTaskStartScheduler is
	called.  The demo applications included in the FreeRTOS.org download switch
	to supervisor mode prior to main being called.  If you are not using one of
	these demo application projects then ensure Supervisor mode is used.
*/


/*
 * Creates all the demo application tasks, then starts the scheduler.  The WEB
 * documentation provides more details of the demo application tasks.
 *
 * Main.c also creates a task called "Check".  This only executes every three
 * seconds but has the highest priority so is guaranteed to get processor time.
 * Its main function is to check that all the other tasks are still operational.
 * Each task (other than the "flash" tasks) maintains a unique count that is
 * incremented each time the task successfully completes its function.  Should
 * any error occur within such a task the count is permanently halted.  The
 * check task inspects the count of each task to ensure it has changed since
 * the last time the check task executed.  If all the count variables have
 * changed all the tasks are still executing error free, and the check task
 * toggles the onboard LED.  Should any task contain an error at any time
 * the LED toggle rate will change from 3 seconds to 500ms.
 *
 * To check the operation of the memory allocator the check task also
 * dynamically creates a task before delaying, and deletes it again when it
 * wakes.  If memory cannot be allocated for the new task the call to xTaskCreate
 * will fail and an error is signalled.  The dynamically created task itself
 * allocates and frees memory just to give the allocator a bit more exercise.
 *
 */

/* Standard includes. */
#include <stdlib.h>
#include <string.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo application includes. */
#include "partest.h"
#include "flash.h"
#include "integer.h"
#include "PollQ.h"
#include "comtest2.h"
#include "semtest.h"
#include "flop.h"
#include "dynamic.h"
#include "BlockQ.h"
#include "serial.h"

/* Hardware specific definitions. */
#include "aic.h"
#include "ebi.h"

/*-----------------------------------------------------------*/

/* Constants for the ComTest tasks. */
#define mainCOM_TEST_BAUD_RATE	( ( unsigned long ) 115200 )
#define mainCOM_TEST_LED		( 5 )

/* Priorities for the demo application tasks. */
#define mainLED_TASK_PRIORITY		( tskIDLE_PRIORITY + 3 )
#define mainCOM_TEST_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainQUEUE_POLL_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainCHECK_TASK_PRIORITY		( tskIDLE_PRIORITY + 4 )
#define mainSEM_TEST_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY		( tskIDLE_PRIORITY + 2 )

/* The rate at which the on board LED will toggle when there is/is not an
error. */
#define mainNO_ERROR_FLASH_PERIOD	( ( TickType_t ) 3000 / portTICK_PERIOD_MS  )
#define mainERROR_FLASH_PERIOD		( ( TickType_t ) 500 / portTICK_PERIOD_MS  )
#define mainON_BOARD_LED_BIT		( ( unsigned long ) 7 )

/* Constants used by the vMemCheckTask() task. */
#define mainCOUNT_INITIAL_VALUE		( ( unsigned long ) 0 )
#define mainNO_TASK					( 0 )

/* The size of the memory blocks allocated by the vMemCheckTask() task. */
#define mainMEM_CHECK_SIZE_1		( ( size_t ) 51 )
#define mainMEM_CHECK_SIZE_2		( ( size_t ) 52 )
#define mainMEM_CHECK_SIZE_3		( ( size_t ) 151 )

#define MAX_WAIT_STATES  8
static const unsigned long ululCSRWaitValues[ MAX_WAIT_STATES + 1 ] =
{
	WaitState1,/* There is no "zero wait state" value, so use one wait state */
	WaitState1,
	WaitState2,
	WaitState3,
	WaitState4,
	WaitState5,
	WaitState6,
	WaitState7,
	WaitState8
};
/*-----------------------------------------------------------*/

/*
 * Checks that all the demo application tasks are still executing without error
 * - as described at the top of the file.
 */
static long prvCheckOtherTasksAreStillRunning( unsigned long ulMemCheckTaskCount );

/*
 * The task that executes at the highest priority and calls
 * prvCheckOtherTasksAreStillRunning().  See the description at the top
 * of the file.
 */
static void vErrorChecks( void *pvParameters );

/*
 * Dynamically created and deleted during each cycle of the vErrorChecks()
 * task.  This is done to check the operation of the memory allocator.
 * See the top of vErrorChecks for more details.
 */
static void vMemCheckTask( void *pvParameters );

/*
 * Configure the processor for use with the Olimex demo board.  This includes
 * setup for the I/O, system clock, and access timings.
 */
static void prvSetupHardware( void );

/*-----------------------------------------------------------*/

/*
 * Starts all the other tasks, then starts the scheduler.
 */
int main( void )
{
	/* Setup the hardware for use with the Olimex demo board. */
	prvSetupHardware();

	/* Start the demo/test application tasks. */
	vStartIntegerMathTasks( tskIDLE_PRIORITY );
	vAltStartComTestTasks( mainCOM_TEST_PRIORITY, mainCOM_TEST_BAUD_RATE, mainCOM_TEST_LED );
	vStartLEDFlashTasks( mainLED_TASK_PRIORITY );
	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
	vStartMathTasks( tskIDLE_PRIORITY );
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
	vStartDynamicPriorityTasks();
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );

	/* Start the check task - which is defined in this file. */
	xTaskCreate( vErrorChecks, "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

	/* Now all the tasks have been started - start the scheduler.

	NOTE : Tasks run in system mode and the scheduler runs in Supervisor mode.
	The processor MUST be in supervisor mode when vTaskStartScheduler is
	called.  The demo applications included in the FreeRTOS.org download switch
	to supervisor mode prior to main being called.  If you are not using one of
	these demo application projects then ensure Supervisor mode is used here. */
	vTaskStartScheduler();

	/* Should never reach here! */
	return 0;
}
/*-----------------------------------------------------------*/

static void vErrorChecks( void *pvParameters )
{
TickType_t xDelayPeriod = mainNO_ERROR_FLASH_PERIOD;
unsigned long ulMemCheckTaskRunningCount;
TaskHandle_t xCreatedTask;

	/* Just to stop compiler warnings. */
	( void ) pvParameters;

	/* Cycle for ever, delaying then checking all the other tasks are still
	operating without error.  If an error is detected then the delay period
	is decreased from mainNO_ERROR_FLASH_PERIOD to mainERROR_FLASH_PERIOD so
	the on board LED flash rate will increase.

	In addition to the standard tests the memory allocator is tested through
	the dynamic creation and deletion of a task each cycle.  Each time the
	task is created memory must be allocated for its stack.  When the task is
	deleted this memory is returned to the heap.  If the task cannot be created
	then it is likely that the memory allocation failed. */

	for( ;; )
	{
		/* Reset xCreatedTask.  This is modified by the task about to be
		created so we can tell if it is executing correctly or not. */
		xCreatedTask = mainNO_TASK;

		/* Dynamically create a task - passing ulMemCheckTaskRunningCount as a
		parameter. */
		ulMemCheckTaskRunningCount = mainCOUNT_INITIAL_VALUE;
		if( xTaskCreate( vMemCheckTask, "MEM_CHECK", configMINIMAL_STACK_SIZE, ( void * ) &ulMemCheckTaskRunningCount, tskIDLE_PRIORITY, &xCreatedTask ) != pdPASS )
		{
			/* Could not create the task - we have probably run out of heap. */
			xDelayPeriod = mainERROR_FLASH_PERIOD;
		}

		/* Delay until it is time to execute again. */
		vTaskDelay( xDelayPeriod );

		/* Delete the dynamically created task. */
		if( xCreatedTask != mainNO_TASK )
		{
			vTaskDelete( xCreatedTask );
		}

		/* Check all the standard demo application tasks are executing without
		error.  ulMemCheckTaskRunningCount is checked to ensure it was
		modified by the task just deleted. */
		if( prvCheckOtherTasksAreStillRunning( ulMemCheckTaskRunningCount ) != pdPASS )
		{
			/* An error has been detected in one of the tasks - flash faster. */
			xDelayPeriod = mainERROR_FLASH_PERIOD;
		}

		/* The toggle rate of the LED depends on how long this task delays for.
		An error reduces the delay period and so increases the toggle rate. */
		vParTestToggleLED( mainON_BOARD_LED_BIT );
	}
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
long lCount;

	#ifdef RUN_FROM_ROM
	{
	portFLOAT nsecsPerClockTick;
	long lNumWaitStates;
	unsigned long ulCSRWaitValue;

		/* We are compiling to run from ROM (either on-chip or off-chip flash).
		Leave the RAM/flash mapped the way they are on reset
		(flash @ 0x00000000, RAM @ 0x00300000), and set up the
		proper flash wait states (starts out at the maximum number
		of wait states on reset, so we should be able to reduce it).
		Most of this code will probably get removed by the compiler
		if optimization is enabled, since these calculations are
		based on constants.  But the compiler should still produce
		a correct wait state register value. */
		nsecsPerClockTick = ( portFLOAT ) 1000000000 / configCPU_CLOCK_HZ;
		lNumWaitStates = ( long )( ( configFLASH_SPEED_NSEC / nsecsPerClockTick ) + 0.5 ) - 1;

		if( lNumWaitStates < 0 )
		{
			lNumWaitStates = 0;
		}

		if( lNumWaitStates > MAX_WAIT_STATES )
		{
			lNumWaitStates = MAX_WAIT_STATES;
		}

		ulCSRWaitValue = ululCSRWaitValues[ lNumWaitStates ];
		ulCSRWaitValue = WaitState5;

		AT91C_BASE_EBI->EBI_CSR[ 0 ] = ulCSRWaitValue | DataBus16 | WaitStateEnable
									   | PageSize1M | tDF_0cycle
									   | ByteWriteAccessType | CSEnable
									   | 0x00000000 /* Base Address */;
	}
	#else  /* else we are compiling to run from on-chip RAM */
	{
		/* If compiling to run from RAM, we expect the on-chip RAM to already
		be mapped at 0x00000000.  This is typically done with an initialization
		script for the JTAG emulator you are using to download and run the
		demo application. So there is nothing to do here in this case. */
	}
	#endif

	/* Disable all interrupts at the AIC level initially... */
	AT91C_BASE_AIC->AIC_IDCR = 0xFFFFFFFF;

	/* Set all SVR and SMR entries to default values (start with a clean slate)... */
	for( lCount = 0; lCount < 32; lCount++ )
	{
		AT91C_BASE_AIC->AIC_SVR[ lCount ] = (unsigned long) 0;
		AT91C_BASE_AIC->AIC_SMR[ lCount ] = AIC_SRCTYPE_INT_EDGE_TRIGGERED;
	}

	/* Disable clocks to all peripherals initially... */
	AT91C_BASE_PS->PS_PCDR = 0xFFFFFFFF;

	/* Clear all interrupts at the AIC level initially... */
	AT91C_BASE_AIC->AIC_ICCR = 0xFFFFFFFF;

	/* Perform 8 "End Of Interrupt" cmds to make sure AIC will not Lock out
	nIRQ */
	for( lCount = 0; lCount < 8; lCount++ )
	{
		AT91C_BASE_AIC->AIC_EOICR = 0;
	}

	/* Initialise LED outputs. */
	vParTestInitialise();
}
/*-----------------------------------------------------------*/

static long prvCheckOtherTasksAreStillRunning( unsigned long ulMemCheckTaskCount )
{
long lReturn = ( long ) pdPASS;

	/* Check all the demo tasks (other than the flash tasks) to ensure
	that they are all still running, and that none of them have detected
	an error. */

	if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
	{
		lReturn = ( long ) pdFAIL;
	}

	if( xAreComTestTasksStillRunning() != pdTRUE )
	{
		lReturn = ( long ) pdFAIL;
	}

	if( xArePollingQueuesStillRunning() != pdTRUE )
	{
		lReturn = ( long ) pdFAIL;
	}

	if( xAreMathsTaskStillRunning() != pdTRUE )
	{
		lReturn = ( long ) pdFAIL;
	}

	if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	{
		lReturn = ( long ) pdFAIL;
	}

	if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
	{
		lReturn = ( long ) pdFAIL;
	}

	if( xAreBlockingQueuesStillRunning() != pdTRUE )
	{
		lReturn = ( long ) pdFAIL;
	}

	if( ulMemCheckTaskCount == mainCOUNT_INITIAL_VALUE )
	{
		/* The vMemCheckTask did not increment the counter - it must
		have failed. */
		lReturn = ( long ) pdFAIL;
	}

	return lReturn;
}
/*-----------------------------------------------------------*/

static void vMemCheckTask( void *pvParameters )
{
unsigned long *pulMemCheckTaskRunningCounter;
void *pvMem1, *pvMem2, *pvMem3;
static long lErrorOccurred = pdFALSE;

	/* This task is dynamically created then deleted during each cycle of the
	vErrorChecks task to check the operation of the memory allocator.  Each time
	the task is created memory is allocated for the stack and TCB.  Each time
	the task is deleted this memory is returned to the heap.  This task itself
	exercises the allocator by allocating and freeing blocks.

	The task executes at the idle priority so does not require a delay.

	pulMemCheckTaskRunningCounter is incremented each cycle to indicate to the
	vErrorChecks() task that this task is still executing without error. */

	pulMemCheckTaskRunningCounter = ( unsigned long * ) pvParameters;

	for( ;; )
	{
		if( lErrorOccurred == pdFALSE )
		{
			/* We have never seen an error so increment the counter. */
			( *pulMemCheckTaskRunningCounter )++;
		}
		else
		{
			/* There has been an error so reset the counter so the check task
			can tell that an error occurred. */
			*pulMemCheckTaskRunningCounter = mainCOUNT_INITIAL_VALUE;
		}

		/* Allocate some memory - just to give the allocator some extra
		exercise.  This has to be in a critical section to ensure the
		task does not get deleted while it has memory allocated. */
		vTaskSuspendAll();
		{
			pvMem1 = pvPortMalloc( mainMEM_CHECK_SIZE_1 );
			if( pvMem1 == NULL )
			{
				lErrorOccurred = pdTRUE;
			}
			else
			{
				memset( pvMem1, 0xaa, mainMEM_CHECK_SIZE_1 );
				vPortFree( pvMem1 );
			}
		}
		xTaskResumeAll();

		/* Again - with a different size block. */
		vTaskSuspendAll();
		{
			pvMem2 = pvPortMalloc( mainMEM_CHECK_SIZE_2 );
			if( pvMem2 == NULL )
			{
				lErrorOccurred = pdTRUE;
			}
			else
			{
				memset( pvMem2, 0xaa, mainMEM_CHECK_SIZE_2 );
				vPortFree( pvMem2 );
			}
		}
		xTaskResumeAll();

		/* Again - with a different size block. */
		vTaskSuspendAll();
		{
			pvMem3 = pvPortMalloc( mainMEM_CHECK_SIZE_3 );
			if( pvMem3 == NULL )
			{
				lErrorOccurred = pdTRUE;
			}
			else
			{
				memset( pvMem3, 0xaa, mainMEM_CHECK_SIZE_3 );
				vPortFree( pvMem3 );
			}
		}
		xTaskResumeAll();
	}
}

