/*
	FreeRTOS.org V5.1.1 - Copyright (C) 2003-2008 Richard Barry.

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
    * SAVE TIME AND MONEY!  We can port FreeRTOS.org to your own hardware,    *
    * and even write all or part of your application on your behalf.          *
    * See http://www.OpenRTOS.com for details of the services we provide to   *
    * expedite your project.                                                  *
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
#define mainCOM_TEST_BAUD_RATE	( ( unsigned portLONG ) 115200 )
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
#define mainNO_ERROR_FLASH_PERIOD	( ( portTickType ) 3000 / portTICK_RATE_MS  )
#define mainERROR_FLASH_PERIOD		( ( portTickType ) 500 / portTICK_RATE_MS  )
#define mainON_BOARD_LED_BIT		( ( unsigned portLONG ) 7 )

/* Constants used by the vMemCheckTask() task. */
#define mainCOUNT_INITIAL_VALUE		( ( unsigned portLONG ) 0 )
#define mainNO_TASK					( 0 )

/* The size of the memory blocks allocated by the vMemCheckTask() task. */
#define mainMEM_CHECK_SIZE_1		( ( size_t ) 51 )
#define mainMEM_CHECK_SIZE_2		( ( size_t ) 52 )
#define mainMEM_CHECK_SIZE_3		( ( size_t ) 151 )

#define MAX_WAIT_STATES  8
static const unsigned portLONG ululCSRWaitValues[ MAX_WAIT_STATES + 1 ] =
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
static portLONG prvCheckOtherTasksAreStillRunning( unsigned portLONG ulMemCheckTaskCount );

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
	xTaskCreate( vErrorChecks, ( signed portCHAR * ) "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

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
portTickType xDelayPeriod = mainNO_ERROR_FLASH_PERIOD;
unsigned portLONG ulMemCheckTaskRunningCount;
xTaskHandle xCreatedTask;

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
		if( xTaskCreate( vMemCheckTask, ( signed portCHAR * ) "MEM_CHECK", configMINIMAL_STACK_SIZE, ( void * ) &ulMemCheckTaskRunningCount, tskIDLE_PRIORITY, &xCreatedTask ) != pdPASS )
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
portLONG lCount;

	#ifdef RUN_FROM_ROM
	{
	portFLOAT nsecsPerClockTick;
	portLONG lNumWaitStates;
	unsigned portLONG ulCSRWaitValue;

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
		lNumWaitStates = ( portLONG )( ( configFLASH_SPEED_NSEC / nsecsPerClockTick ) + 0.5 ) - 1;

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

static portLONG prvCheckOtherTasksAreStillRunning( unsigned portLONG ulMemCheckTaskCount )
{
portLONG lReturn = ( portLONG ) pdPASS;

	/* Check all the demo tasks (other than the flash tasks) to ensure
	that they are all still running, and that none of them have detected
	an error. */

	if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
	{
		lReturn = ( portLONG ) pdFAIL;
	}

	if( xAreComTestTasksStillRunning() != pdTRUE )
	{
		lReturn = ( portLONG ) pdFAIL;
	}

	if( xArePollingQueuesStillRunning() != pdTRUE )
	{
		lReturn = ( portLONG ) pdFAIL;
	}

	if( xAreMathsTaskStillRunning() != pdTRUE )
	{
		lReturn = ( portLONG ) pdFAIL;
	}

	if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	{
		lReturn = ( portLONG ) pdFAIL;
	}

	if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
	{
		lReturn = ( portLONG ) pdFAIL;
	}

	if( xAreBlockingQueuesStillRunning() != pdTRUE )
	{
		lReturn = ( portLONG ) pdFAIL;
	}

	if( ulMemCheckTaskCount == mainCOUNT_INITIAL_VALUE )
	{
		/* The vMemCheckTask did not increment the counter - it must
		have failed. */
		lReturn = ( portLONG ) pdFAIL;
	}

	return lReturn;
}
/*-----------------------------------------------------------*/

static void vMemCheckTask( void *pvParameters )
{
unsigned portLONG *pulMemCheckTaskRunningCounter;
void *pvMem1, *pvMem2, *pvMem3;
static portLONG lErrorOccurred = pdFALSE;

	/* This task is dynamically created then deleted during each cycle of the
	vErrorChecks task to check the operation of the memory allocator.  Each time
	the task is created memory is allocated for the stack and TCB.  Each time
	the task is deleted this memory is returned to the heap.  This task itself
	exercises the allocator by allocating and freeing blocks. 
	
	The task executes at the idle priority so does not require a delay. 
	
	pulMemCheckTaskRunningCounter is incremented each cycle to indicate to the
	vErrorChecks() task that this task is still executing without error. */

	pulMemCheckTaskRunningCounter = ( unsigned portLONG * ) pvParameters;

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

