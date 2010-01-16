/*
    FreeRTOS V6.0.2 - Copyright (C) 2009 Real Time Engineers Ltd.

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

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo application includes. */
#include "BlockQ.h"
#include "death.h"
#include "integer.h"
#include "blocktim.h"
#include "flash.h"
#include "partest.h"
#include "semtest.h"
#include "PollQ.h"
#include "GenQTest.h"
#include "QPeek.h"
#include "recmutex.h"

/* Constants required to configure the hardware. */
#define mainFRQCR_VALUE 					( 0x0303 )	/* Input = 12.5MHz, I Clock = 200MHz, B Clock = 50MHz, P Clock = 50MHz */

/* Task priorities. */
#define mainQUEUE_POLL_PRIORITY				( tskIDLE_PRIORITY + 1 )
#define mainCHECK_TASK_PRIORITY				( tskIDLE_PRIORITY + 3 )
#define mainSEM_TEST_PRIORITY				( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainCREATOR_TASK_PRIORITY           ( tskIDLE_PRIORITY + 3 )
#define mainFLASH_TASK_PRIORITY				( tskIDLE_PRIORITY + 1 )
#define mainINTEGER_TASK_PRIORITY           ( tskIDLE_PRIORITY )
#define mainGEN_QUEUE_TASK_PRIORITY			( tskIDLE_PRIORITY )

/* The LED toggle by the check task. */
#define mainCHECK_LED						( 5 )

/* The rate at which mainCHECK_LED will toggle when all the tasks are running
without error. */
#define mainNO_ERROR_CYCLE_TIME				( 5000 / portTICK_RATE_MS )

/* The rate at which mainCHECK_LED will toggle when an error has been reported
by at least one task. */
#define mainERROR_CYCLE_TIME				( 200 / portTICK_RATE_MS )

void vApplicationMallocFailedHook( void );
void vApplicationIdleHook( void );
static void prvSetupHardware( void );
static void prvCheckTask( void *pvParameters );

extern void vRegTest1Task( void *pvParameters );
extern void vRegTest2Task( void *pvParameters );

volatile unsigned long ulRegTest1CycleCount = 0UL, ulRegTest2CycleCount = 0UL;

/*-----------------------------------------------------------*/

void main(void)
{
	prvSetupHardware();

	/* Start the reg test tasks which test the context switching mechanism. */
	xTaskCreate( vRegTest1Task, "RegTest1", configMINIMAL_STACK_SIZE, ( void * ) 0x12345678UL, tskIDLE_PRIORITY, NULL );
	xTaskCreate( vRegTest2Task, "RegTest2", configMINIMAL_STACK_SIZE, ( void * ) 0x11223344UL, tskIDLE_PRIORITY, NULL );

	/* Start the check task as described at the top of this file. */
	xTaskCreate( prvCheckTask, "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

	/* Start the standard demo tasks.  These don't perform any particular useful
	functionality, other than to demonstrate the FreeRTOS API being used. */
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
	vCreateBlockTimeTasks();
    vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
    vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
    vStartIntegerMathTasks( mainINTEGER_TASK_PRIORITY );
    vStartGenericQueueTasks( mainGEN_QUEUE_TASK_PRIORITY );
	vStartLEDFlashTasks( mainFLASH_TASK_PRIORITY );
    vStartQueuePeekTasks();
    vStartRecursiveMutexTasks();

	/* The suicide tasks must be created last as they need to know how many
	tasks were running prior to their creation in order to ascertain whether
	or not the correct/expected number of tasks are running at any given time. */
    vCreateSuicidalTasks( mainCREATOR_TASK_PRIORITY );

	/* Start the tasks running. */
	vTaskStartScheduler();

	/* Will only get here if there was insufficient heap memory to create the idle
    task.  Increase the configTOTAL_HEAP_SIZE setting in FreeRTOSConfig.h. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvCheckTask( void *pvParameter )
{
portTickType xNextWakeTime, xCycleFrequency = mainNO_ERROR_CYCLE_TIME;
unsigned long ulLastRegTest1CycleCount = 0UL, ulLastRegTest2CycleCount = 0UL;

	/* Initialise xNextWakeTime - this only needs to be done once. */
	xNextWakeTime = xTaskGetTickCount();

	for( ;; )
	{
		/* Place this task in the blocked state until it is time to run again. */
		vTaskDelayUntil( &xNextWakeTime, xCycleFrequency );
		
		/* Inspect all the other tasks to esnure none have experienced any errors. */
		if( xAreGenericQueueTasksStillRunning() != pdTRUE )
		{
			/* Increase the rate at which this task cycles, which will increase the
			rate at which mainCHECK_LED flashes to give visual feedback that an error
			has occurred. */
			xCycleFrequency = mainERROR_CYCLE_TIME;
		}
		else if( xAreQueuePeekTasksStillRunning() != pdTRUE )
		{
			xCycleFrequency = mainERROR_CYCLE_TIME;
		}
		else if( xAreBlockingQueuesStillRunning() != pdTRUE )
		{
			xCycleFrequency = mainERROR_CYCLE_TIME;
		}
		else if( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
		{
			xCycleFrequency = mainERROR_CYCLE_TIME;
		}
	    else if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	    {
	        xCycleFrequency = mainERROR_CYCLE_TIME;
	    }
	    else if( xArePollingQueuesStillRunning() != pdTRUE )
	    {
	        xCycleFrequency = mainERROR_CYCLE_TIME;
	    }
	    else if( xIsCreateTaskStillRunning() != pdTRUE )
	    {
	        xCycleFrequency = mainERROR_CYCLE_TIME;
	    }
	    else if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
	    {
	        xCycleFrequency = mainERROR_CYCLE_TIME;
	    }
	    else if( xAreRecursiveMutexTasksStillRunning() != pdTRUE )
	    {
	    	xCycleFrequency = mainERROR_CYCLE_TIME;
	    }

		/* Check the reg test tasks are still cycling.  They will stop incrementing
		their loop counters if they encounter an error. */
		if( ulRegTest1CycleCount == ulLastRegTest1CycleCount )
		{
			xCycleFrequency = mainERROR_CYCLE_TIME;
		}

		if( ulRegTest2CycleCount == ulLastRegTest2CycleCount )
		{
			xCycleFrequency = mainERROR_CYCLE_TIME;
		}
		
		ulLastRegTest1CycleCount = ulRegTest1CycleCount;
		ulLastRegTest2CycleCount = ulRegTest2CycleCount;
		
		/* Toggle the check LED to give an indication of the system status.  If the
		LED toggles every 5 seconds then everything is ok.  A faster toggle indicates
		an error. */
		vParTestToggleLED( mainCHECK_LED );
	}
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
	/* A call to vPortMalloc() failed, probably during the creation of a task,
	queue or semaphore.  Inspect pxCurrentTCB to find which task is currently
	executing. */
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
	/* Code can be added to the idle task here.  This function must *NOT* attempt
	to block.  Also, if the application uses the vTaskDelete() API function then
	this function must return regularly to ensure the idle task gets a chance to
	clean up the memory used by deleted tasks. */
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( xTaskHandle *pxTask, signed char *pcTaskName )
{
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
volatile unsigned long ul;

	/* Set the CPU and peripheral clocks. */
	CPG.FRQCR.WORD = mainFRQCR_VALUE;
	
	/* Wait for the clock to settle. */
	for( ul = 0; ul < 99; ul++ )
	{
		nop();
	}
	
	/* Initialise the ports used to toggle LEDs. */
	vParTestInitialise();
}
/*-----------------------------------------------------------*/

void vApplicationSetupTimerInterrupt( void )
{
/* The peripheral clock is divided by 32 before feeding the compare match
periphersl (CMT). */
unsigned long ulCompareMatch = ( configPERIPHERAL_CLOCK_HZ / ( configTICK_RATE_HZ * 32 ) ) + 1;

	/* Configure a timer to create the RTOS tick interrupt.  This example uses
	the compare match timer, but the multi function timer or possible even the
	watchdog timer could also be used.  Ensure vPortTickInterrupt() is installed
	as the interrupt handler for whichever peripheral is used. */
	
	/* Turn the CMT on. */
	STB.CR4.BIT._CMT = 0;
	
	/* Set the compare match value for the required tick frequency. */
	CMT0.CMCOR = ( unsigned short ) ulCompareMatch;
	
	/* Divide the peripheral clock by 32. */
	CMT0.CMCSR.BIT.CKS = 0x01;
	
	/* Set the CMT interrupt priority - the interrupt priority must be
	configKERNEL_INTERRUPT_PRIORITY no matter which peripheral is used to generate
	the tick interrupt. */
	INTC.IPR08.BIT._CMT0 = configKERNEL_INTERRUPT_PRIORITY;
	
	/* Clear the interrupt flag. */
	CMT0.CMCSR.BIT.CMF = 0;
	
	/* Enable the compare match interrupt. */
	CMT0.CMCSR.BIT.CMIE = 0x01;
	
	/* Start the timer. */
	CMT.CMSTR.BIT.STR0 = 0x01;
}
/*-----------------------------------------------------------*/

void vApplicationTickHook( void )
{
	CMT0.CMCSR.BIT.CMF = 0;
}
/*-----------------------------------------------------------*/

