/*
    FreeRTOS V8.0.0 - Copyright (C) 2014 Real Time Engineers Ltd. 
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
 * Creates all the demo application tasks, then starts the scheduler.  The WEB
 * documentation provides more details of the standard demo application tasks,
 * which provide no particular functionality but do provide a good example of
 * how to use the FreeRTOS API.  In addition to the standard demo tasks, the 
 * following tasks and tests are defined and/or created within this file:
 *
 * Webserver ("uIP") task - This serves a number of dynamically generated WEB
 * pages to a standard WEB browser.  The IP and MAC addresses are configured by
 * constants defined at the bottom of FreeRTOSConfig.h.  Use either a standard
 * Ethernet cable to connect through a hug, or a cross over (point to point)
 * cable to connect directly.  Ensure the IP address used is compatible with the
 * IP address of the machine running the browser - the easiest way to achieve
 * this is to ensure the first three octets of the IP addresses are the same.
 *
 * "Reg test" tasks - These fill the registers with known values, then check
 * that each register still contains its expected value.  Each task uses
 * different values.  The tasks run with very low priority so get preempted very
 * frequently.  A register containing an unexpected value is indicative of an
 * error in the context switching mechanism.  Both standard and floating point
 * registers are checked.  The nature of the reg test tasks necessitates that
 * they are written in assembly code.  They are defined in regtest.src.
 *
 * "math" tasks - These are a set of 8 tasks that perform various double
 * precision floating point calculations in order to check that the tasks 
 * floating point registers are being correctly saved and restored during
 * context switches.  The math tasks are defined in flop.c.
 *
 * "Check" task - This only executes every five seconds but has a high priority
 * to ensure it gets processor time.  Its main function is to check that all the
 * standard demo tasks are still operational.  While no errors have been
 * discovered the check task will toggle an LED every 5 seconds - the toggle
 * rate increasing to 200ms being a visual indication that at least one task has
 * reported unexpected behaviour.
 *
 * *NOTE 1* If LED5 is toggling every 5 seconds then all the demo application
 * tasks are executing as expected and no errors have been reported in any 
 * tasks.  The toggle rate increasing to 200ms indicates that at least one task
 * has reported unexpected behaviour.
 * 
 * *NOTE 2* This file and flop.c both demonstrate the use of 
 * xPortUsesFloatingPoint() which informs the kernel that a task should maintain
 * a floating point context.
 *
 * *NOTE 3* vApplicationSetupTimerInterrupt() is called by the kernel to let
 * the application set up a timer to generate the tick interrupt.  In this
 * example a compare match timer is used for this purpose.  
 * vApplicationTickHook() is used to clear the timer interrupt and relies on
 * configUSE_TICK_HOOK being set to 1 in FreeRTOSConfig.h.
 *
 * *NOTE 4* The traceTASK_SWITCHED_IN and traceTASK_SWITCHED_OUT trace hooks
 * are used to save and restore the floating point context respectively for
 * those tasks that require it (those for which xPortUsesFloatingPoint() has
 * been called).
 * 
 * *NOTE 5* Any interrupt that can cause a context switch requires an asm 
 * wrapper and must be assigned an interrupt priority of 
 * portKERNEL_INTERRUPT_PRIORITY.
 *
 * *NOTE 6* vSetupClockForRunTimeStats() is called by the kernel (via the 
 * portCONFIGURE_TIMER_FOR_RUN_TIME_STATS()) macro to configure an MTU channel
 * to produce a time base that is used to log how much processor time each task
 * is consuming.  The MTU is used to generate a high(ish) frequency interrupt,
 * and so also provides an example of how interrupts that don't make use of the
 * FreeRTOS kernel can be assigned a priority above any priority used by the
 * kernel itself.
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
#include "flop.h"

/* Constants required to configure the hardware. */
#define mainFRQCR_VALUE 					( 0x0303 )	/* Input = 12.5MHz, I Clock = 200MHz, B Clock = 50MHz, P Clock = 50MHz */

/* Task priorities. */
#define mainQUEUE_POLL_PRIORITY				( tskIDLE_PRIORITY + 1 )
#define mainCHECK_TASK_PRIORITY				( tskIDLE_PRIORITY + 3 )
#define mainSEM_TEST_PRIORITY				( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainCREATOR_TASK_PRIORITY           ( tskIDLE_PRIORITY + 3 )
#define mainFLASH_TASK_PRIORITY				( tskIDLE_PRIORITY + 1 )
#define mainuIP_TASK_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainINTEGER_TASK_PRIORITY           ( tskIDLE_PRIORITY )
#define mainGEN_QUEUE_TASK_PRIORITY			( tskIDLE_PRIORITY )
#define mainFLOP_TASK_PRIORITY				( tskIDLE_PRIORITY )

/* The WEB server uses string handling functions, which in turn use a bit more
stack than most of the other tasks. */
#define mainuIP_STACK_SIZE					( configMINIMAL_STACK_SIZE * 3 )

/* The LED toggled by the check task. */
#define mainCHECK_LED						( 5 )

/* The rate at which mainCHECK_LED will toggle when all the tasks are running
without error. */
#define mainNO_ERROR_CYCLE_TIME				( 5000 / portTICK_PERIOD_MS )

/* The rate at which mainCHECK_LED will toggle when an error has been reported
by at least one task. */
#define mainERROR_CYCLE_TIME				( 200 / portTICK_PERIOD_MS )

/*
 * vApplicationMallocFailedHook() will only be called if
 * configUSE_MALLOC_FAILED_HOOK is set to 1 in FreeRTOSConfig.h.  It is a hook
 * function that will execute if a call to pvPortMalloc() fails.
 * pvPortMalloc() is called internally by the kernel whenever a task, queue or
 * semaphore is created.  It is also called by various parts of the demo
 * application.  
 */
void vApplicationMallocFailedHook( void );

/*
 * vApplicationIdleHook() will only be called if configUSE_IDLE_HOOK is set to 1
 * in FreeRTOSConfig.h.  It is a hook function that is called on each iteration
 * of the idle task.  It is essential that code added to this hook function
 * never attempts to block in any way (for example, call xQueueReceive() with
 * a block time specified).  If the application makes use of the vTaskDelete()
 * API function (as this demo application does) then it is also important that
 * vApplicationIdleHook() is permitted to return to its calling function because
 * it is the responsibility of the idle task to clean up memory allocated by the
 * kernel to any task that has since been deleted.
 */
void vApplicationIdleHook( void );

/*
 * Just sets up clocks, ports, etc. used by the demo application.
 */
static void prvSetupHardware( void );

/*
 * The check task as described at the top of this file.
 */
static void prvCheckTask( void *pvParameters );

/*
 * The reg test tasks as described at the top of this file.
 */
extern void vRegTest1Task( void *pvParameters );
extern void vRegTest2Task( void *pvParameters );

/*
 * Contains the implementation of the WEB server.
 */
extern void vuIP_Task( void *pvParameters );

/*
 * The interrupt handler for the MTU - which is used to maintain the time base
 * used by the run time stats.
 */
#pragma interrupt MTU_Match
void MTU_Match( void );

/*-----------------------------------------------------------*/

/* Variables that are incremented on each iteration of the reg test tasks - 
provided the tasks have not reported any errors.  The check task inspects these
variables to ensure they are still incrementing as expected. */
volatile unsigned long ulRegTest1CycleCount = 0UL, ulRegTest2CycleCount = 0UL;

/* The status message that is displayed at the bottom of the "task stats" WEB
page, which is served by the uIP task. */
const char *pcStatusMessage = "All tasks executing without error.";

/* The time use for the run time stats. */
unsigned long ulRunTime = 0UL;

/*-----------------------------------------------------------*/

/*
 * Creates the majority of the demo application tasks before starting the
 * scheduler.
 */
void main(void)
{
TaskHandle_t xCreatedTask;

	prvSetupHardware();

	/* Start the reg test tasks which test the context switching mechanism. */
	xTaskCreate( vRegTest1Task, "RegTst1", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, &xCreatedTask );
	xPortUsesFloatingPoint( xCreatedTask );
	
	xTaskCreate( vRegTest2Task, "RegTst2", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, &xCreatedTask );
	xPortUsesFloatingPoint( xCreatedTask );

	xTaskCreate( vuIP_Task, "uIP", mainuIP_STACK_SIZE, NULL, mainuIP_TASK_PRIORITY, NULL );

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
	
	/* Start the math tasks as described at the top of this file. */
	vStartMathTasks( mainFLOP_TASK_PRIORITY );

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
TickType_t xNextWakeTime, xCycleFrequency = mainNO_ERROR_CYCLE_TIME;
unsigned long ulLastRegTest1CycleCount = 0UL, ulLastRegTest2CycleCount = 0UL;

	/* Just to remove compiler warning. */
	( void ) pvParameter;

	/* Initialise xNextWakeTime - this only needs to be done once. */
	xNextWakeTime = xTaskGetTickCount();

	for( ;; )
	{
		/* Place this task in the blocked state until it is time to run again. */
		vTaskDelayUntil( &xNextWakeTime, xCycleFrequency );
		
		/* Inspect all the other tasks to ensure none have experienced any errors. */
		if( xAreGenericQueueTasksStillRunning() != pdTRUE )
		{
			/* Increase the rate at which this task cycles, which will increase the
			rate at which mainCHECK_LED flashes to give visual feedback that an error
			has occurred. */
			xCycleFrequency = mainERROR_CYCLE_TIME;
			pcStatusMessage = "Error in GenQ test.";
		}
		else if( xAreQueuePeekTasksStillRunning() != pdTRUE )
		{
			xCycleFrequency = mainERROR_CYCLE_TIME;
			pcStatusMessage = "Error in Queue Peek test.";
		}
		else if( xAreBlockingQueuesStillRunning() != pdTRUE )
		{
			xCycleFrequency = mainERROR_CYCLE_TIME;
			pcStatusMessage = "Error in Blocking Queue test.";
		}
		else if( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
		{
			xCycleFrequency = mainERROR_CYCLE_TIME;
			pcStatusMessage = "Error in BlockTim test.";
		}
	    else if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	    {
	        xCycleFrequency = mainERROR_CYCLE_TIME;
			pcStatusMessage = "Error in Semaphore test.";
	    }
	    else if( xArePollingQueuesStillRunning() != pdTRUE )
	    {
	        xCycleFrequency = mainERROR_CYCLE_TIME;
			pcStatusMessage = "Error in Polling Queue test.";
	    }
	    else if( xIsCreateTaskStillRunning() != pdTRUE )
	    {
	        xCycleFrequency = mainERROR_CYCLE_TIME;
			pcStatusMessage = "Error in Create test.";
	    }
	    else if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
	    {
	        xCycleFrequency = mainERROR_CYCLE_TIME;
			pcStatusMessage = "Error in integer Math test.";
	    }
	    else if( xAreRecursiveMutexTasksStillRunning() != pdTRUE )
	    {
	    	xCycleFrequency = mainERROR_CYCLE_TIME;
			pcStatusMessage = "Error in recursive mutex test.";
	    }
		else if( xAreMathsTaskStillRunning() != pdTRUE )
		{
			xCycleFrequency = mainERROR_CYCLE_TIME;
			pcStatusMessage = "Error in floating point Math test.";
		}

		/* Check the reg test tasks are still cycling.  They will stop incrementing
		their loop counters if they encounter an error. */
		if( ulRegTest1CycleCount == ulLastRegTest1CycleCount )
		{
			xCycleFrequency = mainERROR_CYCLE_TIME;
			pcStatusMessage = "Error in RegTest.";
		}

		if( ulRegTest2CycleCount == ulLastRegTest2CycleCount )
		{
			xCycleFrequency = mainERROR_CYCLE_TIME;
			pcStatusMessage = "Error in RegTest.";
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

void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName )
{
	/* Just to remove compiler warnings.  This function will only actually
	get called if configCHECK_FOR_STACK_OVERFLOW is set to a non zero value.
	By default this demo does not use the stack overflow checking functionality
	as the SuperH will normally execute an exception if the stack overflows. */
	( void ) pxTask;
	( void ) pcTaskName;
	
	taskDISABLE_INTERRUPTS();
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
peripheral (CMT). */
const unsigned long ulCompareMatch = ( configPERIPHERAL_CLOCK_HZ / ( configTICK_RATE_HZ * 32 ) ) + 1;

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
	INTC.IPR08.BIT._CMT0 = portKERNEL_INTERRUPT_PRIORITY;
	
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
	/* Clear the tick inerrupt.  This is called from an interrupt context. */
	CMT0.CMCSR.BIT.CMF = 0;
}
/*-----------------------------------------------------------*/

void vSetupClockForRunTimeStats( void )
{
	/* Configure an MTU channel to generate a periodic interrupt that is used
	as the run time stats time base.  The run time stats keep a track of how
	much processing time each task is using. */

	/* Turn the MTU2 on. */
	STB.CR3.BIT._MTU2 = 0;
		
	/* Clear counter on compare match A. */
	MTU20.TCR.BIT.CCLR = 0x01;
	
	/* Compare match value to give very approximately 10 interrupts per 
	millisecond. */
	MTU20.TGRA = 5000;
	
	/* Ensure the interrupt is clear. */
	MTU20.TSR.BIT.TGFA = 0;
		
	/* Enable the compare match interrupt. */
	MTU20.TIER.BIT.TGIEA = 0x01;	
	
	/* Set the interrupt priority. */
	INTC.IPR09.BIT._MTU20G = portKERNEL_INTERRUPT_PRIORITY + 1;
	
	/* Start the count. */
	MTU2.TSTR.BIT.CST0 = 1;
}
/*-----------------------------------------------------------*/

void MTU_Match( void )
{
volatile unsigned char ucStatus;

	/* Increment the run time stats time base. */
	ulRunTime++;

	/* Clear the interrupt. */
	ucStatus = MTU20.TSR.BYTE;
	MTU20.TSR.BIT.TGFA = 0;
}
/*-----------------------------------------------------------*/

char *pcGetTaskStatusMessage( void )
{
	/* Not bothered about a critical section here.  This just returns a string
	that is displaed on the "Task Stats" WEB page served by this demo. */
	return pcStatusMessage;
}
/*-----------------------------------------------------------*/
