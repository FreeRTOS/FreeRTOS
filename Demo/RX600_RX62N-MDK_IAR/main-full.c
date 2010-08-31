/*
    FreeRTOS V6.0.5 - Copyright (C) 2010 Real Time Engineers Ltd.

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
 * This project includes a lot of tasks and tests and is therefore complex.
 * If you would prefer a much simpler project to get started with then select
 * the 'Blinky' build configuration within the HEW IDE.
 *
 * Creates all the demo application tasks, then starts the scheduler.  The web
 * documentation provides more details of the standard demo application tasks,
 * which provide no particular functionality but do provide a good example of
 * how to use the FreeRTOS API.  The tasks defined in flop.c are included in the
 * set of standard demo tasks to ensure the floating point unit gets some
 * exercise.
 *
 * In addition to the standard demo tasks, the following tasks and tests are
 * defined and/or created within this file:
 *
 * "Reg test" tasks - These fill the registers with known values, then check
 * that each register still contains its expected value.  Each task uses
 * different values.  The tasks run with very low priority so get preempted
 * very frequently.  A check variable is incremented on each iteration of the
 * test loop.  A register containing an unexpected value is indicative of an
 * error in the context switching mechanism and will result in a branch to a
 * null loop - which in turn will prevent the check variable from incrementing
 * any further and allow the check task (described below) to determine that an
 * error has occurred.  The nature of the reg test tasks necessitates that they
 * are written in assembly code.
 *
 * "Check" task - This only executes every five seconds but has a high priority
 * to ensure it gets processor time.  Its main function is to check that all the
 * standard demo tasks are still operational.  While no errors have been
 * discovered the check task will toggle LED 5 every 5 seconds - the toggle
 * rate increasing to 200ms being a visual indication that at least one task has
 * reported unexpected behaviour.
 *
 * "High frequency timer test" - A high frequency periodic interrupt is
 * generated using a timer - the interrupt is assigned a priority above
 * configMAX_SYSCALL_INTERRUPT_PRIORITY so should not be effected by anything
 * the kernel is doing.  The interrupt service routine measures the number of
 * counts a separate timer performs between each interrupt to determine the
 * jitter in the interrupt timing.
 *
 * *NOTE 1* If LED5 is toggling every 5 seconds then all the demo application
 * tasks are executing as expected and no errors have been reported in any
 * tasks.  The toggle rate increasing to 200ms indicates that at least one task
 * has reported unexpected behaviour.
 *
 * *NOTE 2* vApplicationSetupTimerInterrupt() is called by the kernel to let
 * the application set up a timer to generate the tick interrupt.  In this
 * example a compare match timer is used for this purpose.
 *
 * *NOTE 3* The CPU must be in Supervisor mode when the scheduler is started.
 * The PowerON_Reset_PC() supplied in resetprg.c with this demo has
 * Change_PSW_PM_to_UserMode() commented out to ensure this is the case.
 *
 * *NOTE 4* The IntQueue common demo tasks test interrupt nesting and make use
 * of all the 8bit timers (as two cascaded 16bit units).
*/

/* Standard includes. */
#include "string.h"

/* Hardware specific includes. */
#include <iorx62n.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Standard demo includes. */
#include "partest.h"
#include "flash.h"
#include "IntQueue.h"
#include "BlockQ.h"
#include "death.h"
#include "integer.h"
#include "blocktim.h"
#include "semtest.h"
#include "PollQ.h"
#include "GenQTest.h"
#include "QPeek.h"
#include "recmutex.h"
#include "flop.h"

/* Values that are passed into the reg test tasks using the task parameter.  The
tasks check that the values are passed in correctly. */
#define mainREG_TEST_1_PARAMETER	( 0x12121212UL )
#define mainREG_TEST_2_PARAMETER	( 0x12345678UL )

/* Priorities at which the tasks are created. */
#define mainCHECK_TASK_PRIORITY		( configMAX_PRIORITIES - 1 )
#define mainQUEUE_POLL_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainSEM_TEST_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainCREATOR_TASK_PRIORITY   ( tskIDLE_PRIORITY + 3 )
#define mainFLASH_TASK_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainuIP_TASK_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainINTEGER_TASK_PRIORITY   ( tskIDLE_PRIORITY )
#define mainGEN_QUEUE_TASK_PRIORITY	( tskIDLE_PRIORITY )
#define mainFLOP_TASK_PRIORITY		( tskIDLE_PRIORITY )

/* The LED toggled by the check task. */
#define mainCHECK_LED				( 5 )

/* The rate at which mainCHECK_LED will toggle when all the tasks are running
without error.  Controlled by the check task as described at the top of this
file. */
#define mainNO_ERROR_CYCLE_TIME		( 5000 / portTICK_RATE_MS )

/* The rate at which mainCHECK_LED will toggle when an error has been reported
by at least one task.  Controlled by the check task as described at the top of
this file. */
#define mainERROR_CYCLE_TIME		( 200 / portTICK_RATE_MS )

/* The period of the peripheral clock in nano seconds.  This is used to calculate
the jitter time in nano seconds as part of the high frequency timer test.  The
clock driving the timer is divided by 8. */
#define mainNS_PER_CLOCK			( ( unsigned long ) ( ( 1.0 /  ( ( double ) configPERIPHERAL_CLOCK_HZ ) / 8.0 ) * 1000000000.0 ) )

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
 * vApplicationStackOverflowHook() will only be called if
 * configCHECK_FOR_STACK_OVERFLOW is set to a non-zero value.  The handle and
 * name of the offending task should be passed in the function parameters, but
 * it is possible that the stack overflow will have corrupted these - in which
 * case pxCurrentTCB can be inspected to find the same information.
 */
void vApplicationStackOverflowHook( xTaskHandle *pxTask, signed char *pcTaskName );

/*
 * The reg test tasks as described at the top of this file.
 */
static void prvRegTest1Task( void *pvParameters );
static void prvRegTest2Task( void *pvParameters );

/*
 * The actual implementation of the reg test functionality, which, because of
 * the direct register access, have to be in assembly.
 */
extern void prvRegTest1Implementation( void );
extern void prvRegTest2Implementation( void );


/*
 * The check task as described at the top of this file.
 */
static void prvCheckTask( void *pvParameters );

/* Variables that are incremented on each iteration of the reg test tasks -
provided the tasks have not reported any errors.  The check task inspects these
variables to ensure they are still incrementing as expected.  If a variable
stops incrementing then it is likely that its associate task has stalled. */
unsigned long ulRegTest1CycleCount = 0UL, ulRegTest2CycleCount = 0UL;

/*-----------------------------------------------------------*/

void main(void)
{
extern void HardwareSetup( void );

	/* Renesas provided CPU configuration routine.  The clocks are configured in
	here. */
	HardwareSetup();

	/* Start the reg test tasks which test the context switching mechanism. */
	xTaskCreate( prvRegTest1Task, "RegTst1", configMINIMAL_STACK_SIZE, ( void * ) mainREG_TEST_1_PARAMETER, tskIDLE_PRIORITY, NULL );
	xTaskCreate( prvRegTest2Task, "RegTst2", configMINIMAL_STACK_SIZE, ( void * ) mainREG_TEST_2_PARAMETER, tskIDLE_PRIORITY, NULL );

	/* Start the check task as described at the top of this file. */
	xTaskCreate( prvCheckTask, "Check", configMINIMAL_STACK_SIZE * 3, NULL, mainCHECK_TASK_PRIORITY, NULL );

	/* Create the standard demo tasks. */
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
	vCreateBlockTimeTasks();
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
	vStartIntegerMathTasks( mainINTEGER_TASK_PRIORITY );
	vStartGenericQueueTasks( mainGEN_QUEUE_TASK_PRIORITY );
	vStartLEDFlashTasks( mainFLASH_TASK_PRIORITY );
	vStartQueuePeekTasks();
	vStartRecursiveMutexTasks();
	vStartInterruptQueueTasks();
	vStartMathTasks( mainFLOP_TASK_PRIORITY );

	/* The suicide tasks must be created last as they need to know how many
	tasks were running prior to their creation in order to ascertain whether
	or not the correct/expected number of tasks are running at any given time. */
	vCreateSuicidalTasks( mainCREATOR_TASK_PRIORITY );

	/* Start the tasks running. */
	vTaskStartScheduler();

	/* If all is well we will never reach here as the scheduler will now be
	running.  If we do reach here then it is likely that there was insufficient
	heap available for the idle task to be created. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvCheckTask( void *pvParameters )
{
static volatile unsigned long ulLastRegTest1CycleCount = 0UL, ulLastRegTest2CycleCount = 0UL;
portTickType xNextWakeTime, xCycleFrequency = mainNO_ERROR_CYCLE_TIME;
extern void vSetupHighFrequencyTimer( void );
extern volatile unsigned short usMaxJitter;
volatile unsigned long ulActualJitter = 0;
static char cErrorText[ 100 ];

	/* If this is being executed then the kernel has been started.  Start the high
	frequency timer test as described at the top of this file.  This is only
	included in the optimised build configuration - otherwise it takes up too much
	CPU time. */
	#ifdef INCLUDE_HIGH_FREQUENCY_TIMER_TEST
		vSetupHighFrequencyTimer();
	#endif

	/* Initialise xNextWakeTime - this only needs to be done once. */
	xNextWakeTime = xTaskGetTickCount();

	for( ;; )
	{
		/* Place this task in the blocked state until it is time to run again. */
		vTaskDelayUntil( &xNextWakeTime, xCycleFrequency );

		/* Check the standard demo tasks are running without error. */
		if( xAreGenericQueueTasksStillRunning() != pdTRUE )
		{
			/* Increase the rate at which this task cycles, which will increase the
			rate at which mainCHECK_LED flashes to give visual feedback that an error
			has occurred. */
			xCycleFrequency = mainERROR_CYCLE_TIME;
			strcpy( cErrorText, "Error: GenQueue" );
		}
		else if( xAreQueuePeekTasksStillRunning() != pdTRUE )
		{
			xCycleFrequency = mainERROR_CYCLE_TIME;
			strcpy( cErrorText, "Error: QueuePeek" );
		}
		else if( xAreBlockingQueuesStillRunning() != pdTRUE )
		{
			xCycleFrequency = mainERROR_CYCLE_TIME;
			strcpy( cErrorText, "Error: BlockQueue" );
		}
		else if( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
		{
			xCycleFrequency = mainERROR_CYCLE_TIME;
			strcpy( cErrorText, "Error: BlockTime" );
		}
		else if( xAreSemaphoreTasksStillRunning() != pdTRUE )
		{
			xCycleFrequency = mainERROR_CYCLE_TIME;
			strcpy( cErrorText, "Error: SemTest" );
		}
		else if( xArePollingQueuesStillRunning() != pdTRUE )
		{
			xCycleFrequency = mainERROR_CYCLE_TIME;
			strcpy( cErrorText, "Error: PollQueue" );
		}
		else if( xIsCreateTaskStillRunning() != pdTRUE )
		{
			xCycleFrequency = mainERROR_CYCLE_TIME;
			strcpy( cErrorText, "Error: Death" );
		}
		else if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
		{
			xCycleFrequency = mainERROR_CYCLE_TIME;
			strcpy( cErrorText, "Error: IntMath" );
		}
		else if( xAreRecursiveMutexTasksStillRunning() != pdTRUE )
		{
			xCycleFrequency = mainERROR_CYCLE_TIME;
			strcpy( cErrorText, "Error: RecMutex" );
		}
		else if( xAreIntQueueTasksStillRunning() != pdPASS )
		{
			xCycleFrequency = mainERROR_CYCLE_TIME;
			strcpy( cErrorText, "Error: IntQueue" );
		}
		else if( xAreMathsTaskStillRunning() != pdPASS )
		{
			xCycleFrequency = mainERROR_CYCLE_TIME;
			strcpy( cErrorText, "Error: Flop" );
		}

		/* Check the reg test tasks are still cycling.  They will stop incrementing
		their loop counters if they encounter an error. */
		if( ulRegTest1CycleCount == ulLastRegTest1CycleCount )
		{
			xCycleFrequency = mainERROR_CYCLE_TIME;
			strcpy( cErrorText, "Error: RegTest1" );
		}

		if( ulRegTest2CycleCount == ulLastRegTest2CycleCount )
		{
			xCycleFrequency = mainERROR_CYCLE_TIME;
			strcpy( cErrorText, "Error: RegTest2" );
		}

		ulLastRegTest1CycleCount = ulRegTest1CycleCount;
		ulLastRegTest2CycleCount = ulRegTest2CycleCount;

		/* Toggle the check LED to give an indication of the system status.  If
		the LED toggles every 5 seconds then everything is ok.  A faster toggle
		indicates an error. */
		vParTestToggleLED( mainCHECK_LED );

		/* Calculate the maximum jitter experienced by the high frequency timer
		test and print it out.  It is ok to use printf without worrying about
		mutual exclusion as it is not used anywhere else in this demo. */
		//sprintf( cTempBuf, "%s [%fns]\n", "Max Jitter = ", ( ( float ) usMaxJitter ) * mainNS_PER_CLOCK );
		//ulActualJitter = ( ( unsigned long ) usMaxJitter ) * mainNS_PER_CLOCK;

		if( xCycleFrequency == mainERROR_CYCLE_TIME )
		{
			/* Just for break point. */
			portNOP();
		}
	}
}
/*-----------------------------------------------------------*/

/* The RX port uses this callback function to configure its tick interrupt.
This allows the application to choose the tick interrupt source. */
void vApplicationSetupTimerInterrupt( void )
{
	/* Enable compare match timer 0. */
	MSTP( CMT0 ) = 0;

	/* Interrupt on compare match. */
	CMT0.CMCR.BIT.CMIE = 1;

	/* Set the compare match value. */
	CMT0.CMCOR = ( unsigned short ) ( ( ( configPERIPHERAL_CLOCK_HZ / configTICK_RATE_HZ ) -1 ) / 8 );

	/* Divide the PCLK by 8. */
	CMT0.CMCR.BIT.CKS = 0;

	/* Enable the interrupt... */
	_IEN( _CMT0_CMI0 ) = 1;

	/* ...and set its priority to the application defined kernel priority. */
	_IPR( _CMT0_CMI0 ) = configKERNEL_INTERRUPT_PRIORITY;

	/* Start the timer. */
	CMT.CMSTR0.BIT.STR0 = 1;
}
/*-----------------------------------------------------------*/

/* This function is explained by the comments above its prototype at the top
of this file. */
void vApplicationMallocFailedHook( void )
{
	for( ;; );
}
/*-----------------------------------------------------------*/

/* This function is explained by the comments above its prototype at the top
of this file. */
void vApplicationStackOverflowHook( xTaskHandle *pxTask, signed char *pcTaskName )
{
	for( ;; );
}
/*-----------------------------------------------------------*/

/* This function is explained by the comments above its prototype at the top
of this file. */
void vApplicationIdleHook( void )
{
static volatile unsigned long ulIdleLoopCount = 0UL;

	ulIdleLoopCount++;
}
/*-----------------------------------------------------------*/

/* This function is explained in the comments at the top of this file. */
static void prvRegTest1Task( void *pvParameters )
{
	if( ( ( unsigned long ) pvParameters ) != mainREG_TEST_1_PARAMETER )
	{
		/* The parameter did not contain the expected value. */
		for( ;; )
		{
			/* Stop the tick interrupt so its obvious something has gone wrong. */
			taskDISABLE_INTERRUPTS();
		}
	}

	/* This is an asm function that never returns. */
	prvRegTest1Implementation();
}
/*-----------------------------------------------------------*/

/* This function is explained in the comments at the top of this file. */
static void prvRegTest2Task( void *pvParameters )
{
	if( ( ( unsigned long ) pvParameters ) != mainREG_TEST_2_PARAMETER )
	{
		/* The parameter did not contain the expected value. */
		for( ;; )
		{
			/* Stop the tick interrupt so its obvious something has gone wrong. */
			taskDISABLE_INTERRUPTS();
		}
	}

	/* This is an asm function that never returns. */
	prvRegTest2Implementation();
}
/*-----------------------------------------------------------*/





