/*
    FreeRTOS V8.1.2 - Copyright (C) 2014 Real Time Engineers Ltd. 
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

    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<

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

/* ****************************************************************************
 * This project includes a lot of tasks and tests and is therefore complex.
 * If you would prefer a much simpler project to get started with then select
 * the 'Blinky' build configuration within the HEW IDE.
 * ****************************************************************************
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
 * the kernel is doing.  The frequency and priority of the interrupt, in
 * combination with other standard tests executed in this demo, should result
 * in interrupts nesting at least 3 and probably 4 deep.  This test is only
 * included in build configurations that have the optimiser switched on.  In
 * optimised builds the count of high frequency ticks is used as the time base
 * for the run time stats.
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

/* Hardware specific includes. */
#include "iodefine.h"

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

/* The WEB server uses string handling functions, which in turn use a bit more
stack than most of the other tasks. */
#define mainuIP_STACK_SIZE			( configMINIMAL_STACK_SIZE * 3 )

/* The LED toggled by the check task. */
#define mainCHECK_LED				( 5 )

/* The rate at which mainCHECK_LED will toggle when all the tasks are running
without error.  Controlled by the check task as described at the top of this
file. */
#define mainNO_ERROR_CYCLE_TIME		( 5000 / portTICK_PERIOD_MS )

/* The rate at which mainCHECK_LED will toggle when an error has been reported
by at least one task.  Controlled by the check task as described at the top of
this file. */
#define mainERROR_CYCLE_TIME		( 200 / portTICK_PERIOD_MS )


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
void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName );

/*
 * The reg test tasks as described at the top of this file.
 */
static void prvRegTest1Task( void *pvParameters );
static void prvRegTest2Task( void *pvParameters );

/*
 * The actual implementation of the reg test functionality, which, because of
 * the direct register access, have to be in assembly.
 */
static void prvRegTest1Implementation( void ) __attribute__((naked));
static void prvRegTest2Implementation( void ) __attribute__((naked));


/*
 * The check task as described at the top of this file.
 */
static void prvCheckTask( void *pvParameters );

/*
 * Contains the implementation of the WEB server.
 */
extern void vuIP_Task( void *pvParameters );

/*-----------------------------------------------------------*/

/* Variables that are incremented on each iteration of the reg test tasks -
provided the tasks have not reported any errors.  The check task inspects these
variables to ensure they are still incrementing as expected.  If a variable
stops incrementing then it is likely that its associate task has stalled. */
unsigned long ulRegTest1CycleCount = 0UL, ulRegTest2CycleCount = 0UL;

/* The status message that is displayed at the bottom of the "task stats" web
page, which is served by the uIP task.  This will report any errors picked up
by the reg test task. */
static const char *pcStatusMessage = NULL;

/*-----------------------------------------------------------*/

int main(void)
{
extern void HardwareSetup( void );

	/* Renesas provided CPU configuration routine.  The clocks are configured in
	here. */
	HardwareSetup();

	/* Turn all LEDs off. */
	vParTestInitialise();

	/* Start the reg test tasks which test the context switching mechanism. */
	xTaskCreate( prvRegTest1Task, "RegTst1", configMINIMAL_STACK_SIZE, ( void * ) mainREG_TEST_1_PARAMETER, tskIDLE_PRIORITY, NULL );
	xTaskCreate( prvRegTest2Task, "RegTst2", configMINIMAL_STACK_SIZE, ( void * ) mainREG_TEST_2_PARAMETER, tskIDLE_PRIORITY, NULL );

	/* The web server task. */
	xTaskCreate( vuIP_Task, "uIP", mainuIP_STACK_SIZE, NULL, mainuIP_TASK_PRIORITY, NULL );

	/* Start the check task as described at the top of this file. */
	xTaskCreate( prvCheckTask, "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

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
	
	return 0;
}
/*-----------------------------------------------------------*/

static void prvCheckTask( void *pvParameters )
{
static volatile unsigned long ulLastRegTest1CycleCount = 0UL, ulLastRegTest2CycleCount = 0UL;
TickType_t xNextWakeTime, xCycleFrequency = mainNO_ERROR_CYCLE_TIME;
extern void vSetupHighFrequencyTimer( void );

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
			pcStatusMessage = "Error: GenQueue";
		}
		else if( xAreQueuePeekTasksStillRunning() != pdTRUE )
		{
			pcStatusMessage = "Error: QueuePeek\r\n";
		}
		else if( xAreBlockingQueuesStillRunning() != pdTRUE )
		{
			pcStatusMessage = "Error: BlockQueue\r\n";
		}
		else if( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
		{
			pcStatusMessage = "Error: BlockTime\r\n";
		}
	    else if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	    {
			pcStatusMessage = "Error: SemTest\r\n";
	    }
	    else if( xArePollingQueuesStillRunning() != pdTRUE )
	    {
			pcStatusMessage = "Error: PollQueue\r\n";
	    }
	    else if( xIsCreateTaskStillRunning() != pdTRUE )
	    {
			pcStatusMessage = "Error: Death\r\n";
	    }
	    else if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
	    {
			pcStatusMessage = "Error: IntMath\r\n";
	    }
	    else if( xAreRecursiveMutexTasksStillRunning() != pdTRUE )
	    {
			pcStatusMessage = "Error: RecMutex\r\n";
	    }
		else if( xAreIntQueueTasksStillRunning() != pdPASS )
		{
			pcStatusMessage = "Error: IntQueue\r\n";
		}
		else if( xAreMathsTaskStillRunning() != pdPASS )
		{
			pcStatusMessage = "Error: Flop\r\n";
		}

		/* Check the reg test tasks are still cycling.  They will stop incrementing
		their loop counters if they encounter an error. */
		if( ulRegTest1CycleCount == ulLastRegTest1CycleCount )
		{
			pcStatusMessage = "Error: RegTest1\r\n";
		}

		if( ulRegTest2CycleCount == ulLastRegTest2CycleCount )
		{
			pcStatusMessage = "Error: RegTest2\r\n";
		}

		ulLastRegTest1CycleCount = ulRegTest1CycleCount;
		ulLastRegTest2CycleCount = ulRegTest2CycleCount;

		/* Toggle the check LED to give an indication of the system status.  If
		the LED toggles every 5 seconds then everything is ok.  A faster toggle
		indicates an error. */
		vParTestToggleLED( mainCHECK_LED );

		/* Ensure the LED toggles at a faster rate if an error has occurred. */
		if( pcStatusMessage != NULL )
		{
			/* Increase the rate at which this task cycles, which will increase the
			rate at which mainCHECK_LED flashes to give visual feedback that an error
			has occurred. */
			xCycleFrequency = mainERROR_CYCLE_TIME;
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
void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName )
{
	for( ;; );
}
/*-----------------------------------------------------------*/

/* This function is explained by the comments above its prototype at the top
of this file. */
void vApplicationIdleHook( void )
{
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

char *pcGetTaskStatusMessage( void )
{
	/* Not bothered about a critical section here although technically because of
	the task priorities the pointer could change it will be atomic if not near
	atomic and its not critical. */
	if( pcStatusMessage == NULL )
	{
		return "All tasks running without error";
	}
	else
	{
		return ( char * ) pcStatusMessage;
	}
}
/*-----------------------------------------------------------*/

/* This function is explained in the comments at the top of this file. */
static void prvRegTest1Implementation( void )
{
	__asm volatile
	(
			/* Put a known value in each register. */
			"MOV	#1, R1						\n" \
			"MOV	#2, R2						\n" \
			"MOV	#3, R3						\n" \
			"MOV	#4, R4						\n" \
			"MOV	#5, R5						\n" \
			"MOV	#6, R6						\n" \
			"MOV	#7, R7						\n" \
			"MOV	#8, R8						\n" \
			"MOV	#9, R9						\n" \
			"MOV	#10, R10					\n" \
			"MOV	#11, R11					\n" \
			"MOV	#12, R12					\n" \
			"MOV	#13, R13					\n" \
			"MOV	#14, R14					\n" \
			"MOV	#15, R15					\n" \
			
			/* Loop, checking each itteration that each register still contains the
			expected value. */
		"TestLoop1:								\n" \

			/* Push the registers that are going to get clobbered. */
			"PUSHM	R14-R15						\n" \
			
			/* Increment the loop counter to show this task is still getting CPU time. */
			"MOV	#_ulRegTest1CycleCount, R14	\n" \
			"MOV	[ R14 ], R15				\n" \
			"ADD	#1, R15						\n" \
			"MOV	R15, [ R14 ]				\n" \
			
			/* Yield to extend the test coverage.  Set the bit in the ITU SWINTR register. */
			"MOV	#1, R14						\n" \
			"MOV 	#0872E0H, R15				\n" \
			"MOV.B	R14, [R15]					\n" \
			"NOP								\n" \
			"NOP								\n" \
			
			/* Restore the clobbered registers. */
			"POPM	R14-R15						\n" \
			
			/* Now compare each register to ensure it still contains the value that was
			set before this loop was entered. */
			"CMP	#1, R1						\n" \
			"BNE	RegTest1Error				\n" \
			"CMP	#2, R2						\n" \
			"BNE	RegTest1Error				\n" \
			"CMP	#3, R3						\n" \
			"BNE	RegTest1Error				\n" \
			"CMP	#4, R4						\n" \
			"BNE	RegTest1Error				\n" \
			"CMP	#5, R5						\n" \
			"BNE	RegTest1Error				\n" \
			"CMP	#6, R6						\n" \
			"BNE	RegTest1Error				\n" \
			"CMP	#7, R7						\n" \
			"BNE	RegTest1Error				\n" \
			"CMP	#8, R8						\n" \
			"BNE	RegTest1Error				\n" \
			"CMP	#9, R9						\n" \
			"BNE	RegTest1Error				\n" \
			"CMP	#10, R10					\n" \
			"BNE	RegTest1Error				\n" \
			"CMP	#11, R11					\n" \
			"BNE	RegTest1Error				\n" \
			"CMP	#12, R12					\n" \
			"BNE	RegTest1Error				\n" \
			"CMP	#13, R13					\n" \
			"BNE	RegTest1Error				\n" \
			"CMP	#14, R14					\n" \
			"BNE	RegTest1Error				\n" \
			"CMP	#15, R15					\n" \
			"BNE	RegTest1Error				\n" \

			/* All comparisons passed, start a new itteratio of this loop. */
			"BRA		TestLoop1				\n" \
			
		"RegTest1Error:							\n" \
			/* A compare failed, just loop here so the loop counter stops incrementing
			- causing the check task to indicate the error. */
			"BRA RegTest1Error					  "
	);
}
/*-----------------------------------------------------------*/

/* This function is explained in the comments at the top of this file. */
static void prvRegTest2Implementation( void )
{
	__asm volatile
	(
			/* Put a known value in each register. */
			"MOV	#10H, R1					\n" \
			"MOV	#20H, R2					\n" \
			"MOV	#30H, R3					\n" \
			"MOV	#40H, R4					\n" \
			"MOV	#50H, R5					\n" \
			"MOV	#60H, R6					\n" \
			"MOV	#70H, R7					\n" \
			"MOV	#80H, R8					\n" \
			"MOV	#90H, R9					\n" \
			"MOV	#100H, R10					\n" \
			"MOV	#110H, R11					\n" \
			"MOV	#120H, R12					\n" \
			"MOV	#130H, R13					\n" \
			"MOV	#140H, R14					\n" \
			"MOV	#150H, R15					\n" \
			
			/* Loop, checking each itteration that each register still contains the
			expected value. */
		"TestLoop2:								\n" \

			/* Push the registers that are going to get clobbered. */
			"PUSHM	R14-R15						\n" \
			
			/* Increment the loop counter to show this task is still getting CPU time. */
			"MOV	#_ulRegTest2CycleCount, R14	\n" \
			"MOV	[ R14 ], R15				\n" \
			"ADD	#1, R15						\n" \
			"MOV	R15, [ R14 ]				\n" \
			
			/* Restore the clobbered registers. */
			"POPM	R14-R15						\n" \
			
			/* Now compare each register to ensure it still contains the value that was
			set before this loop was entered. */
			"CMP	#10H, R1					\n" \
			"BNE	RegTest2Error				\n" \
			"CMP	#20H, R2					\n" \
			"BNE	RegTest2Error				\n" \
			"CMP	#30H, R3					\n" \
			"BNE	RegTest2Error				\n" \
			"CMP	#40H, R4					\n" \
			"BNE	RegTest2Error				\n" \
			"CMP	#50H, R5					\n" \
			"BNE	RegTest2Error				\n" \
			"CMP	#60H, R6					\n" \
			"BNE	RegTest2Error				\n" \
			"CMP	#70H, R7					\n" \
			"BNE	RegTest2Error				\n" \
			"CMP	#80H, R8					\n" \
			"BNE	RegTest2Error				\n" \
			"CMP	#90H, R9					\n" \
			"BNE	RegTest2Error				\n" \
			"CMP	#100H, R10					\n" \
			"BNE	RegTest2Error				\n" \
			"CMP	#110H, R11					\n" \
			"BNE	RegTest2Error				\n" \
			"CMP	#120H, R12					\n" \
			"BNE	RegTest2Error				\n" \
			"CMP	#130H, R13					\n" \
			"BNE	RegTest2Error				\n" \
			"CMP	#140H, R14					\n" \
			"BNE	RegTest2Error				\n" \
			"CMP	#150H, R15					\n" \
			"BNE	RegTest2Error				\n" \

			/* All comparisons passed, start a new itteratio of this loop. */
			"BRA	TestLoop2					\n" \
			
		"RegTest2Error:							\n" \
			/* A compare failed, just loop here so the loop counter stops incrementing
			- causing the check task to indicate the error. */
			"BRA RegTest2Error					  "
	);
}

