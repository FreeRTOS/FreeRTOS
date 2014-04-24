/*
    FreeRTOS V8.0.1 - Copyright (C) 2014 Real Time Engineers Ltd. 
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
 * the 'Blinky' build configuration within the HEW IDE.  The Blinky 
 * configuration builds main-blinky.c in place of this file.
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
 * "Check" timer - The check software timer period is initially set to five
 * seconds.  The callback function associated with the check software timer
 * checks that all the standard demo tasks, and the register check tasks, are
 * not only still executing, but are executing without reporting any errors.  If
 * the check software timer discovers that a task has either stalled, or
 * reported an error, then it changes its own execution period from the initial
 * five seconds, to just 200ms.  The check software timer callback function
 * also toggles LED3 each time it is called.  This provides a visual indication 
 * of the system status:  If LED3 toggles every five seconds, then no issues 
 * have been discovered.  If the LED toggles every 200ms, then an issue has been 
 * discovered with at least one task.
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
 * *NOTE 1* If LED3 is toggling every 5 seconds then all the demo application
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
 *
 * *
*/

#include <string.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "timers.h"
#include "semphr.h"

/* Standard demo includes. */
#include "partest.h"
#include "flash_timer.h"
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
#define mainuIP_TASK_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainINTEGER_TASK_PRIORITY   ( tskIDLE_PRIORITY )
#define mainGEN_QUEUE_TASK_PRIORITY	( tskIDLE_PRIORITY )
#define mainFLOP_TASK_PRIORITY		( tskIDLE_PRIORITY )

/* The WEB server uses string handling functions, which in turn use a bit more
stack than most of the other tasks. */
#define mainuIP_STACK_SIZE			( configMINIMAL_STACK_SIZE * 3 )

/* The LED toggled by the check timer. */
#define mainCHECK_LED				( 3 )

/* The rate at which mainCHECK_LED will toggle when all the tasks are running
without error.  Controlled by the check timer as described at the top of this
file. */
#define mainNO_ERROR_CHECK_TIMER_PERIOD_MS	( 5000 / portTICK_PERIOD_MS )

/* The rate at which mainCHECK_LED will toggle when an error has been reported
by at least one task.  Controlled by the check timer as described at the top of
this file. */
#define mainERROR_CHECK_TIMER_PERIOD_MS		( 200 / portTICK_PERIOD_MS )

/* A block time of zero simply means "don't block". */
#define mainDONT_BLOCK	( 0UL )

/* A set of timers are created, each of which toggles and LED.  This specifies
the number of timers to create. */
#define mainNUMBER_OF_LEDS_TO_FLASH		( 3 )

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
static void prvRegTest1Implementation( void );
static void prvRegTest2Implementation( void );

/*
 * The check timer callback function, as described at the top of this file.
 */
static void prvCheckTimerCallback( TimerHandle_t xTimer );

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
const char *pcStatusMessage = "All tasks executing without error.";

/*-----------------------------------------------------------*/

void main(void)
{
TimerHandle_t xCheckTimer;
extern void HardwareSetup( void );

	/* Turn all LEDs off. */
	vParTestInitialise();

	/* Start the reg test tasks which test the context switching mechanism. */
	xTaskCreate( prvRegTest1Task, "RegTst1", configMINIMAL_STACK_SIZE, ( void * ) mainREG_TEST_1_PARAMETER, tskIDLE_PRIORITY, NULL );
	xTaskCreate( prvRegTest2Task, "RegTst2", configMINIMAL_STACK_SIZE, ( void * ) mainREG_TEST_2_PARAMETER, tskIDLE_PRIORITY, NULL );

	/* The web server task. */
	xTaskCreate( vuIP_Task, "uIP", mainuIP_STACK_SIZE, NULL, mainuIP_TASK_PRIORITY, NULL );

	/* Create the standard demo tasks. */
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
	vCreateBlockTimeTasks();
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
	vStartIntegerMathTasks( mainINTEGER_TASK_PRIORITY );
	vStartGenericQueueTasks( mainGEN_QUEUE_TASK_PRIORITY );	
	vStartQueuePeekTasks();
	vStartRecursiveMutexTasks();
	vStartInterruptQueueTasks();
	vStartMathTasks( mainFLOP_TASK_PRIORITY );

	/* Create the timers used to toggle the LEDs. */
	vStartLEDFlashTimers( mainNUMBER_OF_LEDS_TO_FLASH );

	/* Create the software timer that performs the 'check' functionality,
	as described at the top of this file. */
	xCheckTimer = xTimerCreate( "CheckTimer",							/* A text name, purely to help debugging. */
								( mainNO_ERROR_CHECK_TIMER_PERIOD_MS ),	/* The timer period, in this case 5000ms (5s). */
								pdTRUE,									/* This is an auto-reload timer, so xAutoReload is set to pdTRUE. */
								( void * ) 0,							/* The ID is not used, so can be set to anything. */
								prvCheckTimerCallback					/* The callback function that inspects the status of all the other tasks. */
							  );	
	
	if( xCheckTimer != NULL )
	{
		xTimerStart( xCheckTimer, mainDONT_BLOCK );
	}

	/* The suicide tasks must be created last as they need to know how many
	tasks were running prior to their creation in order to ascertain whether
	or not the correct/expected number of tasks are running at any given time. */
	vCreateSuicidalTasks( mainCREATOR_TASK_PRIORITY );

	/* Start the tasks running. */
	vTaskStartScheduler();

	/* If all is well, the scheduler will now be running, and the following line
	will never be reached.  If the following line does execute, then there was
	insufficient FreeRTOS heap memory available for the idle and/or timer tasks
	to be created.  See the memory management section on the FreeRTOS web site
	for more details. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvCheckTimerCallback( TimerHandle_t xTimer )
{
static long lChangedTimerPeriodAlready = pdFALSE;
static unsigned long ulLastRegTest1CycleCount = 0, ulLastRegTest2CycleCount = 0;
long lErrorFound = pdFALSE;

	/* If this is being executed then the kernel has been started.  Start the 
	high frequency timer test as described at the top of this file.  This is 
	only included in the optimised build configuration - otherwise it takes up 
	too much CPU time and can disrupt other tests. */
	#ifdef INCLUDE_HIGH_FREQUENCY_TIMER_TEST
		vSetupHighFrequencyTimer();
	#endif

	/* Check the standard demo tasks are running without error. */
	if( xAreGenericQueueTasksStillRunning() != pdTRUE )
	{
		lErrorFound = pdTRUE;
		pcStatusMessage = "Error: GenQueue";
	}
	else if( xAreQueuePeekTasksStillRunning() != pdTRUE )
	{
		lErrorFound = pdTRUE;
		pcStatusMessage = "Error: QueuePeek";
	}
	else if( xAreBlockingQueuesStillRunning() != pdTRUE )
	{
		lErrorFound = pdTRUE;
		pcStatusMessage = "Error: BlockQueue";
	}
	else if( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
	{
		lErrorFound = pdTRUE;
		pcStatusMessage = "Error: BlockTime";
	}
	else if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	{
		lErrorFound = pdTRUE;
		pcStatusMessage = "Error: SemTest";
	}
	else if( xArePollingQueuesStillRunning() != pdTRUE )
	{
		lErrorFound = pdTRUE;
		pcStatusMessage = "Error: PollQueue";
	}
	else if( xIsCreateTaskStillRunning() != pdTRUE )
	{
		lErrorFound = pdTRUE;
		pcStatusMessage = "Error: Death";
	}
	else if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
	{
		lErrorFound = pdTRUE;
		pcStatusMessage = "Error: IntMath";
	}
	else if( xAreRecursiveMutexTasksStillRunning() != pdTRUE )
	{
		lErrorFound = pdTRUE;
		pcStatusMessage = "Error: RecMutex";
	}
	else if( xAreIntQueueTasksStillRunning() != pdPASS )
	{
		lErrorFound = pdTRUE;
		pcStatusMessage = "Error: IntQueue";
	}
	else if( xAreMathsTaskStillRunning() != pdPASS )
	{
		lErrorFound = pdTRUE;
		pcStatusMessage = "Error: Flop";
	}

	/* Check the reg test tasks are still cycling.  They will stop incrementing
	their loop counters if they encounter an error. */
	if( ulRegTest1CycleCount == ulLastRegTest1CycleCount )
	{
		lErrorFound = pdTRUE;
		pcStatusMessage = "Error: RegTest1";
	}

	if( ulRegTest2CycleCount == ulLastRegTest2CycleCount )
	{
		lErrorFound = pdTRUE;
		pcStatusMessage = "Error: RegTest2";
	}

	ulLastRegTest1CycleCount = ulRegTest1CycleCount;
	ulLastRegTest2CycleCount = ulRegTest2CycleCount;

	/* Toggle the check LED to give an indication of the system status.  If
	the LED toggles every mainNO_ERROR_CHECK_TIMER_PERIOD_MS milliseconds then
	everything is ok.  A faster toggle indicates an error. */
	vParTestToggleLED( mainCHECK_LED );	
	
	/* Have any errors been latch in lErrorFound?  If so, shorten the
	period of the check timer to mainERROR_CHECK_TIMER_PERIOD_MS milliseconds.
	This will result in an increase in the rate at which mainCHECK_LED
	toggles. */
	if( lErrorFound != pdFALSE )
	{
		if( lChangedTimerPeriodAlready == pdFALSE )
		{
			lChangedTimerPeriodAlready = pdTRUE;
			
			/* This call to xTimerChangePeriod() uses a zero block time.
			Functions called from inside of a timer callback function must
			*never* attempt	to block. */
			xTimerChangePeriod( xTimer, ( mainERROR_CHECK_TIMER_PERIOD_MS ), mainDONT_BLOCK );
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

	/* This is an inline asm function that never returns. */
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

	/* This is an inline asm function that never returns. */
	prvRegTest2Implementation();
}
/*-----------------------------------------------------------*/

/* This function is explained in the comments at the top of this file. */
#pragma inline_asm prvRegTest1Implementation
static void prvRegTest1Implementation( void )
{
	; Put a known value in each register.
	MOV.L	#1, R1
	MOV.L	#2, R2
	MOV.L	#3, R3
	MOV.L	#4, R4
	MOV.L	#5, R5
	MOV.L	#6, R6
	MOV.L	#7, R7
	MOV.L	#8, R8
	MOV.L	#9, R9
	MOV.L	#10, R10
	MOV.L	#11, R11
	MOV.L	#12, R12
	MOV.L	#13, R13
	MOV.L	#14, R14
	MOV.L	#15, R15

	; Loop, checking each itteration that each register still contains the
	; expected value.
TestLoop1:

	; Push the registers that are going to get clobbered.
	PUSHM	R14-R15

	; Increment the loop counter to show this task is still getting CPU time.
	MOV.L	#_ulRegTest1CycleCount, R14
	MOV.L	[ R14 ], R15
	ADD		#1, R15
	MOV.L	R15, [ R14 ]

	; Yield to extend the text coverage.  Set the bit in the ITU SWINTR register.
	MOV.L	#1, R14
	MOV.L 	#0872E0H, R15
	MOV.B	R14, [R15]
	NOP
	NOP

	; Restore the clobbered registers.
	POPM	R14-R15

	; Now compare each register to ensure it still contains the value that was
	; set before this loop was entered.
	CMP		#1, R1
	BNE		RegTest1Error
	CMP		#2, R2
	BNE		RegTest1Error
	CMP		#3, R3
	BNE		RegTest1Error
	CMP		#4, R4
	BNE		RegTest1Error
	CMP		#5, R5
	BNE		RegTest1Error
	CMP		#6, R6
	BNE		RegTest1Error
	CMP		#7, R7
	BNE		RegTest1Error
	CMP		#8, R8
	BNE		RegTest1Error
	CMP		#9, R9
	BNE		RegTest1Error
	CMP		#10, R10
	BNE		RegTest1Error
	CMP		#11, R11
	BNE		RegTest1Error
	CMP		#12, R12
	BNE		RegTest1Error
	CMP		#13, R13
	BNE		RegTest1Error
	CMP		#14, R14
	BNE		RegTest1Error
	CMP		#15, R15
	BNE		RegTest1Error

	; All comparisons passed, start a new itteratio of this loop.
	BRA		TestLoop1

RegTest1Error:
	; A compare failed, just loop here so the loop counter stops incrementing
	; causing the check task to indicate the error.
	BRA RegTest1Error
}
/*-----------------------------------------------------------*/

/* This function is explained in the comments at the top of this file. */
#pragma inline_asm prvRegTest2Implementation
static void prvRegTest2Implementation( void )
{
	; Put a known value in each register.
	MOV.L	#10, R1
	MOV.L	#20, R2
	MOV.L	#30, R3
	MOV.L	#40, R4
	MOV.L	#50, R5
	MOV.L	#60, R6
	MOV.L	#70, R7
	MOV.L	#80, R8
	MOV.L	#90, R9
	MOV.L	#100, R10
	MOV.L	#110, R11
	MOV.L	#120, R12
	MOV.L	#130, R13
	MOV.L	#140, R14
	MOV.L	#150, R15

	; Loop, checking on each itteration that each register still contains the
	; expected value.
TestLoop2:

	; Push the registers that are going to get clobbered.
	PUSHM	R14-R15

	; Increment the loop counter to show this task is still getting CPU time.
	MOV.L	#_ulRegTest2CycleCount, R14
	MOV.L	[ R14 ], R15
	ADD		#1, R15
	MOV.L	R15, [ R14 ]

	; Restore the clobbered registers.
	POPM	R14-R15

	CMP		#10, R1
	BNE		RegTest2Error
	CMP		#20, R2
	BNE		RegTest2Error
	CMP		#30, R3
	BNE		RegTest2Error
	CMP		#40, R4
	BNE		RegTest2Error
	CMP		#50, R5
	BNE		RegTest2Error
	CMP		#60, R6
	BNE		RegTest2Error
	CMP		#70, R7
	BNE		RegTest2Error
	CMP		#80, R8
	BNE		RegTest2Error
	CMP		#90, R9
	BNE		RegTest2Error
	CMP		#100, R10
	BNE		RegTest2Error
	CMP		#110, R11
	BNE		RegTest2Error
	CMP		#120, R12
	BNE		RegTest2Error
	CMP		#130, R13
	BNE		RegTest2Error
	CMP		#140, R14
	BNE		RegTest2Error
	CMP		#150, R15
	BNE		RegTest2Error

	; All comparisons passed, start a new itteratio of this loop.
	BRA		TestLoop2

RegTest2Error:
	; A compare failed, just loop here so the loop counter stops incrementing
	; - causing the check task to indicate the error.
	BRA RegTest2Error
}
/*-----------------------------------------------------------*/

char *pcGetTaskStatusMessage( void )
{
	/* Not bothered about a critical section here although technically because of
	the task priorities the pointer could change it will be atomic if not near
	atomic and its not critical. */
	return ( char * ) pcStatusMessage;
}
/*-----------------------------------------------------------*/



