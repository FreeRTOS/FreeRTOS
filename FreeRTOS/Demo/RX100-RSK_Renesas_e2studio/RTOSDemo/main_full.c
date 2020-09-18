/*
 * FreeRTOS Kernel V10.4.1
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
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

/* ****************************************************************************
 * This project includes a lot of tasks and tests and is therefore complex.
 * If you would prefer a much simpler project to get started with then select
 * the 'low power' demo by setting configCREATE_LOW_POWER_DEMO to 1 in
 * FreeRTOSConfig.h.  When configCREATE_LOW_POWER_DEMO is set to 1 main() will
 * call main_low_power() instead of main_full().
 * ****************************************************************************
 *
 * Creates all the demo application tasks, then starts the scheduler.  The web
 * documentation provides more details of the standard demo application tasks,
 * which provide no particular functionality but do provide a good example of
 * how to use the FreeRTOS API.
 *
 * In addition to the standard demo tasks, the following tasks and tests are
 * defined and/or created within this file:
 *
 * "Reg test" tasks - These fill the registers with known values, then
 * repeatedly check that each register still contains its expected value for
 * the lifetime of the tasks.  Each task uses different values.  The tasks run
 * with very low priority so get preempted very frequently.  A check variable
 * is incremented on each iteration of the test loop.  A register containing an
 * unexpected value is indicative of an error in the context switching
 * mechanism and will result in a branch to a null loop - which in turn will
 * prevent the check variable from incrementing any further and allow the check
 * timer (described below) to determine that an error has occurred.  The nature
 * of the reg test tasks necessitates that they are written in assembly code.
 *
 * "Check Timer" and Callback Function - The check timer period is initially
 * set to three seconds.  The check timer callback function checks that all the
 * standard demo tasks are not only still executing, but are executing without
 * reporting any errors.  If the check timer discovers that a task has either
 * stalled, or reported an error, then it changes its own period from the
 * initial three seconds, to just 200ms.  The check timer callback function
 * also toggles LED 0 each time it is called.  This provides a visual
 * indication of the system status:  If the LED toggles every three seconds,
 * then no issues have been discovered.  If the LED toggles every 200ms, then
 * an issue has been discovered with at least one task.
 *
 * *NOTE 1* The CPU must be in Supervisor mode when the scheduler is started.
 * The PowerON_Reset_PC() supplied in resetprg.c with this demo has
 * Change_PSW_PM_to_UserMode() commented out to ensure this is the case.
*/

/* Standard includes. */
#include <string.h>

/* Hardware specific includes. */
#include "iodefine.h"

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "timers.h"
#include "semphr.h"

/* Standard demo includes. */
#include "partest.h"
#include "death.h"
#include "blocktim.h"
#include "GenQTest.h"
#include "recmutex.h"

/* The code in this file is only built when configCREATE_LOW_POWER_DEMO is set
to 0, otherwise the code in main_low_power.c is used. */
#if configCREATE_LOW_POWER_DEMO == 0


/* Values that are passed into the reg test tasks using the task parameter.
The tasks check that the values are passed in correctly. */
#define mainREG_TEST_1_PARAMETER	( 0x12121212UL )
#define mainREG_TEST_2_PARAMETER	( 0x12345678UL )

/* Priorities at which the standard demo tasks are created. */
#define mainGEN_QUEUE_TASK_PRIORITY	( tskIDLE_PRIORITY )
#define mainCREATOR_TASK_PRIORITY   ( tskIDLE_PRIORITY + 3 )

/* The LED toggled by the check timer. */
#define mainCHECK_LED				( 0 )

/* The period at which the check timer will expire, in ms, provided no errors
have been reported by any of the standard demo tasks.  ms are converted to the
equivalent in ticks using the portTICK_PERIOD_MS constant. */
#define mainCHECK_TIMER_PERIOD_MS			( 3000UL / portTICK_PERIOD_MS )

/* The period at which the check timer will expire, in ms, if an error has been
reported in one of the standard demo tasks.  ms are converted to the equivalent
in ticks using the portTICK_PERIOD_MS constant. */
#define mainERROR_CHECK_TIMER_PERIOD_MS 	( 200UL / portTICK_PERIOD_MS )

/* A block time of zero simple means "Don't Block". */
#define mainDONT_BLOCK				( 0UL )

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


/*-----------------------------------------------------------*/

/* Variables that are incremented on each iteration of the reg test tasks -
provided the tasks have not reported any errors.  The check timer inspects these
variables to ensure they are still incrementing as expected.  If a variable
stops incrementing then it is likely that its associated task has stalled. */
unsigned long ulRegTest1CycleCount = 0UL, ulRegTest2CycleCount = 0UL;

/* The check timer.  This uses prvCheckTimerCallback() as its callback
function. */
static TimerHandle_t xCheckTimer = NULL;

/*-----------------------------------------------------------*/

void main_full( void )
{
	/* Start the reg test tasks which test the context switching mechanism. */
	xTaskCreate( prvRegTest1Task, "RegTst1", configMINIMAL_STACK_SIZE, ( void * ) mainREG_TEST_1_PARAMETER, tskIDLE_PRIORITY, NULL );
	xTaskCreate( prvRegTest2Task, "RegTst2", configMINIMAL_STACK_SIZE, ( void * ) mainREG_TEST_2_PARAMETER, tskIDLE_PRIORITY, NULL );

	/* Create the standard demo tasks. */
	vCreateBlockTimeTasks();
	vStartGenericQueueTasks( mainGEN_QUEUE_TASK_PRIORITY );
	vStartRecursiveMutexTasks();

	/* The suicide tasks must be created last as they need to know how many
	tasks were running prior to their creation in order to ascertain whether
	or not the correct/expected number of tasks are running at any given time. */
	vCreateSuicidalTasks( mainCREATOR_TASK_PRIORITY );

	/* Create the software timer that performs the 'check' functionality,
	as described at the top of this file. */
	xCheckTimer = xTimerCreate( "CheckTimer",/* A text name, purely to help debugging. */
								( mainCHECK_TIMER_PERIOD_MS ),		/* The timer period, in this case 5000ms (5s). */
								pdTRUE,								/* This is an auto-reload timer, so xAutoReload is set to pdTRUE. */
								( void * ) 0,						/* The ID is not used, so can be set to anything. */
								prvCheckTimerCallback				/* The callback function that inspects the status of all the other tasks. */
							  );

	configASSERT( xCheckTimer );

	/* Start the check timer.  It will actually start when the scheduler is
	started. */
	xTimerStart( xCheckTimer, mainDONT_BLOCK );

	/* Start the tasks running. */
	vTaskStartScheduler();

	/* If all is well execution will never reach here as the scheduler will be
	running.  If this null loop is reached then it is likely there was
	insufficient FreeRTOS heap available for the idle task and/or timer task to
	be created.  See http://www.freertos.org/a00111.html. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvCheckTimerCallback( TimerHandle_t xTimer )
{
static long lChangedTimerPeriodAlready = pdFALSE, lErrorStatus = pdPASS;
static volatile unsigned long ulLastRegTest1CycleCount = 0UL, ulLastRegTest2CycleCount = 0UL;

	/* Remove compiler warnings about unused parameters. */
	( void ) xTimer;

	/* Check the standard demo tasks are running without error. */
	if( xAreGenericQueueTasksStillRunning() != pdTRUE )
	{
		lErrorStatus = pdFAIL;
	}
	else if( xIsCreateTaskStillRunning() != pdTRUE )
	{
		lErrorStatus = pdFAIL;
	}
	else if( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
	{
		lErrorStatus = pdFAIL;
	}
	else if( xAreRecursiveMutexTasksStillRunning() != pdTRUE )
	{
		lErrorStatus = pdFAIL;
	}

	/* Check the reg test tasks are still cycling.  They will stop incrementing
	their loop counters if they encounter an error. */
	if( ulRegTest1CycleCount == ulLastRegTest1CycleCount )
	{
		lErrorStatus = pdFAIL;
	}

	if( ulRegTest2CycleCount == ulLastRegTest2CycleCount )
	{
		lErrorStatus = pdFAIL;
	}

	/* Remember the loop counter values this time around so they can be checked
	again the next time this callback function executes. */
	ulLastRegTest1CycleCount = ulRegTest1CycleCount;
	ulLastRegTest2CycleCount = ulRegTest2CycleCount;

	/* Toggle the check LED to give an indication of the system status.  If
	the LED toggles every three seconds then everything is ok.  A faster toggle
	indicates an error. */
	vParTestToggleLED( mainCHECK_LED );

	/* Was an error detected this time through the callback execution? */
	if( lErrorStatus != pdPASS )
	{
		if( lChangedTimerPeriodAlready == pdFALSE )
		{
			lChangedTimerPeriodAlready = pdTRUE;

			/* This call to xTimerChangePeriod() uses a zero block time.
			Functions called from inside of a timer callback function must
			*never* attempt	to block. */
			xTimerChangePeriod( xCheckTimer, ( mainERROR_CHECK_TIMER_PERIOD_MS ), mainDONT_BLOCK );
		}
	}
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
	MOV.L	#11111111H, R15
	MVTACHI	R15
	MOV.L	#22222222H, R15
	MVTACLO	R15
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

	; Loop, checking each iteration that each register still contains the
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

	;Check the accumulator value.
	MVFACHI	R15
	CMP		#11111111H, R15
	BNE		RegTest2Error
	MVFACMI	R15
	CMP		#11112222H, R15
	BNE		RegTest2Error

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

	; All comparisons passed, start a new iteration of this loop.
	BRA		TestLoop1

RegTest1Error:
	; A compare failed, just loop here so the loop counter stops incrementing
	; causing the check timer to indicate the error.
	BRA RegTest1Error
}
/*-----------------------------------------------------------*/

/* This function is explained in the comments at the top of this file. */
#pragma inline_asm prvRegTest2Implementation
static void prvRegTest2Implementation( void )
{
	; Put a known value in each register.
	MOV.L	#33333333H, R15
	MVTACHI	R15
	MOV.L	#44444444H, R15
	MVTACLO	R15
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

	; Loop, checking on each iteration that each register still contains the
	; expected value.
TestLoop2:

	; Push the registers that are going to get clobbered.
	PUSHM	R14-R15

	; Increment the loop counter to show this task is still getting CPU time.
	MOV.L	#_ulRegTest2CycleCount, R14
	MOV.L	[ R14 ], R15
	ADD		#1, R15
	MOV.L	R15, [ R14 ]

	;Check the accumulator value.
	MVFACHI	R15
	CMP		#33333333H, R15
	BNE		RegTest2Error
	MVFACMI	R15
	CMP		#33334444H, R15
	BNE		RegTest2Error

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
	; - causing the check timer to indicate the error.
	BRA RegTest2Error
}
/*-----------------------------------------------------------*/

#endif /* configCREATE_LOW_POWER_DEMO */
