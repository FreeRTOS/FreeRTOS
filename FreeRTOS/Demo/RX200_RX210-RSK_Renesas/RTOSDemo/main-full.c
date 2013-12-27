/*
    FreeRTOS V7.6.0 - Copyright (C) 2013 Real Time Engineers Ltd. 
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

/* ****************************************************************************
 * This project includes a lot of tasks and tests and is therefore complex.
 * If you would prefer a much simpler project to get started with then select
 * the 'Blinky' build configuration within the HEW IDE.  The Blinky build
 * configuration uses main-blinky.c instead of main-full.c.
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
 * set to five seconds.  The check timer callback function checks that all the 
 * standard demo tasks are not only still executing, but are executing without 
 * reporting any errors.  If the check timer discovers that a task has either 
 * stalled, or reported an error, then it changes its own period from the 
 * initial five seconds, to just 200ms.  The check timer callback function 
 * also toggles LED 3 each time it is called.  This provides a visual 
 * indication of the system status:  If the LED toggles every five seconds, 
 * then no issues have been discovered.  If the LED toggles every 200ms, then 
 * an issue has been discovered with at least one task.
 *
 * "High frequency timer test" - A high frequency periodic interrupt is
 * generated using a timer - the interrupt is assigned a priority above
 * configMAX_SYSCALL_INTERRUPT_PRIORITY, so will not be effected by anything
 * the kernel is doing.  The frequency and priority of the interrupt, in
 * combination with other standard tests executed in this demo, will result
 * in interrupts nesting at least 3 and probably 4 deep.  This test is only
 * included in build configurations that have the optimiser switched on.
 *
 * "Button and LCD test" - This creates two tasks.  The first simply scrolls
 * a message back and forth along the top line of the LCD display.  If no
 * buttons are pushed, the second also scrolls a message back and forth, but
 * along the bottom line of the display.  The automatic scrolling of the second
 * line of the display can be started and stopped using button SW2.  Once 
 * stopped it can then be manually nudged left using button SW3, and manually
 * nudged right using button SW1.  Button pushes generate an interrupt, and the
 * interrupt communicates with the task using a queue.
 *
 * *NOTE 1* vApplicationSetupTimerInterrupt() is called by the kernel to let
 * the application set up a timer to generate the tick interrupt.  In this
 * example a compare match timer is used for this purpose.
 *
 * *NOTE 2* The CPU must be in Supervisor mode when the scheduler is started.
 * The PowerON_Reset_PC() supplied in resetprg.c with this demo has
 * Change_PSW_PM_to_UserMode() commented out to ensure this is the case.
 *
 * *NOTE 3* The IntQueue common demo tasks test interrupt nesting and make use
 * of all the 8bit timers (as two cascaded 16bit units).
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

/* Demo specific tasks. */
#include "ButtonAndLCD.h"

/* Peripheral includes. */
#include "lcd.h"

/* Values that are passed into the reg test tasks using the task parameter.  
The tasks check that the values are passed in correctly. */
#define mainREG_TEST_1_PARAMETER	( 0x12121212UL )
#define mainREG_TEST_2_PARAMETER	( 0x12345678UL )

/* Priorities at which the tasks are created. */
#define mainQUEUE_POLL_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainSEM_TEST_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainCREATOR_TASK_PRIORITY   ( tskIDLE_PRIORITY + 3 )
#define mainFLASH_TASK_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainINTEGER_TASK_PRIORITY   ( tskIDLE_PRIORITY )
#define mainGEN_QUEUE_TASK_PRIORITY	( tskIDLE_PRIORITY )
#define mainFLOP_TASK_PRIORITY		( tskIDLE_PRIORITY )

/* The LED toggled by the check timer. */
#define mainCHECK_LED				( 3 )

/* The period at which the check timer will expire, in ms, provided no errors
have been reported by any of the standard demo tasks.  ms are converted to the
equivalent in ticks using the portTICK_RATE_MS constant. */
#define mainCHECK_TIMER_PERIOD_MS			( 5000UL / portTICK_RATE_MS )

/* The period at which the check timer will expire, in ms, if an error has been
reported in one of the standard demo tasks.  ms are converted to the equivalent
in ticks using the portTICK_RATE_MS constant. */
#define mainERROR_CHECK_TIMER_PERIOD_MS 	( 200UL / portTICK_RATE_MS )

/* A block time of zero simple means "Don't Block". */
#define mainDONT_BLOCK				( 0UL )

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
void vApplicationStackOverflowHook( xTaskHandle pxTask, signed char *pcTaskName );

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
static void prvCheckTimerCallback( xTimerHandle xTimer );


/*-----------------------------------------------------------*/

/* Variables that are incremented on each iteration of the reg test tasks -
provided the tasks have not reported any errors.  The check timer inspects these
variables to ensure they are still incrementing as expected.  If a variable
stops incrementing then it is likely that its associate task has stalled. */
unsigned long ulRegTest1CycleCount = 0UL, ulRegTest2CycleCount = 0UL;

/* The check timer.  This uses prvCheckTimerCallback() as its callback
function. */
static xTimerHandle xCheckTimer = NULL;

/*-----------------------------------------------------------*/

void main(void)
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

	/* The button and LCD tasks, as described at the top of this file. */
	vStartButtonAndLCDDemo();

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

	/* If all is well we will never reach here as the scheduler will now be
	running.  If we do reach here then it is likely that there was insufficient
	heap available for the idle task to be created. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvCheckTimerCallback( xTimerHandle xTimer )
{
static long lChangedTimerPeriodAlready = pdFALSE, lErrorStatus = pdPASS;
static volatile unsigned long ulLastRegTest1CycleCount = 0UL, ulLastRegTest2CycleCount = 0UL;

	/* Check the standard demo tasks are running without error. */
	if( xAreGenericQueueTasksStillRunning() != pdTRUE )
	{
		lErrorStatus = pdFAIL;
	}
	else if( xAreQueuePeekTasksStillRunning() != pdTRUE )
	{
		lErrorStatus = pdFAIL;
	}
	else if( xAreBlockingQueuesStillRunning() != pdTRUE )
	{
		lErrorStatus = pdFAIL;
	}
	else if( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
	{
		lErrorStatus = pdFAIL;
	}
	else if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	{
		lErrorStatus = pdFAIL;
	}
	else if( xArePollingQueuesStillRunning() != pdTRUE )
	{
		lErrorStatus = pdFAIL;
	}
	else if( xIsCreateTaskStillRunning() != pdTRUE )
	{
		lErrorStatus = pdFAIL;
	}
	else if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
	{
		lErrorStatus = pdFAIL;
	}
	else if( xAreRecursiveMutexTasksStillRunning() != pdTRUE )
	{
		lErrorStatus = pdFAIL;
	}
	else if( xAreIntQueueTasksStillRunning() != pdPASS )
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

	ulLastRegTest1CycleCount = ulRegTest1CycleCount;
	ulLastRegTest2CycleCount = ulRegTest2CycleCount;

	/* Toggle the check LED to give an indication of the system status.  If
	the LED toggles every 5 seconds then everything is ok.  A faster toggle
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
void vApplicationStackOverflowHook( xTaskHandle pxTask, signed char *pcTaskName )
{
	for( ;; );
}
/*-----------------------------------------------------------*/

/* This function is explained by the comments above its prototype at the top
of this file. */
void vApplicationIdleHook( void )
{
	/* If this is being executed then the kernel has been started.  Start the high
	frequency timer test as described at the top of this file.  This is only
	included in the optimised build configuration - otherwise it takes up too much
	CPU time and can disrupt other tests. */
	#ifdef INCLUDE_HIGH_FREQUENCY_TIMER_TEST
	static portBASE_TYPE xTimerTestStarted = pdFALSE;
	extern void vSetupHighFrequencyTimer( void );
		if( xTimerTestStarted == pdFALSE )
		{
			vSetupHighFrequencyTimer();
			xTimerTestStarted = pdTRUE;
		}
	#endif
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
	; causing the check timer to indicate the error.
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
	; - causing the check timer to indicate the error.
	BRA RegTest2Error
}
/*-----------------------------------------------------------*/

