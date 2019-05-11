/*
 * FreeRTOS Kernel V10.2.1
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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


/*
 * Creates all the demo application tasks, then starts the scheduler.  The WEB
 * documentation provides more details of the demo application tasks.
 *
 * In addition to the standard demo tasks, the follow demo specific tasks are
 * create:
 *
 * The "Check" task.  This only executes every three seconds but has the highest
 * priority so is guaranteed to get processor time.  Its main function is to
 * check that all the other tasks are still operational.  Most tasks maintain
 * a unique count that is incremented each time the task successfully completes
 * its function.  Should any error occur within such a task the count is
 * permanently halted.  The check task inspects the count of each task to ensure
 * it has changed since the last time the check task executed.  If all the count
 * variables have changed all the tasks are still executing error free, and the
 * check task toggles the onboard LED.  Should any task contain an error at any time
 * the LED toggle rate will change from 3 seconds to 500ms.
 *
 * The "Register Check" tasks.  These tasks fill the CPU registers with known
 * values, then check that each register still contains the expected value 0 the
 * discovery of an unexpected value being indicative of an error in the RTOS
 * context switch mechanism.  The register check tasks operate at low priority
 * so are switched in and out frequently.
 *
 * The "Trace Utility" task.  This can be used to obtain trace and debug
 * information via UART5.
 */


/* Hardware specific includes. */
#include "mb91467d.h"
#include "vectors.h"
#include "watchdog.h"

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo app includes. */
#include "flash.h"
#include "integer.h"
#include "comtest2.h"
#include "semtest.h"
#include "BlockQ.h"
#include "dynamic.h"
#include "flop.h"
#include "GenQTest.h"
#include "QPeek.h"
#include "blocktim.h"
#include "death.h"
#include "taskutility.h"
#include "partest.h"
#include "crflash.h"

/* Demo task priorities. */
#define mainWATCHDOG_TASK_PRIORITY		( tskIDLE_PRIORITY + 5 )
#define mainCHECK_TASK_PRIORITY			( tskIDLE_PRIORITY + 4 )
#define mainUTILITY_TASK_PRIORITY		( tskIDLE_PRIORITY )
#define mainSEM_TEST_PRIORITY			( tskIDLE_PRIORITY + 3 )
#define mainCOM_TEST_PRIORITY			( tskIDLE_PRIORITY + 2 )
#define mainQUEUE_BLOCK_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainDEATH_PRIORITY 				( tskIDLE_PRIORITY + 1 )
#define mainLED_TASK_PRIORITY			( tskIDLE_PRIORITY + 1 )
#define mainGENERIC_QUEUE_PRIORITY		( tskIDLE_PRIORITY )

/* Baud rate used by the COM test tasks. */
#define mainCOM_TEST_BAUD_RATE			( ( unsigned long ) 19200 )

/* The frequency at which the 'Check' tasks executes.  See the comments at the
top of the page.  When the system is operating error free the 'Check' task
toggles an LED every three seconds.  If an error is discovered in any task the
rate is increased to 500 milliseconds.  [in this case the '*' characters on the
LCD represent LEDs]*/
#define mainNO_ERROR_CHECK_DELAY		( ( TickType_t ) 3000 / portTICK_PERIOD_MS  )
#define mainERROR_CHECK_DELAY			( ( TickType_t ) 500 / portTICK_PERIOD_MS  )

/* The total number of LEDs available. */
#define mainNO_CO_ROUTINE_LEDs	( 8 )

/* The first LED used by the comtest tasks. */
#define mainCOM_TEST_LED		( 0x05 )

/* The LED used by the check task. */
#define mainCHECK_TEST_LED		( 0x07 )

/* The number of interrupt levels to use. */
#define mainINTERRUPT_LEVELS	( 31 )

/* The number of 'flash' co-routines to create - each toggles a different LED. */
#define mainNUM_FLASH_CO_ROUTINES	( 8 )

/*---------------------------------------------------------------------------*/

/*
 * The function that implements the Check task.  See the comments at the head
 * of the page for implementation details.
 */
static void prvErrorChecks( void *pvParameters );

/*
 * Called by the Check task.  Returns pdPASS if all the other tasks are found
 * to be operating without error - otherwise returns pdFAIL.
 */
static short prvCheckOtherTasksAreStillRunning( void );

/*
 * Setup the microcontroller as used by this demo.
 */
static void prvSetupHardware( void );

/*
 * Tasks that test the context switch mechanism by filling the CPU registers
 * with known values then checking that each register contains the value
 * expected.  Each of the two tasks use different values, and as low priority
 * tasks, get swapped in and out regularly.
 */
static void vFirstRegisterTestTask( void *pvParameters );
static void vSecondRegisterTestTask( void *pvParameters );

/*---------------------------------------------------------------------------*/

/* The variable that is set to true should an error be found in one of the
register test tasks. */
unsigned long ulRegTestError = pdFALSE;

/*---------------------------------------------------------------------------*/

/* Start all the demo application tasks, then start the scheduler. */
void main(void)
{
	/* Initialise the hardware ready for the demo. */
	prvSetupHardware();

	/* Start the standard demo application tasks. */
	vStartLEDFlashTasks( mainLED_TASK_PRIORITY );
	vStartIntegerMathTasks( tskIDLE_PRIORITY );
	vAltStartComTestTasks( mainCOM_TEST_PRIORITY, mainCOM_TEST_BAUD_RATE, mainCOM_TEST_LED - 1 );
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
	vStartBlockingQueueTasks ( mainQUEUE_BLOCK_PRIORITY );
	vStartDynamicPriorityTasks();
	vStartMathTasks( tskIDLE_PRIORITY );
	vStartGenericQueueTasks( mainGENERIC_QUEUE_PRIORITY );
	vStartQueuePeekTasks();
	vCreateBlockTimeTasks();
	vStartFlashCoRoutines( mainNUM_FLASH_CO_ROUTINES );

	/* Start the 'Check' task which is defined in this file. */
	xTaskCreate( prvErrorChecks, "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

	/* Start the 'Register Test' tasks as described at the top of this file. */
	xTaskCreate( vFirstRegisterTestTask, "Reg1", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
	xTaskCreate( vSecondRegisterTestTask, "Reg2", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );

	/* Start the task that write trace information to the UART. */
	vUtilityStartTraceTask( mainUTILITY_TASK_PRIORITY );

	/* If we are going to service the watchdog from within a task, then create
	the task here. */
	#if WATCHDOG == WTC_IN_TASK
		vStartWatchdogTask( mainWATCHDOG_TASK_PRIORITY );
	#endif

	/* The suicide tasks must be started last as they record the number of other
	tasks that exist within the system.  The value is then used to ensure at run
	time the number of tasks that exists is within expected bounds. */
	vCreateSuicidalTasks( mainDEATH_PRIORITY );

	/* Now start the scheduler.  Following this call the created tasks should
	be executing. */
	vTaskStartScheduler( );

	/* vTaskStartScheduler() will only return if an error occurs while the
	idle task is being created. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvErrorChecks( void *pvParameters )
{
TickType_t xDelayPeriod = mainNO_ERROR_CHECK_DELAY, xLastExecutionTime;

	/* Initialise xLastExecutionTime so the first call to vTaskDelayUntil()
	works correctly. */
	xLastExecutionTime = xTaskGetTickCount();

	/* Cycle for ever, delaying then checking all the other tasks are still
	operating without error. */
	for( ;; )
	{
		/* Wait until it is time to check again.  The time we wait here depends
		on whether an error has been detected or not.  When an error is
		detected the time is shortened resulting in a faster LED flash rate. */
		/* Perform this check every mainCHECK_DELAY milliseconds. */
		vTaskDelayUntil( &xLastExecutionTime, xDelayPeriod );

		/* See if the other tasks are all ok. */
		if( prvCheckOtherTasksAreStillRunning() != pdPASS )
		{
			/* An error occurred in one of the tasks so shorten the delay
			period - which has the effect of increasing the frequency of the
			LED toggle. */
			xDelayPeriod = mainERROR_CHECK_DELAY;
		}

		/* Flash! */
		vParTestToggleLED( mainCHECK_TEST_LED );
	}
}
/*-----------------------------------------------------------*/

static short prvCheckOtherTasksAreStillRunning( void )
{
portBASE_TYPE lReturn = pdPASS;

	/* The demo tasks maintain a count that increments every cycle of the task
	provided that the task has never encountered an error.  This function
	checks the counts maintained by the tasks to ensure they are still being
	incremented.  A count remaining at the same value between calls therefore
	indicates that an error has been detected. */

	if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}

	if( xAreComTestTasksStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}

	if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}

	if( xAreBlockingQueuesStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}

	if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}

	if( xAreMathsTaskStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}

	if( xIsCreateTaskStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}

	if( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}

	if ( xAreGenericQueueTasksStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}

	if ( xAreQueuePeekTasksStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}

	/* Have the register test tasks found any errors? */
	if( ulRegTestError != pdFALSE )
	{
		lReturn = pdFAIL;
	}

	return lReturn;
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	/* Allow all interrupt levels. */
	__set_il( mainINTERRUPT_LEVELS );

	/* Initialise interrupts. */
	InitIrqLevels();

	/* Initialise the ports used by the LEDs. */
	vParTestInitialise();

	/* If we are going to use the watchdog, then initialise it now. */
	#if WATCHDOG != WTC_NONE
		InitWatchdog();
	#endif
}
/*-----------------------------------------------------------*/

/* Idle hook function. */
#if configUSE_IDLE_HOOK == 1
	void vApplicationIdleHook( void )
	{
		/* Are we using the idle task to kick the watchdog?  See watchdog.h
		for watchdog kicking options. Note this is for demonstration only
		and is not a suggested method of servicing the watchdog in a real
		application. */
		#if WATCHDOG == WTC_IN_IDLE
			Kick_Watchdog();
		#endif

		vCoRoutineSchedule();
	}
#else
	#if WATCHDOG == WTC_IN_IDLE
		#error configUSE_IDLE_HOOK must be set to 1 in FreeRTOSConfig.h if the watchdog is being cleared in the idle task hook.
	#endif
#endif

/*-----------------------------------------------------------*/

/* Tick hook function. */
#if configUSE_TICK_HOOK == 1
	void vApplicationTickHook( void )
	{
		/* Are we using the tick to kick the watchdog?  See watchdog.h
		for watchdog kicking options.  Note this is for demonstration
		only and is not a suggested method of servicing the watchdog in
		a real application. */
		#if WATCHDOG == WTC_IN_TICK
			Kick_Watchdog();
		#endif
	}
#else
	#if WATCHDOG == WTC_IN_TICK
		#error configUSE_TICK_HOOK must be set to 1 in FreeRTOSConfig.h if the watchdog is being cleared in the tick hook.
	#endif
#endif
/*-----------------------------------------------------------*/

static void vFirstRegisterTestTask( void *pvParameters )
{
extern volatile unsigned long ulCriticalNesting;

	/* Fills the registers with known values (different to the values
	used in vSecondRegisterTestTask()), then checks that the registers still
	all contain the expected value.  This is done to test the context save
	and restore mechanism as this task is swapped onto and off of the CPU. */

	for( ;; )
	{
		#pragma asm
			;Load known values into each register.
			LDI	#0x11111111, R0
			LDI	#0x22222222, R1
			LDI	#0x33333333, R2
			LDI #0x44444444, R3
			LDI	#0x55555555, R4
			LDI	#0x66666666, R5
			LDI	#0x77777777, R6
			LDI	#0x88888888, R7
			LDI	#0x99999999, R8
			LDI	#0xaaaaaaaa, R9
			LDI	#0xbbbbbbbb, R10
			LDI	#0xcccccccc, R11
			LDI	#0xdddddddd, R12

			;Check each register still contains the expected value.
			LDI #0x11111111, R13
			CMP R13, R0
			BNE First_Set_Error

			LDI #0x22222222, R13
			CMP R13, R1
			BNE First_Set_Error

			LDI #0x33333333, R13
			CMP R13, R2
			BNE First_Set_Error

			LDI #0x44444444, R13
			CMP R13, R3
			BNE First_Set_Error

			LDI #0x55555555, R13
			CMP R13, R4
			BNE First_Set_Error

			LDI #0x66666666, R13
			CMP R13, R5
			BNE First_Set_Error

			LDI #0x77777777, R13
			CMP R13, R6
			BNE First_Set_Error

			LDI #0x88888888, R13
			CMP R13, R7
			BNE First_Set_Error

			LDI #0x99999999, R13
			CMP R13, R8
			BNE First_Set_Error

			LDI #0xaaaaaaaa, R13
			CMP R13, R9
			BNE First_Set_Error

			LDI #0xbbbbbbbb, R13
			CMP R13, R10
			BNE First_Set_Error

			LDI #0xcccccccc, R13
			CMP R13, R11
			BNE First_Set_Error

			LDI #0xdddddddd, R13
			CMP R13, R12
			BNE First_Set_Error

			BRA First_Start_Next_Loop

		First_Set_Error:

			; Latch that an error has occurred.
			LDI #_ulRegTestError, R0
			LDI #0x00000001, R1
			ST R1, @R0


		First_Start_Next_Loop:


		#pragma endasm
	}
}
/*-----------------------------------------------------------*/

static void vSecondRegisterTestTask( void *pvParameters )
{
extern volatile unsigned long ulCriticalNesting;

	/* Fills the registers with known values (different to the values
	used in vFirstRegisterTestTask()), then checks that the registers still
	all contain the expected value.  This is done to test the context save
	and restore mechanism as this task is swapped onto and off of the CPU. */

	for( ;; )
	{
		#pragma asm
			;Load known values into each register.
			LDI	#0x11111111, R1
			LDI	#0x22222222, R2
			INT #40H
			LDI	#0x33333333, R3
			LDI #0x44444444, R4
			LDI	#0x55555555, R5
			LDI	#0x66666666, R6
			LDI	#0x77777777, R7
			LDI	#0x88888888, R8
			LDI	#0x99999999, R9
			INT #40H
			LDI	#0xaaaaaaaa, R10
			LDI	#0xbbbbbbbb, R11
			LDI	#0xcccccccc, R12
			LDI	#0xdddddddd, R0

			;Check each register still contains the expected value.
			LDI #0x11111111, R13
			CMP R13, R1
			BNE Second_Set_Error

			LDI #0x22222222, R13
			CMP R13, R2
			BNE Second_Set_Error

			LDI #0x33333333, R13
			CMP R13, R3
			BNE Second_Set_Error

			LDI #0x44444444, R13
			CMP R13, R4
			BNE Second_Set_Error

			LDI #0x55555555, R13
			CMP R13, R5
			BNE Second_Set_Error

			INT #40H

			LDI #0x66666666, R13
			CMP R13, R6
			BNE Second_Set_Error

			LDI #0x77777777, R13
			CMP R13, R7
			BNE Second_Set_Error

			LDI #0x88888888, R13
			CMP R13, R8
			BNE Second_Set_Error

			LDI #0x99999999, R13
			CMP R13, R9
			BNE Second_Set_Error

			INT #40H

			LDI #0xaaaaaaaa, R13
			CMP R13, R10
			BNE Second_Set_Error

			LDI #0xbbbbbbbb, R13
			CMP R13, R11
			BNE Second_Set_Error

			LDI #0xcccccccc, R13
			CMP R13, R12
			BNE Second_Set_Error

			LDI #0xdddddddd, R13
			CMP R13, R0
			BNE Second_Set_Error

			BRA Second_Start_Next_Loop

		Second_Set_Error:

			; Latch that an error has occurred.
			LDI #_ulRegTestError, R0
			LDI #0x00000001, R1
			ST R1, @R0


		Second_Start_Next_Loop:


		#pragma endasm
	}
}
/*-----------------------------------------------------------*/


