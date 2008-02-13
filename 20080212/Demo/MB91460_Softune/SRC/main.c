/* THIS SAMPLE CODE IS PROVIDED AS IS AND IS SUBJECT TO ALTERATIONS. FUJITSU */
/* MICROELECTRONICS ACCEPTS NO RESPONSIBILITY OR LIABILITY FOR ANY ERRORS OR */
/* ELIGIBILITY FOR ANY PURPOSES.											 */
/*				 (C) Fujitsu Microelectronics Europe GmbH				  */
/*------------------------------------------------------------------------
  MAIN.C
  - description
  - See README.TXT for project description and disclaimer.
-------------------------------------------------------------------------*/


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
#include "PollQ.h"
#include "semtest.h"
#include "BlockQ.h"
#include "dynamic.h"
#include "flop.h"
#include "GenQTest.h"
#include "QPeek.h"
#include "BlockTim.h"
#include "death.h"
#include "taskutility.h"
#include "partest.h"
	
/* Demo task priorities. */
#define mainWATCHDOG_TASK_PRIORITY		( tskIDLE_PRIORITY + 5 )
#define mainCHECK_TASK_PRIORITY			( tskIDLE_PRIORITY + 4 )
#define mainUTILITY_TASK_PRIORITY		( tskIDLE_PRIORITY + 3 )
#define mainSEM_TEST_PRIORITY			( tskIDLE_PRIORITY + 3 )
#define mainCOM_TEST_PRIORITY			( tskIDLE_PRIORITY + 2 )
#define mainQUEUE_POLL_PRIORITY			( tskIDLE_PRIORITY + 2 )
#define mainQUEUE_BLOCK_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainDEATH_PRIORITY 				( tskIDLE_PRIORITY + 1 )
#define mainLED_TASK_PRIORITY			( tskIDLE_PRIORITY + 1 )
#define mainGENERIC_QUEUE_PRIORITY		( tskIDLE_PRIORITY )

/* Baud rate used by the COM test tasks. */
#define mainCOM_TEST_BAUD_RATE			( ( unsigned portLONG ) 19200 )

/* The frequency at which the 'Check' tasks executes.  See the comments at the 
top of the page.  When the system is operating error free the 'Check' task
toggles an LED every three seconds.  If an error is discovered in any task the
rate is increased to 500 milliseconds.  [in this case the '*' characters on the 
LCD represent LED's]*/
#define mainNO_ERROR_CHECK_DELAY		( ( portTickType ) 3000 / portTICK_RATE_MS  )
#define mainERROR_CHECK_DELAY			( ( portTickType ) 500 / portTICK_RATE_MS  )

/* The total number of LEDs available. */
#define mainNO_CO_ROUTINE_LEDs	( 8 )

/* The first LED used by the comtest tasks. */
#define mainCOM_TEST_LED		( 0x05 )

/* The LED used by the check task. */
#define mainCHECK_TEST_LED		( 0x07 )

/* The number of interrupt levels to use. */
#define mainINTERRUPT_LEVELS	( 31 )

/*---------------------------------------------------------------------------*/

/* 
 * The function that implements the Check task.  See the comments at the head
 * of the page for implementation details.
 */ 
static void vErrorChecks( void *pvParameters );

/*
 * Called by the Check task.  Returns pdPASS if all the other tasks are found
 * to be operating without error - otherwise returns pdFAIL.
 */
static portSHORT prvCheckOtherTasksAreStillRunning( void );

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
unsigned portLONG ulRegTestError = pdFALSE;

/* Variables used to ensure the register check tasks are still executing. */
static volatile unsigned portLONG ulRegTest1Counter = 0UL, ulRegTest2Counter = 0UL;

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
	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
	vStartBlockingQueueTasks ( mainQUEUE_BLOCK_PRIORITY );	
	vStartDynamicPriorityTasks();	
	vStartMathTasks( tskIDLE_PRIORITY );	
	vStartGenericQueueTasks( mainGENERIC_QUEUE_PRIORITY );
	vStartQueuePeekTasks();
	vCreateBlockTimeTasks();

	/* Start the 'Check' task which is defined in this file. */
	xTaskCreate( vErrorChecks, ( signed portCHAR * ) "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );	

	xTaskCreate( vFirstRegisterTestTask, ( signed portCHAR * ) "Reg1", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
	xTaskCreate( vSecondRegisterTestTask, ( signed portCHAR * ) "Reg2", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );

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

static void vErrorChecks( void *pvParameters )
{
portTickType xDelayPeriod = mainNO_ERROR_CHECK_DELAY, xLastExecutionTime;

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

static portSHORT prvCheckOtherTasksAreStillRunning( void )
{
portBASE_TYPE lReturn = pdPASS;
static unsigned portLONG ulLastRegTest1Counter = 0UL, ulLastRegTest2Counter = 0UL;

	/* The demo tasks maintain a count that increments every cycle of the task
	provided that the task has never encountered an error.  This function 
	checks the counts maintained by the tasks to ensure they are still being
	incremented.  A count remaining at the same value between calls therefore
	indicates that an error has been detected. */

	if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}

	if( xArePollingQueuesStillRunning() != pdTRUE )
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

	/* Are the register test tasks still running? */
	if( ulLastRegTest1Counter == ulRegTest1Counter )
	{
		lReturn = pdFAIL;
	}
	
	if( ulLastRegTest2Counter == ulRegTest2Counter )
	{
		lReturn = pdFAIL;
	}

	ulLastRegTest1Counter = ulRegTest1Counter;
	ulLastRegTest2Counter = ulRegTest2Counter;

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

/* The below callback function is called from Delayed ISR if configUSE_IDLE_HOOK 
is configured as 1. */  
#if configUSE_IDLE_HOOK == 1
	void vApplicationIdleHook( void )
	{
		/* Are we using the idle task to kick the watchdog? */
		#if WATCHDOG == WTC_IN_IDLE
			Kick_Watchdog();
		#endif

		#if configUSE_CO_ROUTINES == 1		
			vCoRoutineSchedule();
		#endif
	}
#endif
/*-----------------------------------------------------------*/

/*
The below callback function is called from Tick ISR if configUSE_TICK_HOOK 
is configured as 1. */  
#if configUSE_TICK_HOOK == 1
	void vApplicationTickHook( void )
	{
		#if WATCHDOG == WTC_IN_TICK
			Kick_Watchdog();
		#endif
	}
#endif
/*-----------------------------------------------------------*/

static void vFirstRegisterTestTask( void *pvParameters )
{
extern volatile unsigned portLONG ulCriticalNesting;

	/* Fills the registers with known values (different to the values
	used in vSecondRegisterTestTask()), then checks that the registers still
	all contain the expected value.  This is done to test the context save
	and restore mechanism as this task is swapped onto and off of the CPU.

	The critical nesting depth is also saved as part of the context so also
	check this maintains an expected value. */
	ulCriticalNesting = 0x12345678;

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
			NOP

			LDI #0x22222222, R13
			CMP R13, R1
			BNE First_Set_Error
			NOP

			LDI #0x33333333, R13
			CMP R13, R2
			BNE First_Set_Error
			NOP

			LDI #0x44444444, R13
			CMP R13, R3
			BNE First_Set_Error
			NOP

			LDI #0x55555555, R13
			CMP R13, R4
			BNE First_Set_Error
			NOP

			LDI #0x66666666, R13
			CMP R13, R5
			BNE First_Set_Error
			NOP

			LDI #0x77777777, R13
			CMP R13, R6
			BNE First_Set_Error
			NOP

			LDI #0x88888888, R13
			CMP R13, R7
			BNE First_Set_Error
			NOP

			LDI #0x99999999, R13
			CMP R13, R8
			BNE First_Set_Error
			NOP

			LDI #0xaaaaaaaa, R13
			CMP R13, R9
			BNE First_Set_Error
			NOP

			LDI #0xbbbbbbbb, R13
			CMP R13, R10
			BNE First_Set_Error
			NOP

			LDI #0xcccccccc, R13
			CMP R13, R11
			BNE First_Set_Error
			NOP

			LDI #0xdddddddd, R13
			CMP R13, R12
			BNE First_Set_Error
			NOP

			BRA First_Start_Next_Loop
			NOP

		First_Set_Error:

			; Latch that an error has occurred.
			LDI #_ulRegTestError, R0			
			LDI #0x00000001, R1
			ST R1, @R0


		First_Start_Next_Loop:


		#pragma endasm

		ulRegTest1Counter++;

		if( ulCriticalNesting != 0x12345678 )
		{
			ulRegTestError = pdTRUE;
		}
	}
}
/*-----------------------------------------------------------*/

static void vSecondRegisterTestTask( void *pvParameters )
{
extern volatile unsigned portLONG ulCriticalNesting;

	/* Fills the registers with known values (different to the values
	used in vFirstRegisterTestTask()), then checks that the registers still
	all contain the expected value.  This is done to test the context save
	and restore mechanism as this task is swapped onto and off of the CPU.

	The critical nesting depth is also saved as part of the context so also
	check this maintains an expected value. */
	ulCriticalNesting = 0x87654321;

	for( ;; )
	{
		#pragma asm
			;Load known values into each register.
			LDI	#0x11111111, R1
			LDI	#0x22222222, R2
			LDI	#0x33333333, R3
			LDI #0x44444444, R4
			LDI	#0x55555555, R5
			LDI	#0x66666666, R6
			LDI	#0x77777777, R7
			LDI	#0x88888888, R8
			LDI	#0x99999999, R9
			LDI	#0xaaaaaaaa, R10
			LDI	#0xbbbbbbbb, R11
			LDI	#0xcccccccc, R12
			LDI	#0xdddddddd, R0
			
			;Check each register still contains the expected value.
			LDI #0x11111111, R13
			CMP R13, R1
			BNE Second_Set_Error
			NOP

			LDI #0x22222222, R13
			CMP R13, R2
			BNE Second_Set_Error
			NOP

			LDI #0x33333333, R13
			CMP R13, R3
			BNE Second_Set_Error
			NOP

			LDI #0x44444444, R13
			CMP R13, R4
			BNE Second_Set_Error
			NOP

			LDI #0x55555555, R13
			CMP R13, R5
			BNE Second_Set_Error
			NOP

			LDI #0x66666666, R13
			CMP R13, R6
			BNE Second_Set_Error
			NOP

			LDI #0x77777777, R13
			CMP R13, R7
			BNE Second_Set_Error
			NOP

			LDI #0x88888888, R13
			CMP R13, R8
			BNE Second_Set_Error
			NOP

			LDI #0x99999999, R13
			CMP R13, R9
			BNE Second_Set_Error
			NOP

			LDI #0xaaaaaaaa, R13
			CMP R13, R10
			BNE Second_Set_Error
			NOP

			LDI #0xbbbbbbbb, R13
			CMP R13, R11
			BNE Second_Set_Error
			NOP

			LDI #0xcccccccc, R13
			CMP R13, R12
			BNE Second_Set_Error
			NOP

			LDI #0xdddddddd, R13
			CMP R13, R0
			BNE Second_Set_Error
			NOP

			BRA Second_Start_Next_Loop
			NOP

		Second_Set_Error:

			; Latch that an error has occurred.
			LDI #_ulRegTestError, R0			
			LDI #0x00000001, R1
			ST R1, @R0


		Second_Start_Next_Loop:


		#pragma endasm

		ulRegTest2Counter++;

		if( ulCriticalNesting != 0x87654321 )
		{
			ulRegTestError = pdTRUE;
		}
	}
}
/*-----------------------------------------------------------*/


