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
#include "comtest.h"
#include "PollQ.h"
#include "semtest.h"
#include "BlockQ.h"
#include "dynamic.h"
#include "flop.h"
#include "crflash.h"
#include "crhook.h"
#include "GenQTest.h"
#include "QPeek.h"
#include "BlockTim.h"
#include "death.h"
#include "taskutility.h"
	
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
#define ledNUMBER_OF_LEDS		( 8 )

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
	vStartFlashCoRoutines(ledNUMBER_OF_LEDS);	
	vStartHookCoRoutines();
	vStartGenericQueueTasks( mainGENERIC_QUEUE_PRIORITY );
	vStartQueuePeekTasks();
	vCreateBlockTimeTasks();
	
	/* Start the 'Check' task which is defined in this file. */
	xTaskCreate( vErrorChecks, ( signed portCHAR * ) "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );	

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
portTickType xDelayPeriod = mainNO_ERROR_CHECK_DELAY;

	/* Cycle for ever, delaying then checking all the other tasks are still
	operating without error. */
	for( ;; )
	{
		/* Wait until it is time to check again.  The time we wait here depends
		on whether an error has been detected or not.  When an error is 
		detected the time is shortened resulting in a faster LED flash rate. */
		vTaskDelay( xDelayPeriod );

		/* See if the other tasks are all ok. */
		if( prvCheckOtherTasksAreStillRunning() != pdPASS )
		{
			/* An error occurred in one of the tasks so shorten the delay 
			period - which has the effect of increasing the frequency of the
			LED toggle. */
			xDelayPeriod = mainERROR_CHECK_DELAY;
		}

		/* Flash! */
		vParTestToggleLED(mainCHECK_TEST_LED);
	}
}
/*-----------------------------------------------------------*/

static portSHORT prvCheckOtherTasksAreStillRunning( void )
{
static portBASE_TYPE xErrorOccurred = pdFALSE;

	/* The demo tasks maintain a count that increments every cycle of the task
	provided that the task has never encountered an error.  This function 
	checks the counts maintained by the tasks to ensure they are still being
	incremented.  A count remaining at the same value between calls therefore
	indicates that an error has been detected. */

	if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
	{
		xErrorOccurred = pdTRUE
	}

	if( xArePollingQueuesStillRunning() != pdTRUE )
	{
		xErrorOccurred = pdTRUE
	}

	if( xAreComTestTasksStillRunning() != pdTRUE )
	{
		xErrorOccurred = pdTRUE
	}
	
	if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	{
		xErrorOccurred = pdTRUE
	}
	
	if( xAreBlockingQueuesStillRunning() != pdTRUE )
	{
		xErrorOccurred = pdTRUE
	}
	
	if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
	{
		xErrorOccurred = pdTRUE
	}
	
	if( xAreMathsTaskStillRunning() != pdTRUE )
	{
		xErrorOccurred = pdTRUE
	}
	
	if( xAreFlashCoRoutinesStillRunning() != pdTRUE ) 
	{
		xErrorOccurred = pdTRUE
	}
	
	if( xAreHookCoRoutinesStillRunning() != pdTRUE )
	{
		xErrorOccurred = pdTRUE
	}
	
	if( xIsCreateTaskStillRunning() != pdTRUE )
	{
		xErrorOccurred = pdTRUE
	}
	
	if( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
	{
		xErrorOccurred = pdTRUE
	}
	
	if ( xAreGenericQueueTasksStillRunning() != pdTRUE )
	{
		xErrorOccurred = pdTRUE
	}
	
	if ( xAreQueuePeekTasksStillRunning() != pdTRUE )
	{
		xErrorOccurred = pdTRUE
	}
	
	return sNoErrorFound;
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

/* The below callback function is called from Tick ISR if configUSE_TICK_HOOK 
is configured as 1. This function needs to be uncommented if the crhook.c
is not used, since the crhook.c has also defined vApplicationTickHook().  */  
#if configUSE_TICK_HOOK == 1
	void vApplicationTickHook ( void )
	{
		/* Are we using the tick interrupt to kick the watchdog? */
		#if WATCHDOG == WTC_IN_TICK
			Kick_Watchdog();
		#endif
	}
#endif
/*-----------------------------------------------------------*/

/* The below callback function is called from Delayed ISR if configUSE_IDLE_HOOK 
is configured as 1. */  
#if configUSE_IDLE_HOOK == 1
	void vApplicationIdleHook ( void )
	{
		/* Are we using the idle task to kick the watchdog? */
		#if WATCHDOG == WTC_IN_IDLE
			Kick_Watchdog();
		#endif
		
		vCoRoutineSchedule();
	}
#endif
