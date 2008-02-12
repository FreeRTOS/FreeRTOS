/* THIS SAMPLE CODE IS PROVIDED AS IS AND IS SUBJECT TO ALTERATIONS. FUJITSU */
/* MICROELECTRONICS ACCEPTS NO RESPONSIBILITY OR LIABILITY FOR ANY ERRORS OR */
/* ELIGIBILITY FOR ANY PURPOSES.                                             */
/*                 (C) Fujitsu Microelectronics Europe GmbH                  */
/*---------------------------------------------------------------------------
  MAIN.C
  - description
  - See README.TXT for project description and disclaimer.

/*---------------------------------------------------------------------------*/

/* 16FX includes */
#include "mb96348hs.h"

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"
#include <watchdog.h>
#include <config.h>

/*---------------------------------------------------------------------------*/

/* Demo task priorities. */
#define WTC_TASK_PRIORITY				( tskIDLE_PRIORITY + 5 )
#define mainCHECK_TASK_PRIORITY			( tskIDLE_PRIORITY + 4 )
#define TASK_UTILITY_PRIORITY			( tskIDLE_PRIORITY + 3 )
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

/*---------------------------------------------------------------------------*/
#define ledNUMBER_OF_LEDS		8
#define mainCOM_TEST_LED		0x05
#define mainCHECK_TEST_LED		0x07
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

/*---------------------------------------------------------------------------*/

static unsigned portCHAR sState[2] = {0xFF, 0xFF};
/*---------------------------------------------------------------------------
 * The below callback function is called from Tick ISR if configUSE_TICK_HOOK 
 * is configured as 1.
 *---------------------------------------------------------------------------*/  
/*void vApplicationTickHook ( void )
{
#if WATCHDOG == WTC_IN_TICK
	Kick_Watchdog();
#endif
}*/

/*---------------------------------------------------------------------------
 * The below callback function is called from Delayed ISR if configUSE_IDLE_HOOK 
 * is configured as 1.
 *---------------------------------------------------------------------------*/   
void vApplicationIdleHook ( void )
{
#if WATCHDOG == WTC_IN_IDLE
	Kick_Watchdog();
#endif

#if ( INCLUDE_StartFlashCoRoutines == 1 || INCLUDE_StartHookCoRoutines == 1 ) 	
	vCoRoutineSchedule();
#endif	
}
/*---------------------------------------------------------------------------
 * Initialize Port 00
 *---------------------------------------------------------------------------*/ 
static void prvInitPort00( void )
{
	DDR00 = 0xFF;
	PDR00 = 0xFF;
	DDR09 = 0xFF;
	PDR09 = 0xFF;
}
/*---------------------------------------------------------------------------
 * Setup the hardware
 *---------------------------------------------------------------------------*/ 
static void prvSetupHardware( void )
{
	prvInitPort00();

#if WATCHDOG != WTC_NONE	
	InitWatchdog();
#endif
}

/*---------------------------------------------------------------------------
 * main()
 *---------------------------------------------------------------------------*/ 
void main(void)
{
	InitIrqLevels();			/* Initialize interrupts */
	__set_il(7);                /* Allow all levels      */
		
	prvSetupHardware();
	
#if WATCHDOG == WTC_IN_TASK	
	vStartWatchdogTask( WTC_TASK_PRIORITY );
#endif

	/* Start the standard demo application tasks. */

#if ( INCLUDE_StartLEDFlashTasks == 1 )
	vStartLEDFlashTasks( mainLED_TASK_PRIORITY );
#endif
	
#if ( INCLUDE_StartIntegerMathTasks == 1 )	
	vStartIntegerMathTasks( tskIDLE_PRIORITY );
#endif

#if ( INCLUDE_AltStartComTestTasks == 1 )	
	vAltStartComTestTasks( mainCOM_TEST_PRIORITY, mainCOM_TEST_BAUD_RATE, mainCOM_TEST_LED - 1 );
#endif

#if ( INCLUDE_StartPolledQueueTasks == 1 )		
	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
#endif
	
#if ( INCLUDE_StartSemaphoreTasks == 1 )			
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
#endif

#if ( INCLUDE_StartBlockingQueueTasks == 1 )			
	vStartBlockingQueueTasks ( mainQUEUE_BLOCK_PRIORITY );
#endif
	
#if ( INCLUDE_StartDynamicPriorityTasks == 1 )	
	vStartDynamicPriorityTasks();
#endif
	
#if ( INCLUDE_StartMathTasks == 1 )
	vStartMathTasks( tskIDLE_PRIORITY );
#endif
	
#if ( INCLUDE_StartFlashCoRoutines == 1 )	
	vStartFlashCoRoutines( ledNUMBER_OF_LEDS );
#endif	
	
#if ( INCLUDE_StartHookCoRoutines == 1 )
	vStartHookCoRoutines();
#endif
	
#if ( INCLUDE_StartGenericQueueTasks == 1 )
	vStartGenericQueueTasks( mainGENERIC_QUEUE_PRIORITY );
#endif	

#if ( INCLUDE_StartQueuePeekTasks == 1 )
	vStartQueuePeekTasks();
#endif
	
#if ( INCLUDE_CreateBlockTimeTasks == 1 )
	vCreateBlockTimeTasks();
#endif
	
#if ( INCLUDE_CreateSuicidalTasks == 1 )
	vCreateSuicidalTasks( mainDEATH_PRIORITY );
#endif

#if ( INCLUDE_TraceListTasks == 1 )
	vTraceListTasks( TASK_UTILITY_PRIORITY );
#endif
	
	/* Start the 'Check' task which is defined in this file. */
	xTaskCreate( vErrorChecks, ( signed portCHAR * ) "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );	

	vTaskStartScheduler();
	
	/* Should not reach here */
	while (1)
	{
		__asm(" NOP "); // 
	}
}

/*-----------------------------------------------------------*/
void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
	if (uxLED < ledNUMBER_OF_LEDS)
	{
		vTaskSuspendAll();
		
		/* Toggle the state of the single genuine on board LED. */
		if( (sState[0] & ((portCHAR)(1 << uxLED))) == 0)	
		{
			PDR09 |= (1 << uxLED);
			sState[0] |= (1 << uxLED);
		}
		else
		{
			PDR09 &= ~(1 << uxLED);
			sState[0] &= ~(1 << uxLED);
		}
		xTaskResumeAll();
	}
	else
	{
		vTaskSuspendAll();
		
		uxLED -= ledNUMBER_OF_LEDS;
		
		if( (sState[1] & ((portCHAR)(1 << uxLED))) == 0)	
		{
			PDR00 |= (1 << uxLED);
			sState[1] |= (1 << uxLED);
		}
		else
		{
			PDR00 &= ~(1 << uxLED);
			sState[1] &= ~(1 << uxLED);
		}
		
		xTaskResumeAll();
	}
}
/*-----------------------------------------------------------*/
void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
	/* Set or clear the output [in this case show or hide the '*' character. */
	if( uxLED < ledNUMBER_OF_LEDS )
	{
		vTaskSuspendAll();
		{
			if( xValue )
			{
				PDR09 &= ~(1 << uxLED);
				sState[0] &= ~(1 << uxLED);
			}
			else
			{
				PDR09 |= (1 << uxLED);
				sState[0] |= (1 << uxLED);			}
			}
		xTaskResumeAll();
	}
	else
	{
		vTaskSuspendAll();
		{
			if( xValue )
			{
				PDR00 &= ~(1 << uxLED);
				sState[1] &= ~(1 << uxLED);
			}
			else
			{
				PDR00 |= (1 << uxLED);
				sState[1] |= (1 << uxLED);
			}
		}
		xTaskResumeAll();
	}
}
/*-----------------------------------------------------------*/

static void vErrorChecks( void *pvParameters )
{
static volatile unsigned portLONG ulDummyVariable = 3UL;
portTickType xDelayPeriod = mainNO_ERROR_CHECK_DELAY;

	( void ) pvParameters;
	/* Cycle for ever, delaying then checking all the other tasks are still
	operating without error. */
	for( ;; )
	{
		/* Wait until it is time to check again.  The time we wait here depends
		on whether an error has been detected or not.  When an error is 
		detected the time is shortened resulting in a faster LED flash rate. */
		vTaskDelay( xDelayPeriod );

		/* Perform a bit of 32bit maths to ensure the registers used by the 
		integer tasks get some exercise outside of the integer tasks 
		themselves. The result here is not important we are just deliberately
		changing registers used by other tasks to ensure that their context
		switch is operating as required. - see the demo application 
		documentation for more info. */
		ulDummyVariable *= 3UL;
		
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
static portSHORT sNoErrorFound = pdTRUE;

	/* The demo tasks maintain a count that increments every cycle of the task
	provided that the task has never encountered an error.  This function 
	checks the counts maintained by the tasks to ensure they are still being
	incremented.  A count remaining at the same value between calls therefore
	indicates that an error has been detected.  Only tasks that do not flash
	an LED are checked. */
	
#if ( INCLUDE_StartIntegerMathTasks == 1 )
	if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
	{
		sNoErrorFound = pdFALSE;
	}
#endif


#if ( INCLUDE_AltStartComTestTasks == 1 )
	if( xAreComTestTasksStillRunning() != pdTRUE )
	{
		sNoErrorFound = pdFALSE;
	}
#endif	
	

#if ( INCLUDE_StartPolledQueueTasks == 1 )
	if( xArePollingQueuesStillRunning() != pdTRUE )
	{
		sNoErrorFound = pdFALSE;
	}
#endif
	

#if ( INCLUDE_StartSemaphoreTasks == 1 )	
	if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	{
		sNoErrorFound = pdFALSE;
	}
#endif
	

#if ( INCLUDE_StartBlockingQueueTasks == 1 )	
	if( xAreBlockingQueuesStillRunning() != pdTRUE )
	{
		sNoErrorFound = pdFALSE;
	}
#endif
	

#if ( INCLUDE_StartDynamicPriorityTasks == 1 )
	if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
	{
		sNoErrorFound = pdFALSE;
	}
#endif
	

#if ( INCLUDE_StartMathTasks == 1 )
	if( xAreMathsTaskStillRunning() != pdTRUE )
	{
		sNoErrorFound = pdFALSE;
	}
#endif
	

#if ( INCLUDE_StartFlashCoRoutines == 1 )	
	if( xAreFlashCoRoutinesStillRunning() != pdTRUE ) 
	{
		sNoErrorFound = pdFALSE;
	}
#endif
	
#if ( INCLUDE_StartHookCoRoutines == 1 )	
	if( xAreHookCoRoutinesStillRunning() != pdTRUE )
	{
		sNoErrorFound = pdFALSE;
	}
#endif

#if ( INCLUDE_StartGenericQueueTasks == 1 )	
	if ( xAreGenericQueueTasksStillRunning() != pdTRUE )
    {
    	sNoErrorFound = pdFALSE;
    }
#endif
    
#if ( INCLUDE_StartQueuePeekTasks == 1 )	
	if ( xAreQueuePeekTasksStillRunning() != pdTRUE )
    {
    	sNoErrorFound = pdFALSE;
    }
#endif
    
#if ( INCLUDE_CreateBlockTimeTasks == 1 )    
    if( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
	{
		sNoErrorFound = pdFALSE;
    }
#endif
    
#if ( INCLUDE_CreateSuicidalTasks == 1 )
    if( xIsCreateTaskStillRunning() != pdTRUE )
    {
    	sNoErrorFound = pdFALSE;
    }
#endif

	return sNoErrorFound;
}

/*---------------------------------------------------------------------------*/ 