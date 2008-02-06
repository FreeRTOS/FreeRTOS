/* THIS SAMPLE CODE IS PROVIDED AS IS AND IS SUBJECT TO ALTERATIONS. FUJITSU */
/* MICROELECTRONICS ACCEPTS NO RESPONSIBILITY OR LIABILITY FOR ANY ERRORS OR */
/* ELIGIBILITY FOR ANY PURPOSES.                                             */
/*                 (C) Fujitsu Microelectronics Europe GmbH                  */
/*------------------------------------------------------------------------
  MAIN.C
  - description
  - See README.TXT for project description and disclaimer.
-------------------------------------------------------------------------*/
/*************************@INCLUDE_START************************/
#include "mb91467d.h"
#include "vectors.h"
#include "FreeRTOS.h"
#include "task.h"
#include "watchdog.h"

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

static unsigned portSHORT sState[ledNUMBER_OF_LEDS] = {pdFALSE};
static unsigned portSHORT sState1[ledNUMBER_OF_LEDS] = {pdFALSE};

/*---------------------------------------------------------------------------
 * The below callback function is called from Tick ISR if configUSE_TICK_HOOK 
 * is configured as 1. This function needs to be uncommented if the crhook.c
 * is not used, since the crhook.c has also defined vApplicationTickHook(). 
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
	
	vCoRoutineSchedule();
}

/*---------------------------------------------------------------------------
 * Initialize Port 00
 *---------------------------------------------------------------------------*/
static void prvInitPort( void )
{
	DDR16=0xFF;
    DDR25=0xFF;
}
/*---------------------------------------------------------------------------
 * Setup the hardware
 *---------------------------------------------------------------------------*/
static void prvSetupHardware( void )
{
	prvInitPort();
#if WATCHDOG != WTC_NONE	
	InitWatchdog();
#endif
}


/*********************@FUNCTION_HEADER_START*********************
*@FUNCTION NAME:    main()                                      *
*                                                               *
*@DESCRIPTION:      The main function controls the program flow *
*                                                               *
*@PARAMETER:        none                                        *
*                                                               *
*@RETURN:           none                                        *
*                                                               *
***********************@FUNCTION_HEADER_END*********************/

void main(void)
{
	__set_il(31);       /* allow all levels */
	InitIrqLevels();    /* init interrupts */
	
	prvSetupHardware();
	
#if WATCHDOG == WTC_IN_TASK	
	vStartWatchdogTask( WTC_TASK_PRIORITY );
#endif		

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
	
	/* Start the 'Check' task which is defined in this file. */
	xTaskCreate( vErrorChecks, ( signed portCHAR * ) "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );	

	vStartGenericQueueTasks( mainGENERIC_QUEUE_PRIORITY );
	
	vStartQueuePeekTasks();
	
	vTraceListTasks( TASK_UTILITY_PRIORITY );
	
	vCreateBlockTimeTasks();
	
	vCreateSuicidalTasks( mainDEATH_PRIORITY );
	
	vTaskStartScheduler( );
	
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
		if( sState[uxLED])	
		{
			PDR25 |= (1 << uxLED);
		}
		else
		{
			PDR25 &= ~(1 << uxLED);
		}
	
		sState[uxLED] = !(sState[uxLED]);
		
		xTaskResumeAll();
	}
	else
	{
		uxLED -= ledNUMBER_OF_LEDS;
		
		vTaskSuspendAll();
		
		/* Toggle the state of the single genuine on board LED. */
		if( sState1[uxLED])	
		{
			PDR16 |= (1 << uxLED);
		}
		else
		{
			PDR16 &= ~(1 << uxLED);
		}
	
		sState1[uxLED] = !(sState1[uxLED]);
		
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
				PDR25 |= (1 << uxLED);
				sState[uxLED] = 1;
			}
			else
			{
				PDR25 &= ~(1 << uxLED);
				sState[uxLED] = 0;
			}
		}
		xTaskResumeAll();
	}
	else 
	{
		uxLED -= ledNUMBER_OF_LEDS;
		vTaskSuspendAll();
		{
			if( xValue )
			{
				PDR16 |= (1 << uxLED);
				sState1[uxLED] = 1;
			}
			else
			{
				PDR16 &= ~(1 << uxLED);
				sState1[uxLED] = 0;
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

	if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
	{
		sNoErrorFound = pdFALSE;
	}

	if( xArePollingQueuesStillRunning() != pdTRUE )
	{
		sNoErrorFound = pdFALSE;
	}

	if( xAreComTestTasksStillRunning() != pdTRUE )
	{
		sNoErrorFound = pdFALSE;
	}
	
	if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	{
		sNoErrorFound = pdFALSE;
	}
	
	if( xAreBlockingQueuesStillRunning() != pdTRUE )
	{
		sNoErrorFound = pdFALSE;
	}
	
	if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
	{
		sNoErrorFound = pdFALSE;
	}
	
	if( xAreMathsTaskStillRunning() != pdTRUE )
	{
		sNoErrorFound = pdFALSE;
	}
	
	if( xAreFlashCoRoutinesStillRunning() != pdTRUE ) 
	{
		sNoErrorFound = pdFALSE;
	}
	
	if( xAreHookCoRoutinesStillRunning() != pdTRUE )
	{
		sNoErrorFound = pdFALSE;
	}
	
	if( xIsCreateTaskStillRunning() != pdTRUE )
    {
    	sNoErrorFound = pdFALSE;
    }
	
	if( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
	{
		sNoErrorFound = pdFALSE;
    }
    
    if ( xAreGenericQueueTasksStillRunning() != pdTRUE )
    {
    	sNoErrorFound = pdFALSE;
    }
    
    if ( xAreQueuePeekTasksStillRunning() != pdTRUE )
    {
    	sNoErrorFound = pdFALSE;
    }
    
	return sNoErrorFound;
}

/********************@FUNCTION_DECLARATION_END******************/
