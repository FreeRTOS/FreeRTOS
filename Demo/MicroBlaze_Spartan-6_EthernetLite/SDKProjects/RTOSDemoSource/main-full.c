/*
    FreeRTOS V7.0.1 - Copyright (C) 2011 Real Time Engineers Ltd.
	

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS tutorial books are available in pdf and paperback.        *
     *    Complete, revised, and edited pdf reference manuals are also       *
     *    available.                                                         *
     *                                                                       *
     *    Purchasing FreeRTOS documentation will not only help you, by       *
     *    ensuring you get running as quickly as possible and with an        *
     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
     *    the FreeRTOS project to continue with its mission of providing     *
     *    professional grade, cross platform, de facto standard solutions    *
     *    for microcontrollers - completely free of charge!                  *
     *                                                                       *
     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
     *                                                                       *
     *    Thank you for using FreeRTOS, and thank you for your support!      *
     *                                                                       *
    ***************************************************************************


    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    >>>NOTE<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.  FreeRTOS is distributed in the hope that it will be useful, but
    WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
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

/* ****************************************************************************
 * This project includes a lot of demo and test tasks,  and is therefore complex.
 * If you would prefer a much simpler project to get started with, then select
 * the 'Blinky' build configuration within the SDK Eclipse IDE.
 * ****************************************************************************
 *
 * main() creates all the demo application tasks, then starts the scheduler.  
 * The web documentation provides more details of the standard demo application 
 * tasks, which provide no particular functionality, but do provide a good 
 * example of how to use the FreeRTOS API.  
 *
 * In addition to the standard demo tasks, the following tasks and tests are
 * defined and/or created within this file:
 *
 * Webserver ("lwIP") task - TBD _RB_
 *
 * "Reg test" tasks - These fill the registers with known values, then check
 * that each register still contains its expected value.  Each task uses
 * different values.  The tasks run with very low priority so get preempted
 * very frequently.  A check variable is incremented on each iteration of the
 * test loop.  A register containing an unexpected value is indicative of an
 * error in the context switching mechanism and will result in a branch to a
 * null loop - which in turn will prevent the check variable from incrementing
 * any further and allow the check timer (described below) to determine that an
 * error has occurred.  The nature of the reg test tasks necessitates that they
 * are written in assembly code.
 *
 * "Check" timer - The check timer period is initially set to five seconds.  
 * The check timer callback function checks that all the standard demo tasks are 
 * functioning as expected, without error.  If an error is discovered in any 
 * standard demo task, then the check timer period is shortened to 200ms.  The
 * check timer callback function also toggles an LED each time it is called. 
 * Therefore, if the LED toggles every five seconds, all the tasks are
 * functioning as expected, without any error conditions being detected.  If the
 * LED toggles every 200ms then an error has been discovered in at least one
 * task. 
 *
 * This file also includes example implementations of the vApplicationTickHook(),
 * vApplicationIdleHook(), vApplicationStackOverflowHook(),
 * vApplicationMallocFailedHook(), vApplicationClearTimerInterrupt(), and
 * vApplicationSetupTimerInterrupt() callback (hook) functions.
 */

/* Standard includes. */
#include <string.h>
#include <stdio.h>

/* BSP includes. */
#include "xtmrctr.h"

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "timers.h"

/* Standard demo includes. */
#include "partest.h"
#include "flash.h"
#include "BlockQ.h"
#include "death.h"
#include "blocktim.h"
#include "semtest.h"
#include "PollQ.h"
#include "GenQTest.h"
#include "QPeek.h"
#include "recmutex.h"
#include "flop.h"
#include "dynamic.h"
#include "comtest_strings.h"
#include "TimerDemo.h"

/* Priorities at which the tasks are created. */
#define mainQUEUE_POLL_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainSEM_TEST_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainCREATOR_TASK_PRIORITY   ( tskIDLE_PRIORITY + 3 )
#define mainFLASH_TASK_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainuIP_TASK_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainCOM_TEST_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainINTEGER_TASK_PRIORITY   ( tskIDLE_PRIORITY )
#define mainGEN_QUEUE_TASK_PRIORITY	( tskIDLE_PRIORITY )
#define mainFLOP_TASK_PRIORITY		( tskIDLE_PRIORITY )

/* The WEB server uses string handling functions, which in turn use a bit more
stack than most of the other tasks. */
#define mainuIP_STACK_SIZE			( configMINIMAL_STACK_SIZE * 3 )

/* The LED toggled by the check task. */
#define mainCHECK_LED				( 3 )

/* The rate at which mainCHECK_LED will toggle when all the tasks are running
without error.  Controlled by the check task as described at the top of this
file. */
#define mainNO_ERROR_CHECK_TIMER_PERIOD		( 5000 / portTICK_RATE_MS )

/* The rate at which mainCHECK_LED will toggle when an error has been reported
by at least one task.  Controlled by the check task as described at the top of
this file. */
#define mainERROR_CHECK_TIMER_PERIOD		( 200 / portTICK_RATE_MS )

/* A block time of zero means "don't block". */
#define mainDONT_BLOCK						( ( portTickType ) 0 )

/* The LED used by the comtest tasks. See the comtest.c file for more
information.  In this case an invalid LED number is provided as all four
available LEDs are already in use. */
#define mainCOM_TEST_LED			( 4 )

/* Baud rate used by the comtest tasks.  This is actually fixed in the hardware
when the hardware was built, but the standard serial init function required a
baud rate parameter. */
#define mainCOM_TEST_BAUD_RATE				( XPAR_RS232_UART_1_BAUDRATE )

#define mainTIMER_TEST_PERIOD			( 20 )

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
extern void vRegisterTest1( void *pvParameters );
extern void vRegisterTest2( void *pvParameters );

/*
 * Defines the 'check' functionality as described at the top of this file.  This
 * function is the callback function for the 'check' timer.
 */
static void vCheckTimerCallback( xTimerHandle xTimer );


static void prvSetupHardware( void );


/*-----------------------------------------------------------*/

/* The status message that is displayed at the bottom of the "task stats" web
page, which is served by the uIP task.  This will report any errors picked up
by the reg test task. */
static const char *pcStatusMessage = NULL;

static XTmrCtr xTimer0Instance;

/* The 'check' timer, as described at the top of this file. */
static xTimerHandle xCheckTimer = NULL;

/*-----------------------------------------------------------*/

int main( void )
{
	/* *************************************************************************
	This project includes a lot of demo and test tasks,  and is therefore complex.
	If you would prefer a much simpler project to get started with, then select
	the 'Blinky' build configuration within the SDK Eclipse IDE.
	***************************************************************************/

	/* Configure the interrupt controller, LED outputs and button inputs. */
	prvSetupHardware();

	/* Start the reg test tasks which test the context switching mechanism. */
	xTaskCreate( vRegisterTest1, ( const signed char * const ) "RegTst1", configMINIMAL_STACK_SIZE, ( void * ) 0, tskIDLE_PRIORITY, NULL );
	xTaskCreate( vRegisterTest2, ( const signed char * const ) "RegTst2", configMINIMAL_STACK_SIZE, ( void * ) 0, tskIDLE_PRIORITY, NULL );

	/* Create the standard demo tasks. */
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
	vCreateBlockTimeTasks();
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
	vStartGenericQueueTasks( mainGEN_QUEUE_TASK_PRIORITY );
	vStartLEDFlashTasks( mainFLASH_TASK_PRIORITY );
	vStartQueuePeekTasks();
	vStartRecursiveMutexTasks();
	vStartComTestStringsTasks( mainCOM_TEST_PRIORITY, mainCOM_TEST_BAUD_RATE, mainCOM_TEST_LED );
	vStartDynamicPriorityTasks();
	vStartTimerDemoTask( mainTIMER_TEST_PERIOD );

	/* Note - the set of standard demo tasks contains two versions of
	vStartMathTasks.c.  One is defined in flop.c, and uses double precision
	floating point numbers and variables.  The other is defined in sp_flop.c
	and uses single precision floating point numbers and variables.  The
	MicroBlaze floating point unit only handles single precision floating.
	Therefore, to test the floating point unit, sp_flop.c should be included
	in this project. */
	vStartMathTasks( mainFLOP_TASK_PRIORITY );

	/* The suicide tasks must be created last as they need to know how many
	tasks were running prior to their creation in order to ascertain whether
	or not the correct/expected number of tasks are running at any given time. */
	vCreateSuicidalTasks( mainCREATOR_TASK_PRIORITY );

	/* Create the 'check' timer - the timer that periodically calls the
	check function as described at the top of this file.  Note that, for
	the reasons stated in the comments above the call to
	vStartTimerDemoTask(), that the check timer is not actually started
	until after the scheduler has been started. */
	xCheckTimer = xTimerCreate( ( const signed char * ) "Check timer", mainNO_ERROR_CHECK_TIMER_PERIOD, pdTRUE, ( void * ) 0, vCheckTimerCallback );

	/* Start the tasks running. */
	vTaskStartScheduler();

	/* If all is well we will never reach here as the scheduler will now be
	running.  If we do reach here then it is likely that there was insufficient
	heap available for the idle task to be created. */
	taskDISABLE_INTERRUPTS();
	for( ;; );
}
/*-----------------------------------------------------------*/

static void vCheckTimerCallback( xTimerHandle xTimer )
{
extern unsigned long ulRegTest1CycleCount, ulRegTest2CycleCount;
static volatile unsigned long ulLastRegTest1CycleCount = 0UL, ulLastRegTest2CycleCount = 0UL;
static long lErrorAlreadyLatched = pdFALSE;
portTickType xExecutionRate = mainNO_ERROR_CHECK_TIMER_PERIOD;

	/* This is the callback function used by the 'check' timer, as described
	at the top of this file. */

	/* Check the standard demo tasks are running without error. */
	if( xAreGenericQueueTasksStillRunning() != pdTRUE )
	{
		/* Increase the rate at which this task cycles, which will increase the
		rate at which mainCHECK_LED flashes to give visual feedback that an error
		has occurred. */
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
	else if( xAreRecursiveMutexTasksStillRunning() != pdTRUE )
	{
		pcStatusMessage = "Error: RecMutex\r\n";
	}
	else if( xAreMathsTaskStillRunning() != pdPASS )
	{
		pcStatusMessage = "Error: Flop\r\n";
	}
	else if( xAreComTestTasksStillRunning() != pdPASS )
	{
		pcStatusMessage = "Error: Comtest\r\n";
	}
	else if( xAreDynamicPriorityTasksStillRunning() != pdPASS )
	{
		pcStatusMessage = "Error: Dynamic\r\n";
	}
	else if( xAreTimerDemoTasksStillRunning( xExecutionRate ) != pdTRUE )
	{
		pcStatusMessage = "Error: TimerDemo";
	}
	else if( ulRegTest1CycleCount == ulLastRegTest1CycleCount )
	{
		/* Check the reg test tasks are still cycling.  They will stop
		incrementing their loop counters if they encounter an error. */
		pcStatusMessage = "Error: RegTest1\r\n";
	}
	else if( ulRegTest2CycleCount == ulLastRegTest2CycleCount )
	{
		pcStatusMessage = "Error: RegTest2\r\n";
	}

	ulLastRegTest1CycleCount = ulRegTest1CycleCount;
	ulLastRegTest2CycleCount = ulRegTest2CycleCount;

	/* Toggle the check LED to give an indication of the system status.  If
	the LED toggles every 5 seconds then everything is ok.  A faster toggle
	indicates an error. */
	vParTestToggleLED( mainCHECK_LED );

	if( pcStatusMessage != NULL )
	{
		if( lErrorAlreadyLatched == pdFALSE )
		{
			/* Ensure the LED toggles at a faster rate if an error has occurred.
			This is called from a timer callback so must not attempt to block. */
			xTimerChangePeriod( xTimer, mainERROR_CHECK_TIMER_PERIOD, mainDONT_BLOCK );

			/* Update the xExecutionRate variable as the rate at which this
			callback is executed has to be passed into the
			xAreTimerDemoTasksStillRunning() function. */
			xExecutionRate = mainERROR_CHECK_TIMER_PERIOD;

			/* Just to ensure the timer period is not changed on each execution
			of the callback. */
			lErrorAlreadyLatched = pdTRUE;
		}
	}
}
/*-----------------------------------------------------------*/

void vApplicationSetupTimerInterrupt( void )
{
portBASE_TYPE xStatus;
const unsigned char ucTimerCounterNumber = ( unsigned char ) 0U;
const unsigned long ulCounterValue = ( ( XPAR_AXI_TIMER_0_CLOCK_FREQ_HZ / configTICK_RATE_HZ ) - 1UL );
extern void vTickISR( void *pvUnused );

	/* Initialise the timer/counter. */
	xStatus = XTmrCtr_Initialize( &xTimer0Instance, XPAR_AXI_TIMER_0_DEVICE_ID );

	if( xStatus == XST_SUCCESS )
	{
		/* Install the tick interrupt handler as the timer ISR. */
		xStatus = xPortInstallInterruptHandler( XPAR_INTC_0_TMRCTR_0_VEC_ID, vTickISR, NULL );
	}

	if( xStatus == pdPASS )
	{
		vPortEnableInterrupt( XPAR_INTC_0_TMRCTR_0_VEC_ID );

		/* Configure the timer interrupt handler. */
		XTmrCtr_SetHandler( &xTimer0Instance, ( void * ) vTickISR, NULL );

		/* Set the correct period for the timer. */
		XTmrCtr_SetResetValue( &xTimer0Instance, ucTimerCounterNumber, ulCounterValue );

		/* Enable the interrupts.  Auto-reload mode is used to generate a
		periodic tick.  Note that interrupts are disabled when this function is
		called, so interrupts will not start to be processed until the first
		task has started to run. */
		XTmrCtr_SetOptions( &xTimer0Instance, ucTimerCounterNumber, ( XTC_INT_MODE_OPTION | XTC_AUTO_RELOAD_OPTION | XTC_DOWN_COUNT_OPTION ) );

		/* Start the timer. */
		XTmrCtr_Start( &xTimer0Instance, ucTimerCounterNumber );
	}

	configASSERT( ( xStatus == pdPASS ) );
}
/*-----------------------------------------------------------*/

void vApplicationClearTimerInterrupt( void )
{
unsigned long ulCSR;

	/* Clear the timer interrupt */
	ulCSR = XTmrCtr_GetControlStatusReg( XPAR_AXI_TIMER_0_BASEADDR, 0 );
	XTmrCtr_SetControlStatusReg( XPAR_AXI_TIMER_0_BASEADDR, 0, ulCSR );
}
/*-----------------------------------------------------------*/

/* This function is explained by the comments above its prototype at the top
of this file. */
void vApplicationMallocFailedHook( void )
{
	taskDISABLE_INTERRUPTS();
	for( ;; );
}
/*-----------------------------------------------------------*/

/* This function is explained by the comments above its prototype at the top
of this file. */
void vApplicationStackOverflowHook( xTaskHandle *pxTask, signed char *pcTaskName )
{
	taskDISABLE_INTERRUPTS();
	for( ;; );
}
/*-----------------------------------------------------------*/

/* This function is explained by the comments above its prototype at the top
of this file. */
void vApplicationIdleHook( void )
{
static long lCheckTimerStarted = pdFALSE;

	if( lCheckTimerStarted == pdFALSE )
	{
		xTimerStart( xCheckTimer, mainDONT_BLOCK ); //_RB_ comment why this is done here.
		lCheckTimerStarted = pdTRUE;
	}
}
/*-----------------------------------------------------------*/

void vApplicationTickHook( void )
{
	/* Call the periodic timer test, which tests the timer API functions that
	can be called from an ISR. */
	vTimerPeriodicISRTests();
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

static void prvSetupHardware( void )
{
	taskDISABLE_INTERRUPTS();
	vParTestInitialise();

	#if MICROBLAZE_EXCEPTIONS_ENABLED == 1
		microblaze_enable_exceptions();
	#endif

	#if XPAR_MICROBLAZE_USE_ICACHE == 1
		microblaze_invalidate_icache();
		microblaze_enable_icache();
	#endif

	#if XPAR_MICROBLAZE_USE_DCACHE == 1
		microblaze_invalidate_dcache();
		microblaze_enable_dcache();
	#endif

}
/*-----------------------------------------------------------*/

void vApplicationExceptionRegisterDump( xPortRegisterDump *xRegisterDump )
{
	for( ;; )
	{
		portNOP();
	}
}

