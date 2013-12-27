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
 * main-blinky.c is included when the "Blinky" build configuration is used.
 * main-full.c is included when the "Full" build configuration is used.
 *
 * main-full.c creates a lot of demo and test tasks and timers,  and is
 * therefore very comprehensive but also complex.  If you would prefer a much
 * simpler project to get started with, then select the 'Blinky' build
 * configuration within the SDK Eclipse IDE.  See the documentation page for
 * this demo on the http://www.FreeRTOS.org web site for more information.
 * ****************************************************************************
 *
 * main() creates all the demo application tasks and timers, then starts the
 * scheduler.  The web documentation provides more details of the standard demo
 * application tasks, which provide no particular functionality, but do provide
 * a good example of how to use the FreeRTOS API.
 *
 * In addition to the standard demo tasks, the following tasks and tests are
 * defined and/or created within this file:
 *
 * TCP/IP ("lwIP") task - lwIP is used to create a basic web server.  The web
 * server uses server side includes (SSI) to generate tables of task statistics,
 * and run time statistics (run time statistics show how much processing time
 * each task has consumed).  See
 * http://www.FreeRTOS.org/Free-RTOS-for-Xilinx-MicroBlaze-on-Spartan-6-FPGA.html
 * for details on setting up and using the embedded web server.
 *
 * "Reg test" tasks - These test the task context switch mechanism by first
 * filling the MicroBlaze registers with known values, before checking that each
 * register maintains the value that was written to it as the tasks are switched
 * in and out.  The two register test tasks do not use the same values, and
 * execute at a very low priority, to ensure they are pre-empted regularly.
 *
 * "Check" timer - The check timer period is initially set to five seconds.
 * The check timer callback function checks that all the standard demo tasks,
 * and the register check tasks, are not only still executing, but are executing
 * without reporting any errors.  If the check timer discovers that a task has
 * either stalled, or reported an error, then it changes its own period from
 * the initial five seconds, to just 200ms.  The check timer callback function
 * also toggles an LED each time it is called.  This provides a visual
 * indication of the system status:  If the LED toggles every five seconds then
 * no issues have been discovered.  If the LED toggles every 200ms then an issue
 * has been discovered with at least one task.  The last reported issue is
 * latched into the pcStatusMessage variable, and can also be viewed at the
 * bottom of the pages served by the embedded web server.
 *
 * ***NOTE*** This demo uses the standard comtest tasks, which has special
 * hardware requirements.  See
 * http://www.FreeRTOS.org/Free-RTOS-for-Xilinx-MicroBlaze-on-Spartan-6-FPGA.html
 * for more information.
 *
 * This file also includes example implementations of the
 * vApplicationIdleHook(), vApplicationStackOverflowHook(),
 * vApplicationMallocFailedHook(), vApplicationClearTimerInterrupt(), and
 * vApplicationSetupTimerInterrupt() callback (hook) functions.
 */

/* Standard includes. */
#include <string.h>
#include <stdio.h>

/* BSP includes. */
#include "xtmrctr.h"
#include "microblaze_exceptions_g.h"

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

/* lwIP includes. */
#include "lwip/tcpip.h"


/* Priorities at which the various tasks are created. */
#define mainQUEUE_POLL_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainSEM_TEST_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainBLOCK_Q_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainCREATOR_TASK_PRIORITY   ( tskIDLE_PRIORITY + 3 )
#define mainFLASH_TASK_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainCOM_TEST_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainINTEGER_TASK_PRIORITY   ( tskIDLE_PRIORITY )
#define mainGEN_QUEUE_TASK_PRIORITY	( tskIDLE_PRIORITY )
#define mainFLOP_TASK_PRIORITY		( tskIDLE_PRIORITY )

/* The LED toggled by the check task. */
#define mainCHECK_LED				( 3 )

/* The rate at which mainCHECK_LED will toggle when all the tasks are running
without error.  See the description of the check timer in the comments at the
top of this file. */
#define mainNO_ERROR_CHECK_TIMER_PERIOD		( 5000 / portTICK_RATE_MS )

/* The rate at which mainCHECK_LED will toggle when an error has been reported
by at least one task.  See the description of the check timer in the comments at
the top of this file. */
#define mainERROR_CHECK_TIMER_PERIOD		( 200 / portTICK_RATE_MS )

/* A block time of zero simply means "don't block". */
#define mainDONT_BLOCK						( ( portTickType ) 0 )

/* The LED used by the comtest tasks. See the comtest_strings.c file for more
information.  In this case an invalid LED number is provided as all four
available LEDs (LEDs 0 to 3) are already in use. */
#define mainCOM_TEST_LED			( 4 )

/* Baud rate used by the comtest tasks.  The baud rate used is actually fixed in
UARTLite IP when the hardware was built, but the standard serial init function
required a baud rate parameter to be provided - in this case it is just
ignored. */
#define mainCOM_TEST_BAUD_RATE				( XPAR_RS232_UART_1_BAUDRATE )

/* The timer test task generates a lot of timers that all use a different
period that is a multiple of the mainTIMER_TEST_PERIOD definition. */
#define mainTIMER_TEST_PERIOD			( 20 )

/*-----------------------------------------------------------*/

/*
 * The register test tasks as described in the comments at the top of this file.
 * The nature of the register test tasks means they have to be implemented in
 * assembler.
 */
extern void vRegisterTest1( void *pvParameters );
extern void vRegisterTest2( void *pvParameters );

/*
 * Defines the 'check' timer functionality as described at the top of this file.
 * This function is the callback function associated with the 'check' timer.
 */
static void vCheckTimerCallback( xTimerHandle xTimer );

/*
 * Configure the interrupt controller, LED outputs and button inputs.
 */
static void prvSetupHardware( void );

/* Defined in lwIPApps.c. */
extern void lwIPAppsInit( void *pvArguments );

/*-----------------------------------------------------------*/

/* The check timer callback function sets pcStatusMessage to a string that
indicates the last reported error that it discovered. */
static const char *pcStatusMessage = NULL;

/* Structures that hold the state of the various peripherals used by this demo.
These are used by the Xilinx peripheral driver API functions.  In this case,
only the timer/counter is used directly within this file. */
static XTmrCtr xTimer0Instance;

/* The 'check' timer, as described at the top of this file. */
static xTimerHandle xCheckTimer = NULL;

/* Used in the run time stats calculations. */
static unsigned long ulClocksPer10thOfAMilliSecond = 0UL;

/* Constants used to set up the AXI timer to generate ticks. */
static const unsigned char ucTimerCounterNumber = ( unsigned char ) 0U;
static const unsigned long ulCounterReloadValue = ( ( XPAR_AXI_TIMER_0_CLOCK_FREQ_HZ / configTICK_RATE_HZ ) - 1UL );

/*-----------------------------------------------------------*/

int main( void )
{
	/***************************************************************************
	This project includes a lot of demo and test tasks and timers,  and is
	therefore comprehensive, but complex.  If you would prefer a much simpler
	project to get started with, then select the 'Blinky' build configuration
	within the SDK Eclipse IDE.
	***************************************************************************/

	/* Configure the interrupt controller, LED outputs and button inputs. */
	prvSetupHardware();

	/* This call creates the TCP/IP thread. */
	tcpip_init( lwIPAppsInit, NULL );

	/* Start the reg test tasks, as described in the comments at the top of this
	file. */
	xTaskCreate( vRegisterTest1, "RegTst1", configMINIMAL_STACK_SIZE, ( void * ) 0, tskIDLE_PRIORITY, NULL );
	xTaskCreate( vRegisterTest2, "RegTst2", configMINIMAL_STACK_SIZE, ( void * ) 0, tskIDLE_PRIORITY, NULL );

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
	floating point numbers and variables.  The other is defined in sp_flop.c,
	and uses single precision floating point numbers and variables.  The
	MicroBlaze floating point unit only handles single precision floating.
	Therefore, to test the floating point hardware, sp_flop.c should be included
	in this project. */
	vStartMathTasks( mainFLOP_TASK_PRIORITY );

	/* The suicide tasks must be created last as they need to know how many
	tasks were running prior to their creation.  This then allows them to
	ascertain whether or not the correct/expected number of tasks are running at
	any given time. */
	vCreateSuicidalTasks( mainCREATOR_TASK_PRIORITY );

	/* Create the 'check' timer - the timer that periodically calls the
	check function as described in the comments at the top of this file.  Note
	that, for reasons stated in the comments within vApplicationIdleHook()
	(defined in this file), the check timer is not actually started	until after
	the scheduler has been started. */
	xCheckTimer = xTimerCreate( "Check timer", mainNO_ERROR_CHECK_TIMER_PERIOD, pdTRUE, ( void * ) 0, vCheckTimerCallback );

	/* Start the scheduler running.  From this point on, only tasks and
	interrupts will be executing. */
	vTaskStartScheduler();

	/* If all is well then the following line will never be reached.  If
	execution does reach here, then it is highly probably that the heap size
	is too small for the idle and/or timer tasks to be created within
	vTaskStartScheduler(). */
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
	in the comments at the top of this file. */

	/* Don't overwrite any errors that have already been latched. */
	if( pcStatusMessage == NULL )
	{
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
	}

	/* Store a local copy of the current reg test loop counters.  If these have
	not incremented the next time this callback function is executed then the
	reg test tasks have either stalled or discovered an error. */
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
			/* An error has occurred, so change the period of the timer that
			calls this callback function.  This results in the LED toggling at
			a faster rate - giving the user visual feedback that something is not
			as it should be.  This function is called from the context of the
			timer service task so must ***not*** attempt to block while calling
			this function. */
			if( xTimerChangePeriod( xTimer, mainERROR_CHECK_TIMER_PERIOD, mainDONT_BLOCK ) == pdPASS )
			{
				/* If the command to change the timer period was sent to the
				timer command queue successfully, then latch the fact that the
				timer period has already been changed.  This is just done to
				prevent xTimerChangePeriod() being called on every execution of
				this function once an error has been discovered.  */
				lErrorAlreadyLatched = pdTRUE;
			}

			/* Update the xExecutionRate variable too as the rate at which this
			callback is executed has to be passed into the
			xAreTimerDemoTasksStillRunning() function. */
			xExecutionRate = mainERROR_CHECK_TIMER_PERIOD;
		}
	}
}
/*-----------------------------------------------------------*/

/* This is an application defined callback function used to install the tick
interrupt handler.  It is provided as an application callback because the kernel
will run on lots of different MicroBlaze and FPGA configurations - not all of
which will have the same timer peripherals defined or available.  This example
uses the AXI Timer 0.  If that is available on your hardware platform then this
example callback implementation should not require modification.   The name of
the interrupt handler that should be installed is vPortTickISR(), which the
function below declares as an extern. */
void vApplicationSetupTimerInterrupt( void )
{
portBASE_TYPE xStatus;
extern void vPortTickISR( void *pvUnused );

	/* Initialise the timer/counter. */
	xStatus = XTmrCtr_Initialize( &xTimer0Instance, XPAR_AXI_TIMER_0_DEVICE_ID );

	if( xStatus == XST_SUCCESS )
	{
		/* Install the tick interrupt handler as the timer ISR.
		*NOTE* The xPortInstallInterruptHandler() API function must be used for
		this purpose. */
		xStatus = xPortInstallInterruptHandler( XPAR_INTC_0_TMRCTR_0_VEC_ID, vPortTickISR, NULL );
	}

	if( xStatus == pdPASS )
	{
		/* Enable the timer interrupt in the interrupt controller.
		*NOTE* The vPortEnableInterrupt() API function must be used for this
		purpose. */
		vPortEnableInterrupt( XPAR_INTC_0_TMRCTR_0_VEC_ID );

		/* Configure the timer interrupt handler. */
		XTmrCtr_SetHandler( &xTimer0Instance, ( void * ) vPortTickISR, NULL );

		/* Set the correct period for the timer. */
		XTmrCtr_SetResetValue( &xTimer0Instance, ucTimerCounterNumber, ulCounterReloadValue );

		/* Enable the interrupts.  Auto-reload mode is used to generate a
		periodic tick.  Note that interrupts are disabled when this function is
		called, so interrupts will not start to be processed until the first
		task has started to run. */
		XTmrCtr_SetOptions( &xTimer0Instance, ucTimerCounterNumber, ( XTC_INT_MODE_OPTION | XTC_AUTO_RELOAD_OPTION | XTC_DOWN_COUNT_OPTION ) );

		/* Start the timer. */
		XTmrCtr_Start( &xTimer0Instance, ucTimerCounterNumber );
	}

	/* Sanity check that the function executed as expected. */
	configASSERT( ( xStatus == pdPASS ) );
}
/*-----------------------------------------------------------*/

/* This is an application defined callback function used to clear whichever
interrupt was installed by the the vApplicationSetupTimerInterrupt() callback
function - in this case the interrupt generated by the AXI timer.  It is
provided as an application callback because the kernel will run on lots of
different MicroBlaze and FPGA configurations - not all of which will have the
same timer peripherals defined or available.  This example uses the AXI Timer 0.
If that is available on your hardware platform then this example callback
implementation should not require modification provided the example definition
of vApplicationSetupTimerInterrupt() is also not modified. */
void vApplicationClearTimerInterrupt( void )
{
unsigned long ulCSR;

	/* Clear the timer interrupt */
	ulCSR = XTmrCtr_GetControlStatusReg( XPAR_AXI_TIMER_0_BASEADDR, 0 );
	XTmrCtr_SetControlStatusReg( XPAR_AXI_TIMER_0_BASEADDR, 0, ulCSR );
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
	/* vApplicationMallocFailedHook() will only be called if
	configUSE_MALLOC_FAILED_HOOK is set to 1 in FreeRTOSConfig.h.  It is a hook
	function that will get called if a call to pvPortMalloc() fails.
	pvPortMalloc() is called internally by the kernel whenever a task, queue or
	semaphore is created.  It is also called by various parts of the demo
	application.  If heap_1.c or heap_2.c are used, then the size of the heap
	available to pvPortMalloc() is defined by configTOTAL_HEAP_SIZE in
	FreeRTOSConfig.h, and the xPortGetFreeHeapSize() API function can be used
	to query the size of free heap space that remains (although it does not
	provide information on how the remaining heap might be fragmented). */
	taskDISABLE_INTERRUPTS();
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( xTaskHandle pxTask, signed char *pcTaskName )
{
	( void ) pcTaskName;
	( void ) pxTask;

	/* vApplicationStackOverflowHook() will only be called if
	configCHECK_FOR_STACK_OVERFLOW is set to either 1 or 2.  The handle and name
	of the offending task will be passed into the hook function via its
	parameters.  However, when a stack has overflowed, it is possible that the
	parameters will have been corrupted, in which case the pxCurrentTCB variable
	can be inspected directly. */
	taskDISABLE_INTERRUPTS();
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
static long lCheckTimerStarted = pdFALSE;

	/* vApplicationIdleHook() will only be called if configUSE_IDLE_HOOK is set
	to 1 in FreeRTOSConfig.h.  It will be called on each iteration of the idle
	task.  It is essential that code added to this hook function never attempts
	to block in any way (for example, call xQueueReceive() with a block time
	specified, or call vTaskDelay()).  If the application makes use of the
	vTaskDelete() API function (as this demo application does) then it is also
	important that vApplicationIdleHook() is permitted to return to its calling
	function, because it is the responsibility of the idle task to clean up
	memory allocated by the kernel to any task that has since been deleted. */

	/* If the check timer has not already been started, then start it now.
	Normally, the xTimerStart() API function can be called immediately after the
	timer is created - how this demo application includes the timer demo tasks.
	The timer demo tasks, as part of their test function, deliberately fill up
	the timer command queue - meaning the check timer cannot be started until
	after the scheduler has been started - at which point the timer command
	queue will have been drained. */
	if( lCheckTimerStarted == pdFALSE )
	{
		xTimerStart( xCheckTimer, mainDONT_BLOCK );
		lCheckTimerStarted = pdTRUE;
	}
}
/*-----------------------------------------------------------*/

void vApplicationExceptionRegisterDump( xPortRegisterDump *xRegisterDump )
{
	( void ) xRegisterDump;

	/* If configINSTALL_EXCEPTION_HANDLERS is set to 1 in FreeRTOSConfig.h, then
	the kernel will	automatically install its own exception handlers before the
	kernel is started, if the application writer has not already caused them to
	be installed by calling either of the vPortExceptionsInstallHandlers()
	or xPortInstallInterruptHandler() API functions before that time.  The
	kernels exception handler populates an xPortRegisterDump structure with
	the processor state at the point that the exception was triggered - and also
	includes a strings that say what the exception cause was and which task was
	running at the time.  The exception handler then passes the populated
	xPortRegisterDump structure into vApplicationExceptionRegisterDump() to
	allow the application writer to perform any debugging that may be necessary.
	However, defining vApplicationExceptionRegisterDump() within the application
	itself is optional.  The kernel will use a default implementation if the
	application writer chooses not to provide their own. */
	for( ;; )
	{
		portNOP();
	}
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	taskDISABLE_INTERRUPTS();

	/* Configure the LED outputs. */
	vParTestInitialise();

	/* Tasks inherit the exception and cache configuration of the MicroBlaze
	at the point that they are created. */
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

void vMainConfigureTimerForRunTimeStats( void )
{
	/* How many times does the counter counter increment in 10ms? */
	ulClocksPer10thOfAMilliSecond = XPAR_AXI_TIMER_0_CLOCK_FREQ_HZ / 10000UL;
}
/*-----------------------------------------------------------*/

unsigned long ulMainGetRunTimeCounterValue( void )
{
unsigned long ulTimerCounts1, ulTimerCounts2, ulTickCount, ulReturn;

	/* NOTE: This can get called from a yield, in which case interrupts are
	disabled, or from a tick ISR, in which case the effect is the same as if
	interrupts were disabled.  In either case, it is going to run atomically. */

	/* The timer is in down count mode.  How many clocks have passed since it
	was last reloaded? */
	ulTimerCounts1 = ulCounterReloadValue - XTmrCtr_GetValue( &xTimer0Instance, ucTimerCounterNumber );

	/* How many times has it overflowed? */
	ulTickCount = xTaskGetTickCountFromISR();

	/* If this is being called from a yield, has the counter overflowed since
	it was read?  If that is the case then ulTickCounts will need incrementing
	again as it will not yet have been incremented from the tick interrupt. */
	ulTimerCounts2 = ulCounterReloadValue - XTmrCtr_GetValue( &xTimer0Instance, ucTimerCounterNumber );
	if( ulTimerCounts2 < ulTimerCounts1 )
	{
		/* There is a tick interrupt pending but the tick count not yet
		incremented. */
		ulTickCount++;

		/* Use the second timer reading. */
		ulTimerCounts1 = ulTimerCounts2;
	}

	/* Convert the tick count into tenths of a millisecond.  THIS ASSUMES
	configTICK_RATE_HZ is 1000! */
	ulReturn = ( ulTickCount * 10UL );

	/* Add on the number of tenths of a millisecond that have passed since the
	tick count last got updated. */
	ulReturn += ( ulTimerCounts1 / ulClocksPer10thOfAMilliSecond );

	/* Some crude rounding. */
	if( ( ulTimerCounts1 % ulClocksPer10thOfAMilliSecond ) > ( ulClocksPer10thOfAMilliSecond >> 1UL ) )
	{
		ulReturn++;
	}

	return ulReturn;
}
/*-----------------------------------------------------------*/

char *pcMainGetTaskStatusMessage( void )
{
char * pcReturn;

	if( pcStatusMessage == NULL )
	{
		pcReturn = ( char * ) "OK";
	}
	else
	{
		pcReturn = ( char * ) pcStatusMessage;
	}

	return pcReturn;
}



