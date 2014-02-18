/*
    FreeRTOS V8.0.0 - Copyright (C) 2014 Real Time Engineers Ltd.
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

/*
 * main-blinky.c is included when the "Blinky" build configuration is used.
 * main-full.c is included when the "Full" build configuration is used.
 *
 * main-full.c (this file) defines a comprehensive demo that creates many
 * tasks, queues, semaphores and timers.  It also demonstrates how Cortex-M3
 * interrupts can interact with FreeRTOS tasks/timers, a simple web server, and
 * run time statistics gathering functionality.  ***IF YOU ARE LOOKING FOR A
 * SIMPLER STARTING POINT THEN USE THE "BLINKY" BUILD CONFIGURATION FIRST.***
 *
 * If the Ethernet functionality is excluded, then this demo will run 'stand
 * alone' (without the rest of the tower system) on the TWR-K60N512 tower
 * module.  If the Ethernet functionality is included, then the full Freescale
 * K60 tower kit, including both the TWR-K60N512 and TWR-SER modules, is
 * required (as the Ethernet connector is on the TWR-SER).  The TWR-K60N512 is
 * populated with a K60N512 Cortex-M4 microcontroller.
 *
 * The main() Function:
 * main() creates four demo specific software timers, and one demo specific
 * task (the web server task).  It also creates a whole host of 'standard
 * demo' tasks/queues/semaphores/timers, before starting the scheduler.  The
 * demo specific tasks and timers are described in the comments here.  The
 * standard demo tasks are described on the FreeRTOS.org web site.
 *
 * The standard demo tasks provide no specific functionality.  They are
 * included to both test the FreeRTOS port, and provide examples of how the
 * various FreeRTOS API functions can be used.
 *
 * This demo creates 37 persistent tasks, then dynamically creates and destroys
 * another two tasks as the demo executes.
 *
 *
 * The Demo Specific "LED" Timers and Callback Function:
 * Two very simple LED timers are created.  All they do is toggle an LED each
 * when the timer callback function is executed.  The two timers share a
 * callback function, so the callback function parameter is used to determine
 * which timer actually expired, and therefore, which LED to toggle.  Both
 * timers use a different frequency, one toggles the blue LED and the other the
 * green LED.
 *
 * The LED/Button Software Timer and the Button Interrupt:
 * The user button SW2 is configured to generate an interrupt each time it is
 * pressed.  The interrupt service routine switches the orange/yellow LED on,
 * and resets the LED software timer.  The LED timer has a 5000 millisecond (5
 * second) period, and uses a callback function that is defined to just turn the
 * LED off again.  Therefore, pressing the user button will turn the LED on, and
 * the LED will remain on until a full five seconds pass without the button
 * being pressed.
 *
 * The Demo Specific "Check" Timer and Callback Function:
 * The check timer period is initially set to three seconds.  The check timer
 * callback function checks that all the standard demo tasks are not only still
 * executing, but are executing without reporting any errors.  If the check
 * timer discovers that a task has either stalled, or reported an error, then it
 * changes its own period from the initial three seconds, to just 200ms.  The
 * check timer callback function also toggles the orange/red LED each time it is
 * called.  This provides a visual indication of the system status:  If the LED
 * toggles every three seconds, then no issues have been discovered.  If the LED
 * toggles every 200ms, then an issue has been discovered with at least one
 * task.  The last reported issue is latched into the pcStatusMessage variable,
 * and displayed at the bottom of the "task stats" web page served by the
 * embedded web server task.
 *
 * The web server task:
 * The web server task implements a simple embedded web server that includes
 * CGI scripting.  Pages are provided that allow task statistics, network
 * statistics and run time statistics to be viewed.  In addition, an IO page is
 * served that allows the orange/yellow LED to be turned on and off.  Finally,
 * a page is included that serves a large jpg file.  See the documentation page
 * for this demo on the http://www.FreeRTOS.org web site for web server
 * configuration and usage instructions.
 *
 * The Demo Specific Idle Hook Function:
 * The idle hook function demonstrates how to query the amount of FreeRTOS heap
 * space that is remaining (see vApplicationIdleHook() defined in this file).
 *
 * The Demo Specific Tick Hook Function:
 * The tick hook function is used to test the interrupt safe software timer
 * functionality.
 *
 */

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "timers.h"

/* Freescale includes. */
#include "common.h"

/* Common demo includes. */
#include "partest.h"
#include "flash.h"
#include "BlockQ.h"
#include "death.h"
#include "blocktim.h"
#include "semtest.h"
#include "GenQTest.h"
#include "QPeek.h"
#include "recmutex.h"
#include "TimerDemo.h"
#include "PollQ.h"
#include "countsem.h"
#include "dynamic.h"

/* The LED toggled by the check timer callback function.  */
#define mainCHECK_LED				3UL

/* The LED turned on by the button interrupt, and turned off by the LED timer. */
#define mainTIMER_CONTROLLED_LED	2UL

/* The LEDs toggled by the two simple flash LED timers. */
#define mainLED0					0UL
#define mainLED1					1UL

/* Constant used by the standard timer test functions. */
#define mainTIMER_TEST_PERIOD		( 50 )

/* Priorities used by the various different standard demo tasks. */
#define mainQUEUE_POLL_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainSEM_TEST_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainCREATOR_TASK_PRIORITY   ( tskIDLE_PRIORITY + 3 )
#define mainGEN_QUEUE_TASK_PRIORITY	( tskIDLE_PRIORITY )
#define mainuIP_TASK_PRIORITY		( tskIDLE_PRIORITY + 2 )

/* The WEB server uses string handling functions, which in turn use a bit more
stack than most of the other tasks. */
#define mainuIP_STACK_SIZE			( configMINIMAL_STACK_SIZE * 3 )

/* The period at which the check timer will expire, in ms, provided no errors
have been reported by any of the standard demo tasks.  ms are converted to the
equivalent in ticks using the portTICK_PERIOD_MS constant. */
#define mainCHECK_TIMER_PERIOD_MS			( 3000UL / portTICK_PERIOD_MS )

/* The period at which the check timer will expire, in ms, if an error has been
reported in one of the standard demo tasks.  ms are converted to the equivalent
in ticks using the portTICK_PERIOD_MS constant. */
#define mainERROR_CHECK_TIMER_PERIOD_MS 	( 200UL / portTICK_PERIOD_MS )

/* The LED that is turned on by pressing SW2 remains on until the button has not
been pushed for a full 5000ms. */
#define mainBUTTON_LED_TIMER_PERIOD_MS		( 5000UL / portTICK_PERIOD_MS )

/* The period at which the two simple LED flash timers will execute their
callback functions. */
#define mainLED1_TIMER_PERIOD_MS			( 200UL / portTICK_PERIOD_MS )
#define mainLED2_TIMER_PERIOD_MS			( 600UL / portTICK_PERIOD_MS )

/* A block time of zero simply means "don't block". */
#define mainDONT_BLOCK						( 0UL )

/* The vector used by the GPIO port E.  Button SW2 is configured to generate
an interrupt on this port. */
#define mainGPIO_E_VECTOR					( 91 )

/*-----------------------------------------------------------*/

/*
 * Setup the NVIC, LED outputs, and button inputs.
 */
static void prvSetupHardware( void );

/*
 * Creates the timers that are specific to this demo - namely, the check timer
 * the button LED timer, and the two simple LED flash timers.
 */
static void prvCreateDemoSpecificTimers( void );

/*
 * The LED/button timer callback function.  This does nothing but switch an LED
 * off.
 */
static void prvButtonLEDTimerCallback( TimerHandle_t xTimer );

/*
 * The callback function used by both simple LED flash timers.  Both timers use
 * the same callback, so the function parameter is used to determine which LED
 * should be flashed (effectively to determine which timer has expired).
 */
static void prvLEDTimerCallback( TimerHandle_t xTimer );

/*
 * The check timer callback function, as described at the top of this file.
 */
static void prvCheckTimerCallback( TimerHandle_t xTimer );

/*
 * Contains the implementation of the web server.
 */
extern void vuIP_Task( void *pvParameters );

/*-----------------------------------------------------------*/

/* The LED/Button software timer.  This uses prvButtonLEDTimerCallback() as it's
callback function. */
static TimerHandle_t xLEDButtonTimer = NULL;

/* The check timer.  This uses prvCheckTimerCallback() as its callback
function. */
static TimerHandle_t xCheckTimer = NULL;

/* LED timers - these simply flash LEDs, each using a different frequency.  Both
use the same prvLEDTimerCallback() callback function. */
static TimerHandle_t xLED1Timer = NULL, xLED2Timer = NULL;

/* If an error is detected in a standard demo task, then pcStatusMessage will
be set to point to a string that identifies the offending task.  This is just
to make debugging easier. */
static const char *pcStatusMessage = NULL;

/* Used in the run time stats calculations. */
static unsigned long ulClocksPer10thOfAMilliSecond = 0UL;

/*-----------------------------------------------------------*/

void main( void )
{
	/* Configure the NVIC, LED outputs and button inputs. */
	prvSetupHardware();

	/* Create the timers that are specific to this demo - other timers are
	created as part of the standard demo within vStartTimerDemoTask. */
	prvCreateDemoSpecificTimers();

	/* Create a lot of 'standard demo' tasks.  Nearly 40 tasks are created in
	this demo.  For a much simpler demo, select the 'blinky' build
	configuration. */
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
	vCreateBlockTimeTasks();
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
	vStartGenericQueueTasks( mainGEN_QUEUE_TASK_PRIORITY );
	vStartQueuePeekTasks();
	vStartRecursiveMutexTasks();
	vStartTimerDemoTask( mainTIMER_TEST_PERIOD );
	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
	vStartCountingSemaphoreTasks();
	vStartDynamicPriorityTasks();

	/* The web server task. */
	xTaskCreate( vuIP_Task, "uIP", mainuIP_STACK_SIZE, NULL, mainuIP_TASK_PRIORITY, NULL );

	/* The suicide tasks must be created last, as they need to know how many
	tasks were running prior to their creation in order to ascertain whether
	or not the correct/expected number of tasks are running at any given
	time. */
	vCreateSuicidalTasks( mainCREATOR_TASK_PRIORITY );

	/* Start the tasks and timers running. */
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

	/* Check the standard demo tasks are running without error.   Latch the
	latest reported error in the pcStatusMessage character pointer.  The latched
	string can be viewed using the embedded web server - it is displayed at
	the bottom of the served "task stats" page. */
	if( xAreGenericQueueTasksStillRunning() != pdTRUE )
	{
		pcStatusMessage = "Error: GenQueue";
	}

	if( xAreQueuePeekTasksStillRunning() != pdTRUE )
	{
		pcStatusMessage = "Error: QueuePeek\n";
	}

	if( xAreBlockingQueuesStillRunning() != pdTRUE )
	{
		pcStatusMessage = "Error: BlockQueue\n";
	}

	if( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
	{
		pcStatusMessage = "Error: BlockTime\n";
	}

	if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	{
		pcStatusMessage = "Error: SemTest\n";
	}

	if( xIsCreateTaskStillRunning() != pdTRUE )
	{
		pcStatusMessage = "Error: Death\n";
	}

	if( xAreRecursiveMutexTasksStillRunning() != pdTRUE )
	{
		pcStatusMessage = "Error: RecMutex\n";
	}

	if( xAreTimerDemoTasksStillRunning( ( mainCHECK_TIMER_PERIOD_MS ) ) != pdTRUE )
	{
		pcStatusMessage = "Error: TimerDemo\n";
	}

	if( xArePollingQueuesStillRunning() != pdTRUE )
	{
		pcStatusMessage = "Error: PollQueue\n";
	}

	if( xAreCountingSemaphoreTasksStillRunning() != pdTRUE )
	{
		pcStatusMessage = "Error: CountSem\n";
	}

	if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
	{
		pcStatusMessage = "Error: DynamicPriority\n";
	}

	/* Toggle the check LED to give an indication of the system status.  If
	the LED toggles every mainCHECK_TIMER_PERIOD_MS milliseconds then
	everything is ok.  A faster toggle indicates an error. */
	vParTestToggleLED( mainCHECK_LED );

	/* Have any errors been latch in pcStatusMessage?  If so, shorten the
	period of the check timer to mainERROR_CHECK_TIMER_PERIOD_MS milliseconds.
	This will result in an increase in the rate at which mainCHECK_LED
	toggles. */
	if( pcStatusMessage != NULL )
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

static void prvButtonLEDTimerCallback( TimerHandle_t xTimer )
{
	/* The timer has expired - so no button pushes have occurred in the last
	five seconds - turn the LED off. */
	vParTestSetLED( mainTIMER_CONTROLLED_LED, pdFALSE );
}
/*-----------------------------------------------------------*/

static void prvLEDTimerCallback( TimerHandle_t xTimer )
{
unsigned long ulLED;

	/* This callback is shared by two timers, so the parameter is used to
	determine which LED to toggle.  The LED number is stored in the ID of the
	timer. */
	ulLED = ( unsigned long ) pvTimerGetTimerID( xTimer );
	vParTestToggleLED( ulLED );
}
/*-----------------------------------------------------------*/

/* The ISR executed when the user button is pushed. */
void vPort_E_ISRHandler( void )
{
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	/* The button was pushed, so ensure the LED is on before resetting the
	LED timer.  The LED timer will turn the LED off if the button is not
	pushed within 5000ms. */
	vParTestSetLED( mainTIMER_CONTROLLED_LED, pdTRUE );

	/* This interrupt safe FreeRTOS function can be called from this interrupt
	because the interrupt priority is equal to or below the
	configLIBRARY_MAX_SYSCALL_INTERRUPT_PRIORITY setting in FreeRTOSConfig.h. */
	xTimerResetFromISR( xLEDButtonTimer, &xHigherPriorityTaskWoken );

	/* Clear the interrupt before leaving.  */
	PORTE_ISFR = 0xFFFFFFFFUL;

	/* If calling xTimerResetFromISR() caused a task (in this case the timer
	service/daemon task) to unblock, and the unblocked task has a priority
	higher than or equal to the task that was interrupted, then
	xHigherPriorityTaskWoken will now be set to pdTRUE, and calling
	portEND_SWITCHING_ISR() will ensure the unblocked task runs next. */
	portEND_SWITCHING_ISR( xHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	/* Enable the interrupt on SW1. */
	taskDISABLE_INTERRUPTS();
	PORTE_PCR26 = PORT_PCR_MUX( 1 ) | PORT_PCR_IRQC( 0xA ) | PORT_PCR_PE_MASK | PORT_PCR_PS_MASK;
	enable_irq( mainGPIO_E_VECTOR );

	/* The interrupt calls an interrupt safe API function - so its priority must
	be equal to or lower than configLIBRARY_MAX_SYSCALL_INTERRUPT_PRIORITY. */
	set_irq_priority( mainGPIO_E_VECTOR, configLIBRARY_MAX_SYSCALL_INTERRUPT_PRIORITY );

	/* Configure the LED outputs. */
	vParTestInitialise();
}
/*-----------------------------------------------------------*/

static void prvCreateDemoSpecificTimers( void )
{
	/* This function creates the timers, but does not start them.  This is
	because the standard demo timer test is started from main(), after this
	function is	called.  The standard demo timer test will deliberately fill the
	timer command queue - and will fail the test if the command queue already
	holds start commands for the timers created here.  Instead, the timers
	created in this function are started from the idle task, at which time, the
	timer service/daemon task will be running, and will have drained the timer
	command	queue. */

	/* Create the software timer that is responsible for turning off the LED
	if the button is not pushed within 5000ms, as described at the top of
	this file. */
	xLEDButtonTimer = xTimerCreate( "ButtonLEDTimer", 					/* A text name, purely to help debugging. */
									( mainBUTTON_LED_TIMER_PERIOD_MS ),	/* The timer period, in this case 5000ms (5s). */
									pdFALSE,							/* This is a one shot timer, so xAutoReload is set to pdFALSE. */
									( void * ) 0,						/* The ID is not used, so can be set to anything. */
									prvButtonLEDTimerCallback			/* The callback function that switches the LED off. */
							);

	/* Create the software timer that performs the 'check' functionality,
	as described at the top of this file. */
	xCheckTimer = xTimerCreate( "CheckTimer",						/* A text name, purely to help debugging. */
								( mainCHECK_TIMER_PERIOD_MS ),		/* The timer period, in this case 3000ms (3s). */
								pdTRUE,								/* This is an auto-reload timer, so xAutoReload is set to pdTRUE. */
								( void * ) 0,						/* The ID is not used, so can be set to anything. */
								prvCheckTimerCallback				/* The callback function that inspects the status of all the other tasks. */
							  );

	/* Create the software timers used to simply flash LEDs.  These two timers
	share a callback function, so the callback parameter is used to pass in the
	LED that should be toggled. */
	xLED1Timer = xTimerCreate( "LED1Timer",						/* A text name, purely to help debugging. */
								( mainLED1_TIMER_PERIOD_MS ),	/* The timer period, in this case 3000ms (3s). */
								pdTRUE,							/* This is an auto-reload timer, so xAutoReload is set to pdTRUE. */
								( void * ) mainLED0,			/* The ID is used to pass in the number of the LED to be toggled. */
								prvLEDTimerCallback				/* The callback function simply toggles the LED specified by its parameter. */
							  );

	xLED2Timer = xTimerCreate( "LED2Timer",						/* A text name, purely to help debugging. */
								( mainLED2_TIMER_PERIOD_MS ),	/* The timer period, in this case 3000ms (3s). */
								pdTRUE,							/* This is an auto-reload timer, so xAutoReload is set to pdTRUE. */
								( void * ) mainLED1,			/* The ID is used to pass in the number of the LED to be toggled. */
								prvLEDTimerCallback				/* The callback function simply toggles the LED specified by its parameter. */
							  );
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
	/* Called if a call to pvPortMalloc() fails because there is insufficient
	free memory available in the FreeRTOS heap.  pvPortMalloc() is called
	internally by FreeRTOS API functions that create tasks, queues, software
	timers, and semaphores.  The size of the FreeRTOS heap is set by the
	configTOTAL_HEAP_SIZE configuration constant in FreeRTOSConfig.h. */
	taskDISABLE_INTERRUPTS();
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName )
{
	( void ) pcTaskName;
	( void ) pxTask;

	/* Run time stack overflow checking is performed if
	configCHECK_FOR_STACK_OVERFLOW is defined to 1 or 2.  This hook
	function is called if a stack overflow is detected. */
	taskDISABLE_INTERRUPTS();
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
static long lPrintedOut = pdFALSE;
volatile size_t xFreeHeapSpace;

	if( lPrintedOut == pdFALSE )
	{
		lPrintedOut = pdTRUE;

		/* The timer command queue will have been filled when the timer test
		tasks were created in main() (this is part of the test they perform).
		Therefore, while the check and LED timers can be created in main(), they
		cannot be started from main().  Once the scheduler has started, the timer
		service	task will drain the command queue, and now the check and LED
		timers can be started successfully.  Normally the idle task must not
		call a function that could cause it to block in case there are no tasks
		that are able to run.  In this case, however, it is ok as posting to the
		timer command queue guarantees that at least the timer service/daemon
		task will be able to execute. */
		xTimerStart( xCheckTimer, portMAX_DELAY );
		xTimerStart( xLED1Timer, portMAX_DELAY );
		xTimerStart( xLED2Timer, portMAX_DELAY );

		xFreeHeapSpace = xPortGetFreeHeapSize();

		if( xFreeHeapSpace > 100 )
		{
			/* By now, the kernel has allocated everything it is going to, so
			if there is a lot of heap remaining unallocated then
			the value of configTOTAL_HEAP_SIZE in FreeRTOSConfig.h can be
			reduced accordingly. */
		}
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
	/* A simple GET function used by a CGI script so it can display the
	execution status at the bottom of the task stats web page served by the
	embedded web server. */
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

void vMainConfigureTimerForRunTimeStats( void )
{
	/* How many clocks are there per tenth of a millisecond? */
	ulClocksPer10thOfAMilliSecond = configCPU_CLOCK_HZ / 10000UL;
}
/*-----------------------------------------------------------*/

unsigned long ulMainGetRunTimeCounterValue( void )
{
unsigned long ulSysTickCounts, ulTickCount, ulReturn;
const unsigned long ulSysTickReloadValue = ( configCPU_CLOCK_HZ / configTICK_RATE_HZ ) - 1UL;
volatile unsigned long * const pulCurrentSysTickCount = ( ( volatile unsigned long *) 0xe000e018 );
volatile unsigned long * const pulInterruptCTRLState = ( ( volatile unsigned long *) 0xe000ed04 );
const unsigned long ulSysTickPendingBit = 0x04000000UL;

	/* NOTE: There are potentially race conditions here.  However, it is used
	anyway to keep the examples simple, and to avoid reliance on a separate
	timer peripheral. */


	/* The SysTick is a down counter.  How many clocks have passed since it was
	last reloaded? */
	ulSysTickCounts = ulSysTickReloadValue - *pulCurrentSysTickCount;

	/* How many times has it overflowed? */
	ulTickCount = xTaskGetTickCountFromISR();

	/* This is called from the context switch, so will be called from a
	critical section.  xTaskGetTickCountFromISR() contains its own critical
	section, and the ISR safe critical sections are not designed to nest,
	so reset the critical section. */
	portSET_INTERRUPT_MASK_FROM_ISR();

	/* Is there a SysTick interrupt pending? */
	if( ( *pulInterruptCTRLState & ulSysTickPendingBit ) != 0UL )
	{
		/* There is a SysTick interrupt pending, so the SysTick has overflowed
		but the tick count not yet incremented. */
		ulTickCount++;

		/* Read the SysTick again, as the overflow might have occurred since
		it was read last. */
		ulSysTickCounts = ulSysTickReloadValue - *pulCurrentSysTickCount;
	}

	/* Convert the tick count into tenths of a millisecond.  THIS ASSUMES
	configTICK_RATE_HZ is 1000! */
	ulReturn = ( ulTickCount * 10UL ) ;

	/* Add on the number of tenths of a millisecond that have passed since the
	tick count last got updated. */
	ulReturn += ( ulSysTickCounts / ulClocksPer10thOfAMilliSecond );

	return ulReturn;
}
/*-----------------------------------------------------------*/

