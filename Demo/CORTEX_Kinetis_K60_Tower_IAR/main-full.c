/*
    FreeRTOS V7.0.1 - Copyright (C) 2011 Real Time Engineers Ltd.


	FreeRTOS supports many tools and architectures. V7.0.0 is sponsored by:
	Atollic AB - Atollic provides professional embedded systems development
	tools for C/C++ development, code analysis and test automation.
	See http://www.atollic.com


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

/*
 * main-blinky.c is included when the "Blinky" build configuration is used.
 * main-full.c is included when the "Full" build configuration is used.
 *
 * main-full.c (this file) defines a comprehensive demo that creates many
 * tasks, queues, semaphores and timers.  It also demonstrates how Cortex-M3
 * interrupts can interact with FreeRTOS tasks/timers.
 *
 * This project runs on the SK-FM3-100PMC evaluation board, which is populated
 * with an MB9BF5006N Cortex-M3 based microcontroller.
 *
 * The main() Function:
 * main() creates three demo specific software timers, one demo specific queue,
 * and two demo specific tasks.  It then creates a whole host of 'standard
 * demo' tasks/queues/semaphores, before starting the scheduler.  The demo
 * specific tasks and timers are described in the comments here.  The standard
 * demo tasks are described on the FreeRTOS.org web site.
 *
 * The standard demo tasks provide no specific functionality.  They are
 * included to both test the FreeRTOS port, and provide examples of how the
 * various FreeRTOS API functions can be used.
 *
 * This demo creates 43 tasks in total.  If you want a simpler demo, use the
 * Blinky build configuration.
 *
 * The Demo Specific LED Software Timer and the Button Interrupt:
 * The user button SW2 is configured to generate an interrupt each time it is
 * pressed.  The interrupt service routine switches an LED on, and resets the
 * LED software timer.  The LED timer has a 5000 millisecond (5 second) period,
 * and uses a callback function that is defined to just turn the LED off again.
 * Therefore, pressing the user button will turn the LED on, and the LED will
 * remain on until a full five seconds pass without the button being pressed.
 * See the documentation page for this demo on the FreeRTOS.org web site to see
 * which LED is used.
 *
 * The Demo Specific "Check" Callback Function:
 * This is called each time the 'check' timer expires.  The check timer
 * callback function inspects all the standard demo tasks to see if they are
 * all executing as expected.  The check timer is initially configured to
 * expire every three seconds, but will shorted this to every 500ms if an error
 * is ever discovered.  The check timer callback toggles the LED defined by
 * the mainCHECK_LED definition each time it executes.  Therefore, if LED
 * mainCHECK_LED is toggling every three seconds, then no error have been found.
 * If LED mainCHECK_LED is toggling every 500ms, then at least one errors has
 * been found.  The variable pcStatusMessage is set to a string that indicates
 * which task reported an error.  See the documentation page for this demo on
 * the FreeRTOS.org web site to see which LED in the 7 segment display is used.
 *
 * The Demo Specific Idle Hook Function:
 * The idle hook function demonstrates how to query the amount of FreeRTOS heap
 * space that is remaining (see vApplicationIdleHook() defined in this file).
 *
 * The Demo Specific Tick Hook Function:
 * The tick hook function is used to test the interrupt safe software timer
 * functionality.
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
#include "comtest2.h"
#include "PollQ.h"
#include "countsem.h"
#include "dynamic.h"

/* The rate at which data is sent to the queue, specified in milliseconds, and
converted to ticks using the portTICK_RATE_MS constant. */
#define mainQUEUE_SEND_FREQUENCY_MS	( 200 / portTICK_RATE_MS )

/* The number of items the queue can hold.  This is 1 as the receive task
will remove items as they are added, meaning the send task should always find
the queue empty. */
#define mainQUEUE_LENGTH			( 1 )

/* The LED toggled by the check timer callback function.  */
#define mainCHECK_LED				3UL

/* The LED turned on by the button interrupt, and turned off by the LED timer. */
#define mainTIMER_CONTROLLED_LED	2UL

/* The LEDs toggled by the two simple flash LED timers. */
#define mainLED0					0UL
#define mainLED1					1UL

/* The LED used by the comtest tasks. See the comtest.c file for more
information.  In this case, the LED is deliberatly out of the valid range as
all the available LEDs are already used by other tasks and timers. */
#define mainCOM_TEST_LED			( 4 )

/* Constant used by the standard timer test functions. */
#define mainTIMER_TEST_PERIOD		( 50 )

/* Priorities used by the various different standard demo tasks. */
#define mainCHECK_TASK_PRIORITY		( configMAX_PRIORITIES - 1 )
#define mainQUEUE_POLL_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainSEM_TEST_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainCREATOR_TASK_PRIORITY   ( tskIDLE_PRIORITY + 3 )
#define mainINTEGER_TASK_PRIORITY   ( tskIDLE_PRIORITY )
#define mainGEN_QUEUE_TASK_PRIORITY	( tskIDLE_PRIORITY )
#define mainCOM_TEST_PRIORITY		( tskIDLE_PRIORITY + 2 )

/* Priorities defined in this main-full.c file. */
#define mainQUEUE_RECEIVE_TASK_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define	mainQUEUE_SEND_TASK_PRIORITY		( tskIDLE_PRIORITY + 1 )

/* The period at which the check timer will expire, in ms, provided no errors
have been reported by any of the standard demo tasks.  ms are converted to the
equivalent in ticks using the portTICK_RATE_MS constant. */
#define mainCHECK_TIMER_PERIOD_MS			( 3000UL / portTICK_RATE_MS )

/* The period at which the check timer will expire, in ms, if an error has been
reported in one of the standard demo tasks.  ms are converted to the equivalent
in ticks using the portTICK_RATE_MS constant. */
#define mainERROR_CHECK_TIMER_PERIOD_MS 	( 500UL / portTICK_RATE_MS )

/* The LED will remain on until the button has not been pushed for a full
5000ms. */
#define mainBUTTON_LED_TIMER_PERIOD_MS		( 5000UL / portTICK_RATE_MS )

/* The period at which the two simple LED flash timers will execute their
callback functions. */
#define mainLED1_TIMER_PERIOD_MS			( 200 / portTICK_RATE_MS )
#define mainLED2_TIMER_PERIOD_MS			( 600 / portTICK_RATE_MS )

/* A block time of zero simply means "don't block". */
#define mainDONT_BLOCK						( 0UL )

/* Baud rate used by the comtest tasks. */
#define mainCOM_TEST_BAUD_RATE				( 115200UL )

/* The vector used by the GPIO port E.  Button SW2 is configured to generate
an interrput on this port. */
#define mainGPIO_E_VECTOR					( 107 - 16 )

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
 * The LED timer callback function.  This does nothing but switch an LED off.
 */
static void prvButtonLEDTimerCallback( xTimerHandle xTimer );

/*
 * The callback function used by both simple LED flash timers.  Both timers use
 * the same callback, so the function parameter is used to determine which LED
 * should be flashed (effectively to determine which timer has expired.
 */
static void prvLEDTimerCallback( xTimerHandle xTimer );

/*
 * The check timer callback function, as described at the top of this file.
 */
static void prvCheckTimerCallback( xTimerHandle xTimer );

/*
 * This is not a 'standard' partest function, so the prototype is not in
 * partest.h, and is instead included here.
 */
void vParTestSetLEDFromISR( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue );

/*-----------------------------------------------------------*/

/* The queue used by both application specific demo tasks defined in this file. */
static xQueueHandle xQueue = NULL;

/* The LED software timer.  This uses prvButtonLEDTimerCallback() as it's callback
function. */
static xTimerHandle xLEDTimer = NULL;

/* The check timer.  This uses prvCheckTimerCallback() as its callback
function. */
static xTimerHandle xCheckTimer = NULL;

/* LED timers - these simply flash LEDs, each using a different frequency. */
static xTimerHandle xLED1Timer = NULL, xLED2Timer = NULL;

/* If an error is detected in a standard demo task, then pcStatusMessage will
be set to point to a string that identifies the offending task.  This is just
to make debugging easier. */
static const char *pcStatusMessage = NULL;

/*-----------------------------------------------------------*/

void main( void )
{
	/* Configure the NVIC, LED outputs and button inputs. */
	prvSetupHardware();

	/* Create the queue. */
	xQueue = xQueueCreate( mainQUEUE_LENGTH, sizeof( unsigned long ) );

	if( xQueue != NULL )
	{
		/* Create the timers that are specific to this demo - other timers are
		created as part of the standard demo within vStartTimerDemoTask. */
		prvCreateDemoSpecificTimers();

		/* Create a lot of 'standard demo' tasks.  Over 40 tasks are created in
		this demo.  For a much simpler demo, select the 'blinky' build
		configuration. */
		vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
		vCreateBlockTimeTasks();
		vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
		vStartGenericQueueTasks( mainGEN_QUEUE_TASK_PRIORITY );
		vStartQueuePeekTasks();
		vStartRecursiveMutexTasks();
		vStartTimerDemoTask( mainTIMER_TEST_PERIOD );
//_RB_		vAltStartComTestTasks( mainCOM_TEST_PRIORITY, mainCOM_TEST_BAUD_RATE, mainCOM_TEST_LED );
		vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
		vStartCountingSemaphoreTasks();
		vStartDynamicPriorityTasks();
		
		/* The suicide tasks must be created last, as they need to know how many
		tasks were running prior to their creation in order to ascertain whether
		or not the correct/expected number of tasks are running at any given
		time. */
		vCreateSuicidalTasks( mainCREATOR_TASK_PRIORITY );

		/* Start the tasks and timer running. */
		vTaskStartScheduler();
	}

	/* If all is well, the scheduler will now be running, and the following line
	will never be reached.  If the following line does execute, then there was
	insufficient FreeRTOS heap memory available for the idle and/or timer tasks
	to be created.  See the memory management section on the FreeRTOS web site
	for more details. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvCheckTimerCallback( xTimerHandle xTimer )
{
static long lChangedTimerPeriodAlready = pdFALSE;

	/* Check the standard demo tasks are running without error.   Latch the
	latest reported error in the pcStatusMessage character pointer. */
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

if( 0 )//_RB_	if( xAreComTestTasksStillRunning() != pdPASS )
	{
		pcStatusMessage = "Error: ComTest\n";
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
			printf( "%s", pcStatusMessage );
			
			/* This call to xTimerChangePeriod() uses a zero block time.  Functions
			called from inside of a timer callback function must *never* attempt
			to block. */
			xTimerChangePeriod( xCheckTimer, ( mainERROR_CHECK_TIMER_PERIOD_MS ), mainDONT_BLOCK );
		}
	}
}
/*-----------------------------------------------------------*/

static void prvButtonLEDTimerCallback( xTimerHandle xTimer )
{
	/* The timer has expired - so no button pushes have occurred in the last
	five seconds - turn the LED off. */
	vParTestSetLED( mainTIMER_CONTROLLED_LED, pdFALSE );
}
/*-----------------------------------------------------------*/

static void prvLEDTimerCallback( xTimerHandle xTimer )
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
	vParTestToggleLED( mainTIMER_CONTROLLED_LED );

	/* This interrupt safe FreeRTOS function can be called from this interrupt
	because the interrupt priority is below the
	configMAX_SYSCALL_INTERRUPT_PRIORITY setting in FreeRTOSConfig.h. */
	xTimerResetFromISR( xLEDTimer, &xHigherPriorityTaskWoken );

	/* Clear the interrupt before leaving.  This just clears all the interrupts
	for simplicity, as only one is actually used in this simple demo anyway. */
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
	
	/* Configure the LED outputs. */
	vParTestInitialise();
}
/*-----------------------------------------------------------*/

static void prvCreateDemoSpecificTimers( void )
{
	/* This function creates the timers, but does not start them.  This is
	because the standard demo timer test is started after this function is
	called.  The standard demo timer test will deliberatly fill the timer
	command queue - and will fail the test if the command queue already holds
	start commands for the timers created here.  Instead, the timers created in
	this function are started from the idle task, at which time, the timer
	service/daemon task will be running, and will have drained the timer command
	queue. */
	
	/* Create the software timer that is responsible for turning off the LED
	if the button is not pushed within 5000ms, as described at the top of
	this file. */
	xLEDTimer = xTimerCreate( 	( const signed char * ) "ButtonLEDTimer", 	/* A text name, purely to help debugging. */
								( mainBUTTON_LED_TIMER_PERIOD_MS ),			/* The timer period, in this case 5000ms (5s). */
								pdFALSE,									/* This is a one shot timer, so xAutoReload is set to pdFALSE. */
								( void * ) 0,								/* The ID is not used, so can be set to anything. */
								prvButtonLEDTimerCallback					/* The callback function that switches the LED off. */
							);

	/* Create the software timer that performs the 'check' functionality,
	as described at the top of this file. */
	xCheckTimer = xTimerCreate( ( const signed char * ) "CheckTimer",/* A text name, purely to help debugging. */
								( mainCHECK_TIMER_PERIOD_MS ),		/* The timer period, in this case 3000ms (3s). */
								pdTRUE,								/* This is an auto-reload timer, so xAutoReload is set to pdTRUE. */
								( void * ) 0,						/* The ID is not used, so can be set to anything. */
								prvCheckTimerCallback				/* The callback function that inspects the status of all the other tasks. */
							  );
	
	/* Create the software timers used to simply flash LEDs.  These two timers
	share a callback function, so the callback parameter is used to pass in the
	LED that should be toggled. */
	xLED1Timer = xTimerCreate( ( const signed char * ) "LED1Timer",/* A text name, purely to help debugging. */
								( mainLED1_TIMER_PERIOD_MS ),		/* The timer period, in this case 3000ms (3s). */
								pdTRUE,								/* This is an auto-reload timer, so xAutoReload is set to pdTRUE. */
								( void * ) mainLED0,				/* The ID is used to pass in the number of the LED to be toggled. */
								prvLEDTimerCallback					/* The callback function simply toggles the LED specified by its parameter. */
							  );

	xLED2Timer = xTimerCreate( ( const signed char * ) "LED2Timer",/* A text name, purely to help debugging. */
								( mainLED2_TIMER_PERIOD_MS ),		/* The timer period, in this case 3000ms (3s). */
								pdTRUE,								/* This is an auto-reload timer, so xAutoReload is set to pdTRUE. */
								( void * ) mainLED1,				/* The ID is used to pass in the number of the LED to be toggled. */
								prvLEDTimerCallback					/* The callback function simply toggles the LED specified by its parameter. */
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

void vApplicationStackOverflowHook( xTaskHandle *pxTask, signed char *pcTaskName )
{
	( void ) pcTaskName;
	( void ) pxTask;

	/* Run time stack overflow checking is performed if
	configconfigCHECK_FOR_STACK_OVERFLOW is defined to 1 or 2.  This hook
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
		service	task will drain the command queue, and now the check and digit
		counter timers can be started successfully. */
		xTimerStart( xCheckTimer, portMAX_DELAY );
		xTimerStart( xLED1Timer, portMAX_DELAY );
		xTimerStart( xLED2Timer, portMAX_DELAY );
		
		xFreeHeapSpace = xPortGetFreeHeapSize();
		printf( "%d bytes of FreeRTOS heap remain unused - configTOTAL_HEAP_SIZE can be reduced\n", xFreeHeapSpace );
		
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

