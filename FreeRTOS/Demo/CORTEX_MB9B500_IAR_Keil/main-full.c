/*
    FreeRTOS V8.2.1 - Copyright (C) 2015 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    ***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
    ***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that is more than just the market leader, it     *
     *    is the industry's de facto standard.                               *
     *                                                                       *
     *    Help yourself get started quickly while simultaneously helping     *
     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
     *    tutorial book, reference manual, or both:                          *
     *    http://www.FreeRTOS.org/Documentation                              *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
    the FAQ page "My application does not run, what could be wrong?".  Have you
    defined configASSERT()?

    http://www.FreeRTOS.org/support - In return for receiving this top quality
    embedded software for free we request you assist our global community by
    participating in the support forum.

    http://www.FreeRTOS.org/training - Investing in training allows your team to
    be as productive as possible as early as possible.  Now you can receive
    FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
    Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

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
 * The Demo Specific Queue Send Task:
 * The queue send task is implemented by the prvQueueSendTask() function in
 * this file.  prvQueueSendTask() sits in a loop that causes it to repeatedly
 * block for 200 milliseconds, before sending the value 100 to the queue that
 * was created within main().  Once the value is sent, the task loops back
 * around to block for another 200 milliseconds.
 *
 * The Demo Specific Queue Receive Task:
 * The queue receive task is implemented by the prvQueueReceiveTask() function
 * in this file.  prvQueueReceiveTask() sits in a loop that causes it to
 * repeatedly attempt to read data from the queue that was created within
 * main().  When data is received, the task checks the value of the data, and
 * if the value equals the expected 100, toggles an LED in the 7 segment display
 * (see the documentation page for this demo on the FreeRTOS.org site to see
 * which LED is used).  The 'block time' parameter passed to the queue receive
 * function specifies that the task should be held in the Blocked state
 * indefinitely to wait for data to be available on the queue.  The queue
 * receive task will only leave the Blocked state when the queue send task
 * writes to the queue.  As the queue send task writes to the queue every 200
 * milliseconds, the queue receive task leaves the Blocked state every 200
 * milliseconds, and therefore toggles the LED every 200 milliseconds.
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
 * The Demo Specific "Digit Counter" Callback Function:
 * This is called each time the 'digit counter' timer expires.  It causes the
 * digits 0 to 9 to be displayed in turn as the first character of the two
 * character display.  The LEDs in the other digit of the two character
 * display are used as general purpose LEDs, as described in this comment block.
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

/* Fujitsu drivers/libraries. */
#include "mb9bf506n.h"
#include "system_mb9bf50x.h"

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
converted to ticks using the portTICK_PERIOD_MS constant. */
#define mainQUEUE_SEND_FREQUENCY_MS	( 200 / portTICK_PERIOD_MS )

/* The number of items the queue can hold.  This is 1 as the receive task
will remove items as they are added, meaning the send task should always find
the queue empty. */
#define mainQUEUE_LENGTH			( 1 )

/* The LED toggled by the check timer callback function.  This is an LED in the
second digit of the two digit 7 segment display.  See the documentation page
for this demo on the FreeRTOS.org web site to see which LED this relates to. */
#define mainCHECK_LED				0x07UL

/* The LED toggle by the queue receive task.  This is an LED in the second digit
of the two digit 7 segment display.  See the documentation page for this demo on
the FreeRTOS.org web site to see which LED this relates to. */
#define mainTASK_CONTROLLED_LED		0x06UL

/* The LED turned on by the button interrupt, and turned off by the LED timer.
This is an LED in the second digit of the two digit 7 segment display.  See the
documentation page for this demo on the FreeRTOS.org web site to see which LED
this relates to. */
#define mainTIMER_CONTROLLED_LED	0x05UL

/* The LED used by the comtest tasks. See the comtest.c file for more
information.  The LEDs used by the comtest task are in the second digit of the
two digit 7 segment display.  See the documentation page for this demo on the
FreeRTOS.org web site to see which LEDs this relates to. */
#define mainCOM_TEST_LED			( 3 )

/* Constant used by the standard timer test functions. */
#define mainTIMER_TEST_PERIOD		( 50 )

/* Priorities used by the various different standard demo tasks. */
#define mainCHECK_TASK_PRIORITY		( configMAX_PRIORITIES - 1 )
#define mainQUEUE_POLL_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainSEM_TEST_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainCREATOR_TASK_PRIORITY   ( tskIDLE_PRIORITY + 3 )
#define mainFLASH_TASK_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainINTEGER_TASK_PRIORITY   ( tskIDLE_PRIORITY )
#define mainGEN_QUEUE_TASK_PRIORITY	( tskIDLE_PRIORITY )
#define mainCOM_TEST_PRIORITY		( tskIDLE_PRIORITY + 2 )

/* Priorities defined in this main-full.c file. */
#define mainQUEUE_RECEIVE_TASK_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define	mainQUEUE_SEND_TASK_PRIORITY		( tskIDLE_PRIORITY + 1 )

/* The period at which the check timer will expire, in ms, provided no errors
have been reported by any of the standard demo tasks.  ms are converted to the
equivalent in ticks using the portTICK_PERIOD_MS constant. */
#define mainCHECK_TIMER_PERIOD_MS			( 3000UL / portTICK_PERIOD_MS )

/* The period at which the check timer will expire, in ms, if an error has been
reported in one of the standard demo tasks.  ms are converted to the equivalent
in ticks using the portTICK_PERIOD_MS constant. */
#define mainERROR_CHECK_TIMER_PERIOD_MS 	( 500UL / portTICK_PERIOD_MS )

/* The period at which the digit counter timer will expire, in ms, and converted
to ticks using the portTICK_PERIOD_MS constant. */
#define mainDIGIT_COUNTER_TIMER_PERIOD_MS 	( 250UL / portTICK_PERIOD_MS )

/* The LED will remain on until the button has not been pushed for a full
5000ms. */
#define mainLED_TIMER_PERIOD_MS				( 5000UL / portTICK_PERIOD_MS )

/* A zero block time. */
#define mainDONT_BLOCK						( 0UL )

/* Baud rate used by the comtest tasks. */
#define mainCOM_TEST_BAUD_RATE				( 115200UL )

/*-----------------------------------------------------------*/

/*
 * Setup the NVIC, LED outputs, and button inputs.
 */
static void prvSetupHardware( void );

/*
 * The application specific (not common demo) tasks as described in the comments
 * at the top of this file.
 */
static void prvQueueReceiveTask( void *pvParameters );
static void prvQueueSendTask( void *pvParameters );

/*
 * The LED timer callback function.  This does nothing but switch an LED off.
 */
static void prvLEDTimerCallback( TimerHandle_t xTimer );

/*
 * The check timer callback function, as described at the top of this file.
 */
static void prvCheckTimerCallback( TimerHandle_t xTimer );

/*
 * The digit counter callback function, as described at the top of this file.
 */
static void prvDigitCounterTimerCallback( TimerHandle_t xTimer );

/*
 * This is not a 'standard' partest function, so the prototype is not in
 * partest.h, and is instead included here.
 */
void vParTestSetLEDFromISR( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue );

/*-----------------------------------------------------------*/

/* The queue used by both application specific demo tasks defined in this file. */
static QueueHandle_t xQueue = NULL;

/* The LED software timer.  This uses prvLEDTimerCallback() as it's callback
function. */
static TimerHandle_t xLEDTimer = NULL;

/* The digit counter software timer.  This displays a counting digit on one half
of the seven segment displays. */
static TimerHandle_t xDigitCounterTimer = NULL;

/* The check timer.  This uses prvCheckTimerCallback() as its callback
function. */
static TimerHandle_t xCheckTimer = NULL;

/* If an error is detected in a standard demo task, then pcStatusMessage will
be set to point to a string that identifies the offending task.  This is just
to make debugging easier. */
static const char *pcStatusMessage = NULL;

/*-----------------------------------------------------------*/

int main(void)
{
	/* Configure the NVIC, LED outputs and button inputs. */
	prvSetupHardware();

	/* Create the queue. */
	xQueue = xQueueCreate( mainQUEUE_LENGTH, sizeof( unsigned long ) );

	if( xQueue != NULL )
	{
		/* Start the two application specific demo tasks, as described in the
		comments at the top of this	file. */
		xTaskCreate( prvQueueReceiveTask, "Rx", configMINIMAL_STACK_SIZE, NULL, mainQUEUE_RECEIVE_TASK_PRIORITY, NULL );
		xTaskCreate( prvQueueSendTask, "TX", configMINIMAL_STACK_SIZE, NULL, mainQUEUE_SEND_TASK_PRIORITY, NULL );

		/* Create the software timer that is responsible for turning off the LED
		if the button is not pushed within 5000ms, as described at the top of
		this file. */
		xLEDTimer = xTimerCreate( 	"LEDTimer", 				/* A text name, purely to help debugging. */
									( mainLED_TIMER_PERIOD_MS ),/* The timer period, in this case 5000ms (5s). */
									pdFALSE,					/* This is a one shot timer, so xAutoReload is set to pdFALSE. */
									( void * ) 0,				/* The ID is not used, so can be set to anything. */
									prvLEDTimerCallback			/* The callback function that switches the LED off. */
								);

		/* Create the software timer that performs the 'check' functionality,
		as described at the top of this file. */
		xCheckTimer = xTimerCreate( "CheckTimer",					/* A text name, purely to help debugging. */
									( mainCHECK_TIMER_PERIOD_MS ),	/* The timer period, in this case 3000ms (3s). */
									pdTRUE,							/* This is an auto-reload timer, so xAutoReload is set to pdTRUE. */
									( void * ) 0,					/* The ID is not used, so can be set to anything. */
									prvCheckTimerCallback			/* The callback function that inspects the status of all the other tasks. */
								  );

		/* Create the software timer that performs the 'digit counting'
		functionality, as described at the top of this file. */
		xDigitCounterTimer = xTimerCreate( "DigitCounter",					/* A text name, purely to help debugging. */
									( mainDIGIT_COUNTER_TIMER_PERIOD_MS ),	/* The timer period, in this case 3000ms (3s). */
									pdTRUE,									/* This is an auto-reload timer, so xAutoReload is set to pdTRUE. */
									( void * ) 0,							/* The ID is not used, so can be set to anything. */
									prvDigitCounterTimerCallback			/* The callback function that inspects the status of all the other tasks. */
								  );

		/* Create a lot of 'standard demo' tasks.  Over 40 tasks are created in
		this demo.  For a much simpler demo, select the 'blinky' build
		configuration. */
		vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
		vCreateBlockTimeTasks();
		vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
		vStartGenericQueueTasks( mainGEN_QUEUE_TASK_PRIORITY );
		vStartLEDFlashTasks( mainFLASH_TASK_PRIORITY );
		vStartQueuePeekTasks();
		vStartRecursiveMutexTasks();
		vStartTimerDemoTask( mainTIMER_TEST_PERIOD );
		vAltStartComTestTasks( mainCOM_TEST_PRIORITY, mainCOM_TEST_BAUD_RATE, mainCOM_TEST_LED );
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

static void prvCheckTimerCallback( TimerHandle_t xTimer )
{
	/* Check the standard demo tasks are running without error.   Latch the
	latest reported error in the pcStatusMessage character pointer. */
	if( xAreGenericQueueTasksStillRunning() != pdTRUE )
	{
		pcStatusMessage = "Error: GenQueue";
	}

	if( xAreQueuePeekTasksStillRunning() != pdTRUE )
	{
		pcStatusMessage = "Error: QueuePeek\r\n";
	}

	if( xAreBlockingQueuesStillRunning() != pdTRUE )
	{
		pcStatusMessage = "Error: BlockQueue\r\n";
	}

	if( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
	{
		pcStatusMessage = "Error: BlockTime\r\n";
	}

	if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	{
		pcStatusMessage = "Error: SemTest\r\n";
	}

	if( xIsCreateTaskStillRunning() != pdTRUE )
	{
		pcStatusMessage = "Error: Death\r\n";
	}

	if( xAreRecursiveMutexTasksStillRunning() != pdTRUE )
	{
		pcStatusMessage = "Error: RecMutex\r\n";
	}

	if( xAreComTestTasksStillRunning() != pdPASS )
	{
		pcStatusMessage = "Error: ComTest\r\n";
	}

	if( xAreTimerDemoTasksStillRunning( ( mainCHECK_TIMER_PERIOD_MS ) ) != pdTRUE )
	{
		pcStatusMessage = "Error: TimerDemo";
	}

	if( xArePollingQueuesStillRunning() != pdTRUE )
	{
		pcStatusMessage = "Error: PollQueue";
	}

	if( xAreCountingSemaphoreTasksStillRunning() != pdTRUE )
	{
		pcStatusMessage = "Error: CountSem";
	}

	if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
	{
		pcStatusMessage = "Error: DynamicPriority";
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
		/* This call to xTimerChangePeriod() uses a zero block time.  Functions
		called from inside of a timer callback function must *never* attempt
		to block. */
		xTimerChangePeriod( xCheckTimer, ( mainERROR_CHECK_TIMER_PERIOD_MS ), mainDONT_BLOCK );
	}
}
/*-----------------------------------------------------------*/

static void prvLEDTimerCallback( TimerHandle_t xTimer )
{
	/* The timer has expired - so no button pushes have occurred in the last
	five seconds - turn the LED off. */
	vParTestSetLED( mainTIMER_CONTROLLED_LED, pdFALSE );
}
/*-----------------------------------------------------------*/

static void prvDigitCounterTimerCallback( TimerHandle_t xTimer )
{
/* Define the bit patterns that display numbers on the seven segment display. */
static const unsigned short usNumbersPatterns[] = { 0xC000U, 0xF900U, 0xA400U, 0xB000U, 0x9900U, 0x9200U, 0x8200U, 0xF800U, 0x8000U, 0x9000U };
static long lCounter = 0L;
const long lNumberOfDigits = 10L;

	/* Display the next number, counting up. */
	FM3_GPIO->PDOR1 = usNumbersPatterns[ lCounter ];

	/* Move onto the next digit. */
	lCounter++;

	/* Ensure the counter does not go off the end of the array. */
	if( lCounter >= lNumberOfDigits )
	{
		lCounter = 0L;
	}
}
/*-----------------------------------------------------------*/

/* The ISR executed when the user button is pushed. */
void INT0_7_Handler( void )
{
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	/* The button was pushed, so ensure the LED is on before resetting the
	LED timer.  The LED timer will turn the LED off if the button is not
	pushed within 5000ms. */
	vParTestSetLEDFromISR( mainTIMER_CONTROLLED_LED, pdTRUE );

	/* This interrupt safe FreeRTOS function can be called from this interrupt
	because the interrupt priority is below the
	configMAX_SYSCALL_INTERRUPT_PRIORITY setting in FreeRTOSConfig.h. */
	xTimerResetFromISR( xLEDTimer, &xHigherPriorityTaskWoken );

	/* Clear the interrupt before leaving.  This just clears all the interrupts
	for simplicity, as only one is actually used in this simple demo anyway. */
	FM3_EXTI->EICL = 0x0000;

	/* If calling xTimerResetFromISR() caused a task (in this case the timer
	service/daemon task) to unblock, and the unblocked task has a priority
	higher than or equal to the task that was interrupted, then
	xHigherPriorityTaskWoken will now be set to pdTRUE, and calling
	portEND_SWITCHING_ISR() will ensure the unblocked task runs next. */
	portEND_SWITCHING_ISR( xHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/

static void prvQueueSendTask( void *pvParameters )
{
TickType_t xNextWakeTime;
const unsigned long ulValueToSend = 100UL;

	/* The timer command queue will have been filled when the timer test tasks
	were created in main() (this is part of the test they perform).  Therefore,
	while the check and digit counter timers can be created in main(), they
	cannot be started from main().  Once the scheduler has started, the timer
	service	task will drain the command queue, and now the check and digit
	counter timers can be started successfully. */
	xTimerStart( xCheckTimer, portMAX_DELAY );
	xTimerStart( xDigitCounterTimer, portMAX_DELAY );

	/* Initialise xNextWakeTime - this only needs to be done once. */
	xNextWakeTime = xTaskGetTickCount();

	for( ;; )
	{
		/* Place this task in the blocked state until it is time to run again.
		The block time is specified in ticks, the constant used converts ticks
		to ms.  While in the Blocked state this task will not consume any CPU
		time. */
		vTaskDelayUntil( &xNextWakeTime, mainQUEUE_SEND_FREQUENCY_MS );

		/* Send to the queue - causing the queue receive task to unblock and
		toggle an LED.  0 is used as the block time so the sending operation
		will not block - it shouldn't need to block as the queue should always
		be empty at this point in the code. */
		xQueueSend( xQueue, &ulValueToSend, mainDONT_BLOCK );
	}
}
/*-----------------------------------------------------------*/

static void prvQueueReceiveTask( void *pvParameters )
{
unsigned long ulReceivedValue;

	for( ;; )
	{
		/* Wait until something arrives in the queue - this task will block
		indefinitely provided INCLUDE_vTaskSuspend is set to 1 in
		FreeRTOSConfig.h. */
		xQueueReceive( xQueue, &ulReceivedValue, portMAX_DELAY );

		/*  To get here something must have been received from the queue, but
		is it the expected value?  If it is, toggle the LED. */
		if( ulReceivedValue == 100UL )
		{
			vParTestToggleLED( mainTASK_CONTROLLED_LED );
		}
	}
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
const unsigned short usButtonInputBit = 0x01U;

	SystemInit();
	SystemCoreClockUpdate();

	/* Initialise the IO used for the LEDs on the 7 segment displays. */
	vParTestInitialise();

	/* Set the switches to input (P18->P1F). */
	FM3_GPIO->DDR5 = 0x0000;
	FM3_GPIO->PFR5 = 0x0000;

	/* Assign the button input as GPIO. */
	FM3_GPIO->PFR1 |= usButtonInputBit;

	/* Button interrupt on falling edge. */
	FM3_EXTI->ELVR  = 0x0003;

	/* Clear all external interrupts. */
	FM3_EXTI->EICL  = 0x0000;

	/* Enable the button interrupt. */
	FM3_EXTI->ENIR |= usButtonInputBit;

	/* Setup the GPIO and the NVIC for the switch used in this simple demo. */
	NVIC_SetPriority( EXINT0_7_IRQn, configLIBRARY_MAX_SYSCALL_INTERRUPT_PRIORITY );
    NVIC_EnableIRQ( EXINT0_7_IRQn );
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
	/* Called if a call to pvPortMalloc() fails because there is insufficient
	free memory available in the FreeRTOS heap.  pvPortMalloc() is called
	internally by FreeRTOS API functions that create tasks, queues, software
	timers, and semaphores.  The size of the FreeRTOS heap is set by the
	configTOTAL_HEAP_SIZE configuration constant in FreeRTOSConfig.h. */
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName )
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
volatile size_t xFreeStackSpace;

	/* This function is called on each cycle of the idle task.  In this case it
	does nothing useful, other than report the amount of FreeRTOS heap that
	remains unallocated. */
	xFreeStackSpace = xPortGetFreeHeapSize();

	if( xFreeStackSpace > 100 )
	{
		/* By now, the kernel has allocated everything it is going to, so
		if there is a lot of heap remaining unallocated then
		the value of configTOTAL_HEAP_SIZE in FreeRTOSConfig.h can be
		reduced accordingly. */
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

