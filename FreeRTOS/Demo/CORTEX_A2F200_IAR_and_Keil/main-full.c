/*
    FreeRTOS V7.4.0 - Copyright (C) 2013 Real Time Engineers Ltd.

    FEATURES AND PORTS ARE ADDED TO FREERTOS ALL THE TIME.  PLEASE VISIT
    http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

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

    >>>>>>NOTE<<<<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
    details. You should have received a copy of the GNU General Public License
    and the FreeRTOS license exception along with FreeRTOS; if not itcan be
    viewed here: http://www.freertos.org/a00114.html and also obtained by
    writing to Real Time Engineers Ltd., contact details for whom are available
    on the FreeRTOS WEB site.

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
    including FreeRTOS+Trace - an indispensable productivity tool, and our new
    fully thread aware and reentrant UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High 
    Integrity Systems, who sell the code with commercial support, 
    indemnification and middleware, under the OpenRTOS brand.
    
    http://www.SafeRTOS.com - High Integrity Systems also provide a safety 
    engineered and independently SIL3 certified version for use in safety and 
    mission critical applications that require provable dependability.
*/

/*
 * main-blinky.c is included when the "Blinky" build configuration is used.
 * main-full.c is included when the "Full" build configuration is used.
 *
 * main-full.c (this file) defines a comprehensive demo that creates many
 * tasks, queues, semaphores and timers.  It also demonstrates how Cortex-M3
 * interrupts can interact with FreeRTOS tasks/timers, and implements a simple
 * and small interactive web server.
 *
 * This project runs on the SmartFusion A2F-EVAL-KIT evaluation board, which
 * is populated with an A2F200M3F SmartFusion mixed signal FPGA.  The A2F200M3F
 * incorporates a Cortex-M3 microcontroller.
 *
 * The main() Function:
 * main() creates two demo specific software timers, one demo specific queue,
 * and three demo specific tasks.  It then creates a whole host of 'standard
 * demo' tasks/queues/semaphores, before starting the scheduler.  The demo
 * specific tasks and timers are described in the comments here.  The standard
 * demo tasks are described on the FreeRTOS.org web site.
 *
 * The standard demo tasks provide no specific functionality.  They are
 * included to both test the FreeRTOS port, and provide examples of how the
 * various FreeRTOS API functions can be used.
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
 * if the value equals the expected 100, toggles the green LED.  The 'block
 * time' parameter passed to the queue receive function specifies that the task
 * should be held in the Blocked state indefinitely to wait for data to be
 * available on the queue.  The queue receive task will only leave the Blocked
 * state when the queue send task writes to the queue.  As the queue send task
 * writes to the queue every 200 milliseconds, the queue receive task leaves
 * the Blocked state every 200 milliseconds, and therefore toggles the LED
 * every 200 milliseconds.
 *
 * The Demo Specific OLED Task:
 * The OLED task is a very simple task that just scrolls a message across the
 * OLED.  Ideally this would be done in a timer, but the OLED driver accesses
 * the I2C which is time consuming.
 *
 * The Demo Specific LED Software Timer and the Button Interrupt:
 * The user button SW1 is configured to generate an interrupt each time it is
 * pressed.  The interrupt service routine switches an LED on, and resets the
 * LED software timer.  The LED timer has a 5000 millisecond (5 second) period,
 * and uses a callback function that is defined to just turn the LED off again.
 * Therefore, pressing the user button will turn the LED on, and the LED will
 * remain on until a full five seconds pass without the button being pressed.
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
 * been found.  The task in which the error was discovered is displayed at the
 * bottom of the "task stats" page that is served by the embedded web server.
 *
 * The Demo Specific Idle Hook Function:
 * The idle hook function demonstrates how to query the amount of FreeRTOS heap
 * space that is remaining (see vApplicationIdleHook() defined in this file).
 *
 * The Web Server Task:
 * The IP address used by the SmartFusion target is configured by the
 * definitions configIP_ADDR0 to configIP_ADDR3, which are located in the
 * FreeRTOSConfig.h header file.  See the documentation page for this example
 * on the http://www.FreeRTOS.org web site for further connection information.
 */

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "timers.h"

/* Microsemi drivers/libraries includes. */
#include "mss_gpio.h"
#include "mss_watchdog.h"
#include "mss_timer.h"
#include "mss_ace.h"
#include "oled.h"

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

/* Priorities at which the tasks are created. */
#define mainQUEUE_RECEIVE_TASK_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define	mainQUEUE_SEND_TASK_PRIORITY		( tskIDLE_PRIORITY + 1 )

/* The rate at which data is sent to the queue, specified in milliseconds, and
converted to ticks using the portTICK_RATE_MS constant. */
#define mainQUEUE_SEND_FREQUENCY_MS			( 200 / portTICK_RATE_MS )

/* The number of items the queue can hold.  This is 1 as the receive task
will remove items as they are added, meaning the send task should always find
the queue empty. */
#define mainQUEUE_LENGTH			( 1 )

/* The LED toggled by the check timer callback function. */
#define mainCHECK_LED				0x07UL

/* The LED turned on by the button interrupt, and turned off by the LED timer. */
#define mainTIMER_CONTROLLED_LED	0x06UL

/* The LED toggle by the queue receive task. */
#define mainTASK_CONTROLLED_LED		0x05UL

/* Constant used by the standard timer test functions. */
#define mainTIMER_TEST_PERIOD		( 50 )

/* Priorities used by the various different tasks. */
#define mainCHECK_TASK_PRIORITY		( configMAX_PRIORITIES - 1 )
#define mainQUEUE_POLL_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainSEM_TEST_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainCREATOR_TASK_PRIORITY   ( tskIDLE_PRIORITY + 3 )
#define mainFLASH_TASK_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainuIP_TASK_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainOLED_TASK_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainINTEGER_TASK_PRIORITY   ( tskIDLE_PRIORITY )
#define mainGEN_QUEUE_TASK_PRIORITY	( tskIDLE_PRIORITY )

/* The WEB server uses string handling functions, which in turn use a bit more
stack than most of the other tasks. */
#define mainuIP_STACK_SIZE			( configMINIMAL_STACK_SIZE * 3 )

/* The period at which the check timer will expire, in ms, provided no errors
have been reported by any of the standard demo tasks. */
#define mainCHECK_TIMER_PERIOD_MS	( 3000UL / portTICK_RATE_MS )

/* The period at which the OLED timer will expire.  Each time it expires, it's
callback function updates the OLED text. */
#define mainOLED_PERIOD_MS			( 75UL / portTICK_RATE_MS )

/* The period at which the check timer will expire, in ms, if an error has been
reported in one of the standard demo tasks. */
#define mainERROR_CHECK_TIMER_PERIOD_MS ( 500UL / portTICK_RATE_MS )

/* The LED will remain on until the button has not been pushed for a full
5000ms. */
#define mainLED_TIMER_PERIOD_MS		( 5000UL / portTICK_RATE_MS )

/* A zero block time. */
#define mainDONT_BLOCK				( 0UL )
/*-----------------------------------------------------------*/

/*
 * Setup the NVIC, LED outputs, and button inputs.
 */
static void prvSetupHardware( void );

/*
 * The tasks as described in the comments at the top of this file.
 */
static void prvQueueReceiveTask( void *pvParameters );
static void prvQueueSendTask( void *pvParameters );

/*
 * The LED timer callback function.  This does nothing but switch the red LED
 * off.
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

/*
 * Contains the implementation of the WEB server.
 */
extern void vuIP_Task( void *pvParameters );

/*
 * A very simply task that does nothing but scroll the OLED display.  Ideally
 * this would be done within a timer, but it accesses the I2C port which is
 * time consuming.
 */
static void prvOLEDTask( void * pvParameters);

/*-----------------------------------------------------------*/

/* The queue used by both application specific demo tasks defined in this file. */
static xQueueHandle xQueue = NULL;

/* The LED software timer.  This uses prvLEDTimerCallback() as it's callback
function. */
static xTimerHandle xLEDTimer = NULL;

/* The check timer.  This uses prvCheckTimerCallback() as it's callback
function. */
static xTimerHandle xCheckTimer = NULL;

/* The status message that is displayed at the bottom of the "task stats" web
page, which is served by the uIP task.  This will report any errors picked up
by the check timer callback. */
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
		/* Start the three application specific demo tasks, as described in the
		comments at the top of this	file. */
		xTaskCreate( prvQueueReceiveTask, ( signed char * ) "Rx", configMINIMAL_STACK_SIZE, NULL, mainQUEUE_RECEIVE_TASK_PRIORITY, NULL );
		xTaskCreate( prvQueueSendTask, ( signed char * ) "TX", configMINIMAL_STACK_SIZE, NULL, mainQUEUE_SEND_TASK_PRIORITY, NULL );
		xTaskCreate( prvOLEDTask, ( signed char * ) "OLED", configMINIMAL_STACK_SIZE, NULL, mainOLED_TASK_PRIORITY, NULL );

		/* Create the software timer that is responsible for turning off the LED
		if the button is not pushed within 5000ms, as described at the top of
		this file. */
		xLEDTimer = xTimerCreate( 	( const signed char * ) "LEDTimer", /* A text name, purely to help debugging. */
									( mainLED_TIMER_PERIOD_MS ),		/* The timer period, in this case 5000ms (5s). */
									pdFALSE,							/* This is a one shot timer, so xAutoReload is set to pdFALSE. */
									( void * ) 0,						/* The ID is not used, so can be set to anything. */
									prvLEDTimerCallback					/* The callback function that switches the LED off. */
								);

		/* Create the software timer that performs the 'check' functionality,
		as described at the top of this file. */
		xCheckTimer = xTimerCreate( ( const signed char * ) "CheckTimer",/* A text name, purely to help debugging. */
									( mainCHECK_TIMER_PERIOD_MS ),		/* The timer period, in this case 3000ms (3s). */
									pdTRUE,								/* This is an auto-reload timer, so xAutoReload is set to pdTRUE. */
									( void * ) 0,						/* The ID is not used, so can be set to anything. */
									prvCheckTimerCallback				/* The callback function that inspects the status of all the other tasks. */
								  );

		/* Create a lot of 'standard demo' tasks. */
		vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
		vCreateBlockTimeTasks();
		vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
		vStartGenericQueueTasks( mainGEN_QUEUE_TASK_PRIORITY );
		vStartLEDFlashTasks( mainFLASH_TASK_PRIORITY );
		vStartQueuePeekTasks();
		vStartRecursiveMutexTasks();
		vStartTimerDemoTask( mainTIMER_TEST_PERIOD );

		/* Create the web server task. */
		xTaskCreate( vuIP_Task, ( signed char * ) "uIP", mainuIP_STACK_SIZE, NULL, mainuIP_TASK_PRIORITY, NULL );
		
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

	if( xAreTimerDemoTasksStillRunning( ( mainCHECK_TIMER_PERIOD_MS ) ) != pdTRUE )
	{
		pcStatusMessage = "Error: TimerDemo";
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

static void prvLEDTimerCallback( xTimerHandle xTimer )
{
	/* The timer has expired - so no button pushes have occurred in the last
	five seconds - turn the LED off. */
	vParTestSetLED( mainTIMER_CONTROLLED_LED, pdFALSE );
}
/*-----------------------------------------------------------*/

/* The ISR executed when the user button is pushed. */
void GPIO8_IRQHandler( void )
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

	/* Clear the interrupt before leaving. */
    MSS_GPIO_clear_irq( MSS_GPIO_8 );

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
portTickType xNextWakeTime;
const unsigned long ulValueToSend = 100UL;

	/* The timer command queue will have been filled when the timer test tasks
	were created in main() (this is part of the test they perform).  Therefore,
	while the check timer can be created in main(), it cannot be started from 
	main().  Once the scheduler has started, the timer service task will drain 
	the command queue, and now the check timer can be started successfully. */
	xTimerStart( xCheckTimer, portMAX_DELAY );

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

static void prvOLEDTask( void * pvParameters)
{
static struct oled_data xOLEDData;
static unsigned char ucOffset1 = 0, ucOffset2 = 5;
static portTickType xLastScrollTime = 0UL;

	/* Initialise the display. */
	OLED_init();

	/* Initialise the parts of the oled_data structure that do not change. */
	xOLEDData.line1          = FIRST_LINE;
	xOLEDData.string1        = " www.FreeRTOS.org";
	xOLEDData.line2          = SECOND_LINE;
	xOLEDData.string2        = " www.FreeRTOS.org";
	xOLEDData.contrast_val                 = OLED_CONTRAST_VAL;
	xOLEDData.on_off                       = OLED_HORIZ_SCROLL_OFF;
	xOLEDData.column_scrool_per_step       = OLED_HORIZ_SCROLL_STEP;
	xOLEDData.start_page                   = OLED_START_PAGE;
	xOLEDData.time_intrval_btw_scroll_step = OLED_HORIZ_SCROLL_TINVL;
	xOLEDData.end_page                     = OLED_END_PAGE;


	/* Initialise the last scroll time.  This only needs to be done once,
	because from this point on it will get automatically updated in the
	xTaskDelayUntil() API function. */
	xLastScrollTime = xTaskGetTickCount();

	for( ;; )
	{
		/* Wait until it is time to update the OLED again. */
		vTaskDelayUntil( &xLastScrollTime, mainOLED_PERIOD_MS );
		
		xOLEDData.char_offset1   = ucOffset1++;
		xOLEDData.char_offset2   = ucOffset2++;
	
		OLED_write_data( &xOLEDData, BOTH_LINES );
	}
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	SystemCoreClockUpdate();
	
	/* Disable the Watch Dog Timer */
	MSS_WD_disable( );

	/* Configure the GPIO for the LEDs. */
	vParTestInitialise();
	
	/* ACE Initialization */
	ACE_init();

	/* Setup the GPIO and the NVIC for the switch used in this simple demo. */
	NVIC_SetPriority( GPIO8_IRQn, configLIBRARY_MAX_SYSCALL_INTERRUPT_PRIORITY );
    NVIC_EnableIRQ( GPIO8_IRQn );
    MSS_GPIO_config( MSS_GPIO_8, MSS_GPIO_INPUT_MODE | MSS_GPIO_IRQ_EDGE_NEGATIVE );
    MSS_GPIO_enable_irq( MSS_GPIO_8 );
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

void vApplicationStackOverflowHook( xTaskHandle pxTask, signed char *pcTaskName )
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

char *pcGetTaskStatusMessage( void )
{
	/* Not bothered about a critical section here although technically because
	of the task priorities the pointer could change it will be atomic if not
	near atomic and its not critical. */
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
const unsigned long ulMax32BitValue = 0xffffffffUL;

	MSS_TIM64_init( MSS_TIMER_PERIODIC_MODE );
	MSS_TIM64_load_immediate( ulMax32BitValue, ulMax32BitValue );
	MSS_TIM64_start();
}
/*-----------------------------------------------------------*/

unsigned long ulGetRunTimeCounterValue( void )
{
unsigned long long ullCurrentValue;
const unsigned long long ulMax64BitValue = 0xffffffffffffffffULL;
unsigned long *pulHighWord, *pulLowWord;

	pulHighWord = ( unsigned long * ) &ullCurrentValue;
	pulLowWord = pulHighWord++;
	
	MSS_TIM64_get_current_value( ( uint32_t * ) pulHighWord, ( uint32_t * ) pulLowWord );
	
	/* Convert the down count into an upcount. */
	ullCurrentValue = ulMax64BitValue - ullCurrentValue;
	
	/* Scale to a 32bit number of suitable frequency. */
	ullCurrentValue >>= 13;

	/* Just return 32 bits. */
	return ( unsigned long ) ullCurrentValue;
}

