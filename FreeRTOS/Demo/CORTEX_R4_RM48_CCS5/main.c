#if 1
/*
    FreeRTOS V7.2.0 - Copyright (C) 2012 Real Time Engineers Ltd.


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

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                      *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************


    http://www.FreeRTOS.org - Documentation, training, latest information,
    license and contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool.

    Real Time Engineers ltd license FreeRTOS to High Integrity Systems, who sell
    the code with commercial support, indemnification, and middleware, under
    the OpenRTOS brand: http://www.OpenRTOS.com.  High Integrity Systems also
    provide a safety engineered and independently SIL3 certified version under
    the SafeRTOS brand: http://www.SafeRTOS.com.
*/

/******************************************************************************
 * This project provides two demo applications.  A simple blinky style project,
 * and a more comprehensive test and demo application.  The
 * mainCREATE_SIMPLE_BLINKY_DEMO_ONLY setting (defined in this file) is used to
 * select between the two.  The simply blinky demo is implemented and described
 * in main_blinky.c.  The more comprehensive test and demo application is
 * implemented and described in main_full.c.
 *
 * This file implements the code that is not demo specific, including the
 * hardware setup and FreeRTOS hook functions.
 *
 */

/* Standard includes. */
#include <stdio.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Standard demo includes - just needed for the LED (ParTest) initialisation
function. */
#include "partest.h"

/* Library includes. */
#include "het.h"

/* Set mainCREATE_SIMPLE_BLINKY_DEMO_ONLY to one to run the simple blinky demo,
or 0 to run the more comprehensive test and demo application. */
#define mainCREATE_SIMPLE_BLINKY_DEMO_ONLY	0

/*-----------------------------------------------------------*/

/*
 * Set up the hardware ready to run this demo.
 */
static void prvSetupHardware( void );

/*
 * main_blinky() is used when mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is set to 1.
 * main_full() is used when mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is set to 0.
 */
extern void main_blinky( void );
extern void main_full( void );

/*-----------------------------------------------------------*/

/* See the documentation page for this demo on the FreeRTOS.org web site for
full information - including hardware setup requirements. */

int main( void )
{
	/* Prepare the hardware to run this demo. */
	prvSetupHardware();

	/* The mainCREATE_SIMPLE_BLINKY_DEMO_ONLY setting is described at the top
	of this file. */
	#if mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 1
	{
		main_blinky();
	}
	#else
	{
		main_full();
	}
	#endif

	return 0;
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	/* Perform any configuration necessary to use the ParTest LED output
	functions. */
	gioInit();
	vParTestInitialise();
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
	/* vApplicationMallocFailedHook() will only be called if
	configUSE_MALLOC_FAILED_HOOK is set to 1 in FreeRTOSConfig.h.  It is a hook
	function that will get called if a call to pvPortMalloc() fails.
	pvPortMalloc() is called internally by the kernel whenever a task, queue,
	timer or semaphore is created.  It is also called by various parts of the
	demo application.  If heap_1.c or heap_2.c are used, then the size of the
	heap available to pvPortMalloc() is defined by configTOTAL_HEAP_SIZE in
	FreeRTOSConfig.h, and the xPortGetFreeHeapSize() API function can be used
	to query the size of free heap space that remains (although it does not
	provide information on how the remaining heap might be fragmented). */
	taskDISABLE_INTERRUPTS();
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
	/* vApplicationIdleHook() will only be called if configUSE_IDLE_HOOK is set
	to 1 in FreeRTOSConfig.h.  It will be called on each iteration of the idle
	task.  It is essential that code added to this hook function never attempts
	to block in any way (for example, call xQueueReceive() with a block time
	specified, or call vTaskDelay()).  If the application makes use of the
	vTaskDelete() API function (as this demo application does) then it is also
	important that vApplicationIdleHook() is permitted to return to its calling
	function, because it is the responsibility of the idle task to clean up
	memory allocated by the kernel to any task that has since been deleted. */
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( xTaskHandle pxTask, signed char *pcTaskName )
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

void vApplicationTickHook( void )
{
	/* This function will be called by each tick interrupt if
	configUSE_TICK_HOOK is set to 1 in FreeRTOSConfig.h.  User code can be
	added here, but the tick hook is called from an interrupt context, so
	code must not attempt to block, and only the interrupt safe FreeRTOS API
	functions can be used (those that end in FromISR()). */
}
/*-----------------------------------------------------------*/







#else

/*
    FreeRTOS V7.2.0 - Copyright (C) 2012 Real Time Engineers Ltd.


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
    
    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?                                      *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    
    http://www.FreeRTOS.org - Documentation, training, latest information, 
    license and contact details.
    
    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool.

    Real Time Engineers ltd license FreeRTOS to High Integrity Systems, who sell 
    the code with commercial support, indemnification, and middleware, under 
    the OpenRTOS brand: http://www.OpenRTOS.com.  High Integrity Systems also
    provide a safety engineered and independently SIL3 certified version under 
    the SafeRTOS brand: http://www.SafeRTOS.com.
*/

/* Standard includes. */
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "timers.h"
#include "queue.h"

/* Library includes. */
#include "gio.h"

/* Demo application includes. */
#include "TimerDemo.h"
#include "countsem.h"
#include "GenQTest.h"
#include "dynamic.h"


/*
 * "Check" callback function - Called each time the 'check' timer expires.  The
 * check timer executes every five seconds.  Its main function is to check that 
 * all the standard demo tasks are still operational.  Each time it executes it 
 * sends a status code to the LCD task.  The LCD task interprets the code and 
 * displays an appropriate message - which will be PASS if no tasks have 
 * reported any errors, or a message stating which task has reported an error.
 *
 * "Reg test" tasks - These fill the registers with known values, then check
 * that each register still contains its expected value.  Each task uses
 * different values.  The tasks run with very low priority so get preempted
 * very frequently.  A check variable is incremented on each iteration of the
 * test loop.  A register containing an unexpected value is indicative of an
 * error in the context switching mechanism and will result in a branch to a
 * null loop - which in turn will prevent the check variable from incrementing
 * any further and allow the check timer callback (described a above) to 
 * determine that an error has occurred.  The nature of the reg test tasks 
 * necessitates that they are written in assembly code.
 *
 * Tick hook function - called inside the RTOS tick function, this simple 
 * example does nothing but toggle an LED.
 *
 */

/* Codes sent within messages to the LCD task so the LCD task can interpret
exactly what the message it just received was.  These are sent in the
cMessageID member of the message structure (defined below). */
#define mainERROR_DYNAMIC_TASKS			( pdPASS + 1 )
#define mainERROR_GEN_QUEUE_TEST		( pdPASS + 3 )
#define mainERROR_REG_TEST				( pdPASS + 4 )
#define mainERROR_TIMER_TEST			( pdPASS + 5 )
#define mainERROR_COUNT_SEM_TEST		( pdPASS + 6 )

/* Priorities used by the test and demo tasks. */
#define mainPRINT_TASK_PRIORITY			( tskIDLE_PRIORITY + 1 )
#define mainGENERIC_QUEUE_TEST_PRIORITY	( tskIDLE_PRIORITY )
#define mainLED_TASK_PRIORITY			( tskIDLE_PRIORITY + 2 )
#define mainSTAT_TASK_PRIORITY			( tskIDLE_PRIORITY )

/* Just used to ensure parameters are passed into tasks correctly. */
#define mainTASK_PARAMETER_CHECK_VALUE	( ( void * ) 0xDEADBEEF )

/* The length of the queue (the number of items the queue can hold) that is used
to send messages from tasks and interrupts the the Print task. */
#define mainQUEUE_LENGTH				( 5 )

/* The base period used by the timer test tasks. */
#define mainTIMER_TEST_PERIOD			( 50 / portTICK_RATE_MS )

/* The frequency at which the check timer (described in the comments at the top
of this file) will call its callback function. */
#define mainCHECK_TIMER_PERIOD			( 5000UL / ( unsigned long ) portTICK_RATE_MS )

/* A block time of 0 simply means "don't block". */
#define mainDONT_BLOCK					( 0 )

/* 
 * The register check tasks, as decribed in the comments at the top of this 
 * file.  The nature of the tasks necessitates that they are written in 
 * assembler. 
 */
extern void vRegTestTask1(void *pvParameters); 
extern void vRegTestTask2(void *pvParameters); 

/*
 * Definition of the Print task described in the comments at the top of this 
 * file.
 */
static void prvPrintTask( void *pvParameters );

/*
 * Defines the 'check' functionality as described at the top of this file.  This
 * function is the callback function for the 'check' timer. */
static void vCheckTimerCallback( xTimerHandle xTimer );

extern void vLedTask( void * pvParameters );
void vStatsTask(void *pvParameters);

/*-----------------------------------------------------------*/

/* variable incremente in the IDLE hook */
volatile unsigned usIdleCounter = 0;

/* Variables that are incremented on each iteration of the reg test tasks -
provided the tasks have not reported any errors.  The check task inspects these
variables to ensure they are still incrementing as expected.  If a variable
stops incrementing then it is likely that its associate task has stalled. */
volatile unsigned usRegTest1Counter = 0, usRegTest2Counter = 0;

/* The handle of the queue used to send messages from tasks and interrupts to
   the Print task. */
static xQueueHandle xPrintQueue = NULL;

/* The 'check' timer, as described at the top of this file. */
static xTimerHandle xCheckTimer = NULL;


/*-----------------------------------------------------------*/

void main()
{
	/* initalise DIO ports */
	gioInit();

	/* Create the queue used by tasks and interrupts to send strings to the 
	print task. */
	xPrintQueue = xQueueCreate( mainQUEUE_LENGTH, sizeof( unsigned long ) );

	/* If the queue could not be created then don't create any tasks that might
	attempt to use the queue. */
	if( xPrintQueue != NULL )
	{
		/* Create STATS task, this prints out a summary of running tasks every 15s */
		xTaskCreate(vStatsTask, (signed char *)"STATS..", 600, NULL, mainSTAT_TASK_PRIORITY, NULL);

		/* Create LED task, this will flash the LEDs on the USB stick */
		xTaskCreate(vLedTask, (signed char *)"LEDS...", configMINIMAL_STACK_SIZE, NULL, mainLED_TASK_PRIORITY, NULL);

		/* Create the standard demo tasks. */
		vStartDynamicPriorityTasks();
		vStartGenericQueueTasks( mainGENERIC_QUEUE_TEST_PRIORITY );
		vStartCountingSemaphoreTasks();
		
		/* Note that creating the timer test/demo tasks will fill the timer
		command queue.  This is intentional, and forms part of the test the tasks
		perform.  It does mean however that, after this function is called, no
		more timer commands can be sent until after the scheduler has been
		started (at which point the timer daemon will drained the timer command
		queue, freeing up space for more commands to be received). */
		vStartTimerDemoTask(mainTIMER_TEST_PERIOD);
		
		/* Create the Print and register test tasks. */
		xTaskCreate(prvPrintTask, (signed char *)"Print..", 500, mainTASK_PARAMETER_CHECK_VALUE, mainPRINT_TASK_PRIORITY, NULL );
		xTaskCreate(vRegTestTask1, (signed char *)"REG1...", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL);
		xTaskCreate(vRegTestTask2, (signed char *)"REG2...", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL);
		
		/* Create the 'check' timer - the timer that periodically calls the
		check function as described at the top of this file.  Note that, for
		the reasons stated in the comments above the call to 
		vStartTimerDemoTask(), that the check timer is not actually started 
		until after the scheduler has been started. */
		xCheckTimer = xTimerCreate( ( const signed char * ) "Check Timer", mainCHECK_TIMER_PERIOD, pdTRUE, ( void * ) 0, vCheckTimerCallback ); 
		
		/* start FreeRTOS Scheduler */
		vTaskStartScheduler();
	}
	
	/* If all is well then this line will never be reached.  If it is reached
	then it is likely that there was insufficient (FreeRTOS) heap memory space
	to create the idle task.  This may have been trapped by the malloc() failed
	hook function, if one is configured. */	
	for (;;);
}
/*-----------------------------------------------------------*/

void vStatsTask(void *pvParameters)
{
/* Buffer used to hold the table of run time statistics.  This is static so it
does not overflow the task stack. */
static signed char cStatsBuffer[ 1024 ];
const portTickType x15Seconds = 15000 / portTICK_RATE_MS;

	printf("**** Task Statistics Started\n");
	for (;;)
	{
		vTaskDelay( x15Seconds );
		vTaskGetRunTimeStats( cStatsBuffer );
		printf("%s\n", cStatsBuffer );
	}
}
/*-----------------------------------------------------------*/

static void prvPrintTask( void *pvParameters )
{
unsigned long ulReceivedMessage;
static signed char cPrintBuffer[ 50 ];  

	printf( "**** Print Task Started\n" );

	/* Now the scheduler has been started (it must have been for this task to
	be running), start the check timer too.  The call to xTimerStart() will
	block until the command has been accepted. */
	if( xCheckTimer != NULL )
	{
		xTimerStart( xCheckTimer, portMAX_DELAY );
	}

	/*	First print out the number of bytes that remain in the FreeRTOS heap.  This
	is done after a short delay to ensure all the demo tasks have created all
	the objects they are going to use.  */
	vTaskDelay( mainTIMER_TEST_PERIOD * 10 );
	printf( "**** %d heap free\n", ( int ) xPortGetFreeHeapSize() );
	
	/* Just as a test of the port, and for no functional reason, check the task
	parameter contains its expected value. */
	if( pvParameters != mainTASK_PARAMETER_CHECK_VALUE )
	{
		printf("**** Invalid parameter ****\n\n");
	}

	for( ;; )
	{
		/* Wait for a message to be received.  Using portMAX_DELAY as the block
		time will result in an indefinite wait provided INCLUDE_vTaskSuspend is
		set to 1 in FreeRTOSConfig.h, therefore there is no need to check the
		function return value and the function will only return when a value
		has been received. */
		xQueueReceive( xPrintQueue, &ulReceivedMessage, portMAX_DELAY );

		/* What is this message?  What does it contain? */
		switch( ulReceivedMessage )
		{
			case pdPASS						:	sprintf( ( char * ) cPrintBuffer, "Status = PASS" );
												break;
			case mainERROR_DYNAMIC_TASKS	:	sprintf( ( char * ) cPrintBuffer, "Err: Dynamic tsks" );
												break;
			case mainERROR_GEN_QUEUE_TEST 	:	sprintf( ( char * ) cPrintBuffer, "Error: Gen Q test" );
												break;
			case mainERROR_REG_TEST			:	sprintf( ( char * ) cPrintBuffer, "Error: Reg test" );
												break;
			case mainERROR_TIMER_TEST		:	sprintf( ( char * ) cPrintBuffer, "Error: Tmr test" );
												break;
			case mainERROR_COUNT_SEM_TEST	:	sprintf( ( char * ) cPrintBuffer, "Error: Count sem" );
												break;
			default							:	sprintf( ( char * ) cPrintBuffer, "Unknown status" );
												break;
		}
		/* Output the message that was placed into the cBuffer array within the
		switch statement above, then move onto the next line ready for the next
		message to arrive on the queue. */
		printf( "**** Message Received: %s\n", cPrintBuffer );
	}		
}


/* ----------------------------------------------------------------------------------------------------------- */

static void vCheckTimerCallback( xTimerHandle xTimer )
{
	static unsigned short usLastRegTest1Counter = 0, usLastRegTest2Counter = 0;

	/* Define the status message that is sent to the LCD task.  By default the
	   status is PASS. */
	unsigned long ulStatus = pdPASS;

	/* This is the callback function used by the 'check' timer, as described
	at the top of this file. */

	/* The parameter is not used. */
	( void ) xTimer;
	
	/* See if the standard demo tasks are executing as expected, changing
	the message that is sent to the LCD task from PASS to an error code if
	any tasks set reports an error. */
	if( xAreDynamicPriorityTasksStillRunning() != pdPASS )
	{
		ulStatus = mainERROR_DYNAMIC_TASKS;
	}
	
	if( xAreGenericQueueTasksStillRunning() != pdPASS )
	{
		ulStatus = mainERROR_GEN_QUEUE_TEST;
	}			
	
	if( xAreCountingSemaphoreTasksStillRunning() != pdPASS )
	{
		ulStatus = mainERROR_COUNT_SEM_TEST;
	}
	
	if( xAreTimerDemoTasksStillRunning( ( portTickType ) mainCHECK_TIMER_PERIOD ) != pdPASS )
	{
		ulStatus = mainERROR_TIMER_TEST;
	}

	/* Check the reg test tasks are still cycling.  They will stop
	incrementing their loop counters if they encounter an error. */
	if( usRegTest1Counter == usLastRegTest1Counter )
	{
		ulStatus = mainERROR_REG_TEST;
	}

	if( usRegTest2Counter == usLastRegTest2Counter )
	{
		ulStatus = mainERROR_REG_TEST;
	}

	usLastRegTest1Counter = usRegTest1Counter;
	usLastRegTest2Counter = usRegTest2Counter;
	
	/* This is called from a timer callback so must not block! */
	xQueueSendToBack( xPrintQueue, &ulStatus, mainDONT_BLOCK );
}


/* ----------------------------------------------------------------------------------------------------------- */

void vApplicationTickHook( void )
{
	static unsigned long ulCounter = 0;

	/* Is it time to toggle the pin again? */
	ulCounter++;

	/* Just periodically toggle a pin to show that the tick interrupt is
	running.  */
	if( ( ulCounter & 0xff ) == 0 )
	{
		gioSetBit(gioPORTA, 0, 1);
		gioSetBit(gioPORTA, 0, 0);
	}
}


/* ----------------------------------------------------------------------------------------------------------- */

void vApplicationMallocFailedHook( void )
{
	/* Called if a call to pvPortMalloc() fails because there is insufficient
	free memory available in the FreeRTOS heap.  pvPortMalloc() is called
	internally by FreeRTOS API functions that create tasks, queues or
	semaphores. */
	taskDISABLE_INTERRUPTS();
	for( ;; );
}

/* ----------------------------------------------------------------------------------------------------------- */
 
void vApplicationStackOverflowHook( xTaskHandle *pxTask, signed char *pcTaskName )
{
	/* Run time stack overflow checking is performed if
	configconfigCHECK_FOR_STACK_OVERFLOW is defined to 1 or 2.  This hook
	function is called if a stack overflow is detected. */
	taskDISABLE_INTERRUPTS();
	for( ;; );
}

/* ----------------------------------------------------------------------------------------------------------- */

void vApplicationIdleHook(void)
{
	usIdleCounter++;	
}


/* ----------------------------------------------------------------------------------------------------------- */

#endif


