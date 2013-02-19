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

/******************************************************************************
 * NOTE 1:  This project provides two demo applications.  A simple blinky style
 * project, and a more comprehensive test and demo application.  The
 * mainCREATE_SIMPLE_BLINKY_DEMO_ONLY setting in main.c is used to select
 * between the two.  See the notes on using mainCREATE_SIMPLE_BLINKY_DEMO_ONLY
 * in main.c.  This file implements the comprehensive test and demo version.
 *
 * NOTE 2:  This file only contains the source code that is specific to the
 * full demo.  Generic functions, such FreeRTOS hook functions, and functions
 * required to configure the hardware, are defined in main.c.
 ******************************************************************************
 *
 * main_full() creates all the demo application tasks and software timers, then 
 * starts the scheduler.  The WEB documentation provides more details of the 
 * standard demo application tasks.  In addition to the standard demo tasks, the 
 * following tasks and tests are defined and/or created within this file:
 *
 * "LCD" task - the LCD task is a 'gatekeeper' task.  It is the only task that
 * is permitted to access the display directly.  Other tasks wishing to write a
 * message to the LCD send the message on a queue to the LCD task instead of
 * accessing the LCD themselves.  The LCD task just blocks on the queue waiting
 * for messages - waking and displaying the messages as they arrive.
 *
 * "Check" timer - The check software timer period is initially set to three
 * seconds.  The callback function associated with the check software timer
 * checks that all the standard demo tasks, and the register check tasks, are
 * not only still executing, but are executing without reporting any errors.  If
 * the check software timer discovers that a task has either stalled, or
 * reported an error, then it changes its own execution period from the initial
 * three seconds, to just 200ms.  The check software timer callback function
 * also writes a status message to the LCD (via the LCD task).  If all the demo 
 * tasks are executing with their expected behaviour then the check task writes 
 * a count of the number of times the high frequency interrupt has incremented
 * ulHighFrequencyTimerInterrupts - which is one in every 20,000 interrupts.
 *
 * "Register test" tasks - These tasks are used in part to test the kernel port.
 * They set each processor register to a known value, then check that the 
 * register still contains that value.  Each of the tasks sets the registers
 * to different values, and will get swapping in and out between setting and 
 * then subsequently checking the register values.  Discovery of an incorrect
 * value would be indicative of an error in the task switching mechanism.
 *
 * By way of demonstration, the demo application defines 
 * configMAX_SYSCALL_INTERRUPT_PRIORITY to be 3, configKERNEL_INTERRUPT_PRIORITY 
 * to be 1, and all other interrupts as follows:
 *
 *	+ The UART is allocated a priority of 2. This means it can interrupt the 
 *    RTOS tick, and can also safely use queues.
 *  + Two timers are configured to generate interrupts just to test the nesting 
 *    and queue access mechanisms. These timers are allocated priorities 2 and 3 
 *    respectively. Even though they both access the same two queues, the 
 *    priority 3 interrupt can safely interrupt the priority 2 interrupt. Both 
 *    can interrupt the RTOS tick.
 *  + Finally a high frequency timer interrupt is configured to use priority 4 - 
 *    therefore kernel activity will never prevent the high frequency timer from 
 *    executing immediately that the interrupt is raised (within the limitations 
 *    of the hardware itself). It would not be safe to access a queue from this 
 *    interrupt as it is above configMAX_SYSCALL_INTERRUPT_PRIORITY. 
 *
 * See the online documentation for this demo for more information on interrupt
 * usage.
 */

/* Standard includes. */
#include <stdio.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "timers.h"

/* Demo application includes. */
#include "partest.h"
#include "blocktim.h"
#include "flash_timer.h"
#include "semtest.h"
#include "GenQTest.h"
#include "QPeek.h"
#include "lcd.h"
#include "comtest2.h"
#include "timertest.h"
#include "IntQueue.h"

/*-----------------------------------------------------------*/

/* The period after which the check timer will expire, in ms, provided no errors
have been reported by any of the standard demo tasks.  ms are converted to the
equivalent in ticks using the portTICK_RATE_MS constant. */
#define mainCHECK_TIMER_PERIOD_MS			( 3000UL / portTICK_RATE_MS )

/* The period at which the check timer will expire, in ms, if an error has been
reported in one of the standard demo tasks.  ms are converted to the equivalent
in ticks using the portTICK_RATE_MS constant. */
#define mainERROR_CHECK_TIMER_PERIOD_MS 	( 200UL / portTICK_RATE_MS )

/* The priorities of the various demo application tasks. */
#define mainSEM_TEST_PRIORITY				( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainCOM_TEST_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainINTEGER_TASK_PRIORITY           ( tskIDLE_PRIORITY )
#define mainGEN_QUEUE_TASK_PRIORITY			( tskIDLE_PRIORITY )

/* The LED controlled by the 'check' software timer. */
#define mainCHECK_LED						( 7 )

/* The LED used by the comtest tasks.  mainCOM_TEST_LED + 1 is also used.
See the comtest.c file for more information. */
#define mainCOM_TEST_LED					( 4 )

/* Baud rate used by the comtest tasks. */
#define mainCOM_TEST_BAUD_RATE				( 115200 )

/* Misc. */
#define mainDONT_BLOCK						( 0 )

/* Dimension the buffer used to hold the value of the high frequency timer 
count when it is converted to a string. */
#define mainMAX_STRING_LENGTH				( 20 )

/* The frequency at which the "fast interrupt test" interrupt will occur. */
#define mainTEST_INTERRUPT_FREQUENCY		( 20000 )

/* The number of timer clocks expected to occur between each "fast interrupt 
test" interrupt. */
#define mainEXPECTED_CLOCKS_BETWEEN_INTERRUPTS ( ( configCPU_CLOCK_HZ >> 1 ) / mainTEST_INTERRUPT_FREQUENCY )

/* The number of nano seconds between each core clock. */
#define mainNS_PER_CLOCK ( ( unsigned long ) ( ( 1.0 / ( double ) ( configCPU_CLOCK_HZ >> 1 ) ) * 1000000000.0 ) )

/* The number of LEDs that should be controlled by the flash software timer
standard demo. */
#define mainNUM_FLASH_TIMER_LEDS			( 3 )

/*-----------------------------------------------------------*/

/*
 * The check timer callback function, as described at the top of this file.
 */
static void prvCheckTimerCallback( xTimerHandle xTimer );

/*
 * It is important to ensure the high frequency timer test does not start before
 * the kernel.  It is therefore started from inside a software timer callback
 * function, which will not execute until the timer service/daemon task is
 * executing.  A one-shot timer is used, so the callback function will only
 * execute once (unless it is manually reset/restarted).
 */
static void prvSetupHighFrequencyTimerTest( xTimerHandle xTimer );

/*
 * Tasks that test the context switch mechanism by filling the processor 
 * registers with known values, then checking that the values contained
 * within the registers is as expected.  The tasks are likely to get swapped
 * in and out between setting the register values and checking the register
 * values. 
 */
static void prvRegTestTask1( void *pvParameters );
static void prvRegTestTask2( void *pvParameters );

/*-----------------------------------------------------------*/

/* The queue used to send messages to the LCD task. */
static xQueueHandle xLCDQueue;

/* Flag used by prvRegTestTask1() and prvRegTestTask2() to indicate their status
(pass/fail). */
volatile unsigned long ulStatus1 = pdPASS;

/* Variables incremented by prvRegTestTask1() and prvRegTestTask2() respectively on 
each iteration of their function.  This is used to detect either task stopping
their execution.. */
volatile unsigned long ulRegTest1Cycles = 0, ulRegTest2Cycles = 0;

/*-----------------------------------------------------------*/

/*
 * Create the demo tasks then start the scheduler.
 */
int main_full( void )
{
xTimerHandle xTimer = NULL;

	/* Create the LCD task - this returns the queue to use when writing 
	messages to the LCD. */
	xLCDQueue = xStartLCDTask();

	/* Create all the other standard demo tasks. */
	vStartLEDFlashTimers( mainNUM_FLASH_TIMER_LEDS );
    vCreateBlockTimeTasks();
    vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
    vStartGenericQueueTasks( mainGEN_QUEUE_TASK_PRIORITY );
    vStartQueuePeekTasks();
	vStartInterruptQueueTasks();

	/* Create the tasks defined within this file. */
	xTaskCreate( prvRegTestTask1, ( const signed char * const ) "Reg1", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
	xTaskCreate( prvRegTestTask2, ( const signed char * const ) "Reg2", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );

    /* The PIC32MX795 uses an 8 deep fifo where TX interrupts are asserted 
	whilst the TX buffer is empty.  This causes an issue with the test driver so 
	it is not used in this demo */
	#if !defined(__32MX795F512L__)
		vAltStartComTestTasks( mainCOM_TEST_PRIORITY, mainCOM_TEST_BAUD_RATE, mainCOM_TEST_LED );
	#endif	
	
	/* Create the software timer that performs the 'check' functionality, as 
	described at the top of this file. */
	xTimer = xTimerCreate( 	( const signed char * ) "CheckTimer",/* A text name, purely to help debugging. */
							( mainCHECK_TIMER_PERIOD_MS ),		/* The timer period, in this case 3000ms (3s). */
							pdTRUE,								/* This is an auto-reload timer, so xAutoReload is set to pdTRUE. */
							( void * ) 0,						/* The ID is not used, so can be set to anything. */
							prvCheckTimerCallback				/* The callback function that inspects the status of all the other tasks. */
						);	
	
	if( xTimer != NULL )
	{
		xTimerStart( xTimer, mainDONT_BLOCK );
	}
	
	/* A software timer is also used to start the high frequency timer test.
	This is to ensure the test does not start before the kernel.  This time a
	one shot software timer is used. */
	xTimer = xTimerCreate( ( const signed char * ) "HighHzTimerSetup", 1, pdFALSE, ( void * ) 0, prvSetupHighFrequencyTimerTest );
	if( xTimer != NULL )
	{
		xTimerStart( xTimer, mainDONT_BLOCK );
	}

	/* Finally start the scheduler. */
	vTaskStartScheduler();

	/* If all is well, the scheduler will now be running, and the following line
	will never be reached.  If the following line does execute, then there was
	insufficient FreeRTOS heap memory available for the idle and/or timer tasks
	to be created.  See the memory management section on the FreeRTOS web site
	for more details. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvRegTestTask1( void *pvParameters )
{
extern void vRegTest1( volatile unsigned long * );

	for( ;; )
	{
		/* Perform the register test function. */
		vRegTest1( &ulStatus1 );

		/* Increment the counter so the check task knows we are still 
		running. */
		ulRegTest1Cycles++;
	}
}
/*-----------------------------------------------------------*/

static void prvRegTestTask2( void *pvParameters )
{
extern void vRegTest2( volatile unsigned long * );

	for( ;; )
	{
		/* Perform the register test function. */
		vRegTest2( &ulStatus1 );

		/* Increment the counter so the check task knows we are still
		running. */
		ulRegTest2Cycles++;
	}
}
/*-----------------------------------------------------------*/

static void prvCheckTimerCallback( xTimerHandle xTimer )
{
static long lChangedTimerPeriodAlready = pdFALSE;
static unsigned long ulLastRegTest1Value = 0, ulLastRegTest2Value = 0;

/* Buffer into which the high frequency timer count is written as a string. */
static char cStringBuffer[ mainMAX_STRING_LENGTH ];

/* The count of the high frequency timer interrupts. */
extern unsigned long ulHighFrequencyTimerInterrupts;
static xLCDMessage xMessage = { ( 200 / portTICK_RATE_MS ), cStringBuffer };

	/* Has either register check 1 or 2 task discovered an error? */
	if( ulStatus1 != pdPASS )
	{
		xMessage.pcMessage = "Error: Reg test1";
	}

	/* Check that the register test 1 task is still running. */
	if( ulLastRegTest1Value == ulRegTest1Cycles )
	{
		xMessage.pcMessage = "Error: Reg test2";
	}
	ulLastRegTest1Value = ulRegTest1Cycles;

	
	/* Check that the register test 2 task is still running. */
	if( ulLastRegTest2Value == ulRegTest2Cycles )
	{
		xMessage.pcMessage = "Error: Reg test3";
	}
	ulLastRegTest2Value = ulRegTest2Cycles;
	

	/* Have any of the standard demo tasks detected an error in their 
	operation? */
	if( xAreGenericQueueTasksStillRunning() != pdTRUE )
	{
		xMessage.pcMessage = "Error: Gen Q";
	}
	else if( xAreQueuePeekTasksStillRunning() != pdTRUE )
	{
		xMessage.pcMessage = "Error: Q Peek";
	}
	else if( xAreComTestTasksStillRunning() != pdTRUE )
	{
		xMessage.pcMessage = "Error: COM test";
	}
	else if( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
	{
		xMessage.pcMessage = "Error: Blck time";
	}
	else if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	{
		xMessage.pcMessage = "Error: Sem test";
	}
	else if( xAreIntQueueTasksStillRunning() != pdTRUE )
	{
		xMessage.pcMessage = "Error: Int queue";
	}

	if( xMessage.pcMessage != cStringBuffer )
	{
		/* An error string has been logged.  If the timer period has not yet
		been changed it should be changed now.  Increasing the frequency of the
		LED gives visual feedback of the error status (although it is written
		to the LCD too!). */
		if( lChangedTimerPeriodAlready == pdFALSE )
		{
			lChangedTimerPeriodAlready = pdTRUE;
			
			/* This call to xTimerChangePeriod() uses a zero block time.
			Functions called from inside of a timer callback function must
			*never* attempt	to block as to do so could impact other software
			timers. */
			xTimerChangePeriod( xTimer, ( mainERROR_CHECK_TIMER_PERIOD_MS ), mainDONT_BLOCK );
		}		
	}
	else
	{
		/* Write the ulHighFrequencyTimerInterrupts value to the string 
		buffer.  It will only be displayed if no errors have been detected. */
		sprintf( cStringBuffer, "Pass %u", ( unsigned int ) ulHighFrequencyTimerInterrupts );
	}

	/* Send the status message to the LCD task for display on the LCD.  This is 
	a timer callback function, so the queue send function *must not* block. */
	xQueueSend( xLCDQueue, &xMessage, mainDONT_BLOCK );
	vParTestToggleLED( mainCHECK_LED );	
}
/*-----------------------------------------------------------*/

static void prvSetupHighFrequencyTimerTest( xTimerHandle xTimer )
{
	/* Setup the high frequency, high priority, timer test.  It is setup in this
	software timer callback to ensure it does not start before the kernel does.
	This is a one shot timer - so the setup routine will only be executed once. */
	vSetupTimerTest( mainTEST_INTERRUPT_FREQUENCY );	
}

