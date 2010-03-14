/*
    FreeRTOS V6.0.4 - Copyright (C) 2010 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS eBook                                  *
    *                                                                         *
    *        "Using the FreeRTOS Real Time Kernel - a Practical Guide"        *
    *                  http://www.FreeRTOS.org/Documentation                  *
    *                                                                         *
    * A pdf reference manual is also available.  Both are usually delivered   *
    * to your inbox within 20 minutes to two hours when purchased between 8am *
    * and 8pm GMT (although please allow up to 24 hours in case of            *
    * exceptional circumstances).  Thank you for your support!                *
    *                                                                         *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    ***NOTE*** The exception to the GPL is included to allow you to distribute
    a combined work that includes FreeRTOS without being obliged to provide the
    source code for proprietary components outside of the FreeRTOS kernel.
    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
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
 * Creates all the demo application tasks, then starts the scheduler.  The WEB
 * documentation provides more details of the standard demo application tasks.
 * In addition to the standard demo tasks, the following tasks and tests are
 * defined and/or created within this file:
 *
 * "LCD" task - the LCD task is a 'gatekeeper' task.  It is the only task that
 * is permitted to access the display directly.  Other tasks wishing to write a
 * message to the LCD send the message on a queue to the LCD task instead of
 * accessing the LCD themselves.  The LCD task just blocks on the queue waiting
 * for messages - waking and displaying the messages as they arrive.
 *
 * "Check" task -  This only executes every three seconds but has the highest
 * priority so is guaranteed to get processor time.  Its main function is to 
 * check that all the standard demo tasks are still operational.  Should any 
 * unexpected behaviour within a demo task be discovered the check task will 
 * write an error to the LCD (via the LCD task).  If all the demo tasks are 
 * executing with their expected behaviour then the check task instead writes 
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

/* Demo application includes. */
#include "partest.h"
#include "blocktim.h"
#include "flash.h"
#include "semtest.h"
#include "GenQTest.h"
#include "QPeek.h"
#include "lcd.h"
#include "comtest2.h"
#include "timertest.h"
#include "IntQueue.h"

#pragma config FPLLMUL = MUL_20, FPLLIDIV = DIV_2, FPLLODIV = DIV_1, FWDTEN = OFF
#pragma config POSCMOD = HS, FNOSC = PRIPLL, FPBDIV = DIV_2

/*-----------------------------------------------------------*/

/* The rate at which the LED controlled by the 'check' task will flash when no
errors have been detected. */
#define mainNO_ERROR_PERIOD	( 3000 / portTICK_RATE_MS )

/* The rate at which the LED controlled by the 'check' task will flash when an
error has been detected. */
#define mainERROR_PERIOD 	( 500 / portTICK_RATE_MS )

/* The priorities of the various demo application tasks. */
#define mainCHECK_TASK_PRIORITY				( tskIDLE_PRIORITY + 4 )
#define mainSEM_TEST_PRIORITY				( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainCOM_TEST_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainINTEGER_TASK_PRIORITY           ( tskIDLE_PRIORITY )
#define mainGEN_QUEUE_TASK_PRIORITY			( tskIDLE_PRIORITY )

/* The LED controlled by the 'check' task. */
#define mainCHECK_LED						( 7 )

/* The LED used by the comtest tasks.  mainCOM_TEST_LED + 1 is also used.
See the comtest.c file for more information. */
#define mainCOM_TEST_LED					( 4 )

/* Baud rate used by the comtest tasks. */
#define mainCOM_TEST_BAUD_RATE				( 115200 )

/* Misc. */
#define mainDONT_WAIT						( 0 )

/* Dimension the buffer used to hold the value of the high frequency timer 
count when it is converted to a string. */
#define mainMAX_STRING_LENGTH				( 20 )

/* The frequency at which the "fast interrupt test" interrupt will occur. */
#define mainTEST_INTERRUPT_FREQUENCY		( 20000 )

/* The number of timer clocks we expect to occur between each "fast
interrupt test" interrupt. */
#define mainEXPECTED_CLOCKS_BETWEEN_INTERRUPTS ( ( configCPU_CLOCK_HZ >> 1 ) / mainTEST_INTERRUPT_FREQUENCY )

/* The number of nano seconds between each core clock. */
#define mainNS_PER_CLOCK ( ( unsigned portLONG ) ( ( 1.0 / ( double ) ( configCPU_CLOCK_HZ >> 1 ) ) * 1000000000.0 ) )

/*-----------------------------------------------------------*/

/*
 * Setup the processor ready for the demo.
 */
static void prvSetupHardware( void );

/*
 * Implements the 'check' task functionality as described at the top of this 
 * file. 
 */
static void prvCheckTask( void *pvParameters ) __attribute__((noreturn));

/*
 * Tasks that test the context switch mechanism by filling the processor 
 * registers with known values, then checking that the values contained
 * within the registers is as expected.  The tasks are likely to get swapped
 * in and out between setting the register values and checking the register
 * values. */
static void prvTestTask1( void *pvParameters );
static void prvTestTask2( void *pvParameters );

/*-----------------------------------------------------------*/

/* The queue used to send messages to the LCD task. */
static xQueueHandle xLCDQueue;

/* Flag used by prvTestTask1() and prvTestTask2() to indicate their status
(pass/fail). */
unsigned portLONG ulStatus1 = pdPASS;

/* Variables incremented by prvTestTask1() and prvTestTask2() respectively on 
each iteration of their function.  This is used to detect either task stopping
their execution.. */
unsigned portLONG ulRegTest1Cycles = 0, ulRegTest2Cycles = 0;

/*-----------------------------------------------------------*/

/*
 * Create the demo tasks then start the scheduler.
 */
int main( void )
{
	/* Configure any hardware required for this demo. */
	prvSetupHardware();

	/* Create the LCD task - this returns the queue to use when writing 
	messages to the LCD. */
	xLCDQueue = xStartLCDTask();

	/* Create all the other standard demo tasks. */
	vStartLEDFlashTasks( tskIDLE_PRIORITY );
    vCreateBlockTimeTasks();
    vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
    vStartGenericQueueTasks( mainGEN_QUEUE_TASK_PRIORITY );
    vStartQueuePeekTasks();
	vAltStartComTestTasks( mainCOM_TEST_PRIORITY, mainCOM_TEST_BAUD_RATE, mainCOM_TEST_LED );
	vStartInterruptQueueTasks();

	/* Create the tasks defined within this file. */
	xTaskCreate( prvTestTask1, "Tst1", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
	xTaskCreate( prvTestTask2, "Tst2", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );

	/* prvCheckTask uses sprintf so requires more stack. */
	xTaskCreate( prvCheckTask, "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

	/* Finally start the scheduler. */
	vTaskStartScheduler();

	/* Will only reach here if there is insufficient heap available to start
	the scheduler. */
	return 0;
}
/*-----------------------------------------------------------*/

static void prvTestTask1( void *pvParameters )
{
extern void vRegTest1( unsigned long * );

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

static void prvTestTask2( void *pvParameters )
{
extern void vRegTest2( unsigned long * );

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

static void prvSetupHardware( void )
{
	/* Set the system and peripheral bus speeds and enable the program cache*/
    SYSTEMConfigPerformance( configCPU_CLOCK_HZ - 1 );
	mOSCSetPBDIV( OSC_PB_DIV_2 );

	/* Setup to use the external interrupt controller. */
    INTEnableSystemMultiVectoredInt();

	portDISABLE_INTERRUPTS();

	/* Setup the digital IO for the LED's. */
	vParTestInitialise();
}
/*-----------------------------------------------------------*/

static void prvCheckTask( void *pvParameters )
{
unsigned portLONG ulLastRegTest1Value = 0, ulLastRegTest2Value = 0, ulTicksToWait = mainNO_ERROR_PERIOD;
portTickType xLastExecutionTime;

/* Buffer into which the high frequency timer count is written as a string. */
static portCHAR cStringBuffer[ mainMAX_STRING_LENGTH ];

/* The count of the high frequency timer interrupts. */
extern unsigned portLONG ulHighFrequencyTimerInterrupts;
xLCDMessage xMessage = { ( 200 / portTICK_RATE_MS ), cStringBuffer };

	/* Setup the high frequency, high priority, timer test.  It is setup here
	to ensure it does not fire before the scheduler is started. */
	vSetupTimerTest( mainTEST_INTERRUPT_FREQUENCY );

	/* Initialise the variable used to control our iteration rate prior to
	its first use. */
	xLastExecutionTime = xTaskGetTickCount();

	for( ;; )
	{
		/* Wait until it is time to run the tests again. */
		vTaskDelayUntil( &xLastExecutionTime, ulTicksToWait );

		/* Has either register check 1 or 2 task discovered an error? */
		if( ulStatus1 != pdPASS )
		{
			ulTicksToWait = mainERROR_PERIOD;
			xMessage.pcMessage = "Error: Reg test1";
		}

		/* Check that the register test 1 task is still running. */
		if( ulLastRegTest1Value == ulRegTest1Cycles )
		{
			ulTicksToWait = mainERROR_PERIOD;
			xMessage.pcMessage = "Error: Reg test2";
		}
		ulLastRegTest1Value = ulRegTest1Cycles;

		
		/* Check that the register test 2 task is still running. */
		if( ulLastRegTest2Value == ulRegTest2Cycles )
		{
			ulTicksToWait = mainERROR_PERIOD;
			xMessage.pcMessage = "Error: Reg test3";
		}
		ulLastRegTest2Value = ulRegTest2Cycles;
		

		/* Have any of the standard demo tasks detected an error in their 
		operation? */
		if( xAreGenericQueueTasksStillRunning() != pdTRUE )
		{
			ulTicksToWait = mainERROR_PERIOD;
			xMessage.pcMessage = "Error: Gen Q";
		}
		else if( xAreQueuePeekTasksStillRunning() != pdTRUE )
		{
			ulTicksToWait = mainERROR_PERIOD;
			xMessage.pcMessage = "Error: Q Peek";
		}
		else if( xAreComTestTasksStillRunning() != pdTRUE )
		{
			ulTicksToWait = mainERROR_PERIOD;
			xMessage.pcMessage = "Error: COM test";
		}
		else if( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
		{
			ulTicksToWait = mainERROR_PERIOD;
			xMessage.pcMessage = "Error: Blck time";
		}
	    else if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	    {
	        ulTicksToWait = mainERROR_PERIOD;
			xMessage.pcMessage = "Error: Sem test";
	    }
		else if( xAreIntQueueTasksStillRunning() != pdTRUE )
		{
			ulTicksToWait = mainERROR_PERIOD;
			xMessage.pcMessage = "Error: Int queue";
		}

		/* Write the ulHighFrequencyTimerInterrupts value to the string 
		buffer.  It will only be displayed if no errors have been detected. */
		sprintf( cStringBuffer, "Pass %u", ( unsigned int ) ulHighFrequencyTimerInterrupts );

		xQueueSend( xLCDQueue, &xMessage, mainDONT_WAIT );
		vParTestToggleLED( mainCHECK_LED );
	}
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( void )
{
	/* Look at pxCurrentTCB to see which task overflowed its stack. */
	for( ;; );
}
/*-----------------------------------------------------------*/

void _general_exception_handler( unsigned portLONG ulCause, unsigned portLONG ulStatus )
{
	/* This overrides the definition provided by the kernel.  Other exceptions 
	should be handled here. */
	for( ;; );
}
/*-----------------------------------------------------------*/

