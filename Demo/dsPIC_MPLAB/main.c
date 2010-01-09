/*
    FreeRTOS V6.0.2 - Copyright (C) 2010 Real Time Engineers Ltd.

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
 * "Fast Interrupt Test" - A high frequency periodic interrupt is generated
 * using a free running timer to demonstrate the use of the 
 * configKERNEL_INTERRUPT_PRIORITY configuration constant.  The interrupt 
 * service routine measures the number of processor clocks that occur between
 * each interrupt - and in so doing measures the jitter in the interrupt 
 * timing.  The maximum measured jitter time is latched in the usMaxJitter 
 * variable, and displayed on the LCD by the 'Check' as described below.  
 * The fast interrupt is configured and handled in the timer_test.c source 
 * file.
 *
 * "LCD" task - the LCD task is a 'gatekeeper' task.  It is the only task that
 * is permitted to access the LCD directly.  Other tasks wishing to write a
 * message to the LCD send the message on a queue to the LCD task instead of 
 * accessing the LCD themselves.  The LCD task just blocks on the queue waiting 
 * for messages - waking and displaying the messages as they arrive.  The LCD
 * task is defined in lcd.c.  
 * 
 * "Check" task -  This only executes every three seconds but has the highest 
 * priority so is guaranteed to get processor time.  Its main function is to 
 * check that all the standard demo tasks are still operational.  Should any
 * unexpected behaviour within a demo task be discovered the 'check' task will
 * write "FAIL #n" to the LCD (via the LCD task).  If all the demo tasks are 
 * executing with their expected behaviour then the check task writes the max
 * jitter time to the LCD (again via the LCD task), as described above.
 */

/* Standard includes. */
#include <stdio.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "croutine.h"

/* Demo application includes. */
#include "BlockQ.h"
#include "crflash.h"
#include "blocktim.h"
#include "integer.h"
#include "comtest2.h"
#include "partest.h"
#include "lcd.h"
#include "timertest.h"

/* Demo task priorities. */
#define mainBLOCK_Q_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainCHECK_TASK_PRIORITY				( tskIDLE_PRIORITY + 3 )
#define mainCOM_TEST_PRIORITY				( 2 )

/* The check task may require a bit more stack as it calls sprintf(). */
#define mainCHECK_TAKS_STACK_SIZE			( configMINIMAL_STACK_SIZE * 2 )

/* The execution period of the check task. */
#define mainCHECK_TASK_PERIOD				( ( portTickType ) 3000 / portTICK_RATE_MS )

/* The number of flash co-routines to create. */
#define mainNUM_FLASH_COROUTINES			( 5 )

/* Baud rate used by the comtest tasks. */
#define mainCOM_TEST_BAUD_RATE				( 19200 )

/* The LED used by the comtest tasks.  mainCOM_TEST_LED + 1 is also used.
See the comtest.c file for more information. */
#define mainCOM_TEST_LED					( 6 )

/* The frequency at which the "fast interrupt test" interrupt will occur. */
#define mainTEST_INTERRUPT_FREQUENCY		( 20000 )

/* The number of processor clocks we expect to occur between each "fast
interrupt test" interrupt. */
#define mainEXPECTED_CLOCKS_BETWEEN_INTERRUPTS ( configCPU_CLOCK_HZ / mainTEST_INTERRUPT_FREQUENCY )

/* The number of nano seconds between each processor clock. */
#define mainNS_PER_CLOCK ( ( unsigned short ) ( ( 1.0 / ( double ) configCPU_CLOCK_HZ ) * 1000000000.0 ) )

/* Dimension the buffer used to hold the value of the maximum jitter time when
it is converted to a string. */
#define mainMAX_STRING_LENGTH				( 20 )

/*-----------------------------------------------------------*/

/*
 * The check task as described at the top of this file.
 */
static void vCheckTask( void *pvParameters );

/*
 * Setup the processor ready for the demo.
 */
static void prvSetupHardware( void );

/*-----------------------------------------------------------*/

/* The queue used to send messages to the LCD task. */
static xQueueHandle xLCDQueue;

/*-----------------------------------------------------------*/

/*
 * Create the demo tasks then start the scheduler.
 */
int main( void )
{
	/* Configure any hardware required for this demo. */
	prvSetupHardware();

	/* Create the standard demo tasks. */
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );	
	vStartIntegerMathTasks( tskIDLE_PRIORITY );
	vStartFlashCoRoutines( mainNUM_FLASH_COROUTINES );
	vAltStartComTestTasks( mainCOM_TEST_PRIORITY, mainCOM_TEST_BAUD_RATE, mainCOM_TEST_LED );
	vCreateBlockTimeTasks();

	/* Create the test tasks defined within this file. */
	xTaskCreate( vCheckTask, ( signed char * ) "Check", mainCHECK_TAKS_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

	/* Start the task that will control the LCD.  This returns the handle
	to the queue used to write text out to the task. */
	xLCDQueue = xStartLCDTask();

	/* Start the high frequency interrupt test. */
	vSetupTimerTest( mainTEST_INTERRUPT_FREQUENCY );

	/* Finally start the scheduler. */
	vTaskStartScheduler();

	/* Will only reach here if there is insufficient heap available to start
	the scheduler. */
	return 0;
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	vParTestInitialise();
}
/*-----------------------------------------------------------*/

static void vCheckTask( void *pvParameters )
{
/* Used to wake the task at the correct frequency. */
portTickType xLastExecutionTime; 

/* The maximum jitter time measured by the fast interrupt test. */
extern unsigned short usMaxJitter ;

/* Buffer into which the maximum jitter time is written as a string. */
static char cStringBuffer[ mainMAX_STRING_LENGTH ];

/* The message that is sent on the queue to the LCD task.  The first
parameter is the minimum time (in ticks) that the message should be
left on the LCD without being overwritten.  The second parameter is a pointer
to the message to display itself. */
xLCDMessage xMessage = { 0, cStringBuffer };

/* Set to pdTRUE should an error be detected in any of the standard demo tasks. */
unsigned short usErrorDetected = pdFALSE;

	/* Initialise xLastExecutionTime so the first call to vTaskDelayUntil()
	works correctly. */
	xLastExecutionTime = xTaskGetTickCount();

	for( ;; )
	{
		/* Wait until it is time for the next cycle. */
		vTaskDelayUntil( &xLastExecutionTime, mainCHECK_TASK_PERIOD );

		/* Has an error been found in any of the standard demo tasks? */

		if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
		{
			usErrorDetected = pdTRUE;
			sprintf( cStringBuffer, "FAIL #1" );
		}
	
		if( xAreComTestTasksStillRunning() != pdTRUE )
		{
			usErrorDetected = pdTRUE;
			sprintf( cStringBuffer, "FAIL #2" );
		}

		if( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
		{
			usErrorDetected = pdTRUE;
			sprintf( cStringBuffer, "FAIL #3" );
		}

		if( xAreBlockingQueuesStillRunning() != pdTRUE )
		{
			usErrorDetected = pdTRUE;
			sprintf( cStringBuffer, "FAIL #4" );
		}

		if( usErrorDetected == pdFALSE )
		{
			/* No errors have been discovered, so display the maximum jitter
			timer discovered by the "fast interrupt test". */
			sprintf( cStringBuffer, "%dns max jitter", ( short ) ( usMaxJitter - mainEXPECTED_CLOCKS_BETWEEN_INTERRUPTS ) * mainNS_PER_CLOCK );
		}

		/* Send the message to the LCD gatekeeper for display. */
		xQueueSend( xLCDQueue, &xMessage, portMAX_DELAY );
	}
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
	/* Schedule the co-routines from within the idle task hook. */
	vCoRoutineSchedule();
}
/*-----------------------------------------------------------*/

