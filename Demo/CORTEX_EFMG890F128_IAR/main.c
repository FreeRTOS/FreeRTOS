/*
    FreeRTOS V7.0.2 - Copyright (C) 2011 Real Time Engineers Ltd.
	

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
 * Creates all the demo application tasks, then starts the scheduler.  The WEB
 * documentation provides more details of the standard demo application tasks.
 * In addition to the standard demo tasks, the following tasks and tests are
 * defined and/or created within this file:
 *
 * "LCD test" task - the LCD task writes a continually repeating series of patterns
 * to the LCD display.
 *
 * "LED test" task -  This is a very simple task that just turns on user LEDs
 * 8 to 15 in turn, before turning them off again.
 *
 * "Check task" - The check task only runs every five seconds but has the highest
 * priority so is guaranteed to get processing time.  Its main job is to inspect
 * all the other standard demo tasks to ensure they are executing without error.
 * The Check task will toggle LED 0 every five seconds while no errors exist,
 * with the toggle frequency increasing to 200ms should an error be detected in
 * any other task.
 *
 * Both the check task and the idle task place the processor into energy saving
 * mode 1, which will be exited following each tick interrupt.  The check task
 * is the highest priority task in the system, so while it is executing no other
 * task will execute.  If the check task places the processor into a low power
 * mode without blocking then the energy consumption as viewed on the Energy
 * Micro Gecko board will go down noticeably as in effect no tasks will be running.
 * The check task places the processor into low power mode for two out of every
 * five seconds.  The current use of low power modes is very basic.  Future
 * FreeRTOS releases will aim to make significant improvements.
 *
 */
 /* Scheduler includes. */
#include "FreeRTOS.h"
#include "croutine.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* Common demo application includes. */
#include "partest.h"
#include "GenQTest.h"
#include "QPeek.h"
#include "recmutex.h"
#include "semtest.h"

/* Demo application includes. */
#include "lcdcontroller.h"
#include "ledtest.h"
#include "lcdtest.h"
#include "chip.h"

/* Task priorities. */
#define mainLCD_TASK_PRIORITY 			( tskIDLE_PRIORITY + 1 )
#define mainLED_TASK_PRIORITY 			( tskIDLE_PRIORITY + 2 )
#define mainGEN_Q_TASK_PRIORITY			( tskIDLE_PRIORITY )
#define mainSEMAPHORE_TASK_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainCHECK_TASK_PRIORITY			( tskIDLE_PRIORITY + 3 )

/* A period of two seconds, adjusted to use the tick frequency. */
#define mainTWO_SECONDS					( 2000 / portTICK_RATE_MS )

/* The length of the delay between each cycle of the check task when an error
has / has not been detected. */
#define mainNO_ERROR_CHECK_FREQUENCY	( 5000 / portTICK_RATE_MS )
#define mainERROR_CHECK_FREQUENCY		( 200 / portTICK_RATE_MS )

/* The LED that is toggled by the check task.  The rate of the toggle indicates
whether or not an error has been found, as defined by the
mainNO_ERROR_CHECK_FREQUENCY and mainERROR_CHECK_FREQUENCY definitions above. */
#define mainCHECK_LED					( 0 )

/*-----------------------------------------------------------*/

/*
 * Configure the hardware as required by the demo.
 */
static void prvSetupHardware( void );

/*
 * The check task as described at the top of this file.
 */
static void prvCheckTask( void *pvParameters );

/*
 * Put the CPU into the least low power low power mode.
 */
static void prvLowPowerMode1( void );

/*-----------------------------------------------------------*/

int main( void )
{
	/* Perform the necessary hardware configuration. */
	prvSetupHardware();

	/* Create the task that writes various text and patterns to the LCD. */
	xTaskCreate( vLCDTask, "LCD", configMINIMAL_STACK_SIZE, NULL, mainLCD_TASK_PRIORITY, NULL );

	/* Create a task that writes to LEDs 8 to 15. */
	xTaskCreate( vLEDTask, "LCDTask", configMINIMAL_STACK_SIZE, NULL, mainLED_TASK_PRIORITY, NULL );

	/* Create some of the standard demo tasks.  These just test the port and
	demonstrate how the FreeRTOS API can be used.  They do not provide any
	specific functionality. */
	vStartGenericQueueTasks( mainGEN_Q_TASK_PRIORITY );
	vStartQueuePeekTasks();
	vStartRecursiveMutexTasks();
	vStartSemaphoreTasks( mainSEMAPHORE_TASK_PRIORITY );
	
	/* Create the check task as described at the top of this file. */
	xTaskCreate( prvCheckTask, "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );
	
	/* Start the scheduler. */
	vTaskStartScheduler();
	
	/* The scheduler should now be running the tasks so the following code should
	never be reached.  If it is reached then there was insufficient heap space
	for the idle task to be created.  In this case the heap size is set by
	configTOTAL_HEAP_SIZE in FreeRTOSConfig.h. */
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
	/* Use the idle task to place the CPU into a low power mode.  Greater power
	saving could be achieved by not including any demo tasks that never block. */
	prvLowPowerMode1();
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( xTaskHandle *pxTask, signed char *pcTaskName )
{
	/* This function will be called if a task overflows its stack, if
	configCHECK_FOR_STACK_OVERFLOW != 0.  It might be that the function
	parameters have been corrupted, depending on the severity of the stack
	overflow.  When this is the case pxCurrentTCB can be inspected in the
	debugger to find the offending task. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvCheckTask( void *pvParameters )
{
portTickType xLastExecutionTime, xFrequency = mainNO_ERROR_CHECK_FREQUENCY;
long lCount;

	/* Initialise xLastExecutionTime so the first call to vTaskDelayUntil()
	works correctly. */
	xLastExecutionTime = xTaskGetTickCount();

	for( ;; )
	{
		/* Perform this check at a frequency that indicates whether or not an
		error has been found. */
		vTaskDelayUntil( &xLastExecutionTime, xFrequency );
		
		/* Check all the other tasks are running without error. */
		if( xAreGenericQueueTasksStillRunning() != pdPASS )
		{
			xFrequency = mainERROR_CHECK_FREQUENCY;
		}
		
		if( xAreQueuePeekTasksStillRunning() != pdPASS )
		{
			xFrequency = mainERROR_CHECK_FREQUENCY;
		}
		
		if( xAreRecursiveMutexTasksStillRunning() != pdPASS )
		{
			xFrequency = mainERROR_CHECK_FREQUENCY;
		}

		if( xAreSemaphoreTasksStillRunning() != pdPASS )
		{
			xFrequency = mainERROR_CHECK_FREQUENCY;
		}
		
		/* Toggle the LED to show that the check hook function is running.
		The toggle freequency will increase if an error has been found in any
		task. */
		vParTestToggleLED( mainCHECK_LED );
		
		/* Just loop around putting the processor into low power mode 1 for
		a while.  This is the highest priority task, and this loop does not
		cause it to block, so it will remain as the running task.  Each time it
		runs for the next two seconds it will simply put the processor to sleep.
		No other task will run so nothing else will happen.  This periodic two
		seconds of lower power should be viewable using the Advanced Energy
		Monitor on the Energy Micro Gecko board. */
		for( lCount = 0; lCount < mainTWO_SECONDS; lCount++ )
		{
			prvLowPowerMode1();
		}
	}
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	/* Initialise the LEDs. */
	vParTestInitialise();

	/* Configure the LCD. */
	LCD_Init( LCD );
}
/*-----------------------------------------------------------*/

static void prvLowPowerMode1( void )
{
	/* Clear SLEEPDEEP for EM1 */
	SCB->SCR &= ~( 1 << SCB_SCR_SLEEPDEEP_Pos );
	
	/* Power down. */
	__WFI();
}


