/*
    FreeRTOS V9.0.1 - Copyright (C) 2017 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>>> AND MODIFIED BY <<<< the FreeRTOS exception.

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

#include <device.h>

/* RTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* Common Demo includes. */
#include "serial.h"
#include "BlockQ.h"
#include "blocktim.h"
#include "comtest.h"
#include "countsem.h"
#include "death.h"
#include "dynamic.h"
#include "flash.h"
#include "flop.h"
#include "GenQTest.h"
#include "integer.h"
#include "IntQueue.h"
#include "mevents.h"
#include "partest.h"
#include "PollQ.h"
#include "print.h"
#include "QPeek.h"
#include "semtest.h"
/*---------------------------------------------------------------------------*/

/* The time between cycles of the 'check' functionality (defined within the
tick hook. */
#define mainCHECK_DELAY						( ( TickType_t ) 5000 / portTICK_PERIOD_MS )
#define mainCOM_LED							( 3 )

/* The number of nano seconds between each processor clock. */
#define mainNS_PER_CLOCK ( ( unsigned long ) ( ( 1.0 / ( double ) configCPU_CLOCK_HZ ) * 1000000000.0 ) )

/* Task priorities. */
#define mainQUEUE_POLL_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainCHECK_TASK_PRIORITY				( tskIDLE_PRIORITY + 3 )
#define mainSEM_TEST_PRIORITY				( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainCREATOR_TASK_PRIORITY           ( tskIDLE_PRIORITY + 3 )
#define mainINTEGER_TASK_PRIORITY           ( tskIDLE_PRIORITY )
#define mainGEN_QUEUE_TASK_PRIORITY			( tskIDLE_PRIORITY )
#define mainCOM_TEST_TASK_PRIORITY			( tskIDLE_PRIORITY + 1 )
#define mainFLASH_TEST_TASK_PRIORITY		( tskIDLE_PRIORITY + 2 )
/*---------------------------------------------------------------------------*/

/*
 * Configures the timers and interrupts for the fast interrupt test as
 * described at the top of this file.
 */
extern void vSetupTimerTest( void );
/*---------------------------------------------------------------------------*/

/*
 * The Check task periodical interrogates each of the running tests to
 * ensure that they are still executing correctly.
 * If all the tests pass, then the LCD is updated with Pass, the number of
 * iterations and the Jitter time calculated but the Fast Interrupt Test.
 * If any one of the tests fail, it is indicated with an error code printed on
 * the display. This indicator won't disappear until the device is reset.
 */
void vCheckTask( void *pvParameters );

/*
 * Installs the RTOS interrupt handlers and starts the peripherals.
 */
static void prvHardwareSetup( void );
/*---------------------------------------------------------------------------*/

void main( void )
{
    /* Place your initialization/startup code here (e.g. MyInst_Start()) */
	prvHardwareSetup();

	/* Start the standard demo tasks.  These are just here to exercise the
	kernel port and provide examples of how the FreeRTOS API can be used. */
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
	vCreateBlockTimeTasks();
	vStartCountingSemaphoreTasks();
	vStartDynamicPriorityTasks();
	vStartMathTasks( mainINTEGER_TASK_PRIORITY );
	vStartGenericQueueTasks( mainGEN_QUEUE_TASK_PRIORITY );
	vStartIntegerMathTasks( mainINTEGER_TASK_PRIORITY );
	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
	vStartQueuePeekTasks();
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
	vStartLEDFlashTasks( mainFLASH_TEST_TASK_PRIORITY );
	vAltStartComTestTasks( mainCOM_TEST_TASK_PRIORITY, 57600, mainCOM_LED );
	vStartInterruptQueueTasks();

	/* Start the error checking task. */
  	( void ) xTaskCreate( vCheckTask, "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

	/* Configure the timers used by the fast interrupt timer test. */
	vSetupTimerTest();

	/* The suicide tasks must be created last as they need to know how many
	tasks were running prior to their creation in order to ascertain whether
	or not the correct/expected number of tasks are running at any given time. */
	vCreateSuicidalTasks( mainCREATOR_TASK_PRIORITY );

	/* Will only get here if there was insufficient memory to create the idle
    task.  The idle task is created within vTaskStartScheduler(). */
	vTaskStartScheduler();

	/* Should never reach here as the kernel will now be running.  If
	vTaskStartScheduler() does return then it is very likely that there was
	insufficient (FreeRTOS) heap space available to create all the tasks,
	including the idle task that is created within vTaskStartScheduler() itself. */
	for( ;; );
}
/*---------------------------------------------------------------------------*/

void prvHardwareSetup( void )
{
/* Port layer functions that need to be copied into the vector table. */
extern void xPortPendSVHandler( void );
extern void xPortSysTickHandler( void );
extern void vPortSVCHandler( void );
extern cyisraddress CyRamVectors[];

	/* Install the OS Interrupt Handlers. */
	CyRamVectors[ 11 ] = ( cyisraddress ) vPortSVCHandler;
	CyRamVectors[ 14 ] = ( cyisraddress ) xPortPendSVHandler;
	CyRamVectors[ 15 ] = ( cyisraddress ) xPortSysTickHandler;

	/* Start-up the peripherals. */

	/* Enable and clear the LCD Display. */
	LCD_Character_Display_Start();
	LCD_Character_Display_ClearDisplay();
	LCD_Character_Display_Position( 0, 0 );
	LCD_Character_Display_PrintString( "www.FreeRTOS.org " );
	LCD_Character_Display_Position( 1, 0 );
	LCD_Character_Display_PrintString("CY8C5588AX-060  ");

	/* Start the UART. */
	UART_1_Start();

	/* Initialise the LEDs. */
	vParTestInitialise();

	/* Start the PWM modules that drive the IntQueue tests. */
	High_Frequency_PWM_0_Start();
	High_Frequency_PWM_1_Start();

	/* Start the timers for the Jitter test. */
	Timer_20KHz_Start();
	Timer_48MHz_Start();
}
/*---------------------------------------------------------------------------*/

void vCheckTask( void *pvParameters )
{
unsigned long ulRow = 0;
TickType_t xDelay = 0;
unsigned short usErrorCode = 0;
unsigned long ulIteration = 0;
extern unsigned short usMaxJitter;

	/* Intialise the sleeper. */
	xDelay = xTaskGetTickCount();

	for( ;; )
	{
		/* Perform this check every mainCHECK_DELAY milliseconds. */
		vTaskDelayUntil( &xDelay, mainCHECK_DELAY );

		/* Check that all of the Demo tasks are still running. */
		if( pdTRUE != xAreBlockingQueuesStillRunning() )
		{
			usErrorCode |= 0x1;
		}

		if( pdTRUE != xAreBlockTimeTestTasksStillRunning() )
		{
			usErrorCode |= 0x2;
		}

		if( pdTRUE != xAreCountingSemaphoreTasksStillRunning() )
		{
			usErrorCode |= 0x4;
		}

		if( pdTRUE != xIsCreateTaskStillRunning() )
		{
			usErrorCode |= 0x8;
		}

		if( pdTRUE != xAreDynamicPriorityTasksStillRunning() )
		{
			usErrorCode |= 0x10;
		}

		if( pdTRUE != xAreMathsTaskStillRunning() )
		{
			usErrorCode |= 0x20;
		}

		if( pdTRUE != xAreGenericQueueTasksStillRunning() )
		{
			usErrorCode |= 0x40;
		}

		if( pdTRUE != xAreIntegerMathsTaskStillRunning() )
		{
			usErrorCode |= 0x80;
		}

		if( pdTRUE != xArePollingQueuesStillRunning() )
		{
			usErrorCode |= 0x100;
		}

		if( pdTRUE != xAreQueuePeekTasksStillRunning() )
		{
			usErrorCode |= 0x200;
		}

		if( pdTRUE != xAreSemaphoreTasksStillRunning() )
		{
			usErrorCode |= 0x400;
		}

		if( pdTRUE != xAreComTestTasksStillRunning() )
		{
			usErrorCode |= 0x800;
		}

		if( pdTRUE != xAreIntQueueTasksStillRunning() )
		{
			usErrorCode |= 0x1000;
		}

		/* Clear the display. */
		LCD_Character_Display_ClearDisplay();
		if( 0 == usErrorCode )
		{
			LCD_Character_Display_Position( ( ulRow ) & 0x1, 0);
			LCD_Character_Display_PrintString( "Pass: " );
			LCD_Character_Display_PrintNumber( ulIteration++ );
			LCD_Character_Display_Position( ( ++ulRow ) & 0x1, 0 );
			LCD_Character_Display_PrintString( "Jitter(ns):" );
			LCD_Character_Display_PrintNumber( ( usMaxJitter * mainNS_PER_CLOCK ) );
		}
		else
		{
			/* Do something to indicate the failure. */
			LCD_Character_Display_Position( ( ulRow ) & 0x1, 0 );
			LCD_Character_Display_PrintString( "Fail at: " );
			LCD_Character_Display_PrintNumber( ulIteration );
			LCD_Character_Display_Position( ( ++ulRow ) & 0x1, 0 );
			LCD_Character_Display_PrintString( "Error: 0x" );
			LCD_Character_Display_PrintHexUint16( usErrorCode );
		}
	}
}
/*---------------------------------------------------------------------------*/

void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName )
{
	/* The stack space has been execeeded for a task, considering allocating more. */
	taskDISABLE_INTERRUPTS();
	for( ;; );
}
/*---------------------------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
	/* The heap space has been execeeded. */
	taskDISABLE_INTERRUPTS();
	for( ;; );
}
/*---------------------------------------------------------------------------*/
