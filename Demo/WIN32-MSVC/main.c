/*
    FreeRTOS V6.1.0 - Copyright (C) 2010 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS books - available as PDF or paperback  *
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

#include <stdio.h>
#include <FreeRTOS.h>
#include "task.h"
#include "queue.h"

/* Task priorities. */
#define mainSTDOUT_TASK_PRIORITY	tskIDLE_PRIORITY

/* Stack sizes. */
#define mainSTDOUT_TASK_STACK_SIZE		( configMINIMAL_STACK_SIZE * 4 )

/* File scope variables. */
static volatile unsigned long ul1 = 0, ul2 = 0;
static xQueueHandle xStdoutQueue = NULL;

/* Task function prototypes. */
static void prvTask1( void *pvParameters );
static void prvTask2( void *pvParameters );
static void prvStdoutTask( void *pvParameters );

/* Create a queue on which console output strings can be posted, then start the
task that processes the queue - printf()'ing each string that is received. */
static void prvStartStdoutTask( void );

/* Post a message for output by the stdout task.  Basically queues the message
pointed to by pcTextToPrint for output to stdout in a thread safe manner. */
void vMainConsolePrint( const char *pcTextToPrint, portTickType xTicksToWait );

volatile unsigned long ulIdleCount = 0UL, ulT1Count = 0UL, ulT2Count = 0UL, ulTicks = 0UL;
/*-----------------------------------------------------------*/

int main( void )
{
	prvStartStdoutTask();
	xTaskCreate( prvTask1, "t1", 100, NULL, 0, NULL );
	xTaskCreate( prvTask2, "t2", 100, NULL, 0, NULL );
	vTaskStartScheduler();

    /* Should never get here unless there was not enough heap space to create 
	the idle and other system tasks. */
    return 0;
}
/*-----------------------------------------------------------*/

void vMainConsolePrint( const char *pcTextToPrint, portTickType xTicksToWait )
{
	if( xStdoutQueue != NULL )
	{
		xQueueSend( xStdoutQueue, &pcTextToPrint, xTicksToWait );
	}
}
/*-----------------------------------------------------------*/

static void prvStartStdoutTask( void )
{
const unsigned long ulQueueLength = 20;

	/* Create the queue on which starings for output will be stored. */
	xStdoutQueue = xQueueCreate( ulQueueLength, ( unsigned portBASE_TYPE ) sizeof( char * ) );

	if( xStdoutQueue != NULL )
	{
		/* Create the task that processes the stdout messages. */
		xTaskCreate( prvStdoutTask, "stdout task", mainSTDOUT_TASK_STACK_SIZE, NULL, mainSTDOUT_TASK_PRIORITY, NULL );
	}
}
/*-----------------------------------------------------------*/

static void prvStdoutTask( void *pvParameters )
{
char *pcString;

	/* Just to remove compiler warnings. */
	( void ) pvParameters;

	for( ;; )
	{
		/* This task would not have been created if the queue had not been created
		successfully too.  Also, because of the FreeRTOSConfig.h settings using
		portMAX_DELAY in this case means wait forever, so when this function returns
		we know there is a string to print. */
		xQueueReceive( xStdoutQueue, &pcString, portMAX_DELAY );
		printf( "%s", pcString );
		//fflush( stdout );
	}
}
/*-----------------------------------------------------------*/

static void prvTask1( void *pvParameters )
{
const char *pcTask1Message = "Task 1 running\r\n";
const portTickType xTicksToDelay = 1000 / portTICK_RATE_MS;

	/* Just to remove compiler warnings. */
	( void ) pvParameters;

	for( ;; )
	{
//		ul1++;
		vMainConsolePrint( pcTask1Message, 0 );
		vTaskDelay( xTicksToDelay );
		ulT1Count++;
	}
}
/*-----------------------------------------------------------*/

static void prvTask2( void *pvParameters )
{
const char *pcTask2Message = "Task 2 running\r\n";
const portTickType xTicksToDelay = 500 / portTICK_RATE_MS;

	/* Just to remove compiler warnings. */
	( void ) pvParameters;

	for( ;; )
	{
//		ul2++;
		vMainConsolePrint( pcTask2Message, 0 );
		vTaskDelay( xTicksToDelay );
		ulT2Count++;
//		taskYIELD();
	}
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook()
{
const unsigned long ulMSToSleep = 5;

	/* Sleep to reduce CPU load, but don't sleep indefinitely if not using 
	preemption as as nothing will cause	a task switch. */
	#if configUSE_PREEMPTION != 0
	{
		SleepEx( INFINITE, TRUE );
	}
	#else
	{
		SleepEx( ulMSToSleep, TRUE );
	}
	#endif

	ulIdleCount++;
}
