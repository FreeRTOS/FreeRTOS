/*
 * FreeRTOS Kernel V10.3.1
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

/**
 * Defines the tasks and co-routines used to toggle the segments of the two
 * seven segment displays, as described at the top of main.c
 */


#include <stdlib.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "croutine.h"

/* Demo program include files. */
#include "partest.h"

/*-----------------------------------------------------------*/

/* One task per segment of the left side display. */
#define ledNUM_OF_LED_TASKS	( 7 )

/* Each task toggles at a frequency that is a multiple of 333ms. */
#define ledFLASH_RATE_BASE	( ( TickType_t ) 333 )

/* One co-routine per segment of the right hand display. */
#define ledNUM_OF_LED_CO_ROUTINES	7

/* All co-routines run at the same priority. */
#define ledCO_ROUTINE_PRIORITY		0

/*-----------------------------------------------------------*/

/* The task that is created 7 times. */
static void vLEDFlashTask( void *pvParameters );

/* The co-routine that is created 7 times. */
static void prvFixedDelayCoRoutine( CoRoutineHandle_t xHandle, unsigned short usIndex );

/* This task is created once, but itself creates 7 co-routines. */
static void vLEDCoRoutineControlTask( void *pvParameters );

/* Handles to each of the 7 tasks.  Used so the tasks can be suspended
and resumed. */
static TaskHandle_t xFlashTaskHandles[ ledNUM_OF_LED_TASKS ] = { 0 };

/* Handle to the task in which the co-routines run.  Used so the
co-routines can be suspended and resumed. */
static TaskHandle_t xCoroutineTask;

/*-----------------------------------------------------------*/

/**
 * Creates the tasks and co-routines used to toggle the segments of the two
 * seven segment displays, as described at the top of main.c
 */
void vCreateFlashTasksAndCoRoutines( void )
{
signed short sLEDTask;

	/* Create the tasks that flash segments on the first LED. */
	for( sLEDTask = 0; sLEDTask < ledNUM_OF_LED_TASKS; ++sLEDTask )
	{
		/* Spawn the task. */
		xTaskCreate( vLEDFlashTask, "LEDt", configMINIMAL_STACK_SIZE, ( void * ) sLEDTask, ( tskIDLE_PRIORITY + 1 ), &( xFlashTaskHandles[ sLEDTask ] ) );
	}

	/* Create the task in which the co-routines run.  The co-routines themselves
	are created within the task. */
	xTaskCreate( vLEDCoRoutineControlTask, "LEDc", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, &xCoroutineTask );
}
/*-----------------------------------------------------------*/

void vSuspendFlashTasks( unsigned char ucIndex, short sSuspendTasks )
{
short sLEDTask;

	if( ucIndex == configLEFT_DISPLAY )
	{
		/* Suspend or resume the tasks that are toggling the segments of the
		left side display. */
		for( sLEDTask = 0; sLEDTask < ledNUM_OF_LED_TASKS; ++sLEDTask )
		{
			if( xFlashTaskHandles[ sLEDTask ] != NULL )
			{
				if( sSuspendTasks == pdTRUE )
				{
					vTaskSuspend( xFlashTaskHandles[ sLEDTask ] );
				}
				else
				{
					vTaskResume( xFlashTaskHandles[ sLEDTask ] );
				}
			}
		}
	}
	else
	{
		/* Suspend or resume the task in which the co-routines are running.  The
		co-routines toggle the segments of the right side display. */
		if( sSuspendTasks == pdTRUE )
		{
			vTaskSuspend( xCoroutineTask );
		}
		else
		{
			vTaskResume( xCoroutineTask );
		}
	}
}
/*-----------------------------------------------------------*/

static void vLEDFlashTask( void * pvParameters )
{
TickType_t xFlashRate, xLastFlashTime;
unsigned short usLED;

	/* The LED to flash is passed in as the task parameter. */
	usLED = ( unsigned short ) pvParameters;

	/* Calculate the rate at which this task is going to toggle its LED. */
	xFlashRate = ledFLASH_RATE_BASE + ( ledFLASH_RATE_BASE * ( TickType_t ) usLED );
	xFlashRate /= portTICK_PERIOD_MS;

	/* We will turn the LED on and off again in the delay period, so each
	delay is only half the total period. */
	xFlashRate /= ( TickType_t ) 2;

	/* We need to initialise xLastFlashTime prior to the first call to
	vTaskDelayUntil(). */
	xLastFlashTime = xTaskGetTickCount();

	for(;;)
	{
		/* Delay for half the flash period then turn the LED on. */
		vTaskDelayUntil( &xLastFlashTime, xFlashRate );
		vParTestToggleLED( usLED );

		/* Delay for half the flash period then turn the LED off. */
		vTaskDelayUntil( &xLastFlashTime, xFlashRate );
		vParTestToggleLED( usLED );
	}
}
/*-----------------------------------------------------------*/

static void vLEDCoRoutineControlTask( void *pvParameters )
{
unsigned short usCoroutine;

	( void ) pvParameters;

	/* Create the co-routines - one of each segment of the right side display. */
	for( usCoroutine = 0; usCoroutine < ledNUM_OF_LED_CO_ROUTINES; usCoroutine++ )
	{
		xCoRoutineCreate( prvFixedDelayCoRoutine, ledCO_ROUTINE_PRIORITY, usCoroutine );
	}

	/* This task has nothing else to do except scheduler the co-routines it just
	created. */
	for( ;; )
	{
		vCoRoutineSchedule();
	}
}
/*-----------------------------------------------------------*/

static void prvFixedDelayCoRoutine( CoRoutineHandle_t xHandle, unsigned short usIndex )
{
/* The usIndex parameter of the co-routine function is used as an index into
the xFlashRates array to obtain the delay period to use. */
static const TickType_t xFlashRates[ ledNUM_OF_LED_CO_ROUTINES ] = { 150 / portTICK_PERIOD_MS,
																300 / portTICK_PERIOD_MS,
																450 / portTICK_PERIOD_MS,
																600 / portTICK_PERIOD_MS,
																750 / portTICK_PERIOD_MS,
																900 / portTICK_PERIOD_MS,
																1050 / portTICK_PERIOD_MS };

	/* Co-routines MUST start with a call to crSTART. */
	crSTART( xHandle );

	for( ;; )
	{
		/* Toggle the LED.  An offset of 8 is used to skip over the segments of
		the left side display which use the low numbers. */
		vParTestToggleLED( usIndex + 8 );

		/* Delay until it is time to toggle the segment that this co-routine is
		controlling again. */
		crDELAY( xHandle, xFlashRates[ usIndex ] );
	}

	/* Co-routines MUST end with a call to crEND. */
	crEND();
}
/*-----------------------------------------------------------*/


