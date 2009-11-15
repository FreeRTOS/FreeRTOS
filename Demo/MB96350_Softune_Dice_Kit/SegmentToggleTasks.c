/*
    FreeRTOS V6.0.1 - Copyright (C) 2009 Real Time Engineers Ltd.

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
#define ledFLASH_RATE_BASE	( ( portTickType ) 333 )

/* One co-routine per segment of the right hand display. */
#define ledNUM_OF_LED_CO_ROUTINES	7

/* All co-routines run at the same priority. */
#define ledCO_ROUTINE_PRIORITY		0

/*-----------------------------------------------------------*/

/* The task that is created 7 times. */
static void vLEDFlashTask( void *pvParameters );

/* The co-routine that is created 7 times. */
static void prvFixedDelayCoRoutine( xCoRoutineHandle xHandle, unsigned short usIndex );

/* This task is created once, but itself creates 7 co-routines. */
static void vLEDCoRoutineControlTask( void *pvParameters );

/* Handles to each of the 7 tasks.  Used so the tasks can be suspended
and resumed. */
static xTaskHandle xFlashTaskHandles[ ledNUM_OF_LED_TASKS ] = { 0 };

/* Handle to the task in which the co-routines run.  Used so the
co-routines can be suspended and resumed. */
static xTaskHandle xCoroutineTask;

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
		xTaskCreate( vLEDFlashTask, ( signed char * ) "LEDt", configMINIMAL_STACK_SIZE, ( void * ) sLEDTask, ( tskIDLE_PRIORITY + 1 ), &( xFlashTaskHandles[ sLEDTask ] ) );
	}

	/* Create the task in which the co-routines run.  The co-routines themselves
	are created within the task. */
	xTaskCreate( vLEDCoRoutineControlTask, ( signed char * ) "LEDc", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, &xCoroutineTask );
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
portTickType xFlashRate, xLastFlashTime;
unsigned short usLED;

	/* The LED to flash is passed in as the task parameter. */
	usLED = ( unsigned short ) pvParameters;

	/* Calculate the rate at which this task is going to toggle its LED. */
	xFlashRate = ledFLASH_RATE_BASE + ( ledFLASH_RATE_BASE * ( portTickType ) usLED );
	xFlashRate /= portTICK_RATE_MS;

	/* We will turn the LED on and off again in the delay period, so each
	delay is only half the total period. */
	xFlashRate /= ( portTickType ) 2;

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

static void prvFixedDelayCoRoutine( xCoRoutineHandle xHandle, unsigned short usIndex )
{
/* The usIndex parameter of the co-routine function is used as an index into
the xFlashRates array to obtain the delay period to use. */
static const portTickType xFlashRates[ ledNUM_OF_LED_CO_ROUTINES ] = { 150 / portTICK_RATE_MS,
																300 / portTICK_RATE_MS,
																450 / portTICK_RATE_MS,
																600 / portTICK_RATE_MS,
																750 / portTICK_RATE_MS,
																900 / portTICK_RATE_MS,
																1050 / portTICK_RATE_MS };

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


