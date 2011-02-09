/*
    FreeRTOS V6.1.1 - Copyright (C) 2011 Real Time Engineers Ltd.

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


/* 
 * Tests the behaviour of timers.  Some timers are created before hte scheudler
 * is started, and some after.
 */


/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "timers.h"

/* Demo program include files. */
#include "TimerDemo.h"

#if configTIMER_TASK_PRIORITY < 1
	#error configTIMER_TASK_PRIORITY must be set to at least 1 for this test/demo to function correctly.
#endif

#define tmrdemoDONT_BLOCK				( ( portTickType ) 0 )
#define tmrdemoONE_SHOT_TIMER_FREQUENCY ( xBaseFrequency * ( portTickType ) 3 )
#define trmdemoNUM_TIMER_RESETS			( ( unsigned char ) 10 )

/*-----------------------------------------------------------*/

static void prvFreeRunningTimerCallback( xTimerHandle pxExpiredTimer );
static void prvTimerControlTask( void *pvParameters );

/*-----------------------------------------------------------*/

/* Flag that will be latched to pdFAIL should any unexpected behaviour be
detected in any of the demo tests. */
static volatile portBASE_TYPE xTestStatus = pdPASS;

/* Counter that is incremented on each cycle of a test.  This is used to
detect a stalled task - a test that is no longer running. */
static volatile unsigned portLONG ulLoopCounter = 0;

xTimerHandle xFreeRunningTimers[ configTIMER_QUEUE_LENGTH + 1 ] = { 0 };
unsigned char ucFreeRunningTimerCounters[ configTIMER_QUEUE_LENGTH + 1 ] = { 0 };
unsigned char ucOneShotTimerCounter = ( unsigned char ) 0;

static portTickType xBaseFrequency = 0;

/*-----------------------------------------------------------*/

void vStartTimerDemoTask( portTickType xBaseFrequencyIn )
{
portBASE_TYPE xTimer;

	xBaseFrequency = xBaseFrequencyIn;

	for( xTimer = 0; xTimer < configTIMER_QUEUE_LENGTH; xTimer++ )
	{
		/* As the timer queue is not yet full, it should be possible to both create
		and start a timer.  These timers are being started before the scheduler has
		been started, so their block times should get set to zero within the timer
		API itself. */
		xFreeRunningTimers[ xTimer ] = xTimerCreate( "FR Timer",						/* Text name to facilitate debugging.  The kernel does not use this itself. */
													( ( xTimer + 1 ) * xBaseFrequency ),/* The period for the timer.  The plus 1 ensures a period of zero is not specified. */
													pdTRUE,								/* Autoreload is set to true. */
													( void * ) xTimer,					/* An identifier for the timer as all the free running timers use the same callback. */
													prvFreeRunningTimerCallback );		/* The callback to be called when the timer expires. */

		if( xFreeRunningTimers[ xTimer ] == NULL )
		{
			xTestStatus = pdFAIL;
		}
		else
		{
			/* The scheduler has not yet started, so the block period of 
			portMAX_DELAY should just get set to zero in xTimerStart().  Also,
			the timer queue is not yet full so xTimerStart() should return
			pdPASS. */
			if( xTimerStart( xFreeRunningTimers[ xTimer ], portMAX_DELAY ) != pdPASS )
			{
				xTestStatus = pdFAIL;
			}
		}
	}

	/* The timers queue should now be full, so it should be possible to create
	another timer, but not possible to start it (the timer queue will not get
	drained until the scheduler has been started. */
	xFreeRunningTimers[ configTIMER_QUEUE_LENGTH ] = xTimerCreate( "FR Timer",		/* Text name to facilitate debugging.  The kernel does not use this itself. */
													( configTIMER_QUEUE_LENGTH * xBaseFrequency ),	/* The period for the timer. */
													pdTRUE,							/* Autoreload is set to true. */
													( void * ) xTimer,				/* An identifier for the timer as all the free running timers use the same callback. */
													prvFreeRunningTimerCallback );	/* The callback to be called when the timer expires. */

	if( xFreeRunningTimers[ configTIMER_QUEUE_LENGTH ] == NULL )
	{
		xTestStatus = pdFAIL;
	}
	else
	{
		if( xTimerStart( xFreeRunningTimers[ xTimer ], portMAX_DELAY ) == pdPASS )
		{
			/* This time it would not be expected that the timer could be
			started at this point. */
			xTestStatus = pdFAIL;
		}
	}

	/* Create the task that will control and monitor the timers.  This is 
	created at a lower priority than the timer service task to ensure, as
	far as it is concerned, commands on timers are actioned immediately 
	(sending a command to the timer service task will unblock the timer service
	task, which will then preempt this task). */
	if( xTestStatus != pdFAIL )
	{
		xTaskCreate( prvTimerControlTask, ( signed portCHAR * ) "Tmr Ctl", configMINIMAL_STACK_SIZE, NULL, configTIMER_TASK_PRIORITY - 1, NULL );
	}
}
/*-----------------------------------------------------------*/

static void prvFreeRunningTimerCallback( xTimerHandle pxExpiredTimer )
{
portBASE_TYPE xTimerID;

	xTimerID = ( portBASE_TYPE ) pvTimerGetTimerID( pxExpiredTimer );
	if( xTimerID <= ( configTIMER_QUEUE_LENGTH + 1 ) )
	{
		( ucFreeRunningTimerCounters[ xTimerID ] )++;
	}
	else
	{
		/* The timer ID appears to be unexpected (invalid). */
		xTestStatus = pdFAIL;
	}
}
/*-----------------------------------------------------------*/

static void prvOneShotTimerCallback( xTimerHandle pxExpiredTimer )
{
	/* The parameter is not used in this case as only one timer uses this
	callback function. */
	( void ) pxExpiredTimer;

	ucOneShotTimerCounter++;
}
/*-----------------------------------------------------------*/

static void prvTimerControlTask( void *pvParameters )
{
portTickType xNextWakeTime;
unsigned char ucTimer;
unsigned char ucMaxAllowableValue, ucMinAllowableValue;
xTimerHandle xOneShotTimer = NULL;

	( void ) pvParameters;

	/* Create a one-shot timer for use later on in this test. */
	xOneShotTimer = xTimerCreate(	"Oneshot Timer",				/* Text name to facilitate debugging.  The kernel does not use this itself. */
									tmrdemoONE_SHOT_TIMER_FREQUENCY,/* The period for the timer. */
									pdFALSE,						/* Don't autoreload - hence a one shot timer. */
									( void * ) 0,					/* The timer identifier.  In this case this is not used as the timer has its own callback. */
									prvOneShotTimerCallback );		/* The callback to be called when the timer expires. */

	if( xOneShotTimer == NULL )
	{
		xTestStatus = pdFAIL;
	}


	/*-----------------------------------------------------------*/
	/* Test 1 - ensure all the timers are in their expected initial state.  This
	depends on the timer service task having a higher priority than this task. */

	/* Free running timers 0 to ( configTIMER_QUEUE_LENGTH - 1 ) should now
	be active, and free running timer configTIMER_QUEUE_LENGTH should not
	yet be active (it could not be started prior to the scheduler being
	started. */
	for( ucTimer = 0; ucTimer < ( unsigned char ) configTIMER_QUEUE_LENGTH; ucTimer++ )
	{
		if( xTimerIsTimerActive( xFreeRunningTimers[ ucTimer ] ) == pdFALSE )
		{
			xTestStatus = pdFAIL;
		}
	}

	if( xTimerIsTimerActive( xFreeRunningTimers[ configTIMER_QUEUE_LENGTH ] ) != pdFALSE )
	{
		xTestStatus = pdFAIL;
	}

	for( ;; )
	{
		/*-----------------------------------------------------------*/
		/* Test 2 - Check the free running timers expire at the expcted rates. */

		/* Initialise the next wake time value before the call to 
		vTaskDelayUntil() as this is not really a periodic task. */
		xNextWakeTime = xTaskGetTickCount();

		/* Delaying for configTIMER_QUEUE_LENGTH * xBaseFrequency ticks 
		should allow all the free running timers to expire at least once. */
		vTaskDelayUntil( &xNextWakeTime, ( ( portTickType ) configTIMER_QUEUE_LENGTH ) * xBaseFrequency );

		/* Check that all the free running timers have called their callback 
		function the expected number of times. */
		for( ucTimer = 0; ucTimer < ( unsigned char ) configTIMER_QUEUE_LENGTH; ucTimer++ )
		{
			/* The timer in array position 0 should elapse every xBaseFrequency 
			ticks, the timer in array position 1 should elapse every
			( 2 * xBaseFrequency ) ticks, etc.  This task blocked for 
			configTIMER_QUEUE_LENGTH * xBaseFrequency, so the timer in array
			position 0 should have elapsed configTIMER_QUEUE_LENGTH times, the
			timer in array possition 1 should have elapsed 
			( configTIMER_QUEUE_LENGTH - 1 ) times, etc. */
			ucMaxAllowableValue = ( ( ( unsigned char ) configTIMER_QUEUE_LENGTH ) - ucTimer );
			ucMinAllowableValue = ( ( ( unsigned char ) configTIMER_QUEUE_LENGTH ) - ucTimer ) - 1;

			if( ( ucFreeRunningTimerCounters[ ucTimer ] < ucMinAllowableValue ) ||
				( ucFreeRunningTimerCounters[ ucTimer ] > ucMaxAllowableValue )
			  )
			{
				xTestStatus = pdFAIL;
			}
		}

		if( xTestStatus == pdPASS )
		{
			/* No errors have been reported so increment the loop counter so
			the check task knows this task is still running. */
			ulLoopCounter++;
		}




		/*-----------------------------------------------------------*/
		/* Test 3 - Check the free running timers can be stopped correctly, and
		correctly report their state. */

		/* Stop all the active timers. */
		for( ucTimer = 0; ucTimer < ( unsigned char ) configTIMER_QUEUE_LENGTH; ucTimer++ )
		{
			/* The timer has not been stopped yet! */
			if( xTimerIsTimerActive( xFreeRunningTimers[ ucTimer ] ) == pdFALSE )
			{
				xTestStatus = pdFAIL;
			}

			/* Now stop the timer.  This will appear to happen immediately to 
			this task because this task is running at a priority below the 
			timer service task. */
			xTimerStop( xFreeRunningTimers[ ucTimer ], tmrdemoDONT_BLOCK );

			/* The timer should now be inactive. */
			if( xTimerIsTimerActive( xFreeRunningTimers[ ucTimer ] ) != pdFALSE )
			{
				xTestStatus = pdFAIL;
			}
		}

		taskENTER_CRITICAL();
		{
			/* The timer in array position configTIMER_QUEUE_LENGTH should not 
			be active.  The critical section is used to ensure the timer does 
			not call its callback between the next line running and the array 
			being cleared back to zero, as that would mask an error condition. */
			if( ucFreeRunningTimerCounters[ configTIMER_QUEUE_LENGTH ] != ( unsigned char ) 0 )
			{
				xTestStatus = pdFAIL;
			}

			/* Clear the timer callback count. */
			memset( ( void * ) ucFreeRunningTimerCounters, 0, sizeof( ucFreeRunningTimerCounters ) );
		}
		taskEXIT_CRITICAL();

		/* The timers are now all inactive, so this time, after delaying, none
		of the callback counters should have incremented. */
		vTaskDelay( ( ( portTickType ) configTIMER_QUEUE_LENGTH ) * xBaseFrequency );
		for( ucTimer = 0; ucTimer < ( unsigned char ) configTIMER_QUEUE_LENGTH; ucTimer++ )
		{
			if( ucFreeRunningTimerCounters[ ucTimer ] != ( unsigned char ) 0 )
			{
				xTestStatus = pdFAIL;
			}
		}

		if( xTestStatus == pdPASS )
		{
			/* No errors have been reported so increment the loop counter so
			the check task knows this task is still running. */
			ulLoopCounter++;
		}



		/*-----------------------------------------------------------*/
		/* Test 4 - Check the one shot timer only calls its callback once after
		it has been started, and that it reports its state correctly. */

		/* The one shot timer should not be active yet. */
		if( xTimerIsTimerActive( xOneShotTimer ) != pdFALSE )
		{
			xTestStatus = pdFAIL;
		}

		if( ucOneShotTimerCounter != ( unsigned char ) 0 )
		{
			xTestStatus = pdFAIL;
		}

		/* Start the one shot timer and check that it reports its state
		correctly. */
		xTimerStart( xOneShotTimer, tmrdemoDONT_BLOCK );
		if( xTimerIsTimerActive( xOneShotTimer ) == pdFALSE )
		{
			xTestStatus = pdFAIL;
		}

		/* Delay for three times as long as the one shot timer period, then
		check to ensure it has only called its callback once, and is now
		not in the active state. */
		vTaskDelay( tmrdemoONE_SHOT_TIMER_FREQUENCY * ( portTickType ) 3 );

		if( xTimerIsTimerActive( xOneShotTimer ) != pdFALSE )
		{
			xTestStatus = pdFAIL;
		}

		if( ucOneShotTimerCounter != ( unsigned char ) 1 )
		{
			xTestStatus = pdFAIL;
		}
		else
		{
			/* Reset the one shot timer callback count. */
			ucOneShotTimerCounter = ( unsigned char ) 0;
		}

		if( xTestStatus == pdPASS )
		{
			/* No errors have been reported so increment the loop counter so
			the check task knows this task is still running. */
			ulLoopCounter++;
		}




		/*-----------------------------------------------------------*/
		/* Test 5 - Check all the timers can be reset while they are running. */

		/* Restart the one shot timer and check it reports its status 
		correctly. */
		xTimerStart( xOneShotTimer, tmrdemoDONT_BLOCK );
		if( xTimerIsTimerActive( xOneShotTimer ) == pdFALSE )
		{
			xTestStatus = pdFAIL;
		}

		/* Restart one of the free running timers and check that it reports its
		status correctly. */
		xTimerStart( xFreeRunningTimers[ configTIMER_QUEUE_LENGTH - 1 ], tmrdemoDONT_BLOCK );
		if( xTimerIsTimerActive( xFreeRunningTimers[ configTIMER_QUEUE_LENGTH - 1 ] ) == pdFALSE )
		{
			xTestStatus = pdFAIL;
		}

		for( ucTimer = 0; ucTimer < trmdemoNUM_TIMER_RESETS; ucTimer++ )
		{
			/* Delay for half as long as the one shot timer period, then
			reset it.  It should never expire while this is done, so its callback
			count should never increment. */
			vTaskDelay( tmrdemoONE_SHOT_TIMER_FREQUENCY / 2 );

			/* Check both running timers are still active, but have not called their
			callback functions. */
			if( xTimerIsTimerActive( xOneShotTimer ) != pdFALSE )
			{
				xTestStatus = pdFAIL;
			}

			if( ucOneShotTimerCounter != ( unsigned char ) 0 )
			{
				xTestStatus = pdFAIL;
			}

			if( xTimerIsTimerActive( xFreeRunningTimers[ configTIMER_QUEUE_LENGTH - 1 ] ) != pdFALSE )
			{
				xTestStatus = pdFAIL;
			}

			if( ucFreeRunningTimerCounters[ configTIMER_QUEUE_LENGTH - 1 ] != ( unsigned char ) 0 )
			{
				xTestStatus = pdFAIL;
			}

			/* Reset both running timers. */
			xTimerReset( xOneShotTimer, tmrdemoDONT_BLOCK );
			xTimerReset( xFreeRunningTimers[ configTIMER_QUEUE_LENGTH - 1 ], tmrdemoDONT_BLOCK );

			if( xTestStatus == pdPASS )
			{
				/* No errors have been reported so increment the loop counter so
				the check task knows this task is still running. */
				ulLoopCounter++;
			}
		}

		/* Finally delay long enough for both running timers to expire. */
		vTaskDelay( ( ( portTickType ) configTIMER_QUEUE_LENGTH ) * xBaseFrequency );

		/* The timers were not reset during the above delay period so should now
		both have called their callback functions. */
		if( ucOneShotTimerCounter != ( unsigned char ) 1 )
		{
			xTestStatus = pdFAIL;
		}

		if( ucFreeRunningTimerCounters[ configTIMER_QUEUE_LENGTH - 1 ] == 0 )
		{
			xTestStatus = pdFAIL;
		}

		/* The one shot timer should no longer be active, while the free running
		timer should still be active. */
		if( xTimerIsTimerActive( xFreeRunningTimers[ configTIMER_QUEUE_LENGTH - 1 ] ) == pdFALSE )
		{
			xTestStatus = pdFAIL;
		}

		if( xTimerIsTimerActive( xOneShotTimer ) == pdTRUE )
		{
			xTestStatus = pdFAIL;
		}

		/* Stop the free running timer again. */
		xTimerStop( xFreeRunningTimers[ configTIMER_QUEUE_LENGTH - 1 ], tmrdemoDONT_BLOCK );

		if( xTimerIsTimerActive( xFreeRunningTimers[ configTIMER_QUEUE_LENGTH - 1 ] ) != pdFALSE )
		{
			xTestStatus = pdFAIL;
		}

		/* Clear the timer callback counts, ready for another iteration of these
		tests. */
		ucFreeRunningTimerCounters[ configTIMER_QUEUE_LENGTH - 1 ] = ( unsigned char ) 0;
		ucOneShotTimerCounter = ( unsigned char ) 0;

		if( xTestStatus == pdPASS )
		{
			/* No errors have been reported so increment the loop counter so
			the check task knows this task is still running. */
			ulLoopCounter++;
		}




		/*-----------------------------------------------------------*/
		/* Start the timers again to start all the tests over again. */


		/* Start the timers again. */
		for( ucTimer = 0; ucTimer < ( unsigned char ) configTIMER_QUEUE_LENGTH; ucTimer++ )
		{
			/* The timer has not been started yet! */
			if( xTimerIsTimerActive( xFreeRunningTimers[ ucTimer ] ) != pdFALSE )
			{
				xTestStatus = pdFAIL;
			}

			/* Now start the timer.  This will appear to happen immediately to 
			this task because this task is running at a priority below the 
			timer service task. */
			xTimerStart( xFreeRunningTimers[ ucTimer ], tmrdemoDONT_BLOCK );

			/* The timer should now be active. */
			if( xTimerIsTimerActive( xFreeRunningTimers[ ucTimer ] ) == pdFALSE )
			{
				xTestStatus = pdFAIL;
			}
		}

		if( xTestStatus == pdPASS )
		{
			/* No errors have been reported so increment the loop counter so
			the check task knows this task is still running. */
			ulLoopCounter++;
		}
	}
}
/*-----------------------------------------------------------*/

/* This is called to check that the created task is still running and has not
detected any errors. */
portBASE_TYPE xAreTimerDemoTasksStillRunning( void )
{
static unsigned portLONG ulLastLoopCounter = 0;

	/* If the demo task is still running then we expect the loopcounter to
	have incremented since this function was last called. */
	if( ulLastLoopCounter == ulLoopCounter )
	{
		xTestStatus = pdFAIL;
	}

	ulLastLoopCounter = ulLoopCounter;

	/* Errors detected in the task itself will have latched xTestStatus
	to pdFAIL. */

	return xTestStatus;
}

