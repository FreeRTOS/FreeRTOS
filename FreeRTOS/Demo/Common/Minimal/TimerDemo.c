/*
 * FreeRTOS Kernel V10.0.0
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. If you wish to use our Amazon
 * FreeRTOS name, please do so in a fair use way that does not cause confusion.
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


/*
 * Tests the behaviour of timers.  Some timers are created before the scheduler
 * is started, and some after.
 */

/* Standard includes. */
#include <string.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "timers.h"

/* Demo program include files. */
#include "TimerDemo.h"

#if ( configTIMER_TASK_PRIORITY < 1 )
	#error configTIMER_TASK_PRIORITY must be set to at least 1 for this test/demo to function correctly.
#endif

#define tmrdemoDONT_BLOCK				( ( TickType_t ) 0 )
#define tmrdemoONE_SHOT_TIMER_PERIOD	( xBasePeriod * ( TickType_t ) 3 )
#define trmdemoNUM_TIMER_RESETS			( ( uint8_t ) 10 )

/*-----------------------------------------------------------*/

/* The callback functions used by the timers.  These each increment a counter
to indicate which timer has expired.  The auto-reload timers that are used by
the test task (as opposed to being used from an ISR) all share the same
prvAutoReloadTimerCallback() callback function, and use the ID of the
pxExpiredTimer parameter passed into that function to know which counter to
increment.  The other timers all have their own unique callback function and
simply increment their counters without using the callback function parameter. */
static void prvAutoReloadTimerCallback( TimerHandle_t pxExpiredTimer );
static void prvOneShotTimerCallback( TimerHandle_t pxExpiredTimer );
static void prvTimerTestTask( void *pvParameters );
static void prvISRAutoReloadTimerCallback( TimerHandle_t pxExpiredTimer );
static void prvISROneShotTimerCallback( TimerHandle_t pxExpiredTimer );

/* The test functions used by the timer test task.  These manipulate the auto
reload and one shot timers in various ways, then delay, then inspect the timers
to ensure they have behaved as expected. */
static void prvTest1_CreateTimersWithoutSchedulerRunning( void );
static void prvTest2_CheckTaskAndTimersInitialState( void );
static void	prvTest3_CheckAutoReloadExpireRates( void );
static void prvTest4_CheckAutoReloadTimersCanBeStopped( void );
static void prvTest5_CheckBasicOneShotTimerBehaviour( void );
static void prvTest6_CheckAutoReloadResetBehaviour( void );
static void prvResetStartConditionsForNextIteration( void );

/*-----------------------------------------------------------*/

/* Flag that will be latched to pdFAIL should any unexpected behaviour be
detected in any of the demo tests. */
static volatile BaseType_t xTestStatus = pdPASS;

/* Counter that is incremented on each cycle of a test.  This is used to
detect a stalled task - a test that is no longer running. */
static volatile uint32_t ulLoopCounter = 0;

/* A set of auto reload timers - each of which use the same callback function.
The callback function uses the timer ID to index into, and then increment, a
counter in the ucAutoReloadTimerCounters[] array.  The auto reload timers
referenced from xAutoReloadTimers[] are used by the prvTimerTestTask task. */
static TimerHandle_t xAutoReloadTimers[ configTIMER_QUEUE_LENGTH + 1 ] = { 0 };
static uint8_t ucAutoReloadTimerCounters[ configTIMER_QUEUE_LENGTH + 1 ] = { 0 };

/* The one shot timer is configured to use a callback function that increments
ucOneShotTimerCounter each time it gets called. */
static TimerHandle_t xOneShotTimer = NULL;
static uint8_t ucOneShotTimerCounter = ( uint8_t ) 0;

/* The ISR reload timer is controlled from the tick hook to exercise the timer
API functions that can be used from an ISR.  It is configured to increment
ucISRReloadTimerCounter each time its callback function is executed. */
static TimerHandle_t xISRAutoReloadTimer = NULL;
static uint8_t ucISRAutoReloadTimerCounter = ( uint8_t ) 0;

/* The ISR one shot timer is controlled from the tick hook to exercise the timer
API functions that can be used from an ISR.  It is configured to increment
ucISRReloadTimerCounter each time its callback function is executed. */
static TimerHandle_t xISROneShotTimer = NULL;
static uint8_t ucISROneShotTimerCounter = ( uint8_t ) 0;

/* The period of all the timers are a multiple of the base period.  The base
period is configured by the parameter to vStartTimerDemoTask(). */
static TickType_t xBasePeriod = 0;

/*-----------------------------------------------------------*/

void vStartTimerDemoTask( TickType_t xBasePeriodIn )
{
	/* Start with the timer and counter arrays clear - this is only necessary
	where the compiler does not clear them automatically on start up. */
	memset( ucAutoReloadTimerCounters, 0x00, sizeof( ucAutoReloadTimerCounters ) );
	memset( xAutoReloadTimers, 0x00, sizeof( xAutoReloadTimers ) );

	/* Store the period from which all the timer periods will be generated from
	(multiples of). */
	xBasePeriod = xBasePeriodIn;

	/* Create a set of timers for use by this demo/test. */
	prvTest1_CreateTimersWithoutSchedulerRunning();

	/* Create the task that will control and monitor the timers.  This is
	created at a lower priority than the timer service task to ensure, as
	far as it is concerned, commands on timers are actioned immediately
	(sending a command to the timer service task will unblock the timer service
	task, which will then preempt this task). */
	if( xTestStatus != pdFAIL )
	{
		xTaskCreate( prvTimerTestTask, "Tmr Tst", configMINIMAL_STACK_SIZE, NULL, configTIMER_TASK_PRIORITY - 1, NULL );
	}
}
/*-----------------------------------------------------------*/

static void prvTimerTestTask( void *pvParameters )
{
	( void ) pvParameters;

	/* Create a one-shot timer for use later on in this test. */
	xOneShotTimer = xTimerCreate(	"Oneshot Timer",				/* Text name to facilitate debugging.  The kernel does not use this itself. */
									tmrdemoONE_SHOT_TIMER_PERIOD,	/* The period for the timer. */
									pdFALSE,						/* Don't auto-reload - hence a one shot timer. */
									( void * ) 0,					/* The timer identifier.  Initialise to 0, then increment each time it is called. */
									prvOneShotTimerCallback );		/* The callback to be called when the timer expires. */

	if( xOneShotTimer == NULL )
	{
		xTestStatus = pdFAIL;
		configASSERT( xTestStatus );
	}


	/* Ensure all the timers are in their expected initial state.  This
	depends on the timer service task having a higher priority than this task. */
	prvTest2_CheckTaskAndTimersInitialState();

	for( ;; )
	{
		/* Check the auto reload timers expire at the expected/correct rates. */
		prvTest3_CheckAutoReloadExpireRates();

		/* Check the auto reload timers can be stopped correctly, and correctly
		report their state. */
		prvTest4_CheckAutoReloadTimersCanBeStopped();

		/* Check the one shot timer only calls its callback once after it has been
		started, and that it reports its state correctly. */
		prvTest5_CheckBasicOneShotTimerBehaviour();

		/* Check timer reset behaviour. */
		prvTest6_CheckAutoReloadResetBehaviour();

		/* Start the timers again to restart all the tests over again. */
		prvResetStartConditionsForNextIteration();
	}
}
/*-----------------------------------------------------------*/

/* This is called to check that the created task is still running and has not
detected any errors. */
BaseType_t xAreTimerDemoTasksStillRunning( TickType_t xCycleFrequency )
{
static uint32_t ulLastLoopCounter = 0UL;
TickType_t xMaxBlockTimeUsedByTheseTests, xLoopCounterIncrementTimeMax;
static TickType_t xIterationsWithoutCounterIncrement = ( TickType_t ) 0, xLastCycleFrequency;

	if( xLastCycleFrequency != xCycleFrequency )
	{
		/* The cycle frequency has probably become much faster due to an error
		elsewhere.  Start counting Iterations again. */
		xIterationsWithoutCounterIncrement = ( TickType_t ) 0;
		xLastCycleFrequency = xCycleFrequency;
	}

	/* Calculate the maximum number of times that it is permissible for this
	function to be called without ulLoopCounter being incremented.  This is
	necessary because the tests in this file block for extended periods, and the
	block period might be longer than the time between calls to this function. */
	xMaxBlockTimeUsedByTheseTests = ( ( TickType_t ) configTIMER_QUEUE_LENGTH ) * xBasePeriod;
	xLoopCounterIncrementTimeMax = ( xMaxBlockTimeUsedByTheseTests / xCycleFrequency ) + 1;

	/* If the demo task is still running then the loop counter is expected to
	have incremented every xLoopCounterIncrementTimeMax calls. */
	if( ulLastLoopCounter == ulLoopCounter )
	{
		xIterationsWithoutCounterIncrement++;
		if( xIterationsWithoutCounterIncrement > xLoopCounterIncrementTimeMax )
		{
			/* The tests appear to be no longer running (stalled). */
			xTestStatus = pdFAIL;
			configASSERT( xTestStatus );
		}
	}
	else
	{
		/* ulLoopCounter changed, so the count of times this function was called
		without a change can be reset to zero. */
		xIterationsWithoutCounterIncrement = ( TickType_t ) 0;
	}

	ulLastLoopCounter = ulLoopCounter;

	/* Errors detected in the task itself will have latched xTestStatus
	to pdFAIL. */

	return xTestStatus;
}
/*-----------------------------------------------------------*/

static void prvTest1_CreateTimersWithoutSchedulerRunning( void )
{
TickType_t xTimer;

	for( xTimer = 0; xTimer < configTIMER_QUEUE_LENGTH; xTimer++ )
	{
		/* As the timer queue is not yet full, it should be possible to both
		create and start a timer.  These timers are being started before the
		scheduler has been started, so their block times should get set to zero
		within the timer API itself. */
		xAutoReloadTimers[ xTimer ] = xTimerCreate( "FR Timer",							/* Text name to facilitate debugging.  The kernel does not use this itself. */
													( ( xTimer + ( TickType_t ) 1 ) * xBasePeriod ),/* The period for the timer.  The plus 1 ensures a period of zero is not specified. */
													pdTRUE,								/* Auto-reload is set to true. */
													( void * ) xTimer,					/* An identifier for the timer as all the auto reload timers use the same callback. */
													prvAutoReloadTimerCallback );		/* The callback to be called when the timer expires. */

		if( xAutoReloadTimers[ xTimer ] == NULL )
		{
			xTestStatus = pdFAIL;
			configASSERT( xTestStatus );
		}
		else
		{
			configASSERT( strcmp( pcTimerGetName( xAutoReloadTimers[ xTimer ] ), "FR Timer" ) == 0 );

			/* The scheduler has not yet started, so the block period of
			portMAX_DELAY should just get set to zero in xTimerStart().  Also,
			the timer queue is not yet full so xTimerStart() should return
			pdPASS. */
			if( xTimerStart( xAutoReloadTimers[ xTimer ], portMAX_DELAY ) != pdPASS )
			{
				xTestStatus = pdFAIL;
				configASSERT( xTestStatus );
			}
		}
	}

	/* The timers queue should now be full, so it should be possible to create
	another timer, but not possible to start it (the timer queue will not get
	drained until the scheduler has been started. */
	xAutoReloadTimers[ configTIMER_QUEUE_LENGTH ] = xTimerCreate( "FR Timer",					/* Text name to facilitate debugging.  The kernel does not use this itself. */
													( configTIMER_QUEUE_LENGTH * xBasePeriod ),	/* The period for the timer. */
													pdTRUE,										/* Auto-reload is set to true. */
													( void * ) xTimer,							/* An identifier for the timer as all the auto reload timers use the same callback. */
													prvAutoReloadTimerCallback );				/* The callback executed when the timer expires. */

	if( xAutoReloadTimers[ configTIMER_QUEUE_LENGTH ] == NULL )
	{
		xTestStatus = pdFAIL;
		configASSERT( xTestStatus );
	}
	else
	{
		if( xTimerStart( xAutoReloadTimers[ xTimer ], portMAX_DELAY ) == pdPASS )
		{
			/* This time it would not be expected that the timer could be
			started at this point. */
			xTestStatus = pdFAIL;
			configASSERT( xTestStatus );
		}
	}

	/* Create the timers that are used from the tick interrupt to test the timer
	API functions that can be called from an ISR. */
	xISRAutoReloadTimer = xTimerCreate( "ISR AR",							/* The text name given to the timer. */
										0xffff,								/* The timer is not given a period yet - this will be done from the tick hook, but a period of 0 is invalid. */
										pdTRUE,								/* This is an auto reload timer. */
										( void * ) NULL,					/* The identifier is not required. */
										prvISRAutoReloadTimerCallback );	/* The callback that is executed when the timer expires. */

	xISROneShotTimer = xTimerCreate( 	"ISR OS",							/* The text name given to the timer. */
										0xffff,								/* The timer is not given a period yet - this will be done from the tick hook, but a period of 0 is invalid. */
										pdFALSE,							/* This is a one shot timer. */
										( void * ) NULL,					/* The identifier is not required. */
										prvISROneShotTimerCallback );		/* The callback that is executed when the timer expires. */

	if( ( xISRAutoReloadTimer == NULL ) || ( xISROneShotTimer == NULL ) )
	{
		xTestStatus = pdFAIL;
		configASSERT( xTestStatus );
	}
}
/*-----------------------------------------------------------*/

static void prvTest2_CheckTaskAndTimersInitialState( void )
{
uint8_t ucTimer;

	/* Ensure all the timers are in their expected initial state.  This	depends
	on the timer service task having a higher priority than this task.

	auto reload timers 0 to ( configTIMER_QUEUE_LENGTH - 1 ) should now be active,
	and auto reload timer configTIMER_QUEUE_LENGTH should not yet be active (it
	could not be started prior to the scheduler being started when it was
	created). */
	for( ucTimer = 0; ucTimer < ( uint8_t ) configTIMER_QUEUE_LENGTH; ucTimer++ )
	{
		if( xTimerIsTimerActive( xAutoReloadTimers[ ucTimer ] ) == pdFALSE )
		{
			xTestStatus = pdFAIL;
			configASSERT( xTestStatus );
		}
	}

	if( xTimerIsTimerActive( xAutoReloadTimers[ configTIMER_QUEUE_LENGTH ] ) != pdFALSE )
	{
		xTestStatus = pdFAIL;
		configASSERT( xTestStatus );
	}
}
/*-----------------------------------------------------------*/

static void	prvTest3_CheckAutoReloadExpireRates( void )
{
uint8_t ucMaxAllowableValue, ucMinAllowableValue, ucTimer;
TickType_t xBlockPeriod, xTimerPeriod, xExpectedNumber;
UBaseType_t uxOriginalPriority;

	/* Check the auto reload timers expire at the expected rates.  Do this at a
	high priority for maximum accuracy.  This is ok as most of the time is spent
	in the Blocked state. */
	uxOriginalPriority = uxTaskPriorityGet( NULL );
	vTaskPrioritySet( NULL, ( configMAX_PRIORITIES - 1 ) );

	/* Delaying for configTIMER_QUEUE_LENGTH * xBasePeriod ticks should allow
	all the auto reload timers to expire at least once. */
	xBlockPeriod = ( ( TickType_t ) configTIMER_QUEUE_LENGTH ) * xBasePeriod;
	vTaskDelay( xBlockPeriod );

	/* Check that all the auto reload timers have called their callback
	function the expected number of times. */
	for( ucTimer = 0; ucTimer < ( uint8_t ) configTIMER_QUEUE_LENGTH; ucTimer++ )
	{
		/* The expected number of expiries is equal to the block period divided
		by the timer period. */
		xTimerPeriod = ( ( ( TickType_t ) ucTimer + ( TickType_t ) 1 ) * xBasePeriod );
		xExpectedNumber = xBlockPeriod / xTimerPeriod;

		ucMaxAllowableValue = ( ( uint8_t ) xExpectedNumber ) ;
		ucMinAllowableValue = ( uint8_t ) ( ( uint8_t ) xExpectedNumber - ( uint8_t ) 1 ); /* Weird casting to try and please all compilers. */

		if( ( ucAutoReloadTimerCounters[ ucTimer ] < ucMinAllowableValue ) ||
			( ucAutoReloadTimerCounters[ ucTimer ] > ucMaxAllowableValue )
			)
		{
			xTestStatus = pdFAIL;
			configASSERT( xTestStatus );
		}
	}

	/* Return to the original priority. */
	vTaskPrioritySet( NULL, uxOriginalPriority );

	if( xTestStatus == pdPASS )
	{
		/* No errors have been reported so increment the loop counter so the
		check task knows this task is still running. */
		ulLoopCounter++;
	}
}
/*-----------------------------------------------------------*/

static void prvTest4_CheckAutoReloadTimersCanBeStopped( void )
{
uint8_t ucTimer;

	/* Check the auto reload timers can be stopped correctly, and correctly
	report their state. */

	/* Stop all the active timers. */
	for( ucTimer = 0; ucTimer < ( uint8_t ) configTIMER_QUEUE_LENGTH; ucTimer++ )
	{
		/* The timer has not been stopped yet! */
		if( xTimerIsTimerActive( xAutoReloadTimers[ ucTimer ] ) == pdFALSE )
		{
			xTestStatus = pdFAIL;
			configASSERT( xTestStatus );
		}

		/* Now stop the timer.  This will appear to happen immediately to
		this task because this task is running at a priority below the
		timer service task. */
		xTimerStop( xAutoReloadTimers[ ucTimer ], tmrdemoDONT_BLOCK );

		/* The timer should now be inactive. */
		if( xTimerIsTimerActive( xAutoReloadTimers[ ucTimer ] ) != pdFALSE )
		{
			xTestStatus = pdFAIL;
			configASSERT( xTestStatus );
		}
	}

	taskENTER_CRITICAL();
	{
		/* The timer in array position configTIMER_QUEUE_LENGTH should not
		be active.  The critical section is used to ensure the timer does
		not call its callback between the next line running and the array
		being cleared back to zero, as that would mask an error condition. */
		if( ucAutoReloadTimerCounters[ configTIMER_QUEUE_LENGTH ] != ( uint8_t ) 0 )
		{
			xTestStatus = pdFAIL;
			configASSERT( xTestStatus );
		}

		/* Clear the timer callback count. */
		memset( ( void * ) ucAutoReloadTimerCounters, 0, sizeof( ucAutoReloadTimerCounters ) );
	}
	taskEXIT_CRITICAL();

	/* The timers are now all inactive, so this time, after delaying, none
	of the callback counters should have incremented. */
	vTaskDelay( ( ( TickType_t ) configTIMER_QUEUE_LENGTH ) * xBasePeriod );
	for( ucTimer = 0; ucTimer < ( uint8_t ) configTIMER_QUEUE_LENGTH; ucTimer++ )
	{
		if( ucAutoReloadTimerCounters[ ucTimer ] != ( uint8_t ) 0 )
		{
			xTestStatus = pdFAIL;
			configASSERT( xTestStatus );
		}
	}

	if( xTestStatus == pdPASS )
	{
		/* No errors have been reported so increment the loop counter so
		the check task knows this task is still running. */
		ulLoopCounter++;
	}
}
/*-----------------------------------------------------------*/

static void prvTest5_CheckBasicOneShotTimerBehaviour( void )
{
	/* Check the one shot timer only calls its callback once after it has been
	started, and that it reports its state correctly. */

	/* The one shot timer should not be active yet. */
	if( xTimerIsTimerActive( xOneShotTimer ) != pdFALSE )
	{
		xTestStatus = pdFAIL;
		configASSERT( xTestStatus );
	}

	if( ucOneShotTimerCounter != ( uint8_t ) 0 )
	{
		xTestStatus = pdFAIL;
		configASSERT( xTestStatus );
	}

	/* Start the one shot timer and check that it reports its state correctly. */
	xTimerStart( xOneShotTimer, tmrdemoDONT_BLOCK );
	if( xTimerIsTimerActive( xOneShotTimer ) == pdFALSE )
	{
		xTestStatus = pdFAIL;
		configASSERT( xTestStatus );
	}

	/* Delay for three times as long as the one shot timer period, then check
	to ensure it has only called its callback once, and is now not in the
	active state. */
	vTaskDelay( tmrdemoONE_SHOT_TIMER_PERIOD * ( TickType_t ) 3 );

	if( xTimerIsTimerActive( xOneShotTimer ) != pdFALSE )
	{
		xTestStatus = pdFAIL;
		configASSERT( xTestStatus );
	}

	if( ucOneShotTimerCounter != ( uint8_t ) 1 )
	{
		xTestStatus = pdFAIL;
		configASSERT( xTestStatus );
	}
	else
	{
		/* Reset the one shot timer callback count. */
		ucOneShotTimerCounter = ( uint8_t ) 0;
	}

	if( xTestStatus == pdPASS )
	{
		/* No errors have been reported so increment the loop counter so the
		check task knows this task is still running. */
		ulLoopCounter++;
	}
}
/*-----------------------------------------------------------*/

static void prvTest6_CheckAutoReloadResetBehaviour( void )
{
uint8_t ucTimer;

	/* Check timer reset behaviour. */

	/* Restart the one shot timer and check it reports its status correctly. */
	xTimerStart( xOneShotTimer, tmrdemoDONT_BLOCK );
	if( xTimerIsTimerActive( xOneShotTimer ) == pdFALSE )
	{
		xTestStatus = pdFAIL;
		configASSERT( xTestStatus );
	}

	/* Restart one of the auto reload timers and check that it reports its
	status correctly. */
	xTimerStart( xAutoReloadTimers[ configTIMER_QUEUE_LENGTH - 1 ], tmrdemoDONT_BLOCK );
	if( xTimerIsTimerActive( xAutoReloadTimers[ configTIMER_QUEUE_LENGTH - 1 ] ) == pdFALSE )
	{
		xTestStatus = pdFAIL;
		configASSERT( xTestStatus );
	}

	for( ucTimer = 0; ucTimer < trmdemoNUM_TIMER_RESETS; ucTimer++ )
	{
		/* Delay for half as long as the one shot timer period, then reset it.
		It should never expire while this is done, so its callback count should
		never increment. */
		vTaskDelay( tmrdemoONE_SHOT_TIMER_PERIOD / 2 );

		/* Check both running timers are still active, but have not called their
		callback functions. */
		if( xTimerIsTimerActive( xOneShotTimer ) == pdFALSE )
		{
			xTestStatus = pdFAIL;
			configASSERT( xTestStatus );
		}

		if( ucOneShotTimerCounter != ( uint8_t ) 0 )
		{
			xTestStatus = pdFAIL;
			configASSERT( xTestStatus );
		}

		if( xTimerIsTimerActive( xAutoReloadTimers[ configTIMER_QUEUE_LENGTH - 1 ] ) == pdFALSE )
		{
			xTestStatus = pdFAIL;
			configASSERT( xTestStatus );
		}

		if( ucAutoReloadTimerCounters[ configTIMER_QUEUE_LENGTH - 1 ] != ( uint8_t ) 0 )
		{
			xTestStatus = pdFAIL;
			configASSERT( xTestStatus );
		}

		/* Reset both running timers. */
		xTimerReset( xOneShotTimer, tmrdemoDONT_BLOCK );
		xTimerReset( xAutoReloadTimers[ configTIMER_QUEUE_LENGTH - 1 ], tmrdemoDONT_BLOCK );

		if( xTestStatus == pdPASS )
		{
			/* No errors have been reported so increment the loop counter so
			the check task knows this task is still running. */
			ulLoopCounter++;
		}
	}

	/* Finally delay long enough for both running timers to expire. */
	vTaskDelay( ( ( TickType_t ) configTIMER_QUEUE_LENGTH ) * xBasePeriod );

	/* The timers were not reset during the above delay period so should now
	both have called their callback functions. */
	if( ucOneShotTimerCounter != ( uint8_t ) 1 )
	{
		xTestStatus = pdFAIL;
		configASSERT( xTestStatus );
	}

	if( ucAutoReloadTimerCounters[ configTIMER_QUEUE_LENGTH - 1 ] == 0 )
	{
		xTestStatus = pdFAIL;
		configASSERT( xTestStatus );
	}

	/* The one shot timer should no longer be active, while the auto reload
	timer should still be active. */
	if( xTimerIsTimerActive( xAutoReloadTimers[ configTIMER_QUEUE_LENGTH - 1 ] ) == pdFALSE )
	{
		xTestStatus = pdFAIL;
		configASSERT( xTestStatus );
	}

	if( xTimerIsTimerActive( xOneShotTimer ) == pdTRUE )
	{
		xTestStatus = pdFAIL;
		configASSERT( xTestStatus );
	}

	/* Stop the auto reload timer again. */
	xTimerStop( xAutoReloadTimers[ configTIMER_QUEUE_LENGTH - 1 ], tmrdemoDONT_BLOCK );

	if( xTimerIsTimerActive( xAutoReloadTimers[ configTIMER_QUEUE_LENGTH - 1 ] ) != pdFALSE )
	{
		xTestStatus = pdFAIL;
		configASSERT( xTestStatus );
	}

	/* Clear the timer callback counts, ready for another iteration of these
	tests. */
	ucAutoReloadTimerCounters[ configTIMER_QUEUE_LENGTH - 1 ] = ( uint8_t ) 0;
	ucOneShotTimerCounter = ( uint8_t ) 0;

	if( xTestStatus == pdPASS )
	{
		/* No errors have been reported so increment the loop counter so the check
		task knows this task is still running. */
		ulLoopCounter++;
	}
}
/*-----------------------------------------------------------*/

static void prvResetStartConditionsForNextIteration( void )
{
uint8_t ucTimer;

	/* Start the timers again to start all the tests over again. */

	/* Start the timers again. */
	for( ucTimer = 0; ucTimer < ( uint8_t ) configTIMER_QUEUE_LENGTH; ucTimer++ )
	{
		/* The timer has not been started yet! */
		if( xTimerIsTimerActive( xAutoReloadTimers[ ucTimer ] ) != pdFALSE )
		{
			xTestStatus = pdFAIL;
			configASSERT( xTestStatus );
		}

		/* Now start the timer.  This will appear to happen immediately to
		this task because this task is running at a priority below the timer
		service task. */
		xTimerStart( xAutoReloadTimers[ ucTimer ], tmrdemoDONT_BLOCK );

		/* The timer should now be active. */
		if( xTimerIsTimerActive( xAutoReloadTimers[ ucTimer ] ) == pdFALSE )
		{
			xTestStatus = pdFAIL;
			configASSERT( xTestStatus );
		}
	}

	if( xTestStatus == pdPASS )
	{
		/* No errors have been reported so increment the loop counter so the
		check task knows this task is still running. */
		ulLoopCounter++;
	}
}
/*-----------------------------------------------------------*/

void vTimerPeriodicISRTests( void )
{
static TickType_t uxTick = ( TickType_t ) -1;

#if( configTIMER_TASK_PRIORITY != ( configMAX_PRIORITIES - 1 ) )
	/* The timer service task is not the highest priority task, so it cannot
	be assumed that timings will be exact.  Timers should never call their
	callback before their expiry time, but a margin is permissible for calling
	their callback after their expiry time.  If exact timing is required then
	configTIMER_TASK_PRIORITY must be set to ensure the timer service task
	is the highest priority task in the system.

	This function is called from the tick hook.  The tick hook is called
	even when the scheduler is suspended.  Therefore it is possible that the
	uxTick count maintained in this function is temporarily ahead of the tick
	count maintained by the kernel.  When this is the case a message posted from
	this function will assume a time stamp in advance of the real time stamp,
	which can result in a timer being processed before this function expects it
	to.  For example, if the kernel's tick count was 100, and uxTick was 102,
	then this function will not expect the timer to have expired until the
	kernel's tick count is (102 + xBasePeriod), whereas in reality the timer
	will expire when the kernel's tick count is (100 + xBasePeriod).  For this
	reason xMargin is used as an allowable margin for premature timer expiries
	as well as late timer expiries. */
	#ifdef _WINDOWS_
		/* Windows is not real real time. */
		const TickType_t xMargin = 20;
	#else
		const TickType_t xMargin = 6;
	#endif /* _WINDOWS_ */
#else
	#ifdef _WINDOWS_
		/* Windows is not real real time. */
		const TickType_t xMargin = 20;
	#else
		const TickType_t xMargin = 4;
	#endif /* _WINDOWS_ */
#endif


	uxTick++;

	if( uxTick == 0 )
	{
		/* The timers will have been created, but not started.  Start them now
		by setting their period. */
		ucISRAutoReloadTimerCounter = 0;
		ucISROneShotTimerCounter = 0;

		/* It is possible that the timer task has not yet made room in the
		timer queue.  If the timers cannot be started then reset uxTick so
		another attempt is made later. */
		uxTick = ( TickType_t ) -1;

		/* Try starting first timer. */
		if( xTimerChangePeriodFromISR( xISRAutoReloadTimer, xBasePeriod, NULL ) == pdPASS )
		{
			/* First timer was started, try starting the second timer. */
			if( xTimerChangePeriodFromISR( xISROneShotTimer, xBasePeriod, NULL ) == pdPASS )
			{
				/* Both timers were started, so set the uxTick back to its
				proper value. */
				uxTick = 0;
			}
			else
			{
				/* Second timer could not be started, so stop the first one
				again. */
				xTimerStopFromISR( xISRAutoReloadTimer, NULL );
			}
		}
	}
	else if( uxTick == ( xBasePeriod - xMargin ) )
	{
		/* Neither timer should have expired yet. */
		if( ( ucISRAutoReloadTimerCounter != 0 ) || ( ucISROneShotTimerCounter != 0 ) )
		{
			xTestStatus = pdFAIL;
			configASSERT( xTestStatus );
		}
	}
	else if( uxTick == ( xBasePeriod + xMargin ) )
	{
		/* Both timers should now have expired once.  The auto reload timer will
		still be active, but the one shot timer should now have stopped. */
		if( ( ucISRAutoReloadTimerCounter != 1 ) || ( ucISROneShotTimerCounter != 1 ) )
		{
			xTestStatus = pdFAIL;
			configASSERT( xTestStatus );
		}
	}
	else if( uxTick == ( ( 2 * xBasePeriod ) - xMargin ) )
	{
		/* The auto reload timer will still be active, but the one shot timer
		should now have stopped - however, at this time neither of the timers
		should have expired again since the last test. */
		if( ( ucISRAutoReloadTimerCounter != 1 ) || ( ucISROneShotTimerCounter != 1 ) )
		{
			xTestStatus = pdFAIL;
			configASSERT( xTestStatus );
		}
	}
	else if( uxTick == ( ( 2 * xBasePeriod ) + xMargin ) )
	{
		/* The auto reload timer will still be active, but the one shot timer
		should now have stopped.  At this time the auto reload timer should have
		expired again, but the one shot timer count should not have changed. */
		if( ucISRAutoReloadTimerCounter != 2 )
		{
			xTestStatus = pdFAIL;
			configASSERT( xTestStatus );
		}

		if( ucISROneShotTimerCounter != 1 )
		{
			xTestStatus = pdFAIL;
			configASSERT( xTestStatus );
		}
	}
	else if( uxTick == ( ( 2 * xBasePeriod ) + ( xBasePeriod >> ( TickType_t ) 2U ) ) )
	{
		/* The auto reload timer will still be active, but the one shot timer
		should now have stopped.  Again though, at this time, neither timer call
		back should have been called since the last test. */
		if( ucISRAutoReloadTimerCounter != 2 )
		{
			xTestStatus = pdFAIL;
			configASSERT( xTestStatus );
		}

		if( ucISROneShotTimerCounter != 1 )
		{
			xTestStatus = pdFAIL;
			configASSERT( xTestStatus );
		}
	}
	else if( uxTick == ( 3 * xBasePeriod ) )
	{
		/* Start the one shot timer again. */
		xTimerStartFromISR( xISROneShotTimer, NULL );
	}
	else if( uxTick == ( ( 3 * xBasePeriod ) + xMargin ) )
	{
		/* The auto reload timer and one shot timer will be active.  At
		this time the auto reload timer should have	expired again, but the one
		shot timer count should not have changed yet. */
		if( ucISRAutoReloadTimerCounter != 3 )
		{
			xTestStatus = pdFAIL;
			configASSERT( xTestStatus );
		}

		if( ucISROneShotTimerCounter != 1 )
		{
			xTestStatus = pdFAIL;
			configASSERT( xTestStatus );
		}

		/* Now stop the auto reload timer.  The one shot timer was started
		a few ticks ago. */
		xTimerStopFromISR( xISRAutoReloadTimer, NULL );
	}
	else if( uxTick == ( 4 * ( xBasePeriod - xMargin ) ) )
	{
		/* The auto reload timer is now stopped, and the one shot timer is
		active, but at this time neither timer should have expired since the
		last test. */
		if( ucISRAutoReloadTimerCounter != 3 )
		{
			xTestStatus = pdFAIL;
			configASSERT( xTestStatus );
		}

		if( ucISROneShotTimerCounter != 1 )
		{
			xTestStatus = pdFAIL;
			configASSERT( xTestStatus );
		}
	}
	else if( uxTick == ( ( 4 * xBasePeriod ) + xMargin ) )
	{
		/* The auto reload timer is now stopped, and the one shot timer is
		active.  The one shot timer should have expired again, but the auto
		reload timer should not have executed its callback. */
		if( ucISRAutoReloadTimerCounter != 3 )
		{
			xTestStatus = pdFAIL;
			configASSERT( xTestStatus );
		}

		if( ucISROneShotTimerCounter != 2 )
		{
			xTestStatus = pdFAIL;
			configASSERT( xTestStatus );
		}
	}
	else if( uxTick == ( 8 * xBasePeriod ) )
	{
		/* The auto reload timer is now stopped, and the one shot timer has
		already expired and then stopped itself.  Both callback counters should
		not have incremented since the last test. */
		if( ucISRAutoReloadTimerCounter != 3 )
		{
			xTestStatus = pdFAIL;
			configASSERT( xTestStatus );
		}

		if( ucISROneShotTimerCounter != 2 )
		{
			xTestStatus = pdFAIL;
			configASSERT( xTestStatus );
		}

		/* Now reset the one shot timer. */
		xTimerResetFromISR( xISROneShotTimer, NULL );
	}
	else if( uxTick == ( ( 9 * xBasePeriod ) - xMargin ) )
	{
		/* Only the one shot timer should be running, but it should not have
		expired since the last test.  Check the callback counters have not
		incremented, then reset the one shot timer again. */
		if( ucISRAutoReloadTimerCounter != 3 )
		{
			xTestStatus = pdFAIL;
			configASSERT( xTestStatus );
		}

		if( ucISROneShotTimerCounter != 2 )
		{
			xTestStatus = pdFAIL;
			configASSERT( xTestStatus );
		}

		xTimerResetFromISR( xISROneShotTimer, NULL );
	}
	else if( uxTick == ( ( 10 * xBasePeriod ) - ( 2 * xMargin ) ) )
	{
		/* Only the one shot timer should be running, but it should not have
		expired since the last test.  Check the callback counters have not
		incremented, then reset the one shot timer again. */
		if( ucISRAutoReloadTimerCounter != 3 )
		{
			xTestStatus = pdFAIL;
			configASSERT( xTestStatus );
		}

		if( ucISROneShotTimerCounter != 2 )
		{
			xTestStatus = pdFAIL;
			configASSERT( xTestStatus );
		}

		xTimerResetFromISR( xISROneShotTimer, NULL );
	}
	else if( uxTick == ( ( 11 * xBasePeriod ) - ( 3 * xMargin ) ) )
	{
		/* Only the one shot timer should be running, but it should not have
		expired since the last test.  Check the callback counters have not
		incremented, then reset the one shot timer once again. */
		if( ucISRAutoReloadTimerCounter != 3 )
		{
			xTestStatus = pdFAIL;
			configASSERT( xTestStatus );
		}

		if( ucISROneShotTimerCounter != 2 )
		{
			xTestStatus = pdFAIL;
			configASSERT( xTestStatus );
		}

		xTimerResetFromISR( xISROneShotTimer, NULL );
	}
	else if( uxTick == ( ( 12 * xBasePeriod ) - ( 2 * xMargin ) ) )
	{
		/* Only the one shot timer should have been running and this time it
		should have	expired.  Check its callback count has been incremented.
		The auto reload	timer is still not running so should still have the same
		count value.  This time the one shot timer is not reset so should not
		restart from its expiry period again. */
		if( ucISRAutoReloadTimerCounter != 3 )
		{
			xTestStatus = pdFAIL;
			configASSERT( xTestStatus );
		}

		if( ucISROneShotTimerCounter != 3 )
		{
			xTestStatus = pdFAIL;
			configASSERT( xTestStatus );
		}
	}
	else if( uxTick == ( 15 * xBasePeriod ) )
	{
		/* Neither timer should be running now.  Check neither callback count
		has incremented, then go back to the start to run these tests all
		over again. */
		if( ucISRAutoReloadTimerCounter != 3 )
		{
			xTestStatus = pdFAIL;
			configASSERT( xTestStatus );
		}

		if( ucISROneShotTimerCounter != 3 )
		{
			xTestStatus = pdFAIL;
			configASSERT( xTestStatus );
		}

		uxTick = ( TickType_t ) -1;
	}
}
/*-----------------------------------------------------------*/

/*** Timer callback functions are defined below here. ***/

static void prvAutoReloadTimerCallback( TimerHandle_t pxExpiredTimer )
{
size_t uxTimerID;

	uxTimerID = ( size_t ) pvTimerGetTimerID( pxExpiredTimer );
	if( uxTimerID <= ( configTIMER_QUEUE_LENGTH + 1 ) )
	{
		( ucAutoReloadTimerCounters[ uxTimerID ] )++;
	}
	else
	{
		/* The timer ID appears to be unexpected (invalid). */
		xTestStatus = pdFAIL;
		configASSERT( xTestStatus );
	}
}
/*-----------------------------------------------------------*/

static void prvOneShotTimerCallback( TimerHandle_t pxExpiredTimer )
{
/* A count is kept of the number of times this callback function is executed.
The count is stored as the timer's ID.  This is only done to test the
vTimerSetTimerID() function. */
static size_t uxCallCount = 0;
size_t uxLastCallCount;

	/* Obtain the timer's ID, which should be a count of the number of times
	this callback function has been executed. */
	uxLastCallCount = ( size_t ) pvTimerGetTimerID( pxExpiredTimer );
	configASSERT( uxLastCallCount == uxCallCount );

	/* Increment the call count, then save it back as the timer's ID.  This is
	only done to test the vTimerSetTimerID() API function. */
	uxLastCallCount++;
	vTimerSetTimerID( pxExpiredTimer, ( void * ) uxLastCallCount );
	uxCallCount++;

	ucOneShotTimerCounter++;
}
/*-----------------------------------------------------------*/

static void prvISRAutoReloadTimerCallback( TimerHandle_t pxExpiredTimer )
{
	/* The parameter is not used in this case as only one timer uses this
	callback function. */
	( void ) pxExpiredTimer;

	ucISRAutoReloadTimerCounter++;
}
/*-----------------------------------------------------------*/

static void prvISROneShotTimerCallback( TimerHandle_t pxExpiredTimer )
{
	/* The parameter is not used in this case as only one timer uses this
	callback function. */
	( void ) pxExpiredTimer;

	ucISROneShotTimerCounter++;
}
/*-----------------------------------------------------------*/




