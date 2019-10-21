/*
 * FreeRTOS Kernel V10.2.1
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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


/*
 * Tests the behaviour of direct task notifications.
 */

/* Standard includes. */
#include <limits.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "timers.h"

/* Demo program include files. */
#include "TaskNotify.h"

/* Allow parameters to be overridden on a demo by demo basis. */
#ifndef notifyNOTIFIED_TASK_STACK_SIZE
	#define notifyNOTIFIED_TASK_STACK_SIZE configMINIMAL_STACK_SIZE
#endif

#define notifyTASK_PRIORITY		( tskIDLE_PRIORITY )
#define notifyUINT32_MAX	( ( uint32_t ) 0xffffffff )
#define notifySUSPENDED_TEST_TIMER_PERIOD pdMS_TO_TICKS( 50 )

/*-----------------------------------------------------------*/

/*
 * Implementation of the task that gets notified.
 */
static void prvNotifiedTask( void *pvParameters );

/*
 * Performs a few initial tests that can be done prior to creating the second
 * task.
 */
static void prvSingleTaskTests( void );

/*
 * Software timer callback function from which xTaskNotify() is called.
 */
static void prvNotifyingTimer( TimerHandle_t xTimer );

/*
 * Utility function to create pseudo random numbers.
 */
static UBaseType_t prvRand( void );

/*
 * Callback for a timer that is used during preliminary testing.  The timer
 * tests the behaviour when 1: a task waiting for a notification is suspended
 * and then resumed without ever receiving a notification, and 2: when a task
 * waiting for a notification receives a notification while it is suspended.
 */
static void prvSuspendedTaskTimerTestCallback( TimerHandle_t xExpiredTimer );

/*-----------------------------------------------------------*/

/* Used to latch errors during the test's execution. */
static BaseType_t xErrorStatus = pdPASS;

/* Used to ensure the task has not stalled. */
static volatile uint32_t ulNotifyCycleCount = 0;

/* The handle of the task that receives the notifications. */
static TaskHandle_t xTaskToNotify = NULL;

/* Used to count the notifications sent to the task from a software timer and
the number of notifications received by the task from the software timer.  The
two should stay synchronised. */
static uint32_t ulTimerNotificationsReceived = 0UL, ulTimerNotificationsSent = 0UL;

/* The timer used to notify the task. */
static TimerHandle_t xTimer = NULL;

/* Used by the pseudo random number generating function. */
static size_t uxNextRand = 0;

/*-----------------------------------------------------------*/

void vStartTaskNotifyTask( void  )
{
	/* Create the task that performs some tests by itself, then loops around
	being notified by both a software timer and an interrupt. */
	xTaskCreate( prvNotifiedTask, /* Function that implements the task. */
				 "Notified", /* Text name for the task - for debugging only - not used by the kernel. */
				 notifyNOTIFIED_TASK_STACK_SIZE, /* Task's stack size in words, not bytes!. */
				 NULL, /* Task parameter, not used in this case. */
				 notifyTASK_PRIORITY, /* Task priority, 0 is the lowest. */
				 &xTaskToNotify ); /* Used to pass a handle to the task out is needed, otherwise set to NULL. */

	/* Pseudo seed the random number generator. */
	uxNextRand = ( size_t ) prvRand;
}
/*-----------------------------------------------------------*/

static void prvSingleTaskTests( void )
{
const TickType_t xTicksToWait = pdMS_TO_TICKS( 100UL );
BaseType_t xReturned;
uint32_t ulNotifiedValue, ulLoop, ulNotifyingValue, ulPreviousValue, ulExpectedValue;
TickType_t xTimeOnEntering;
const uint32_t ulFirstNotifiedConst = 100001UL, ulSecondNotifiedValueConst = 5555UL, ulMaxLoops = 5UL;
const uint32_t ulBit0 = 0x01UL, ulBit1 = 0x02UL;
TimerHandle_t xSingleTaskTimer;


	/* ------------------------------------------------------------------------
	Check blocking when there are no notifications. */
	xTimeOnEntering = xTaskGetTickCount();
	xReturned = xTaskNotifyWait( notifyUINT32_MAX, 0, &ulNotifiedValue, xTicksToWait );
	( void ) xReturned; /* In case configASSERT() is not defined. */

	/* Should have blocked for the entire block time. */
	if( ( xTaskGetTickCount() - xTimeOnEntering ) < xTicksToWait )
	{
		xErrorStatus = pdFAIL;
	}
	configASSERT( xReturned == pdFAIL );
	configASSERT( ulNotifiedValue == 0UL );
	( void ) xReturned; /* In case configASSERT() is not defined. */
	( void ) ulNotifiedValue;




	/* ------------------------------------------------------------------------
	Check no blocking when notifications are pending.  First notify itself -
	this would not be a normal thing to do and is done here for test purposes
	only. */
	xReturned = xTaskNotifyAndQuery( xTaskToNotify, ulFirstNotifiedConst, eSetValueWithoutOverwrite, &ulPreviousValue );

	/* Even through the 'without overwrite' action was used the update should
	have been successful. */
	configASSERT( xReturned == pdPASS );
	( void ) xReturned; /* In case configASSERT() is not defined. */

	/* No bits should have been pending previously. */
	configASSERT( ulPreviousValue == 0 );
	( void ) ulPreviousValue;

	/* The task should now have a notification pending, and so not time out. */
	xTimeOnEntering = xTaskGetTickCount();
	xReturned = xTaskNotifyWait( notifyUINT32_MAX, 0, &ulNotifiedValue, xTicksToWait );

	if( ( xTaskGetTickCount() - xTimeOnEntering ) >= xTicksToWait )
	{
		xErrorStatus = pdFAIL;
	}

	/* The task should have been notified, and the notified value should
	be equal to ulFirstNotifiedConst. */
	configASSERT( xReturned == pdPASS );
	configASSERT( ulNotifiedValue == ulFirstNotifiedConst );
	( void ) xReturned; /* In case configASSERT() is not defined. */
	( void ) ulNotifiedValue;

	/* Incremented to show the task is still running. */
	ulNotifyCycleCount++;





	/*-------------------------------------------------------------------------
	Check the non-overwriting functionality.  The notification is done twice
	using two different notification values.  The action says don't overwrite so
	only the first notification should pass and the value read back should also
	be that used with the first notification. */
	xReturned = xTaskNotify( xTaskToNotify, ulFirstNotifiedConst, eSetValueWithoutOverwrite );
	configASSERT( xReturned == pdPASS );
	( void ) xReturned; /* In case configASSERT() is not defined. */

	xReturned = xTaskNotify( xTaskToNotify, ulSecondNotifiedValueConst, eSetValueWithoutOverwrite );
	configASSERT( xReturned == pdFAIL );
	( void ) xReturned; /* In case configASSERT() is not defined. */

	/* Waiting for the notification should now return immediately so a block
	time of zero is used. */
	xReturned = xTaskNotifyWait( notifyUINT32_MAX, 0, &ulNotifiedValue, 0 );

	configASSERT( xReturned == pdPASS );
	configASSERT( ulNotifiedValue == ulFirstNotifiedConst );
	( void ) xReturned; /* In case configASSERT() is not defined. */
	( void ) ulNotifiedValue;





	/*-------------------------------------------------------------------------
	Do the same again, only this time use the overwriting version.  This time
	both notifications should pass, and the value written the second time should
	overwrite the value written the first time, and so be the value that is read
	back. */
	xReturned = xTaskNotify( xTaskToNotify, ulFirstNotifiedConst, eSetValueWithOverwrite );
	configASSERT( xReturned == pdPASS );
	( void ) xReturned; /* In case configASSERT() is not defined. */
	xReturned = xTaskNotify( xTaskToNotify, ulSecondNotifiedValueConst, eSetValueWithOverwrite );
	configASSERT( xReturned == pdPASS );
	( void ) xReturned; /* In case configASSERT() is not defined. */
	xReturned = xTaskNotifyWait( notifyUINT32_MAX, 0, &ulNotifiedValue, 0 );
	configASSERT( xReturned == pdPASS );
	( void ) xReturned; /* In case configASSERT() is not defined. */
	configASSERT( ulNotifiedValue == ulSecondNotifiedValueConst );
	( void ) ulNotifiedValue;




	/*-------------------------------------------------------------------------
	Check notifications with no action pass without updating the value.  Even
	though ulFirstNotifiedConst is used as the value the value read back should
	remain at ulSecondNotifiedConst. */
	xReturned = xTaskNotify( xTaskToNotify, ulFirstNotifiedConst, eNoAction );
	configASSERT( xReturned == pdPASS );
	( void ) xReturned; /* In case configASSERT() is not defined. */
	xReturned = xTaskNotifyWait( notifyUINT32_MAX, 0, &ulNotifiedValue, 0 );
	configASSERT( ulNotifiedValue == ulSecondNotifiedValueConst );
	( void ) ulNotifiedValue; /* In case configASSERT() is not defined. */




	/*-------------------------------------------------------------------------
	Check incrementing values.  Send ulMaxLoop increment notifications, then
	ensure the received value is as expected - which should be
	ulSecondNotificationValueConst plus how ever many times to loop iterated. */
	for( ulLoop = 0; ulLoop < ulMaxLoops; ulLoop++ )
	{
		xReturned = xTaskNotify( xTaskToNotify, 0, eIncrement );
		configASSERT( xReturned == pdPASS );
		( void ) xReturned; /* In case configASSERT() is not defined. */
	}

	xReturned = xTaskNotifyWait( notifyUINT32_MAX, 0, &ulNotifiedValue, 0 );
	configASSERT( xReturned == pdPASS );
	configASSERT( ulNotifiedValue == ( ulSecondNotifiedValueConst + ulMaxLoops ) );
	( void ) xReturned; /* In case configASSERT() is not defined. */
	( void ) ulNotifiedValue;

	/* Should not be any notifications pending now. */
	xReturned = xTaskNotifyWait( 0, 0, &ulNotifiedValue, 0 );
	configASSERT( xReturned == pdFAIL );
	( void ) xReturned; /* In case configASSERT() is not defined. */
	( void ) ulNotifiedValue;




	/*-------------------------------------------------------------------------
	Check all bits can be set by notifying the task with one additional bit	set
	on each notification, and exiting the loop when all the bits are found to be
	set.  As there are 32-bits the loop should execute 32 times before all the
	bits are found to be set. */
	ulNotifyingValue = 0x01;
	ulLoop = 0;

	/* Start with all bits clear. */
	xTaskNotifyWait( notifyUINT32_MAX, 0, &ulNotifiedValue, 0 );

	do
	{
		/* Set the next bit in the task's notified value. */
		xTaskNotify( xTaskToNotify, ulNotifyingValue, eSetBits );

		/* Wait for the notified value - which of course will already be
		available.  Don't clear the bits on entry or exit as this loop is exited
		when all the bits are set. */
		xReturned = xTaskNotifyWait( 0, 0, &ulNotifiedValue, 0 );
		configASSERT( xReturned == pdPASS );
		( void ) xReturned; /* In case configASSERT() is not defined. */

		ulLoop++;

		/* Use the next bit on the next iteration around this loop. */
		ulNotifyingValue <<= 1UL;

	} while ( ulNotifiedValue != notifyUINT32_MAX );

	/* As a 32-bit value was used the loop should have executed 32 times before
	all the bits were set. */
	configASSERT( ulLoop == 32 );




	/*-------------------------------------------------------------------------
	Check bits are cleared on entry but not on exit when a notification fails
	to arrive before timing out - both with and without a timeout value.  Wait
	for the notification again - but this time it is not given by anything and
	should return pdFAIL.  The parameters are set to clear bit zero on entry and
	bit one on exit.  As no notification was received only the bit cleared on
	entry should actually get cleared. */
	xReturned = xTaskNotifyWait( ulBit0, ulBit1, &ulNotifiedValue, xTicksToWait );
	configASSERT( xReturned == pdFAIL );
	( void ) xReturned; /* In case configASSERT() is not defined. */

	/* Notify the task with no action so as not to update the bits even though
	notifyUINT32_MAX is used as the notification value. */
	xTaskNotify( xTaskToNotify, notifyUINT32_MAX, eNoAction );

	/* Reading back the value should should find bit 0 is clear, as this was
	cleared on entry, but bit 1 is not clear as it will not have been cleared on
	exit as no notification was received. */
	xReturned = xTaskNotifyWait( 0x00UL, 0x00UL, &ulNotifiedValue, 0 );
	configASSERT( xReturned == pdPASS );
	configASSERT( ulNotifiedValue == ( notifyUINT32_MAX & ~ulBit0 ) );
	( void ) xReturned; /* In case configASSERT() is not defined. */





	/*-------------------------------------------------------------------------
	Now try clearing the bit on exit.  For that to happen a notification must be
	received, so the task is notified first. */
	xTaskNotify( xTaskToNotify, 0, eNoAction );
	xTaskNotifyWait( 0x00, ulBit1, &ulNotifiedValue, 0 );

	/* However as the bit is cleared on exit, after the returned notification
	value is set, the returned notification value should not have the bit
	cleared... */
	configASSERT( ulNotifiedValue == ( notifyUINT32_MAX & ~ulBit0 ) );

	/* ...but reading the value back again should find that the bit was indeed
	cleared internally.  The returned value should be pdFAIL however as nothing
	has notified the task in the mean time. */
	xReturned = xTaskNotifyWait( 0x00, 0x00, &ulNotifiedValue, 0 );
	configASSERT( xReturned == pdFAIL );
	configASSERT( ulNotifiedValue == ( notifyUINT32_MAX & ~( ulBit0 | ulBit1 ) ) );
	( void ) xReturned; /* In case configASSERT() is not defined. */




	/*-------------------------------------------------------------------------
	Now try querying the previous value while notifying a task. */
	xTaskNotifyAndQuery( xTaskToNotify, 0x00, eSetBits, &ulPreviousValue );
	configASSERT( ulNotifiedValue == ( notifyUINT32_MAX & ~( ulBit0 | ulBit1 ) ) );

	/* Clear all bits. */
	xTaskNotifyWait( 0x00, notifyUINT32_MAX, &ulNotifiedValue, 0 );
	xTaskNotifyAndQuery( xTaskToNotify, 0x00, eSetBits, &ulPreviousValue );
	configASSERT( ulPreviousValue == 0 );

	ulExpectedValue = 0;
	for( ulLoop = 0x01; ulLoop < 0x80UL; ulLoop <<= 1UL )
	{
		/* Set the next bit up, and expect to receive the last bits set (so
		the previous value will not yet have the bit being set this time
		around). */
		xTaskNotifyAndQuery( xTaskToNotify, ulLoop, eSetBits, &ulPreviousValue );
		configASSERT( ulExpectedValue == ulPreviousValue );
		ulExpectedValue |= ulLoop;
	}



	/* ------------------------------------------------------------------------
	Clear the previous notifications. */
	xTaskNotifyWait( notifyUINT32_MAX, 0, &ulNotifiedValue, 0 );

	/* The task should not have any notifications pending, so an attempt to clear
	the notification state should fail. */
	configASSERT( xTaskNotifyStateClear( NULL ) == pdFALSE );

	/* Get the task to notify itself.  This is not a normal thing to do, and is
	only done here for test purposes. */
	xTaskNotifyAndQuery( xTaskToNotify, ulFirstNotifiedConst, eSetValueWithoutOverwrite, &ulPreviousValue );

	/* Now the notification state should be eNotified, so it should now be
	possible to clear the notification state. */
	configASSERT( xTaskNotifyStateClear( NULL ) == pdTRUE );
	configASSERT( xTaskNotifyStateClear( NULL ) == pdFALSE );



	/* ------------------------------------------------------------------------
	Create a timer that will try notifying this task while it is suspended. */
	xSingleTaskTimer = xTimerCreate( "SingleNotify", notifySUSPENDED_TEST_TIMER_PERIOD, pdFALSE, NULL, prvSuspendedTaskTimerTestCallback );
	configASSERT( xSingleTaskTimer );

	/* Incremented to show the task is still running. */
	ulNotifyCycleCount++;

	/* Ensure no notifications are pending. */
	xTaskNotifyWait( notifyUINT32_MAX, 0, NULL, 0 );

	/* Raise the task's priority so it can suspend itself before the timer
	expires. */
	vTaskPrioritySet( NULL, configMAX_PRIORITIES - 1 );

	/* Start the timer that will try notifying this task while it is
	suspended, then wait for a notification.  The first time the callback
	executes the timer will suspend the task, then resume the task, without
	ever sending a notification to the task. */
	ulNotifiedValue = 0;
	xTimerStart( xSingleTaskTimer, portMAX_DELAY );

	/* Check a notification is not received. */
	xReturned = xTaskNotifyWait( 0, 0, &ulNotifiedValue, portMAX_DELAY );
	configASSERT( xReturned == pdFALSE );
	configASSERT( ulNotifiedValue == 0 );
	( void ) xReturned; /* In case configASSERT() is not defined. */

	/* Incremented to show the task is still running. */
	ulNotifyCycleCount++;

	/* Start the timer that will try notifying this task while it is
	suspended, then wait for a notification.  The second time the callback
	executes the timer will suspend the task, notify the task, then resume the
	task (previously it was suspended and resumed without being notified). */
	xTimerStart( xSingleTaskTimer, portMAX_DELAY );

	/* Check a notification is received. */
	xReturned = xTaskNotifyWait( 0, 0, &ulNotifiedValue, portMAX_DELAY );
	configASSERT( xReturned == pdPASS );
	( void ) xReturned; /* In case configASSERT() is not defined. */
	configASSERT( ulNotifiedValue != 0 );

	/* Return the task to its proper priority and delete the timer as it is
	not used again. */
	vTaskPrioritySet( NULL, notifyTASK_PRIORITY );
	xTimerDelete( xSingleTaskTimer, portMAX_DELAY );

	/* Incremented to show the task is still running. */
	ulNotifyCycleCount++;

	/* Leave all bits cleared. */
	xTaskNotifyWait( notifyUINT32_MAX, 0, NULL, 0 );
}
/*-----------------------------------------------------------*/

static void prvSuspendedTaskTimerTestCallback( TimerHandle_t xExpiredTimer )
{
static uint32_t ulCallCount = 0;

	/* Remove compiler warnings about unused parameters. */
	( void ) xExpiredTimer;

	/* Callback for a timer that is used during preliminary testing.  The timer
	tests the behaviour when 1: a task waiting for a notification is suspended
	and then resumed without ever receiving a notification, and 2: when a task
	waiting for a notification receives a notification while it is suspended. */

	if( ulCallCount == 0 )
	{
		vTaskSuspend( xTaskToNotify );
		configASSERT( eTaskGetState( xTaskToNotify ) == eSuspended );
		vTaskResume( xTaskToNotify );
	}
	else
	{
		vTaskSuspend( xTaskToNotify );

		/* Sending a notification while the task is suspended should pass, but
		not cause the task to resume.  ulCallCount is just used as a convenient
		non-zero value. */
		xTaskNotify( xTaskToNotify, ulCallCount, eSetValueWithOverwrite );

		/* Make sure giving the notification didn't resume the task. */
		configASSERT( eTaskGetState( xTaskToNotify ) == eSuspended );

		vTaskResume( xTaskToNotify );
	}

	ulCallCount++;
}
/*-----------------------------------------------------------*/

static void prvNotifyingTimer( TimerHandle_t xNotUsed )
{
	( void ) xNotUsed;

	xTaskNotifyGive( xTaskToNotify );

	/* This value is also incremented from an interrupt. */
	taskENTER_CRITICAL();
	{
		ulTimerNotificationsSent++;
	}
	taskEXIT_CRITICAL();
}
/*-----------------------------------------------------------*/

static void prvNotifiedTask( void *pvParameters )
{
const TickType_t xMaxPeriod = pdMS_TO_TICKS( 90 ), xMinPeriod = pdMS_TO_TICKS( 10 ), xDontBlock = 0;
TickType_t xPeriod;
const uint32_t ulCyclesToRaisePriority = 50UL;

	/* Remove compiler warnings about unused parameters. */
	( void ) pvParameters;

	/* Run a few tests that can be done from a single task before entering the
	main loop. */
	prvSingleTaskTests();

	/* Create the software timer that is used to send notifications to this
	task.  Notifications are also received from an interrupt. */
	xTimer = xTimerCreate( "Notifier", xMaxPeriod, pdFALSE, NULL, prvNotifyingTimer );

	for( ;; )
	{
		/* Start the timer again with a different period.  Sometimes the period
		will be higher than the task's block time, sometimes it will be lower
		than the task's block time. */
		xPeriod = prvRand() % xMaxPeriod;
		if( xPeriod < xMinPeriod )
		{
			xPeriod = xMinPeriod;
		}

		/* Change the timer period and start the timer. */
		xTimerChangePeriod( xTimer, xPeriod, portMAX_DELAY );

		/* Block waiting for the notification again with a different period.
		Sometimes the period will be higher than the task's block time,
		sometimes it will be lower than the task's block time. */
		xPeriod = prvRand() % xMaxPeriod;
		if( xPeriod < xMinPeriod )
		{
			xPeriod = xMinPeriod;
		}

		/* Block to wait for a notification but without clearing the
		notification count, so only add one to the count of received
		notifications as any other notifications will remain pending. */
		if( ulTaskNotifyTake( pdFALSE, xPeriod ) != 0 )
		{
			ulTimerNotificationsReceived++;
		}


		/* Take a notification without clearing again, but this time without a
		block time specified. */
		if( ulTaskNotifyTake( pdFALSE, xDontBlock ) != 0 )
		{
			ulTimerNotificationsReceived++;
		}

		/* Wait for the next notification from the timer, clearing all
		notifications if one is received, so this time adding the total number
		of notifications that were pending as none will be left pending after
		the function call. */
		ulTimerNotificationsReceived += ulTaskNotifyTake( pdTRUE, xPeriod );

		/* Occasionally raise the priority of the task being notified to test
		the path where the task is notified from an ISR and becomes the highest
		priority ready state task, but the pxHigherPriorityTaskWoken parameter
		is NULL (which it is in the tick hook that sends notifications to this
		task). */
		if( ( ulNotifyCycleCount % ulCyclesToRaisePriority ) == 0 )
		{
			vTaskPrioritySet( xTaskToNotify, configMAX_PRIORITIES - 1 );

			/* Wait for the next notification again, clearing all notifications
			if one is received, but this time blocking indefinitely. */
			ulTimerNotificationsReceived += ulTaskNotifyTake( pdTRUE, portMAX_DELAY );

			/* Reset the priority. */
			vTaskPrioritySet( xTaskToNotify, notifyTASK_PRIORITY );
		}
		else
		{
			/* Wait for the next notification again, clearing all notifications
			if one is received, but this time blocking indefinitely. */
			ulTimerNotificationsReceived += ulTaskNotifyTake( pdTRUE, portMAX_DELAY );
		}

		/* Incremented to show the task is still running. */
		ulNotifyCycleCount++;
	}
}
/*-----------------------------------------------------------*/

void xNotifyTaskFromISR( void )
{
static BaseType_t xCallCount = 0, xAPIToUse = 0;
const BaseType_t xCallInterval = pdMS_TO_TICKS( 50 );
uint32_t ulPreviousValue;
const uint32_t ulUnexpectedValue = 0xff;

	/* Check the task notification demo tasks were actually created. */
	configASSERT( xTaskToNotify );

	/* The task performs some tests before starting the timer that gives the
	notification from this interrupt.  If the timer has not been created yet
	then the initial tests have not yet completed and the notification should
	not be sent. */
	if( xTimer != NULL )
	{
		xCallCount++;

		if( xCallCount >= xCallInterval )
		{
			/* It is time to 'give' the notification again. */
			xCallCount = 0;

			/* Test using both vTaskNotifyGiveFromISR(), xTaskNotifyFromISR()
			and xTaskNotifyAndQueryFromISR(). */
			switch( xAPIToUse )
			{
				case 0:	vTaskNotifyGiveFromISR( xTaskToNotify, NULL );
						xAPIToUse++;
						break;

				case 1:	xTaskNotifyFromISR( xTaskToNotify, 0, eIncrement, NULL );
						xAPIToUse++;
						break;

				case 2: ulPreviousValue = ulUnexpectedValue;
						xTaskNotifyAndQueryFromISR( xTaskToNotify, 0, eIncrement, &ulPreviousValue, NULL );
						configASSERT( ulPreviousValue != ulUnexpectedValue );
						xAPIToUse = 0;
						break;

				default:/* Should never get here!. */
						break;
			}

			ulTimerNotificationsSent++;
		}
	}
}
/*-----------------------------------------------------------*/

/* This is called to check the created tasks are still running and have not
detected any errors. */
BaseType_t xAreTaskNotificationTasksStillRunning( void )
{
static uint32_t ulLastNotifyCycleCount = 0;
const uint32_t ulMaxSendReceiveDeviation = 5UL;

	/* Check the cycle count is still incrementing to ensure the task is still
	actually running. */
	if( ulLastNotifyCycleCount == ulNotifyCycleCount )
	{
		xErrorStatus = pdFAIL;
	}
	else
	{
		ulLastNotifyCycleCount = ulNotifyCycleCount;
	}

	/* Check the count of 'takes' from the software timer is keeping track with
	the amount of 'gives'. */
	if( ulTimerNotificationsSent > ulTimerNotificationsReceived )
	{
		if( ( ulTimerNotificationsSent - ulTimerNotificationsReceived ) > ulMaxSendReceiveDeviation )
		{
			xErrorStatus = pdFAIL;
		}
	}

	return xErrorStatus;
}
/*-----------------------------------------------------------*/

static UBaseType_t prvRand( void )
{
const size_t uxMultiplier = ( size_t ) 0x015a4e35, uxIncrement = ( size_t ) 1;

	/* Utility function to generate a pseudo random number. */
	uxNextRand = ( uxMultiplier * uxNextRand ) + uxIncrement;
	return( ( uxNextRand >> 16 ) & ( ( size_t ) 0x7fff ) );
}
/*-----------------------------------------------------------*/
