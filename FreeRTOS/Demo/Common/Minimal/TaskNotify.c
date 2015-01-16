/*
    FreeRTOS V8.2.0 - Copyright (C) 2015 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

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

#define notifyTASK_PRIORITY		( tskIDLE_PRIORITY )

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
static uint32_t ulNextRand = 0;

/*-----------------------------------------------------------*/

void vStartTaskNotifyTask( void  )
{
	/* Create the task that performs some tests by itself, then loops around
	being notified by both a software timer and an interrupt. */
	xTaskCreate( prvNotifiedTask, "Notified", configMINIMAL_STACK_SIZE, NULL, notifyTASK_PRIORITY, &xTaskToNotify );

	/* Pseudo seed the random number generator. */
	ulNextRand = ( uint32_t ) prvRand;
}
/*-----------------------------------------------------------*/

static void prvSingleTaskTests( void )
{
const TickType_t xTicksToWait = pdMS_TO_TICKS( 100UL );
BaseType_t xReturned;
uint32_t ulNotifiedValue, ulLoop, ulNotifyingValue;
TickType_t xTimeOnEntering;
const uint32_t ulFirstNotifiedConst = 100001UL, ulSecondNotifiedValueConst = 5555UL, ulMaxLoops = 5UL;
const uint32_t ulBit0 = 0x01UL, ulBit1 = 0x02UL;

	/* -------------------------------------------------------------------------
	Check blocking when there are no notifications. */
	xTimeOnEntering = xTaskGetTickCount();
	xReturned = xTaskNotifyWait( ULONG_MAX, 0, &ulNotifiedValue, xTicksToWait );

	/* Should have blocked for the entire block time. */
	if( ( xTaskGetTickCount() - xTimeOnEntering ) < xTicksToWait )
	{
		xErrorStatus = pdFAIL;
	}
	configASSERT( xReturned == pdFAIL );
	configASSERT( ulNotifiedValue == 0UL );




	/* -------------------------------------------------------------------------
	Check no blocking when notifications are pending.  First notify itself -
	this would not be a normal thing to do and is done here for test purposes
	only. */
	xReturned = xTaskNotify( xTaskToNotify, ulFirstNotifiedConst, eSetValueWithoutOverwrite );

	/* Even through the 'without overwrite' action was used the update should
	have been successful. */
	configASSERT( xReturned == pdPASS );

	/* The task should now have a notification pending, and so not time out. */
	xTimeOnEntering = xTaskGetTickCount();
	xReturned = xTaskNotifyWait( ULONG_MAX, 0, &ulNotifiedValue, xTicksToWait );

	if( ( xTaskGetTickCount() - xTimeOnEntering ) >= xTicksToWait )
	{
		xErrorStatus = pdFAIL;
	}

	/* The task should have been notified, and the notified value should
	be equal to ulFirstNotifiedConst. */
	configASSERT( xReturned == pdPASS );
	configASSERT( ulNotifiedValue == ulFirstNotifiedConst );

	/* Incremented to show the task is still running. */
	ulNotifyCycleCount++;





	/*--------------------------------------------------------------------------
	Check the non-overwriting functionality.  The notification is done twice
	using two different notification values.  The action says don't overwrite so
	only the first notification should pass and the value read back should also
	be that used with the first notification. */
	xReturned = xTaskNotify( xTaskToNotify, ulFirstNotifiedConst, eSetValueWithoutOverwrite );
	configASSERT( xReturned == pdPASS );

	xReturned = xTaskNotify( xTaskToNotify, ulSecondNotifiedValueConst, eSetValueWithoutOverwrite );
	configASSERT( xReturned == pdFAIL );

	/* Waiting for the notification should now return immediately so a block
	time of zero is used. */
	xReturned = xTaskNotifyWait( ULONG_MAX, 0, &ulNotifiedValue, 0 );

	configASSERT( xReturned == pdPASS );
	configASSERT( ulNotifiedValue == ulFirstNotifiedConst );





	/*--------------------------------------------------------------------------
	Do the same again, only this time use the overwriting version.  This time
	both notifications should pass, and the value written the second time should
	overwrite the value written the first time, and so be the value that is read
	back. */
	xReturned = xTaskNotify( xTaskToNotify, ulFirstNotifiedConst, eSetValueWithOverwrite );
	configASSERT( xReturned == pdPASS );
	xReturned = xTaskNotify( xTaskToNotify, ulSecondNotifiedValueConst, eSetValueWithOverwrite );
	configASSERT( xReturned == pdPASS );
	xReturned = xTaskNotifyWait( ULONG_MAX, 0, &ulNotifiedValue, 0 );
	configASSERT( xReturned == pdPASS );
	configASSERT( ulNotifiedValue == ulSecondNotifiedValueConst );




	/*--------------------------------------------------------------------------
	Check notifications with no action pass without updating the value.  Even
	though ulFirstNotifiedConst is used as the value the value read back should
	remain at ulSecondNotifiedConst. */
	xReturned = xTaskNotify( xTaskToNotify, ulFirstNotifiedConst, eNoAction );
	configASSERT( xReturned == pdPASS );
	xReturned = xTaskNotifyWait( ULONG_MAX, 0, &ulNotifiedValue, 0 );
	configASSERT( ulNotifiedValue == ulSecondNotifiedValueConst );




	/*--------------------------------------------------------------------------
	Check incrementing values.  Send ulMaxLoop increment notifications, then
	ensure the received value is as expected - which should be
	ulSecondNotificationValueConst plus how ever many times to loop iterated. */
	for( ulLoop = 0; ulLoop < ulMaxLoops; ulLoop++ )
	{
		xReturned = xTaskNotify( xTaskToNotify, 0, eIncrement );
		configASSERT( xReturned == pdPASS );
	}

	xReturned = xTaskNotifyWait( ULONG_MAX, 0, &ulNotifiedValue, 0 );
	configASSERT( xReturned == pdPASS );
	configASSERT( ulNotifiedValue == ( ulSecondNotifiedValueConst + ulMaxLoops ) );

	/* Should not be any notifications pending now. */
	xReturned = xTaskNotifyWait( 0, 0, &ulNotifiedValue, 0 );
	configASSERT( xReturned == pdFAIL );




	/*--------------------------------------------------------------------------
	Check all bits can be set by notifying the task with one additional bit	set
	on each notification, and exiting the loop when all the bits are found to be
	set.  As there are 32-bits the loop should execute 32 times before all the
	bits are found to be set. */
	ulNotifyingValue = 0x01;
	ulLoop = 0;

	/* Start with all bits clear. */
	xTaskNotifyWait( ULONG_MAX, 0, &ulNotifiedValue, 0 );

	do
	{
		/* Set the next bit in the task's notified value. */
		xTaskNotify( xTaskToNotify, ulNotifyingValue, eSetBits );

		/* Wait for the notified value - which of course will already be
		available.  Don't clear the bits on entry or exit as this loop is exited
		when all the bits are set. */
		xReturned = xTaskNotifyWait( 0, 0, &ulNotifiedValue, 0 );
		configASSERT( xReturned == pdPASS );

		ulLoop++;

		/* Use the next bit on the next iteration around this loop. */
		ulNotifyingValue <<= 1UL;

	} while ( ulNotifiedValue != ULONG_MAX );

	/* As a 32-bit value was used the loop should have executed 32 times before
	all the bits were set. */
	configASSERT( ulLoop == 32 );




	/*--------------------------------------------------------------------------
	Check bits are cleared on entry but not on exit when a notification fails
	to arrive before timing out - both with and without a timeout value.  Wait
	for the notification again - but this time it is not given by anything and
	should return pdFAIL.  The parameters are set to clear bit zero on entry and
	bit one on exit.  As no notification was received only the bit cleared on
	entry should actually get cleared. */
	xReturned = xTaskNotifyWait( ulBit0, ulBit1, &ulNotifiedValue, xTicksToWait );
	configASSERT( xReturned == pdFAIL );

	/* Notify the task with no action so as not to update the bits even though
	ULONG_MAX is used as the notification value. */
	xTaskNotify( xTaskToNotify, ULONG_MAX, eNoAction );

	/* Reading back the value should should find bit 0 is clear, as this was
	cleared on entry, but bit 1 is not clear as it will not have been cleared on
	exit as no notification was received. */
	xReturned = xTaskNotifyWait( 0x00UL, 0x00UL, &ulNotifiedValue, 0 );
	configASSERT( xReturned == pdPASS );
	configASSERT( ulNotifiedValue == ( ULONG_MAX & ~ulBit0 ) );





	/*--------------------------------------------------------------------------
	Now try clearing the bit on exit.  For that to happen a notification must be
	received, so the task is notified first. */
	xTaskNotify( xTaskToNotify, 0, eNoAction );
	xTaskNotifyWait( 0x00, ulBit1, &ulNotifiedValue, 0 );

	/* However as the bit is cleared on exit, after the returned notification
	value is set, the returned notification value should not have the bit
	cleared... */
	configASSERT( ulNotifiedValue == ( ULONG_MAX & ~ulBit0 ) );

	/* ...but reading the value back again should find that the bit was indeed
	cleared internally.  The returned value should be pdFAIL however as nothing
	has notified the task in the mean time. */
	xReturned = xTaskNotifyWait( 0x00, 0x00, &ulNotifiedValue, 0 );
	configASSERT( xReturned == pdFAIL );
	configASSERT( ulNotifiedValue == ( ULONG_MAX & ~( ulBit0 | ulBit1 ) ) );



	/* Incremented to show the task is still running. */
	ulNotifyCycleCount++;

	/* Leave all bits cleared. */
	xTaskNotifyWait( ULONG_MAX, 0, NULL, 0 );
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
		will be higher than the tasks block time, sometimes it will be lower
		than the tasks block time. */
		xPeriod = prvRand() % xMaxPeriod;
		if( xPeriod < xMinPeriod )
		{
			xPeriod = xMinPeriod;
		}

		xTimerChangePeriod( xTimer, xPeriod, portMAX_DELAY );
		xTimerStart( xTimer, portMAX_DELAY );

		/* Block waiting for the notification again with a different period.
		Sometimes the period will be higher than the tasks block time, sometimes
		it will be lower than the tasks block time. */
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

		/* Wait for the next notification again, clearing all notifications if
		one is received, but this time blocking indefinitely. */
		ulTimerNotificationsReceived += ulTaskNotifyTake( pdTRUE, portMAX_DELAY );

		/* Incremented to show the task is still running. */
		ulNotifyCycleCount++;
	}
}
/*-----------------------------------------------------------*/

void xNotifyTaskFromISR( void )
{
static BaseType_t xCallCount = 0;
const BaseType_t xCallInterval = pdMS_TO_TICKS( 50 );

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

			vTaskNotifyGiveFromISR( xTaskToNotify, NULL );
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
	if( ulTimerNotificationsSent > ulTimerNotificationsSent )
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
const uint32_t ulMultiplier = 0x015a4e35UL, ulIncrement = 1UL;

	/* Utility function to generate a pseudo random number. */
	ulNextRand = ( ulMultiplier * ulNextRand ) + ulIncrement;
	return( ( int ) ( ulNextRand >> 16UL ) & 0x7fffUL );
}
/*-----------------------------------------------------------*/
