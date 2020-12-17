/*
 * FreeRTOS V202012.00
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


/*
 * Tests the behaviour of arrays of task notifications per task.  The tests in this
 * file are additive to those implemented in FreeRTOS/Demo/Common/Minimal/TaskNotify.c.
 */

/* Standard includes. */
#include <limits.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "timers.h"

/* Demo program include files. */
#include "TaskNotifyArray.h"

#if( configTASK_NOTIFICATION_ARRAY_ENTRIES < 3 )
	#error This file tests direct to task notification arrays and needs configTASK_NOTIFICATION_ARRAY_ENTRIES to be at least 3.
#endif

/* Allow parameters to be overridden on a demo by demo basis. */
#ifndef notifyNOTIFY_ARRAY_TASK_STACK_SIZE
	#define notifyNOTIFY_ARRAY_TASK_STACK_SIZE configMINIMAL_STACK_SIZE
#endif

#define notifyTASK_PRIORITY		( tskIDLE_PRIORITY )

/* Constants used in tests when setting/clearing bits. */
#define notifyUINT32_MAX		( ( uint32_t ) 0xffffffff )
#define notifyUINT32_HIGH_BYTE	( ( uint32_t ) 0xff000000 )
#define notifyUINT32_LOW_BYTE	( ( uint32_t ) 0x000000ff )

/*-----------------------------------------------------------*/

/*
 * Implementation of the task that runs the tests - the task runs some tests
 * itself, and others where notifications are sent from a software timer or
 * an interrupt (specifically the tick hook function).
 */
static void prvNotifiedTask( void *pvParameters );

/*
 * Performs the tests that don't require notifications to be sent from a
 * remote source.
 */
static void prvSingleTaskTests( void );

/*
 * Uses a software timer to send notifications to the task while the task is
 * suspended.
 */
static void prvTestNotifyTaskWhileSuspended( void );

/*
 * Uses a software timer to send notifications to the index within the array of
 * task notifications on which the task is blocked.  The task should unblock and
 * the state of all the other task notifications within the array should remain
 * unchanged.
 */
static void prvBlockOnTheNotifiedIndexed( void );

/*
 * As per prvBlockOnTheNotifiedIndexed(), but this time the notification comes from
 * the tick hook function, so from an interrupt rather than from a software timer.
 */
static void prvBlockOnNotificationsComingFromInterrupts( void );

/*
 * As per prvBlockOnTheNotifiedIndexed(), except this time the notification is
 * sent to an index within the task notification array on which the task is not
 * blocked, so this time the task should not unblock and the state of all the
 * task notifications other than the one to which the notification was actually
 * sent should remain unchanged.
 */
static void prvBlockOnANonNotifiedIndexed( void );

/*
 * Callback of the software timer used to send notifications for the
 * prvBlockOnTheNotifiedIndexed() and prvBlockOnANonNotifiedIndexed() tests.
 */
static void prvNotifyingTimerCallback( TimerHandle_t xTimer );

/*
 * Callback for a timer that is used by the prvTestNotifyTaskWhileSuspended()
 * test.
 */
static void prvSuspendedTaskTimerTestCallback( TimerHandle_t xExpiredTimer );

/*
 * Utility function to create pseudo random numbers.
 */
static UBaseType_t prvRand( void );


/*-----------------------------------------------------------*/

/* Counters used to check the task has not stalled.  ulFineCycleCount is
incremented within each test.  ulCourseCycleCounter is incremented one every
loop of all the tests to ensure each test is actually executing.  The check task
calls xAreTaskNotificationArrayTasksStillRunning() (implemented within this
file) to check both counters are changing. */
static volatile uint32_t ulFineCycleCount = 0, ulCourseCycleCounter = 0;

/* The handle of the task that runs the tests and receives the notifications
from the software timers and interrupts. */
static TaskHandle_t xTaskToNotify = NULL;

/* The software timers used to send notifications to the main test task. */
static TimerHandle_t xIncrementingIndexTimer = NULL;
static TimerHandle_t xNotifyWhileSuspendedTimer = NULL;

/* Used by the pseudo random number generating function. */
static size_t uxNextRand = 0;

/* Used to communicate when to send a task notification to the tick hook tests. */
static volatile BaseType_t xSendNotificationFromISR = pdFALSE;

/*-----------------------------------------------------------*/

void vStartTaskNotifyArrayTask( void  )
{
const TickType_t xIncrementingIndexTimerPeriod = pdMS_TO_TICKS( 100 );
const TickType_t xSuspendTimerPeriod = pdMS_TO_TICKS( 50 );

	/* Create the software timers used for these tests.  The timer callbacks send
	notifications to this task. */
	xNotifyWhileSuspendedTimer = xTimerCreate( "SingleNotify", xSuspendTimerPeriod, pdFALSE, NULL, prvSuspendedTaskTimerTestCallback );
	xIncrementingIndexTimer = xTimerCreate( "Notifier", xIncrementingIndexTimerPeriod, pdFALSE, NULL, prvNotifyingTimerCallback );
	configASSERT( xNotifyWhileSuspendedTimer );
	configASSERT( xIncrementingIndexTimer );

	/* Create the task that performs some tests by itself, then loops around
	being notified by both a software timer and an interrupt. */
	xTaskCreate( prvNotifiedTask, /* Function that implements the task. */
				 "ArrayNotifed", /* Text name for the task - for debugging only - not used by the kernel. */
				 notifyNOTIFY_ARRAY_TASK_STACK_SIZE, /* Task's stack size in words, not bytes!. */
				 NULL, /* Task parameter, not used in this case. */
				 notifyTASK_PRIORITY, /* Task priority, 0 is the lowest. */
				 &xTaskToNotify ); /* Used to pass a handle to the task out if needed, otherwise set to NULL. */

	/* Pseudo seed the random number generator. */
	uxNextRand = ( size_t ) prvRand;
}
/*-----------------------------------------------------------*/

static void prvNotifiedTask( void *pvParameters )
{
	/* Remove compiler warnings about unused parameters. */
	( void ) pvParameters;

	/* Loop through each set of test functions in turn.  See the comments above
	the respective function prototypes above for more details. */
	for( ;; )
	{
		prvSingleTaskTests();
		prvTestNotifyTaskWhileSuspended();
		prvBlockOnTheNotifiedIndexed();
		prvBlockOnANonNotifiedIndexed();
		prvBlockOnNotificationsComingFromInterrupts();
		ulCourseCycleCounter++;
	}
}
/*-----------------------------------------------------------*/

static void prvSingleTaskTests( void )
{
const TickType_t xTicksToWait = pdMS_TO_TICKS( 100UL );
BaseType_t xReturned;
uint32_t ulNotifiedValue, ulLoop, ulNotifyingValue, ulPreviousValue, ulExpectedValue;
TickType_t xTimeOnEntering, xTimeNow, xTimeDifference;
const uint32_t ulFirstNotifiedConst = 100001UL, ulSecondNotifiedValueConst = 5555UL, ulMaxLoops = 5UL;
const uint32_t ulBit0 = 0x01UL, ulBit1 = 0x02UL;
UBaseType_t uxIndexToTest, uxOtherIndexes;


	/* ------------------------------------------------------------------------
	Check blocking when there are no notifications. */
	for( uxIndexToTest = 0; uxIndexToTest < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxIndexToTest++ )
	{
		/* Send notifications to the task notification in each index of the
		task notification array other than the one on which this task will
		block. */
		for( uxOtherIndexes = 0; uxOtherIndexes < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxOtherIndexes++ )
		{
			if( uxOtherIndexes != uxIndexToTest )
			{
				xTaskNotifyIndexed( xTaskToNotify, uxOtherIndexes, 0, eNoAction );
			}
		}

		xTimeOnEntering = xTaskGetTickCount();
		xReturned = xTaskNotifyWaitIndexed( uxIndexToTest, notifyUINT32_MAX, 0, &ulNotifiedValue, xTicksToWait );
		( void ) xReturned; /* Remove compiler warnings in case configASSERT() is not defined. */

		/* Should have blocked for the entire block time. */
		xTimeNow = xTaskGetTickCount();
		xTimeDifference = xTimeNow - xTimeOnEntering;
		configASSERT( xTimeDifference >= xTicksToWait );
		configASSERT( xReturned == pdFAIL );
		configASSERT( ulNotifiedValue == 0UL );
		( void ) xReturned; /* Remove compiler warnings in case configASSERT() is not defined. */
		( void ) ulNotifiedValue;

		/* Clear all the other notifications within the array of task
		notifications again ready for the next round. */
		for( uxOtherIndexes = 0; uxOtherIndexes < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxOtherIndexes++ )
		{
			if( uxOtherIndexes != uxIndexToTest )
			{
				xReturned = xTaskNotifyStateClearIndexed( xTaskToNotify, uxOtherIndexes );

				/* The notification state was set above so expect it to still be
				set. */
				configASSERT( xReturned == pdTRUE );
				( void ) xReturned; /* Remove compiler warnings in case configASSERT() is not defined. */
			}
		}
	}



	/* ------------------------------------------------------------------------
	Check no blocking when notifications are pending. */
	for( uxIndexToTest = 0; uxIndexToTest < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxIndexToTest++ )
	{
		/* First notify the task notification at index uxIndexToTest within this
		task's own array of task notifications - this would not be a normal
		thing to do and is done here for test purposes only. */
		xReturned = xTaskNotifyAndQueryIndexed( xTaskToNotify, uxIndexToTest, ulFirstNotifiedConst, eSetValueWithoutOverwrite, &ulPreviousValue );

		/* Even through the 'without overwrite' action was used the update should
		have been successful. */
		configASSERT( xReturned == pdPASS );
		( void ) xReturned; /* Remove compiler warnings in case configASSERT() is not defined. */

		/* No bits should have been pending previously. */
		configASSERT( ulPreviousValue == 0 );
		( void ) ulPreviousValue;

		/* The task should now have a notification pending in the task
		notification at index uxIndexToTest within the task notification array,
		and so not time out. */
		xTimeOnEntering = xTaskGetTickCount();
		xReturned = xTaskNotifyWaitIndexed( uxIndexToTest, notifyUINT32_MAX, 0, &ulNotifiedValue, xTicksToWait );
		xTimeNow = xTaskGetTickCount();
		xTimeDifference = xTimeNow - xTimeOnEntering;
		configASSERT( xTimeDifference < xTicksToWait );

		/* The task should have been notified, and the notified value should
		be equal to ulFirstNotifiedConst. */
		configASSERT( xReturned == pdPASS );
		configASSERT( ulNotifiedValue == ulFirstNotifiedConst );
		( void ) xReturned; /* Remove compiler warnings in case configASSERT() is not defined. */
		( void ) ulNotifiedValue;
	}




	/*-------------------------------------------------------------------------
	Check the non-overwriting functionality. */
	for( uxIndexToTest = 0; uxIndexToTest < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxIndexToTest++ )
	{
		/* Send notifications to all indexes with the array of task
		notificaitons other than the one on which this task will block. */
		for( uxOtherIndexes = 0; uxOtherIndexes < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxOtherIndexes++ )
		{
			if( uxOtherIndexes != uxIndexToTest )
			{
				xReturned = xTaskNotifyIndexed( xTaskToNotify, uxOtherIndexes, ulFirstNotifiedConst, eSetValueWithOverwrite );
				configASSERT(xReturned == pdPASS);
				(void)xReturned; /* Remove compiler warnings in case configASSERT() is not defined. */
			}
		}

		/* The notification is performed twice using two different notification
		values.  The action says don't overwrite so only the first notification
		should pass and the value read back should also be that used with the
		first notification. The notification is sent to the task notification at
		index uxIndexToTest within the array of task notifications. */
		xReturned = xTaskNotifyIndexed( xTaskToNotify, uxIndexToTest, ulFirstNotifiedConst, eSetValueWithoutOverwrite );
		configASSERT( xReturned == pdPASS );
		( void ) xReturned; /* Remove compiler warnings in case configASSERT() is not defined. */

		xReturned = xTaskNotifyIndexed( xTaskToNotify, uxIndexToTest, ulSecondNotifiedValueConst, eSetValueWithoutOverwrite );
		configASSERT( xReturned == pdFAIL );
		( void ) xReturned; /* Remove compiler warnings in case configASSERT() is not defined. */

		/* Waiting for the notification should now return immediately so a block
		time of zero is used. */
		xReturned = xTaskNotifyWaitIndexed( uxIndexToTest, notifyUINT32_MAX, 0, &ulNotifiedValue, 0 );

		configASSERT( xReturned == pdPASS );
		configASSERT( ulNotifiedValue == ulFirstNotifiedConst );
		( void ) xReturned; /* Remove compiler warnings in case configASSERT() is not defined. */
		( void ) ulNotifiedValue;

		/* Clear all the other task notifications within the array of task
		notifications again ready for the next round. */
		for( uxOtherIndexes = 0; uxOtherIndexes < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxOtherIndexes++ )
		{
			if( uxOtherIndexes != uxIndexToTest )
			{
				xReturned = xTaskNotifyStateClearIndexed( xTaskToNotify, uxOtherIndexes );
				configASSERT( xReturned == pdTRUE );
				( void ) xReturned; /* Remove compiler warnings in case configASSERT() is not defined. */

				ulNotifiedValue = ulTaskNotifyValueClearIndexed( xTaskToNotify, uxOtherIndexes, notifyUINT32_MAX );

				/* The notification value was set to ulFirstNotifiedConst in all
				the other indexes, so expect it to still have that value. */
				configASSERT( ulNotifiedValue == ulFirstNotifiedConst );
				( void ) ulNotifiedValue; /* Remove compiler warnings in case configASSERT() is not defined. */
			}
		}
	}




	/*-------------------------------------------------------------------------
	Do the same again, only this time use the overwriting version.  This time
	both notifications should pass, and the value written the second time should
	overwrite the value written the first time, and so be the value that is read
	back. */
	for( uxIndexToTest = 0; uxIndexToTest < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxIndexToTest++ )
	{
		for( uxOtherIndexes = 0; uxOtherIndexes < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxOtherIndexes++ )
		{
			if( uxOtherIndexes != uxIndexToTest )
			{
				xTaskNotifyIndexed( xTaskToNotify, uxOtherIndexes, ulFirstNotifiedConst, eSetValueWithOverwrite );
			}
		}

		xReturned = xTaskNotifyIndexed( xTaskToNotify, uxIndexToTest, ulFirstNotifiedConst, eSetValueWithOverwrite );
		configASSERT( xReturned == pdPASS );
		( void ) xReturned; /* Remove compiler warnings in case configASSERT() is not defined. */
		xReturned = xTaskNotifyIndexed( xTaskToNotify, uxIndexToTest, ulSecondNotifiedValueConst, eSetValueWithOverwrite );
		configASSERT( xReturned == pdPASS );
		( void ) xReturned; /* Remove compiler warnings in case configASSERT() is not defined. */
		xReturned = xTaskNotifyWaitIndexed( uxIndexToTest, 0, notifyUINT32_MAX, &ulNotifiedValue, 0 );
		configASSERT( xReturned == pdPASS );
		( void ) xReturned; /* Remove compiler warnings in case configASSERT() is not defined. */
		configASSERT( ulNotifiedValue == ulSecondNotifiedValueConst );
		( void ) ulNotifiedValue;

		for( uxOtherIndexes = 0; uxOtherIndexes < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxOtherIndexes++ )
		{
			if( uxOtherIndexes != uxIndexToTest )
			{
				xReturned = xTaskNotifyStateClearIndexed( xTaskToNotify, uxOtherIndexes );
				configASSERT( xReturned == pdTRUE );
				( void ) xReturned; /* Remove compiler warnings in case configASSERT() is not defined. */
				ulNotifiedValue = ulTaskNotifyValueClearIndexed( xTaskToNotify, uxOtherIndexes, notifyUINT32_MAX );
				configASSERT( ulNotifiedValue == ulFirstNotifiedConst );
				( void ) ulNotifiedValue; /* Remove compiler warnings in case configASSERT() is not defined. */
			}
		}
	}




	/*-------------------------------------------------------------------------
	For each task notification within the array of task notifications, check
	notifications with no action pass without updating the value. */
	for( uxIndexToTest = 0; uxIndexToTest < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxIndexToTest++ )
	{
		/* First set the notification values of the task notification at index
		uxIndexToTest of the array of task notification to
		ulSecondNotifiedValueConst. */
		xReturned = xTaskNotifyIndexed( xTaskToNotify, uxIndexToTest, ulSecondNotifiedValueConst, eSetValueWithOverwrite );
		configASSERT( xReturned == pdPASS );
		( void ) xReturned; /* Remove compiler warnings in case configASSERT() is not defined. */

		/* Even though ulFirstNotifiedConst is used as the value next, the value
		read back should remain at ulSecondNotifiedConst as the action is set
		to eNoAction. */
		xReturned = xTaskNotifyIndexed( xTaskToNotify, uxIndexToTest, ulFirstNotifiedConst, eNoAction );
		configASSERT( xReturned == pdPASS );
		( void ) xReturned; /* Remove compiler warnings in case configASSERT() is not defined. */

		/* All task notifications in the array of task notifications up to and
		including index uxIndexToTest should still contain the same value. */
		for( uxOtherIndexes = 0; uxOtherIndexes <= uxIndexToTest; uxOtherIndexes++ )
		{
			/* First zero is bits to clear on entry, the second is bits to clear on
			exist, the last 0 is the block time. */
			xReturned = xTaskNotifyWaitIndexed( uxOtherIndexes, 0, 0, &ulNotifiedValue, 0 );
			configASSERT( ulNotifiedValue == ulSecondNotifiedValueConst );
			( void ) ulNotifiedValue; /* Remove compiler warnings in case configASSERT() is not defined. */
		}

		/* All array indexes in the array of task notifications after index
		uxIndexToTest should still contain 0 as they have not been set in this
		loop yet.  This time use ulTaskNotifyValueClearIndexed() instead of
		xTaskNotifyWaitIndexed(), just for test coverage. */
		for( uxOtherIndexes = uxIndexToTest + 1; uxOtherIndexes < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxOtherIndexes++ )
		{
			/* This time 0 is the bits to clear parameter - so clearing no bits. */
			ulNotifiedValue = ulTaskNotifyValueClearIndexed( NULL, uxOtherIndexes, 0 );
			configASSERT( ulNotifiedValue == 0 );
			( void ) ulNotifiedValue; /* Remove compiler warnings in case configASSERT() is not defined. */
		}
	}




	/*-------------------------------------------------------------------------
	Check incrementing values.  For each task notification in the array of task
	notifications in turn, send ulMaxLoop increment notifications, then ensure
	the received value is as expected - which should be
	ulSecondNotificationValueConst plus how ever many times to loop iterated. */
	for( uxIndexToTest = 0; uxIndexToTest < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxIndexToTest++ )
	{
		for( ulLoop = 0; ulLoop < ulMaxLoops; ulLoop++ )
		{
			/* Increment the value of the task notification at index
			uxIndexToTest within the array of task notifications. */
			xReturned = xTaskNotifyIndexed( xTaskToNotify, uxIndexToTest, 0, eIncrement );
			configASSERT( xReturned == pdPASS );
			( void ) xReturned; /* Remove compiler warnings in case configASSERT() is not defined. */
		}

		/* All array indexes up to and including uxIndexToTest should still
		contain the updated value. */
		for( uxOtherIndexes = 0; uxOtherIndexes <= uxIndexToTest; uxOtherIndexes++ )
		{
			/* First zero is bits to clear on entry, the second is bits to clear on
			exist, the last 0 is the block time. */
			xReturned = xTaskNotifyWaitIndexed( uxOtherIndexes, 0, 0, &ulNotifiedValue, 0 );
			configASSERT( ulNotifiedValue == ( ulSecondNotifiedValueConst + ulMaxLoops ) );
			( void ) ulNotifiedValue; /* Remove compiler warnings in case configASSERT() is not defined. */
		}

		/* Should not be any notifications pending now. */
		xReturned = xTaskNotifyWaitIndexed( uxIndexToTest, 0, 0, &ulNotifiedValue, 0 );
		configASSERT( xReturned == pdFAIL );
		( void ) xReturned; /* Remove compiler warnings in case configASSERT() is not defined. */
		( void ) ulNotifiedValue;

		/* All notifications values in the array of task notifications after
		index uxIndexToTest should still contain the un-incremented
		ulSecondNotifiedValueConst as they have not been set in this loop yet.
		This time use ulTaskNotifyValueClearIndexed() instead of xTaskNotifyWaitIndexed(),
		just for test coverage. */
		for( uxOtherIndexes = uxIndexToTest + 1; uxOtherIndexes < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxOtherIndexes++ )
		{
			/* This time 0 is the bits to clear parameter - so clearing no bits. */
			ulNotifiedValue = ulTaskNotifyValueClearIndexed( NULL, uxOtherIndexes, 0 );
			configASSERT( ulNotifiedValue == ulSecondNotifiedValueConst );
			( void ) ulNotifiedValue; /* Remove compiler warnings in case configASSERT() is not defined. */
		}
	}

	/* Clear all bits ready for next test. */
	for( uxIndexToTest = 0; uxIndexToTest < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxIndexToTest++ )
	{
		/* Start with all bits clear. */
		ulTaskNotifyValueClearIndexed( NULL, uxIndexToTest, notifyUINT32_MAX );
	}



	/*-------------------------------------------------------------------------
	For each task notification in the array of task notifications in turn, check
	all bits in the notification's value can be set by notifying the task with
	one additional bit set on each notification, and exiting the loop when all
	the bits are found to be set.  As there are 32-bits the loop should execute
	32 times before all the bits are found to be set. */
	for( uxIndexToTest = 0; uxIndexToTest < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxIndexToTest++ )
	{
		ulNotifyingValue = 0x01;
		ulLoop = 0;

		do
		{
			/* Set the next bit in the value of the task notification at index
			uxIndexToTest within the array of task notifications. */
			xTaskNotifyIndexed( xTaskToNotify, uxIndexToTest, ulNotifyingValue, eSetBits );

			/* Wait for the notified value - which of course will already be
			available.  Don't clear the bits on entry or exit as this loop is
			exited when all the bits are set. */
			xReturned = xTaskNotifyWaitIndexed( uxIndexToTest, 0, 0, &ulNotifiedValue, 0 );
			configASSERT( xReturned == pdPASS );
			( void ) xReturned; /* Remove compiler warnings in case configASSERT() is not defined. */

			ulLoop++;

			/* Use the next bit on the next iteration around this loop. */
			ulNotifyingValue <<= 1UL;

		} while ( ulNotifiedValue != notifyUINT32_MAX );

		/* As a 32-bit value was used the loop should have executed 32 times before
		all the bits were set. */
		configASSERT( ulLoop == 32 );

		/* The value of each task notification within the array of task
		notifications up to and including index uxIndexToTest should still have
		all bits set. */
		for( uxOtherIndexes = 0; uxOtherIndexes <= uxIndexToTest; uxOtherIndexes++ )
		{
			/* First zero is bits to clear on entry, the second is bits to clear on
			exist, the last 0 is the block time. */
			xReturned = xTaskNotifyWaitIndexed( uxOtherIndexes, 0, 0, &ulNotifiedValue, 0 );
			configASSERT( ulNotifiedValue == notifyUINT32_MAX );
			( void ) ulNotifiedValue; /* Remove compiler warnings in case configASSERT() is not defined. */
		}

		/* The value of each task notification within the array of task
		notifications after index uxIndexToTest should still contain 0 as they
		have not been set in this loop yet.  This time use ulTaskNotifyValueClearIndexed()
		instead of xTaskNotifyWaitIndexed(), just for test coverage. */
		for( uxOtherIndexes = uxIndexToTest + 1; uxOtherIndexes < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxOtherIndexes++ )
		{
			/* This time 0 is the bits to clear parameter - so clearing no bits. */
			ulNotifiedValue = ulTaskNotifyValueClearIndexed( NULL, uxOtherIndexes, 0 );
			configASSERT( ulNotifiedValue == 0 );
			( void ) ulNotifiedValue; /* Remove compiler warnings in case configASSERT() is not defined. */
		}
	}



	/*-------------------------------------------------------------------------
	For each task notification within the array of task notifications in turn,
	check bits are cleared on entry but not on exit when a notification fails
	to arrive before timing out - both with and without a timeout value. */
	for( uxIndexToTest = 0; uxIndexToTest < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxIndexToTest++ )
	{
		/* Wait for the notification - but this time it is not given by anything
		and should return pdFAIL.  The parameters are set to clear bit zero on
		entry and bit one on exit.  As no notification was received only the bit
		cleared on entry should actually get cleared. */
		xReturned = xTaskNotifyWaitIndexed( uxIndexToTest, ulBit0, ulBit1, &ulNotifiedValue, xTicksToWait );
		configASSERT( xReturned == pdFAIL );
		( void ) xReturned; /* Remove compiler warnings in case configASSERT() is not defined. */

		/* Send a notification with no action to the task notification at index
		uxIndexToTest within the array of task notifications.  This should not
		update the bits even though notifyUINT32_MAX is used as the notification
		value. */
		xTaskNotifyIndexed( xTaskToNotify, uxIndexToTest, notifyUINT32_MAX, eNoAction );

		/* All array indexes up to and including uxIndexToTest within the array
		of task notifications should have the modified value.  */
		for( uxOtherIndexes = 0; uxOtherIndexes <= uxIndexToTest; uxOtherIndexes++ )
		{
			/* Reading back the value should find bit 0 is clear, as this was cleared
			on entry, but bit 1 is not clear as it will not have been cleared on exit
			as no notification was received. */
			xReturned = xTaskNotifyWaitIndexed( uxOtherIndexes, 0x00UL, 0x00UL, &ulNotifiedValue, 0 );
			if( uxOtherIndexes == uxIndexToTest )
			{
				/* This is the index being used this time round the loop and its
				notification state was set immediately above. */
				configASSERT( xReturned == pdPASS );
			}
			else
			{
				/* Nothing should have set this index's notification state again. */
				configASSERT( xReturned == pdFAIL );
			}

			configASSERT( ulNotifiedValue == ( notifyUINT32_MAX & ~ulBit0 ) );
			( void ) xReturned; /* Remove compiler warnings in case configASSERT() is not defined. */
		}

		/* All array indexes after uxIndexToTest should still contain notifyUINT32_MAX
		left over from the previous test.  This time use xTaskNotifyValueClear()
		instead of xTaskNotifyWaitIndexed(), just for test coverage. */
		for( uxOtherIndexes = uxIndexToTest + 1; uxOtherIndexes < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxOtherIndexes++ )
		{
			/* This time 0 is the bits to clear parameter - so clearing no bits. */
			ulNotifiedValue = ulTaskNotifyValueClearIndexed( NULL, uxOtherIndexes, 0 );
			configASSERT( ulNotifiedValue == notifyUINT32_MAX );
			( void ) ulNotifiedValue; /* Remove compiler warnings in case configASSERT() is not defined. */
		}
	}




	/*-------------------------------------------------------------------------
	Now try clearing the bit on exit. */
	for( uxIndexToTest = 0; uxIndexToTest < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxIndexToTest++ )
	{
		/* The task is notified first using the task notification at index
		uxIndexToTest within the array of task notifications. */
		xTaskNotifyIndexed( xTaskToNotify, uxIndexToTest, 0, eNoAction );
		xTaskNotifyWaitIndexed( uxIndexToTest, 0x00, ulBit1, &ulNotifiedValue, 0 );

		/* However as the bit is cleared on exit, after the returned notification
		value is set, the returned notification value should not have the bit
		cleared... */
		configASSERT( ulNotifiedValue == ( notifyUINT32_MAX & ~ulBit0 ) );

		/* ...but reading the value back again should find that the bit was indeed
		cleared internally.  The returned value should be pdFAIL however as nothing
		has notified the task in the mean time. */
		xReturned = xTaskNotifyWaitIndexed( uxIndexToTest, 0x00, 0x00, &ulNotifiedValue, 0 );
		configASSERT( xReturned == pdFAIL );
		configASSERT( ulNotifiedValue == ( notifyUINT32_MAX & ~( ulBit0 | ulBit1 ) ) );
		( void ) xReturned; /* Remove compiler warnings in case configASSERT() is not defined. */

		/* No other indexes should have a notification pending. */
		for( uxOtherIndexes = 0; uxOtherIndexes < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxOtherIndexes++ )
		{
			if( uxOtherIndexes != uxIndexToTest )
			{
				xReturned = xTaskNotifyWaitIndexed( uxOtherIndexes, 0x00UL, 0x00UL, &ulNotifiedValue, 0 );
				configASSERT( xReturned == pdFAIL );
				( void ) xReturned; /* Remove compiler warnings in case configASSERT() is not defined. */
			}
		}
	}



	/*-------------------------------------------------------------------------
	For each task notification within the array of task notifications, try
	querying the previous value while notifying a task. */
	for( uxIndexToTest = 0; uxIndexToTest < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxIndexToTest++ )
	{
		xTaskNotifyAndQueryIndexed( xTaskToNotify, uxIndexToTest, 0x00, eSetBits, &ulPreviousValue );
		configASSERT( ulNotifiedValue == ( notifyUINT32_MAX & ~( ulBit0 | ulBit1 ) ) );

		/* Clear all bits. */
		xTaskNotifyWaitIndexed( uxIndexToTest, 0x00, notifyUINT32_MAX, &ulNotifiedValue, 0 );
		xTaskNotifyAndQueryIndexed( xTaskToNotify, uxIndexToTest, 0x00, eSetBits, &ulPreviousValue );
		configASSERT( ulPreviousValue == 0 );

		ulExpectedValue = 0;
		for( ulLoop = 0x01; ulLoop < 0x80UL; ulLoop <<= 1UL )
		{
			/* Set the next bit up, and expect to receive the last bits set (so
			the previous value will not yet have the bit being set this time
			around). */
			xTaskNotifyAndQueryIndexed( xTaskToNotify, uxIndexToTest, ulLoop, eSetBits, &ulPreviousValue );
			configASSERT( ulExpectedValue == ulPreviousValue );
			ulExpectedValue |= ulLoop;
		}
	}


	/* ---------------------------------------------------------------------- */
	for( uxIndexToTest = 0; uxIndexToTest < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxIndexToTest++ )
	{
		/* Clear the previous notifications. */
		xTaskNotifyWaitIndexed( uxIndexToTest, notifyUINT32_MAX, 0, &ulNotifiedValue, 0 );
	}

	for( uxIndexToTest = 0; uxIndexToTest < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxIndexToTest++ )
	{
		/* No task notification within the array of task notifications should
		have any notification pending, so an attempt to clear the notification
		state should fail. */
		for( uxOtherIndexes = 0; uxOtherIndexes < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxOtherIndexes++ )
		{
			configASSERT( xTaskNotifyStateClearIndexed( NULL, uxOtherIndexes ) == pdFALSE );
		}

		/* Get the task to notify itself using the task notification at index
		uxIndexToTest within the array of task notifications.  This is not a
		normal thing to do, and is only done here for test purposes. */
		xTaskNotifyAndQueryIndexed( xTaskToNotify, uxIndexToTest, ulFirstNotifiedConst, eSetValueWithoutOverwrite, &ulPreviousValue );

		/* Now the notification state should be eNotified, so it should now be
		possible to clear the notification state.  Other indexes should still
		not have a notification pending - likewise uxIndexToTest should not have
		a notification pending once it has been cleared. */
		for( uxOtherIndexes = 0; uxOtherIndexes < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxOtherIndexes++ )
		{
			if( uxOtherIndexes == uxIndexToTest )
			{
				configASSERT( xTaskNotifyStateClearIndexed( NULL, uxOtherIndexes ) == pdTRUE );
			}

			configASSERT( xTaskNotifyStateClearIndexed( NULL, uxOtherIndexes ) == pdFALSE );
		}
	}


	/* ------------------------------------------------------------------------
	For each task notification within the array of task notifications, clear
	bits in the notification value. */
	for( uxIndexToTest = 0; uxIndexToTest < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxIndexToTest++ )
	{
		/* Get the task to set all bits in its task notification at index
		uxIndexToTest within its array of task notifications.  This is not a
		normal thing to do, and is only done here for test purposes. */
		xTaskNotifyIndexed( xTaskToNotify, uxIndexToTest, notifyUINT32_MAX, eSetBits );

		/* Now clear the top bytes - the returned value from the first call
		should indicate that previously all bits were set. */
		configASSERT( ulTaskNotifyValueClearIndexed( xTaskToNotify, uxIndexToTest, notifyUINT32_HIGH_BYTE ) == notifyUINT32_MAX );

		/* Next clear the bottom bytes - the returned value this time should
		indicate that the top byte was clear (before the bottom byte was
		cleared. */
		configASSERT( ulTaskNotifyValueClearIndexed( xTaskToNotify, uxIndexToTest, notifyUINT32_LOW_BYTE ) == ( notifyUINT32_MAX & ~notifyUINT32_HIGH_BYTE ) );

		/* Next clear all bytes - the returned value should indicate that previously the
		high and low bytes were clear. */
		configASSERT( ulTaskNotifyValueClearIndexed( xTaskToNotify, uxIndexToTest, notifyUINT32_MAX ) == ( notifyUINT32_MAX & ~notifyUINT32_HIGH_BYTE & ~notifyUINT32_LOW_BYTE ) );

		/* Now all bits should be clear. */
		configASSERT( ulTaskNotifyValueClearIndexed( xTaskToNotify, uxIndexToTest, notifyUINT32_MAX ) == 0 );
		configASSERT( ulTaskNotifyValueClearIndexed( xTaskToNotify, uxIndexToTest, 0UL ) == 0 );
		configASSERT( ulTaskNotifyValueClearIndexed( xTaskToNotify, uxIndexToTest, notifyUINT32_MAX ) == 0 );

		/* Now the notification state should be eNotified, so it should now be
		possible to clear the notification state. */
		configASSERT( xTaskNotifyStateClearIndexed( NULL, uxIndexToTest ) == pdTRUE );
		configASSERT( xTaskNotifyStateClearIndexed( NULL, uxIndexToTest ) == pdFALSE );
	}




	/* Incremented to show the task is still running. */
	ulFineCycleCount++;

	/* Leave all bits cleared. */
	for( uxIndexToTest = 0; uxIndexToTest < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxIndexToTest++ )
	{
		xTaskNotifyWaitIndexed( uxIndexToTest, notifyUINT32_MAX, 0, NULL, 0 );
	}
}
/*-----------------------------------------------------------*/

static void prvSuspendedTaskTimerTestCallback( TimerHandle_t xExpiredTimer )
{
static uint32_t ulCallCount = 0;
static UBaseType_t uxIndexToNotify = 0;

	/* Remove compiler warnings about unused parameters. */
	( void ) xExpiredTimer;

	/* Callback for a timer that is used to send notifications to a task while
	it is suspended.  The timer tests the behaviour when 1: a task waiting for a
	notification is suspended and then resumed without ever receiving a
	notification, and 2: when a task waiting for a notification receives a
	notification while it is suspended.  Run one of two tests on every other
	invocation of this callback.  The notification is sent to the task
	notification at index uxIndexToNotify. */
	if( ( ulCallCount & 0x01 ) == 0 )
	{
		vTaskSuspend( xTaskToNotify );
		configASSERT( eTaskGetState( xTaskToNotify ) == eSuspended );
		vTaskResume( xTaskToNotify );
	}
	else
	{
		vTaskSuspend( xTaskToNotify );

		/* Sending a notification while the task is suspended should pass, but
		not cause the task to resume. */
		xTaskNotifyIndexed( xTaskToNotify, uxIndexToNotify, 1, eSetValueWithOverwrite );

		/* Use the next task notification within the array of task notifications
		the next time around. */
		uxIndexToNotify++;
		if( uxIndexToNotify >= configTASK_NOTIFICATION_ARRAY_ENTRIES )
		{
			uxIndexToNotify = 0;
		}

		/* Make sure giving the notification didn't resume the task. */
		configASSERT( eTaskGetState( xTaskToNotify ) == eSuspended );

		vTaskResume( xTaskToNotify );
	}

	ulCallCount++;
}
/*-----------------------------------------------------------*/

static void prvNotifyingTimerCallback( TimerHandle_t xNotUsed )
{
static BaseType_t uxIndexToNotify = 0;

	( void ) xNotUsed;

	/* "Give" the task notification (which increments the target task
	notification value) at index uxIndexToNotify within the array of task
	notifications. */
	xTaskNotifyGiveIndexed( xTaskToNotify, uxIndexToNotify );

	/* Use the next task notification within the array of task notifications the
	next time around. */
	uxIndexToNotify++;
	if( uxIndexToNotify >= configTASK_NOTIFICATION_ARRAY_ENTRIES )
	{
		uxIndexToNotify = 0;
	}
}
/*-----------------------------------------------------------*/

static void prvTestNotifyTaskWhileSuspended( void )
{
UBaseType_t uxIndexToTest, uxOtherIndexes;
BaseType_t xReturned;
uint32_t ulNotifiedValue;

	/* Raise the task's priority so it can suspend itself before the timer
	expires. */
	vTaskPrioritySet( NULL, configMAX_PRIORITIES - 1 );

	/* Perform the test on each task notification within the array or task
	notifications. */
	for( uxIndexToTest = 0; uxIndexToTest < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxIndexToTest++ )
	{
		/* Ensure no notifications within the array of task notifications are
		pending. */
		for( uxOtherIndexes = 0; uxOtherIndexes < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxOtherIndexes++ )
		{
			xReturned = xTaskNotifyWaitIndexed( uxOtherIndexes, 0, 0, NULL, 0 );
			configASSERT( xReturned == pdFALSE );
			( void ) xReturned; /* Remove compiler warnings in case configASSERT() is not defined. */
		}

		/* Start the timer that will try notifying this task while it is
		suspended, then wait for a notification.  The first time the callback
		executes the timer will suspend the task, then resume the task, without
		ever sending a notification to the task. */
		ulNotifiedValue = 0;
		xTimerStart( xNotifyWhileSuspendedTimer, portMAX_DELAY );

		/* Check a notification is not received on the task notification at
		index uxIndexToTest within the array of task notifications. */
		xReturned = xTaskNotifyWaitIndexed( uxIndexToTest, 0, 0, &ulNotifiedValue, portMAX_DELAY );
		configASSERT( xReturned == pdFALSE );
		configASSERT( ulNotifiedValue == 0 );
		( void ) xReturned; /* Remove compiler warnings in case configASSERT() is not defined. */

		/* Check none of the task notifications within the array of task
		notifications as been notified. */
		for( uxOtherIndexes = 0; uxOtherIndexes < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxOtherIndexes++ )
		{
			xReturned = xTaskNotifyWaitIndexed( uxOtherIndexes, 0, 0, &ulNotifiedValue, 0 );
			configASSERT( xReturned == pdFALSE );
			( void ) xReturned; /* Remove compiler warnings in case configASSERT() is not defined. */
		}

		/* Start the timer that will try notifying this task while it is
		suspended, then wait for a notification at index uxIndexToTest within
		the array of task notifications.  The second time the callback executes
		the timer will suspend the task, notify the task, then resume the task
		(previously it was suspended and resumed without being notified). */
		xTimerStart( xNotifyWhileSuspendedTimer, portMAX_DELAY );

		/* Check a notification is only received in the index within the array
		of task notifications under test. */
		xReturned = xTaskNotifyWaitIndexed( uxIndexToTest, 0, 0, &ulNotifiedValue, portMAX_DELAY );
		configASSERT( xReturned == pdPASS );
		( void ) xReturned; /* Remove compiler warnings in case configASSERT() is not defined. */
		configASSERT( ulNotifiedValue != 0 );

		/* Check a notification is not received in any index within the array
		of task notifications at and below the index being tested have a notification
		value, and that indexes above the index being tested to not have
		notification values. */
		for( uxOtherIndexes = 0; uxOtherIndexes < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxOtherIndexes++ )
		{
			xReturned = xTaskNotifyWaitIndexed( uxOtherIndexes, 0, 0, &ulNotifiedValue, 0 );
			configASSERT( xReturned == pdFALSE );

			if( uxOtherIndexes <= uxIndexToTest )
			{
				configASSERT( ulNotifiedValue == 1 );
			}
			else
			{
				configASSERT( ulNotifiedValue == 0 );
			}
			( void ) xReturned; /* Remove compiler warnings in case configASSERT() is not defined. */
			( void ) ulNotifiedValue;
		}
	}

	/* Return the task to its proper priority */
	vTaskPrioritySet( NULL, notifyTASK_PRIORITY );

	/* Incremented to show the task is still running. */
	ulFineCycleCount++;

	/* Leave all bits cleared. */
	for( uxIndexToTest = 0; uxIndexToTest < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxIndexToTest++ )
	{
		xTaskNotifyWaitIndexed( uxIndexToTest, notifyUINT32_MAX, 0, NULL, 0 );
	}
}
/* ------------------------------------------------------------------------ */

static void prvBlockOnTheNotifiedIndexed( void )
{
const TickType_t xTimerPeriod = pdMS_TO_TICKS( 100 ), xMargin = pdMS_TO_TICKS( 50 ), xDontBlock = 0;
UBaseType_t uxIndex, uxIndexToNotify;
uint32_t ulReceivedValue;
BaseType_t xReturned;

	/* Set the value of each notification in the array of task notifications to
	the value of its index position plus 1 so everything starts in a known
	state, then clear the notification state ready for the next test.  Plus 1 is
	used because the index under test will use 0. */
	for( uxIndex = 0; uxIndex < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxIndex++ )
	{
		xTaskNotifyIndexed( xTaskToNotify, uxIndex, uxIndex + 1, eSetValueWithOverwrite );
		xTaskNotifyStateClearIndexed( xTaskToNotify, uxIndex );
	}

	/* Peform the test on each task notification within the array of task
	notifications. */
	for( uxIndexToNotify = 0; uxIndexToNotify < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxIndexToNotify++ )
	{
		/* Set the notification value of the index being tested to 0 so the
		notification value increment/decrement functions can be tested. */
		xTaskNotifyIndexed( xTaskToNotify, uxIndexToNotify, 0, eSetValueWithOverwrite );
		xTaskNotifyStateClearIndexed( xTaskToNotify, uxIndexToNotify );

		/* Start the software timer then wait for it to notify this task.  Block
		on the notification index we expect to receive the notification on.  The
		margin is to ensure the task blocks longer than the timer period. */
		xTimerStart( xIncrementingIndexTimer, portMAX_DELAY );
		ulReceivedValue = ulTaskNotifyTakeIndexed( uxIndexToNotify, pdFALSE, xTimerPeriod + xMargin );

		/* The notification value was initially zero, and should have been
		incremented by the software timer, so now one.  It will also have been
		decremented again by the call to ulTaskNotifyTakeIndexed() so gone back
		to 0. */
		configASSERT( ulReceivedValue == 1UL );
		( void ) ulReceivedValue; /* Remove compiler warnings in case configASSERT() is not defined. */

		/* No other notification indexes should have changed, and therefore should
		still have their value set to their index plus 1 within the array of
		notifications. */
		for( uxIndex = 0; uxIndex < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxIndex++ )
		{
			if( uxIndex != uxIndexToNotify )
			{
				xReturned = xTaskNotifyWaitIndexed( uxIndex, 0, 0, &ulReceivedValue, xDontBlock );
				configASSERT( xReturned == pdFALSE );
				configASSERT( ulReceivedValue == ( uxIndex + 1 ) );
				( void ) ulReceivedValue; /* Remove compiler warnings in case configASSERT() is not defined. */
				( void ) xReturned;
			}
		}

		/* Reset the notification value for the index just tested back to the
		index value plus 1 ready for the next iteration around this loop. */
		xTaskNotifyIndexed( xTaskToNotify, uxIndexToNotify, uxIndexToNotify + 1, eSetValueWithOverwrite );
		xTaskNotifyStateClearIndexed( xTaskToNotify, uxIndexToNotify );

		/* Incremented to show the task is still running. */
		ulFineCycleCount++;
	}
}
/* ------------------------------------------------------------------------ */

static void prvBlockOnANonNotifiedIndexed( void )
{
const TickType_t xTimerPeriod = pdMS_TO_TICKS( 100 ), xMargin = pdMS_TO_TICKS( 50 ), xDontBlock = 0;
UBaseType_t uxIndex, uxIndexToNotify;
uint32_t ulReceivedValue;
BaseType_t xReturned;
TickType_t xTimeBeforeBlocking, xTimeNow, xTimeDifference;

	/* Set all notify values within the array of tasks notifications to zero
	ready for the next test. */
	for( uxIndexToNotify = 0; uxIndexToNotify < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxIndexToNotify++ )
	{
		ulTaskNotifyValueClearIndexed( xTaskToNotify, uxIndexToNotify, notifyUINT32_MAX );
	}

	/* Perform the test for each notification within the array of task
	notifications. */
	for( uxIndexToNotify = 0; uxIndexToNotify < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxIndexToNotify++ )
	{
		/* Start the software timer then wait for it to notify this task.  Block
		on a notification index that we do not expect to receive the notification
		on.  The margin is to ensure the task blocks longer than the timer period. */
		xTimerStart( xIncrementingIndexTimer, portMAX_DELAY );
		xTimeBeforeBlocking = xTaskGetTickCount();


		if( uxIndexToNotify == ( configTASK_NOTIFICATION_ARRAY_ENTRIES - 1 ) )
		{
			/* configTASK_NOTIFICATION_ARRAY_ENTRIES - 1 is to be notified, so
			block on index 0. */
			uxIndex = 0;
		}
		else
		{
			/* The next index to get notified will be uxIndexToNotify, so block
			on uxIndexToNotify + 1 */
			uxIndex = uxIndexToNotify + 1;
		}

		xReturned = xTaskNotifyWaitIndexed( uxIndex, 0, 0, &ulReceivedValue, xTimerPeriod + xMargin );

		/* The notification will have been sent to task notification at index
		uxIndexToNotify in this task by the timer callback after xTimerPeriodTicks.
		The notification should not have woken this task, so xReturned should
		be false and at least xTimerPeriod + xMargin ticks should have passed. */
		configASSERT( xReturned == pdFALSE );
		xTimeNow = xTaskGetTickCount();
		xTimeDifference = xTimeNow - xTimeBeforeBlocking;
		configASSERT( xTimeDifference >= ( xTimerPeriod + xMargin ) );
		( void ) xReturned; /* Remove compiler warnings if configASSERT() is not defined. */
		( void ) xTimeBeforeBlocking;
		( void ) xTimeDifference;

		/* Only the notification at index position uxIndexToNotify should be
		set.  Calling this function will clear it again. */
		for( uxIndex = 0; uxIndex < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxIndex++ )
		{
			xReturned = xTaskNotifyWaitIndexed( uxIndex, 0, 0, &ulReceivedValue, xDontBlock );

			if( uxIndex == uxIndexToNotify )
			{
				/* Expect the notification state to be set and the notification
				value to have been incremented. */
				configASSERT( xReturned == pdTRUE );
				configASSERT( ulReceivedValue == 1 );

				/* Set the notification value for this array index back to 0. */
				ulTaskNotifyValueClearIndexed( xTaskToNotify, uxIndex, notifyUINT32_MAX );
			}
			else
			{
				/* Expect the notification state to be clear and the notification
				value to remain at zer0. */
				configASSERT( xReturned == pdFALSE );
				configASSERT( ulReceivedValue == 0 );
			}
		}

		/* Incremented to show the task is still running. */
		ulFineCycleCount++;
	}
}
/* ------------------------------------------------------------------------ */

static void prvBlockOnNotificationsComingFromInterrupts( void )
{
UBaseType_t uxIndex, uxIndexToNotify;
uint32_t ulReceivedValue;
BaseType_t xReturned;
const TickType_t xDontBlock = 0;

	/* Set the value of each notification within the array of task notifications
	to zero so the task can block on xTaskNotifyTake(). */
	for( uxIndex = 0; uxIndex < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxIndex++ )
	{
		xTaskNotifyIndexed( xTaskToNotify, uxIndex, 0, eSetValueWithOverwrite );
		xTaskNotifyStateClearIndexed( xTaskToNotify, uxIndex );
	}

	/* Perform the test on each task notification within the array of task
	notifications. */
	for( uxIndexToNotify = 0; uxIndexToNotify < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxIndexToNotify++ )
	{
		/* Tell the interrupt to send the next notification. */
		taskENTER_CRITICAL();
		{
			/* Don't expect to find xSendNotificationFromISR set at this time as
			the interrupt should have cleared it back to pdFALSE last time it
			executed. */
			configASSERT( xSendNotificationFromISR == pdFALSE );
			xSendNotificationFromISR = pdTRUE;
		}
		taskEXIT_CRITICAL();

		/* Wait for a notification on the task notification at index
		uxIndexToNotify within the array of task notifications. */
		ulReceivedValue = ulTaskNotifyTakeIndexed( uxIndexToNotify, pdTRUE, portMAX_DELAY );

		/* Interrupt should have reset xSendNotificationFromISR after it sent
		the notificatino. */
		configASSERT( xSendNotificationFromISR == pdFALSE );

		/* The notification value was initially zero, and should have been
		incremented by the interrupt, so now one. */
		configASSERT( ulReceivedValue == 1UL );
		( void ) ulReceivedValue; /* Remove compiler warnings in case configASSERT() is not defined. */

		/* No other notification indexes should have changed, and therefore should
		still have their value set to 0.  The value in array index uxIndexToNotify
		should also have been decremented back to zero by the call to
		ulTaskNotifyTakeIndexed(). */
		for( uxIndex = 0; uxIndex < configTASK_NOTIFICATION_ARRAY_ENTRIES; uxIndex++ )
		{
			xReturned = xTaskNotifyWaitIndexed( uxIndexToNotify, 0, 0, &ulReceivedValue, xDontBlock );
			configASSERT( xReturned == pdFALSE );
			configASSERT( ulReceivedValue == 0 );
			( void ) ulReceivedValue; /* Remove compiler warnings in case configASSERT() is not defined. */
			( void ) xReturned;
		}

		/* Incremented to show the task is still running. */
		ulFineCycleCount++;
	}
}
/*-----------------------------------------------------------*/

void xNotifyArrayTaskFromISR( void )
{
static BaseType_t xAPIToUse = 0;
uint32_t ulPreviousValue;
const uint32_t ulUnexpectedValue = 0xff;
static UBaseType_t uxIndexToNotify = 0;

	/* Check the task notification demo task was actually created. */
	configASSERT( xTaskToNotify );

	/* The task sets xSendNotificationFromISR to pdTRUE each time it wants this
	interrupt (this function runs in the RTOS tick hook) to send the next
	notification. */
	if( xSendNotificationFromISR == pdTRUE )
	{
		xSendNotificationFromISR = pdFALSE;

		/* Test using both vTaskNotifyGiveFromISR(), xTaskNotifyFromISR()
		and xTaskNotifyAndQueryFromISR(). The notification is set to the task
		notification at index uxIndexToNotify within the array of task
		notifications. */
		switch( xAPIToUse )
		{
			case 0:	vTaskNotifyGiveIndexedFromISR( xTaskToNotify, uxIndexToNotify, NULL );
					xAPIToUse++;
					break;

			case 1:	xTaskNotifyIndexedFromISR( xTaskToNotify, uxIndexToNotify, 0, eIncrement, NULL );
					xAPIToUse++;
					break;

			case 2: ulPreviousValue = ulUnexpectedValue;
					xTaskNotifyAndQueryIndexedFromISR( xTaskToNotify, uxIndexToNotify, 0, eIncrement, &ulPreviousValue, NULL );
					configASSERT( ulPreviousValue == 0 );
					xAPIToUse = 0;
					break;

			default:/* Should never get here!. */
					break;
		}

		/* Use the next index in the array of task notifications the next time
		around. */
		uxIndexToNotify++;
		if( uxIndexToNotify >= configTASK_NOTIFICATION_ARRAY_ENTRIES )
		{
			uxIndexToNotify = 0;
		}
	}
}
/*-----------------------------------------------------------*/

/* This is called to check the created tasks are still running and have not
detected any errors. */
BaseType_t xAreTaskNotificationArrayTasksStillRunning( void )
{
static uint32_t ulLastFineCycleCount = 0, ulLastCourseCycleCount = 0, ulCallCount = 0;
const uint32_t ulCallsBetweenCourseCycleCountChecks = 3UL;
static BaseType_t xErrorStatus = pdPASS;

	/* Check the cycle count is still incrementing to ensure the task is still
	actually running.  The fine counter is incremented within individual test
	functions.  The course counter is incremented one each time all the test
	functions have been executed to ensure all the tests are running. */
	if( ulLastFineCycleCount == ulFineCycleCount )
	{
		xErrorStatus = pdFAIL;
	}
	else
	{
		ulLastFineCycleCount = ulFineCycleCount;
	}

	ulCallCount++;
	if( ulCallCount >= ulCallsBetweenCourseCycleCountChecks )
	{
		ulCallCount = 0;
		if( ulLastCourseCycleCount == ulCourseCycleCounter )
		{
			xErrorStatus = pdFAIL;
		}
		else
		{
			ulLastCourseCycleCount = ulCourseCycleCounter;
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
