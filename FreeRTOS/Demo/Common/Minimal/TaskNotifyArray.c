/*
 * FreeRTOS Kernel V10.3.0
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
 * Tests the behaviour of direct task notifications.
 */

/* Standard includes. */
#include <limits.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "timers.h"

/* Demo program include files. */
#include "TaskNotifyArray.h"

#if( configNUMBER_OF_TASK_NOTIFICATIONS < 2 )
	#error This file is intended to test direct to task notification arrays but the array does not contain more than one index.
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

void vStartTaskNotifyArrayTask( void  )
{
	/* Create the task that performs some tests by itself, then loops around
	being notified by both a software timer and an interrupt. */
	xTaskCreate( prvNotifiedTask, /* Function that implements the task. */
				 "ArrayNotifed", /* Text name for the task - for debugging only - not used by the kernel. */
				 notifyNOTIFY_ARRAY_TASK_STACK_SIZE, /* Task's stack size in words, not bytes!. */
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
UBaseType_t uxIndexToTest, uxOtherIndexes;


	/* ------------------------------------------------------------------------
	Check blocking when there are no notifications. */
	for( uxIndexToTest = 0; uxIndexToTest < configNUMBER_OF_TASK_NOTIFICATIONS; uxIndexToTest++ )
	{
		/* Send notifications to all array indexes other than the one on which
		this task will block. */
		for( uxOtherIndexes = 0; uxOtherIndexes < configNUMBER_OF_TASK_NOTIFICATIONS; uxOtherIndexes++ )
		{
			if( uxOtherIndexes != uxIndexToTest )
			{
				xTaskNotifyArray( xTaskToNotify, uxOtherIndexes, 0, eNoAction );
			}
		}

		xTimeOnEntering = xTaskGetTickCount();
		xReturned = xTaskNotifyArrayWait( uxIndexToTest, notifyUINT32_MAX, 0, &ulNotifiedValue, xTicksToWait );
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

		/* Clear all the other notifications again ready for the next round. */
		for( uxOtherIndexes = 0; uxOtherIndexes < configNUMBER_OF_TASK_NOTIFICATIONS; uxOtherIndexes++ )
		{
			if( uxOtherIndexes != uxIndexToTest )
			{
				xReturned = xTaskNotifyArrayStateClear( xTaskToNotify, uxOtherIndexes );

				/* The notification state was set in the outer loop so expect
				it to still be set. */
				configASSERT( xReturned == pdTRUE );
				( void ) xReturned; /* In case configASSERT() is not defined. */
			}
		}
	}



	/* ------------------------------------------------------------------------
	Check no blocking when notifications are pending. */
	for( uxIndexToTest = 0; uxIndexToTest < configNUMBER_OF_TASK_NOTIFICATIONS; uxIndexToTest++ )
	{
		/* First notify itself - this would not be a normal thing to do and is
		done here for test purposes only. */
		xReturned = xTaskNotifyArrayAndQuery( xTaskToNotify, uxIndexToTest, ulFirstNotifiedConst, eSetValueWithoutOverwrite, &ulPreviousValue );

		/* Even through the 'without overwrite' action was used the update should
		have been successful. */
		configASSERT( xReturned == pdPASS );
		( void ) xReturned; /* In case configASSERT() is not defined. */

		/* No bits should have been pending previously. */
		configASSERT( ulPreviousValue == 0 );
		( void ) ulPreviousValue;

		/* The task should now have a notification pending, and so not time out. */
		xTimeOnEntering = xTaskGetTickCount();
		xReturned = xTaskNotifyArrayWait( uxIndexToTest, notifyUINT32_MAX, 0, &ulNotifiedValue, xTicksToWait );

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
	}




	/*-------------------------------------------------------------------------
	Check the non-overwriting functionality. */
	for( uxIndexToTest = 0; uxIndexToTest < configNUMBER_OF_TASK_NOTIFICATIONS; uxIndexToTest++ )
	{
		/* Send notifications to all array indexes other than the one on which
		this task will block. */
		for( uxOtherIndexes = 0; uxOtherIndexes < configNUMBER_OF_TASK_NOTIFICATIONS; uxOtherIndexes++ )
		{
			if( uxOtherIndexes != uxIndexToTest )
			{
				xTaskNotifyArray( xTaskToNotify, uxOtherIndexes, ulFirstNotifiedConst, eSetValueWithOverwrite );
			}
		}

		/* The notification is done twice using two different notification
		values.  The action says don't overwrite so only the first notification
		should pass and the value read back should also be that used with the
		first notification. */
		xReturned = xTaskNotifyArray( xTaskToNotify, uxIndexToTest, ulFirstNotifiedConst, eSetValueWithoutOverwrite );
		configASSERT( xReturned == pdPASS );
		( void ) xReturned; /* In case configASSERT() is not defined. */

		xReturned = xTaskNotifyArray( xTaskToNotify, uxIndexToTest, ulSecondNotifiedValueConst, eSetValueWithoutOverwrite );
		configASSERT( xReturned == pdFAIL );
		( void ) xReturned; /* In case configASSERT() is not defined. */

		/* Waiting for the notification should now return immediately so a block
		time of zero is used. */
		xReturned = xTaskNotifyArrayWait( uxIndexToTest, notifyUINT32_MAX, 0, &ulNotifiedValue, 0 );

		configASSERT( xReturned == pdPASS );
		configASSERT( ulNotifiedValue == ulFirstNotifiedConst );
		( void ) xReturned; /* In case configASSERT() is not defined. */
		( void ) ulNotifiedValue;

		/* Clear all the other notifications again ready for the next round. */
		for( uxOtherIndexes = 0; uxOtherIndexes < configNUMBER_OF_TASK_NOTIFICATIONS; uxOtherIndexes++ )
		{
			if( uxOtherIndexes != uxIndexToTest )
			{
				xReturned = xTaskNotifyArrayStateClear( xTaskToNotify, uxOtherIndexes );

				/* The notification state in all the other indexes was set at
				the start of the outer loop, so expect it to still be set. */
				configASSERT( xReturned == pdTRUE );
				( void ) xReturned; /* In case configASSERT() is not defined. */

				ulNotifiedValue = ulTaskNotifyArrayValueClear( xTaskToNotify, uxOtherIndexes, notifyUINT32_MAX );

				/* The notification value was set to ulFirstNotifiedConst in all
				the other indexes by the outer loop, so expect it to still have
				that value. */
				configASSERT( ulNotifiedValue == ulFirstNotifiedConst );
				( void ) ulNotifiedValue; /* In case configASSERT() is not defined. */
			}
		}
	}




	/*-------------------------------------------------------------------------
	Do the same again, only this time use the overwriting version.  This time
	both notifications should pass, and the value written the second time should
	overwrite the value written the first time, and so be the value that is read
	back. */
	for( uxIndexToTest = 0; uxIndexToTest < configNUMBER_OF_TASK_NOTIFICATIONS; uxIndexToTest++ )
	{
		for( uxOtherIndexes = 0; uxOtherIndexes < configNUMBER_OF_TASK_NOTIFICATIONS; uxOtherIndexes++ )
		{
			if( uxOtherIndexes != uxIndexToTest )
			{
				xTaskNotifyArray( xTaskToNotify, uxOtherIndexes, ulFirstNotifiedConst, eSetValueWithOverwrite );
			}
		}

		xReturned = xTaskNotifyArray( xTaskToNotify, uxIndexToTest, ulFirstNotifiedConst, eSetValueWithOverwrite );
		configASSERT( xReturned == pdPASS );
		( void ) xReturned; /* In case configASSERT() is not defined. */
		xReturned = xTaskNotifyArray( xTaskToNotify, uxIndexToTest, ulSecondNotifiedValueConst, eSetValueWithOverwrite );
		configASSERT( xReturned == pdPASS );
		( void ) xReturned; /* In case configASSERT() is not defined. */
		xReturned = xTaskNotifyArrayWait( uxIndexToTest, 0, notifyUINT32_MAX, &ulNotifiedValue, 0 );
		configASSERT( xReturned == pdPASS );
		( void ) xReturned; /* In case configASSERT() is not defined. */
		configASSERT( ulNotifiedValue == ulSecondNotifiedValueConst );
		( void ) ulNotifiedValue;

		for( uxOtherIndexes = 0; uxOtherIndexes < configNUMBER_OF_TASK_NOTIFICATIONS; uxOtherIndexes++ )
		{
			if( uxOtherIndexes != uxIndexToTest )
			{
				xReturned = xTaskNotifyArrayStateClear( xTaskToNotify, uxOtherIndexes );
				configASSERT( xReturned == pdTRUE );
				( void ) xReturned; /* In case configASSERT() is not defined. */
				ulNotifiedValue = ulTaskNotifyArrayValueClear( xTaskToNotify, uxOtherIndexes, notifyUINT32_MAX );
				configASSERT( ulNotifiedValue == ulFirstNotifiedConst );
				( void ) ulNotifiedValue; /* In case configASSERT() is not defined. */
			}
		}
	}




	/*-------------------------------------------------------------------------
	Check notifications with no action pass without updating the value. */
	for( uxIndexToTest = 0; uxIndexToTest < configNUMBER_OF_TASK_NOTIFICATIONS; uxIndexToTest++ )
	{
		/* First the notification values to ulSecondNotifiedValueConst. */
		xReturned = xTaskNotifyArray( xTaskToNotify, uxIndexToTest, ulSecondNotifiedValueConst, eSetValueWithOverwrite );
		configASSERT( xReturned == pdPASS );
		( void ) xReturned; /* In case configASSERT() is not defined. */

		/* Even though ulFirstNotifiedConst is used as the value next the value
		read back should remain at ulSecondNotifiedConst. */
		xReturned = xTaskNotifyArray( xTaskToNotify, uxIndexToTest, ulFirstNotifiedConst, eNoAction );
		configASSERT( xReturned == pdPASS );
		( void ) xReturned; /* In case configASSERT() is not defined. */

		/* All array indexes up to and including uxIndexToTest should still
		contain the same value. */
		for( uxOtherIndexes = 0; uxOtherIndexes <= uxIndexToTest; uxOtherIndexes++ )
		{
			/* First zero is bits to clear on entry, the second is bits to clear on
			exist, the last 0 is the block time. */
			xReturned = xTaskNotifyArrayWait( uxOtherIndexes, 0, 0, &ulNotifiedValue, 0 );
			configASSERT( ulNotifiedValue == ulSecondNotifiedValueConst );
			( void ) ulNotifiedValue; /* In case configASSERT() is not defined. */
		}

		/* All array indexes after uxIndexToTest should still contain 0 as they
		have not been set in this loop yet.  This time use xTaskNotifyValueClear()
		instead of xTaskNotifyArrayWait(), just for test coverage. */
		for( uxOtherIndexes = uxIndexToTest + 1; uxOtherIndexes < configNUMBER_OF_TASK_NOTIFICATIONS; uxOtherIndexes++ )
		{
			/* This time 0 is the bits to clear parameter - so clearing no bits. */
			ulNotifiedValue = ulTaskNotifyArrayValueClear( NULL, uxOtherIndexes, 0 );
			configASSERT( ulNotifiedValue == 0 );
			( void ) ulNotifiedValue; /* In case configASSERT() is not defined. */
		}
	}




	/*-------------------------------------------------------------------------
	Check incrementing values.  Send ulMaxLoop increment notifications, then
	ensure the received value is as expected - which should be
	ulSecondNotificationValueConst plus how ever many times to loop iterated. */
	for( uxIndexToTest = 0; uxIndexToTest < configNUMBER_OF_TASK_NOTIFICATIONS; uxIndexToTest++ )
	{
		for( ulLoop = 0; ulLoop < ulMaxLoops; ulLoop++ )
		{
			xReturned = xTaskNotifyArray( xTaskToNotify, uxIndexToTest, 0, eIncrement );
			configASSERT( xReturned == pdPASS );
			( void ) xReturned; /* In case configASSERT() is not defined. */
		}

		/* All array indexes up to and including uxIndexToTest should still
		contain the updated value. */
		for( uxOtherIndexes = 0; uxOtherIndexes <= uxIndexToTest; uxOtherIndexes++ )
		{
			/* First zero is bits to clear on entry, the second is bits to clear on
			exist, the last 0 is the block time. */
			xReturned = xTaskNotifyArrayWait( uxOtherIndexes, 0, 0, &ulNotifiedValue, 0 );
			configASSERT( ulNotifiedValue == ( ulSecondNotifiedValueConst + ulMaxLoops ) );
			( void ) ulNotifiedValue; /* In case configASSERT() is not defined. */
		}

		/* Should not be any notifications pending now. */
		xReturned = xTaskNotifyArrayWait( uxIndexToTest, 0, 0, &ulNotifiedValue, 0 );
		configASSERT( xReturned == pdFAIL );
		( void ) xReturned; /* In case configASSERT() is not defined. */
		( void ) ulNotifiedValue;

		/* All array indexes after uxIndexToTest should still contain the
		un-incremented ulSecondNotifiedValueConst as they have not been set in
		this loop yet.  This time use xTaskNotifyValueClear() instead of
		xTaskNotifyArrayWait(), just for test coverage. */
		for( uxOtherIndexes = uxIndexToTest + 1; uxOtherIndexes < configNUMBER_OF_TASK_NOTIFICATIONS; uxOtherIndexes++ )
		{
			/* This time 0 is the bits to clear parameter - so clearing no bits. */
			ulNotifiedValue = ulTaskNotifyArrayValueClear( NULL, uxOtherIndexes, 0 );
			configASSERT( ulNotifiedValue == ulSecondNotifiedValueConst );
			( void ) ulNotifiedValue; /* In case configASSERT() is not defined. */
		}
	}

	/* Clear all bits ready for next test. */
	for( uxIndexToTest = 0; uxIndexToTest < configNUMBER_OF_TASK_NOTIFICATIONS; uxIndexToTest++ )
	{
		/* Start with all bits clear. */
		ulTaskNotifyArrayValueClear( NULL, uxIndexToTest, notifyUINT32_MAX );
	}



	/*-------------------------------------------------------------------------
	Check all bits can be set by notifying the task with one additional bit	set
	on each notification, and exiting the loop when all the bits are found to be
	set.  As there are 32-bits the loop should execute 32 times before all the
	bits are found to be set. */
	for( uxIndexToTest = 0; uxIndexToTest < configNUMBER_OF_TASK_NOTIFICATIONS; uxIndexToTest++ )
	{
		ulNotifyingValue = 0x01;
		ulLoop = 0;

		do
		{
			/* Set the next bit in the task's notified value. */
			xTaskNotifyArray( xTaskToNotify, uxIndexToTest, ulNotifyingValue, eSetBits );

			/* Wait for the notified value - which of course will already be
			available.  Don't clear the bits on entry or exit as this loop is
			exited when all the bits are set. */
			xReturned = xTaskNotifyArrayWait( uxIndexToTest, 0, 0, &ulNotifiedValue, 0 );
			configASSERT( xReturned == pdPASS );
			( void ) xReturned; /* In case configASSERT() is not defined. */

			ulLoop++;

			/* Use the next bit on the next iteration around this loop. */
			ulNotifyingValue <<= 1UL;

		} while ( ulNotifiedValue != notifyUINT32_MAX );

		/* As a 32-bit value was used the loop should have executed 32 times before
		all the bits were set. */
		configASSERT( ulLoop == 32 );

		/* All array indexes up to and including uxIndexToTest should still
		have all bits set. */
		for( uxOtherIndexes = 0; uxOtherIndexes <= uxIndexToTest; uxOtherIndexes++ )
		{
			/* First zero is bits to clear on entry, the second is bits to clear on
			exist, the last 0 is the block time. */
			xReturned = xTaskNotifyArrayWait( uxOtherIndexes, 0, 0, &ulNotifiedValue, 0 );
			configASSERT( ulNotifiedValue == notifyUINT32_MAX );
			( void ) ulNotifiedValue; /* In case configASSERT() is not defined. */
		}

		/* All array indexes after uxIndexToTest should still contain 0 as they
		have not been set in this loop yet.  This time use xTaskNotifyValueClear()
		instead of xTaskNotifyArrayWait(), just for test coverage. */
		for( uxOtherIndexes = uxIndexToTest + 1; uxOtherIndexes < configNUMBER_OF_TASK_NOTIFICATIONS; uxOtherIndexes++ )
		{
			/* This time 0 is the bits to clear parameter - so clearing no bits. */
			ulNotifiedValue = ulTaskNotifyArrayValueClear( NULL, uxOtherIndexes, 0 );
			configASSERT( ulNotifiedValue == 0 );
			( void ) ulNotifiedValue; /* In case configASSERT() is not defined. */
		}
	}



	/*-------------------------------------------------------------------------
	Check bits are cleared on entry but not on exit when a notification fails
	to arrive before timing out - both with and without a timeout value. */
	for( uxIndexToTest = 0; uxIndexToTest < configNUMBER_OF_TASK_NOTIFICATIONS; uxIndexToTest++ )
	{
		/* Wait for the notification again - but this time it is not given by
		anything and should return pdFAIL.  The parameters are set to clear bit zero
		on entry and bit one on exit.  As no notification was received only the bit
		cleared on entry should actually get cleared. */
		xReturned = xTaskNotifyArrayWait( uxIndexToTest, ulBit0, ulBit1, &ulNotifiedValue, xTicksToWait );
		configASSERT( xReturned == pdFAIL );
		( void ) xReturned; /* In case configASSERT() is not defined. */

		/* Notify the task with no action so as not to update the bits even though
		notifyUINT32_MAX is used as the notification value. */
		xTaskNotifyArray( xTaskToNotify, uxIndexToTest, notifyUINT32_MAX, eNoAction );

		/* All array indexes up to and including uxIndexToTest should have the
		modified value.  */
		for( uxOtherIndexes = 0; uxOtherIndexes <= uxIndexToTest; uxOtherIndexes++ )
		{
			/* Reading back the value should find bit 0 is clear, as this was cleared
			on entry, but bit 1 is not clear as it will not have been cleared on exit
			as no notification was received. */
			xReturned = xTaskNotifyArrayWait( uxOtherIndexes, 0x00UL, 0x00UL, &ulNotifiedValue, 0 );
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
			( void ) xReturned; /* In case configASSERT() is not defined. */
		}

		/* All array indexes after uxIndexToTest should still contain notifyUINT32_MAX
		left over from the previous test.  This time use xTaskNotifyValueClear()
		instead of xTaskNotifyArrayWait(), just for test coverage. */
		for( uxOtherIndexes = uxIndexToTest + 1; uxOtherIndexes < configNUMBER_OF_TASK_NOTIFICATIONS; uxOtherIndexes++ )
		{
			/* This time 0 is the bits to clear parameter - so clearing no bits. */
			ulNotifiedValue = ulTaskNotifyArrayValueClear( NULL, uxOtherIndexes, 0 );
			configASSERT( ulNotifiedValue == notifyUINT32_MAX );
			( void ) ulNotifiedValue; /* In case configASSERT() is not defined. */
		}
	}




	/*-------------------------------------------------------------------------
	Now try clearing the bit on exit. */
	for( uxIndexToTest = 0; uxIndexToTest < configNUMBER_OF_TASK_NOTIFICATIONS; uxIndexToTest++ )
	{
		/* The task is notified first. */
		xTaskNotifyArray( xTaskToNotify, uxIndexToTest, 0, eNoAction );
		xTaskNotifyArrayWait( uxIndexToTest, 0x00, ulBit1, &ulNotifiedValue, 0 );

		/* However as the bit is cleared on exit, after the returned notification
		value is set, the returned notification value should not have the bit
		cleared... */
		configASSERT( ulNotifiedValue == ( notifyUINT32_MAX & ~ulBit0 ) );

		/* ...but reading the value back again should find that the bit was indeed
		cleared internally.  The returned value should be pdFAIL however as nothing
		has notified the task in the mean time. */
		xReturned = xTaskNotifyArrayWait( uxIndexToTest, 0x00, 0x00, &ulNotifiedValue, 0 );
		configASSERT( xReturned == pdFAIL );
		configASSERT( ulNotifiedValue == ( notifyUINT32_MAX & ~( ulBit0 | ulBit1 ) ) );
		( void ) xReturned; /* In case configASSERT() is not defined. */

		/* No other indexes should have a notification pending. */
		for( uxOtherIndexes = 0; uxOtherIndexes < configNUMBER_OF_TASK_NOTIFICATIONS; uxOtherIndexes++ )
		{
			if( uxOtherIndexes != uxIndexToTest )
			{
				xReturned = xTaskNotifyArrayWait( uxOtherIndexes, 0x00UL, 0x00UL, &ulNotifiedValue, 0 );
				configASSERT( xReturned == pdFAIL );
				( void ) xReturned; /* In case configASSERT() is not defined. */
			}
		}
	}



	/*-------------------------------------------------------------------------
	Now try querying the previous value while notifying a task. */
	for( uxIndexToTest = 0; uxIndexToTest < configNUMBER_OF_TASK_NOTIFICATIONS; uxIndexToTest++ )
	{
		xTaskNotifyArrayAndQuery( xTaskToNotify, uxIndexToTest, 0x00, eSetBits, &ulPreviousValue );
		configASSERT( ulNotifiedValue == ( notifyUINT32_MAX & ~( ulBit0 | ulBit1 ) ) );

		/* Clear all bits. */
		xTaskNotifyArrayWait( uxIndexToTest, 0x00, notifyUINT32_MAX, &ulNotifiedValue, 0 );
		xTaskNotifyArrayAndQuery( xTaskToNotify, uxIndexToTest, 0x00, eSetBits, &ulPreviousValue );
		configASSERT( ulPreviousValue == 0 );

		ulExpectedValue = 0;
		for( ulLoop = 0x01; ulLoop < 0x80UL; ulLoop <<= 1UL )
		{
			/* Set the next bit up, and expect to receive the last bits set (so
			the previous value will not yet have the bit being set this time
			around). */
			xTaskNotifyArrayAndQuery( xTaskToNotify, uxIndexToTest, ulLoop, eSetBits, &ulPreviousValue );
			configASSERT( ulExpectedValue == ulPreviousValue );
			ulExpectedValue |= ulLoop;
		}
	}


	/* ---------------------------------------------------------------------- */
	for( uxIndexToTest = 0; uxIndexToTest < configNUMBER_OF_TASK_NOTIFICATIONS; uxIndexToTest++ )
	{
		/* Clear the previous notifications. */
		xTaskNotifyArrayWait( uxIndexToTest, notifyUINT32_MAX, 0, &ulNotifiedValue, 0 );
	}

	for( uxIndexToTest = 0; uxIndexToTest < configNUMBER_OF_TASK_NOTIFICATIONS; uxIndexToTest++ )
	{
		/* No task should not have any notifications pending, so an attempt to
		clear the notification state should fail. */
		for( uxOtherIndexes = 0; uxOtherIndexes < configNUMBER_OF_TASK_NOTIFICATIONS; uxOtherIndexes++ )
		{
			configASSERT( xTaskNotifyArrayStateClear( NULL, uxOtherIndexes ) == pdFALSE );
		}

		/* Get the task to notify itself.  This is not a normal thing to do, and
		is only done here for test purposes. */
		xTaskNotifyArrayAndQuery( xTaskToNotify, uxIndexToTest, ulFirstNotifiedConst, eSetValueWithoutOverwrite, &ulPreviousValue );

		/* Now the notification state should be eNotified, so it should now be
		possible to clear the notification state.  Other indexes should still
		not have a notification pending - likewise uxIndexToTest should not have
		a notification pending once it has been cleared. */
		for( uxOtherIndexes = 0; uxOtherIndexes < configNUMBER_OF_TASK_NOTIFICATIONS; uxOtherIndexes++ )
		{
			if( uxOtherIndexes == uxIndexToTest )
			{
				configASSERT( xTaskNotifyArrayStateClear( NULL, uxOtherIndexes ) == pdTRUE );
			}

			configASSERT( xTaskNotifyArrayStateClear( NULL, uxOtherIndexes ) == pdFALSE );
		}
	}


	/* ------------------------------------------------------------------------
	Clear bits in the notification value. */

	for( uxIndexToTest = 0; uxIndexToTest < configNUMBER_OF_TASK_NOTIFICATIONS; uxIndexToTest++ )
	{
		/* Get the task to set all bits its own notification value.  This is not
		a normal thing to do, and is only done here for test purposes. */
		xTaskNotifyArray( xTaskToNotify, uxIndexToTest, notifyUINT32_MAX, eSetBits );

		/* Now clear the top bytes - the returned value from the first call
		should indicate that previously all bits were set. */
		configASSERT( ulTaskNotifyArrayValueClear( xTaskToNotify, uxIndexToTest, notifyUINT32_HIGH_BYTE ) == notifyUINT32_MAX );

		/* Next clear the bottom bytes - the returned value this time should
		indicate that the top byte was clear (before the bottom byte was
		cleared. */
		configASSERT( ulTaskNotifyArrayValueClear( xTaskToNotify, uxIndexToTest, notifyUINT32_LOW_BYTE ) == ( notifyUINT32_MAX & ~notifyUINT32_HIGH_BYTE ) );

		/* Next clear all bytes - the returned value should indicate that previously the
		high and low bytes were clear. */
		configASSERT( ulTaskNotifyArrayValueClear( xTaskToNotify, uxIndexToTest, notifyUINT32_MAX ) == ( notifyUINT32_MAX & ~notifyUINT32_HIGH_BYTE & ~notifyUINT32_LOW_BYTE ) );

		/* Now all bits should be clear. */
		configASSERT( ulTaskNotifyArrayValueClear( xTaskToNotify, uxIndexToTest, notifyUINT32_MAX ) == 0 );
		configASSERT( ulTaskNotifyArrayValueClear( xTaskToNotify, uxIndexToTest, 0UL ) == 0 );
		configASSERT( ulTaskNotifyArrayValueClear( xTaskToNotify, uxIndexToTest, notifyUINT32_MAX ) == 0 );

		/* Now the notification state should be eNotified, so it should now be
		possible to clear the notification state. */
		configASSERT( xTaskNotifyArrayStateClear( NULL, uxIndexToTest ) == pdTRUE );
		configASSERT( xTaskNotifyArrayStateClear( NULL, uxIndexToTest ) == pdFALSE );
	}

	/* ------------------------------------------------------------------------
	Create a timer that will try notifying this task while it is suspended. */
	xSingleTaskTimer = xTimerCreate( "SingleNotify", notifySUSPENDED_TEST_TIMER_PERIOD, pdFALSE, NULL, prvSuspendedTaskTimerTestCallback );
	configASSERT( xSingleTaskTimer );

	/* Raise the task's priority so it can suspend itself before the timer
	expires. */
	vTaskPrioritySet( NULL, configMAX_PRIORITIES - 1 );

	for( uxIndexToTest = 0; uxIndexToTest < configNUMBER_OF_TASK_NOTIFICATIONS; uxIndexToTest++ )
	{
		/* Incremented to show the task is still running. */
		ulNotifyCycleCount++;

		/* Ensure no notifications are pending in any index. */
		for( uxOtherIndexes = 0; uxOtherIndexes < configNUMBER_OF_TASK_NOTIFICATIONS; uxOtherIndexes++ )
		{
			xReturned = xTaskNotifyArrayWait( uxOtherIndexes, 0, 0, NULL, 0 );
			configASSERT( xReturned == pdFALSE );
			( void ) xReturned; /* In case configASSERT() is not defined. */
		}

		/* Start the timer that will try notifying this task while it is
		suspended, then wait for a notification.  The first time the callback
		executes the timer will suspend the task, then resume the task, without
		ever sending a notification to the task. */
		ulNotifiedValue = 0;
		xTimerStart( xSingleTaskTimer, portMAX_DELAY );

		/* Check a notification is not received. */
		xReturned = xTaskNotifyArrayWait( uxIndexToTest, 0, 0, &ulNotifiedValue, portMAX_DELAY );
		configASSERT( xReturned == pdFALSE );
		configASSERT( ulNotifiedValue == 0 );
		( void ) xReturned; /* In case configASSERT() is not defined. */

		/* Check no index has been notified. */
		for( uxOtherIndexes = 0; uxOtherIndexes < configNUMBER_OF_TASK_NOTIFICATIONS; uxOtherIndexes++ )
		{
			xReturned = xTaskNotifyArrayWait( uxOtherIndexes, 0, 0, &ulNotifiedValue, 0 );
			configASSERT( xReturned == pdFALSE );
			( void ) xReturned; /* In case configASSERT() is not defined. */
		}

		/* Incremented to show the task is still running. */
		ulNotifyCycleCount++;

		/* Start the timer that will try notifying this task while it is
		suspended, then wait for a notification.  The second time the callback
		executes the timer will suspend the task, notify the task, then resume the
		task (previously it was suspended and resumed without being notified). */
		xTimerStart( xSingleTaskTimer, portMAX_DELAY );

		/* Check a notification is only received in the index under test. */
		xReturned = xTaskNotifyArrayWait( uxIndexToTest, 0, 0, &ulNotifiedValue, portMAX_DELAY );
		configASSERT( xReturned == pdPASS );
		( void ) xReturned; /* In case configASSERT() is not defined. */
		configASSERT( ulNotifiedValue != 0 );

		/* Check a notification is not received in any index, that indexes at and
		below the index being tested have a notification value, and that indexes
		above the index being tested to not have notification values. */
		for( uxOtherIndexes = 0; uxOtherIndexes < configNUMBER_OF_TASK_NOTIFICATIONS; uxOtherIndexes++ )
		{
			xReturned = xTaskNotifyArrayWait( uxOtherIndexes, 0, 0, &ulNotifiedValue, 0 );
			configASSERT( xReturned == pdFALSE );

			if( uxOtherIndexes <= uxIndexToTest )
			{
				configASSERT( ulNotifiedValue == 1 );
			}
			else
			{
				configASSERT( ulNotifiedValue == 0 );
			}
			( void ) xReturned; /* In case configASSERT() is not defined. */
			( void ) ulNotifiedValue;
		}
	}

	/* Return the task to its proper priority and delete the timer as it is
	not used again. */
	vTaskPrioritySet( NULL, notifyTASK_PRIORITY );
	xTimerDelete( xSingleTaskTimer, portMAX_DELAY );

	/* Incremented to show the task is still running. */
	ulNotifyCycleCount++;

	/* Leave all bits cleared. */
	for( uxIndexToTest = 0; uxIndexToTest < configNUMBER_OF_TASK_NOTIFICATIONS; uxIndexToTest++ )
	{
		xTaskNotifyArrayWait( uxIndexToTest, notifyUINT32_MAX, 0, NULL, 0 );
	}
}
/*-----------------------------------------------------------*/

static void prvSuspendedTaskTimerTestCallback( TimerHandle_t xExpiredTimer )
{
static uint32_t ulCallCount = 0;
static UBaseType_t uxIndexToNotify = 0;

	/* Remove compiler warnings about unused parameters. */
	( void ) xExpiredTimer;

	/* Callback for a timer that is used during preliminary testing.  The timer
	tests the behaviour when 1: a task waiting for a notification is suspended
	and then resumed without ever receiving a notification, and 2: when a task
	waiting for a notification receives a notification while it is suspended.  Run
	one of two tests on every other invocation of this callback. */
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
		not cause the task to resume.  ulCallCount is just used as a convenient
		non-zero value. */
		xTaskNotifyArray( xTaskToNotify, uxIndexToNotify, 1, eSetValueWithOverwrite );
		uxIndexToNotify++;

		/* Make sure giving the notification didn't resume the task. */
		configASSERT( eTaskGetState( xTaskToNotify ) == eSuspended );

		vTaskResume( xTaskToNotify );
	}

	ulCallCount++;
}
/*-----------------------------------------------------------*/

static void prvNotifyingTimer( TimerHandle_t xNotUsed )
{
static BaseType_t uxIndexToNotify = 0;

	( void ) xNotUsed;

	xTaskNotifyArrayGive( xTaskToNotify, uxIndexToNotify );

	/* Use the next notification index on the next invocation of this timer callback,
	wrapping back to 0 when all indexes have been used. */
	uxIndexToNotify++;
	if( uxIndexToNotify >= configNUMBER_OF_TASK_NOTIFICATIONS )
	{
		uxIndexToNotify = 0;
	}
}
/*-----------------------------------------------------------*/

static void prvNotifiedTask( void *pvParameters )
{
const TickType_t xTimerPeriod = pdMS_TO_TICKS( 100 ), xMargin = pdMS_TO_TICKS( 50 ), xDontBlock = 0;
TickType_t xTimeBeforeBlocking;
UBaseType_t uxIndexToNotify = 0, uxIndex;
uint32_t ulReceivedValue;
BaseType_t xReturned;

	/* Remove compiler warnings about unused parameters. */
	( void ) pvParameters;

	/* Run a few tests that can be done from a single task before entering the
	main loop. */
	prvSingleTaskTests();

	/* Set the value of each notification in the array to the value of its index
	position plus 1 so everything starts in a known state, then clear the
	notification state ready for the next test.  Plus 1 is used because the index
	under test will use 0. */
	for( uxIndex = 0; uxIndex < configNUMBER_OF_TASK_NOTIFICATIONS; uxIndex++ )
	{
		xTaskNotifyArray( xTaskToNotify, uxIndex, uxIndex + 1, eSetValueWithOverwrite );
		xTaskNotifyArrayStateClear( xTaskToNotify, uxIndex );
	}

	/* Create the software timer that is used to send notifications to this
	task. */
	xTimer = xTimerCreate( "Notifier", xTimerPeriod, pdFALSE, NULL, prvNotifyingTimer );

	for( ;; )
	{
		for( uxIndexToNotify = 0; uxIndexToNotify < configNUMBER_OF_TASK_NOTIFICATIONS; uxIndexToNotify++ )
		{
			/* Set the notification value of the index being tested to 0 so the
			notification value increment/decrement functions can be tested. */
			xTaskNotifyArray( xTaskToNotify, uxIndexToNotify, 0, eSetValueWithOverwrite );
			xTaskNotifyArrayStateClear( xTaskToNotify, uxIndexToNotify );

			/* Start the software timer then wait for it to notify this task.  Block
			on the notification index we expect to receive the notification on.  The
			margin is to ensure the task blocks longer than the timer period. */
			xTimerStart( xTimer, portMAX_DELAY );
			ulReceivedValue = ulTaskNotifyArrayTake( uxIndexToNotify, pdFALSE, xTimerPeriod + xMargin );

			/* The notification value was initially zero, and should have been
			incremented by the software timer, so now one.  It will also have been
			decremented again by the call to ulTaskNotifyArrayTake() so gone back
			to 0. */
			configASSERT( ulReceivedValue == ( BaseType_t ) 1 );
			( void ) ulReceivedValue; /* In case configASSERT() is not defined. */

			/* No other notification indexes should have changed, and therefore should
			still have their value set to their index plus 1 within the array of
			notifications. */
			for( uxIndex = 0; uxIndex < configNUMBER_OF_TASK_NOTIFICATIONS; uxIndex++ )
			{
				if( uxIndex != uxIndexToNotify )
				{
					xReturned = xTaskNotifyArrayWait( uxIndex, 0, 0, &ulReceivedValue, xDontBlock );
					configASSERT( xReturned == pdFALSE );
					configASSERT( ulReceivedValue == ( uxIndex + 1 ) );
					( void ) ulReceivedValue; /* In case configASSERT() is not defined. */
					( void ) xReturned;
				}
			}

			/* Reset the notification value for the index just tested back to the
			index value plus 1 ready for the next iteration around this loop. */
			xTaskNotifyArray( xTaskToNotify, uxIndexToNotify, uxIndexToNotify + 1, eSetValueWithOverwrite );
			xTaskNotifyArrayStateClear( xTaskToNotify, uxIndexToNotify );
		}

		/* Set all notify values to zero ready for the next test. */
		for( uxIndexToNotify = 0; uxIndexToNotify < configNUMBER_OF_TASK_NOTIFICATIONS; uxIndexToNotify++ )
		{
			ulTaskNotifyArrayValueClear( xTaskToNotify, uxIndexToNotify, notifyUINT32_MAX );
		}

		for( uxIndexToNotify = 0; uxIndexToNotify < configNUMBER_OF_TASK_NOTIFICATIONS; uxIndexToNotify++ )
		{
			/* Start the software timer then wait for it to notify this task.  Block
			on a notification index that we do not expect to receive the notification
			on.  The margin is to ensure the task blocks longer than the timer period. */
			xTimerStart( xTimer, portMAX_DELAY );
			xTimeBeforeBlocking = xTaskGetTickCount();


			if( uxIndexToNotify == ( configNUMBER_OF_TASK_NOTIFICATIONS - 1 ) )
			{
				/* configNUMBER_OF_TASK_NOTIFICATIONS - 1 is to be notified, so
				block on index 0. */
				uxIndex = 0;
			}
			else
			{
				/* The next index to get notified will be uxIndexToNotify, so block
				on uxIndexToNotify + 1 */
				uxIndex = uxIndexToNotify + 1;
			}

			xReturned = xTaskNotifyArrayWait( uxIndex, 0, 0, &ulReceivedValue, xTimerPeriod + xMargin );

			/* The notification will have been sent to this task by the timer
			callback after xTimerPeriodTicks.  The notification should not have
			woken this task, so xReturned should be false and at least xTimerPeriod +
			xMargin ticks should have passed. */
			configASSERT( xReturned == pdFALSE );
			configASSERT( ( xTaskGetTickCount() - xTimeBeforeBlocking ) >= ( xTimerPeriod + xMargin ) );
			( void ) xReturned; /* Remove compiler warnings if configASSERT() is not defined. */
			( void ) xTimeBeforeBlocking;

			/* Only the notification at index position uxIndexToNotify() should be
			set.  Calling this function will clear it again. */
			for( uxIndex = 0; uxIndex < configNUMBER_OF_TASK_NOTIFICATIONS; uxIndex++ )
			{
				xReturned = xTaskNotifyArrayWait( uxIndex, 0, 0, &ulReceivedValue, xDontBlock );

				if( uxIndex == uxIndexToNotify )
				{
					/* Expect the notification state to be set and the notification
					value to have been incremented. */
					configASSERT( xReturned == pdTRUE );
					configASSERT( ulReceivedValue == 1 );

					/* Set the notification value for this array index back to 0. */
					ulTaskNotifyArrayValueClear( xTaskToNotify, uxIndex, notifyUINT32_MAX );
				}
				else
				{
					/* Expect the notification state to be clear and the notification
					value to remain at zer0. */
					configASSERT( xReturned == pdFALSE );
					configASSERT( ulReceivedValue == 0 );
				}
			}
		}
			__asm { NOP };

	}
}
/*-----------------------------------------------------------*/

void xNotifyArrayTaskFromISR( void )
{
static BaseType_t xCallCount = 0, xAPIToUse = 0;
const BaseType_t xCallInterval = pdMS_TO_TICKS( 50 );
uint32_t ulPreviousValue;
const uint32_t ulUnexpectedValue = 0xff;

return;

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
BaseType_t xAreTaskNotificationArrayTasksStillRunning( void )
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
