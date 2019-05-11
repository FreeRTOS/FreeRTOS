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
* This file contains fairly comprehensive checks on the behaviour of event
* groups.  It is not intended to be a user friendly demonstration of the
* event groups API.
*
* NOTE:  The tests implemented in this file are informal 'sanity' tests
* only and are not part of the module tests that make use of the
* mtCOVERAGE_TEST_MARKER macro within the event groups implementation.
*/


/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "event_groups.h"

/* Demo app includes. */
#include "EventGroupsDemo.h"

#if( INCLUDE_eTaskGetState != 1 )
	#error INCLUDE_eTaskGetState must be set to 1 in FreeRTOSConfig.h to use this demo file.
#endif

/* Priorities used by the tasks. */
#define ebSET_BIT_TASK_PRIORITY		( tskIDLE_PRIORITY )
#define ebWAIT_BIT_TASK_PRIORITY	( tskIDLE_PRIORITY + 1 )

/* Generic bit definitions. */
#define ebBIT_0		( 0x01 )
#define ebBIT_1		( 0x02 )
#define ebBIT_2		( 0x04 )
#define ebBIT_3		( 0x08 )
#define ebBIT_4		( 0x10 )
#define ebBIT_5		( 0x20 )
#define ebBIT_6		( 0x40 )
#define ebBIT_7		( 0x80 )

/* Combinations of bits used in the demo. */
#define ebCOMBINED_BITS ( ebBIT_1 | ebBIT_5 | ebBIT_7 )
#define ebALL_BITS ( ebBIT_0 | ebBIT_1 | ebBIT_2 | ebBIT_3 | ebBIT_4 | ebBIT_5 | ebBIT_6 | ebBIT_7 )

/* Associate a bit to each task.  These bits are used to identify all the tasks
that synchronise with the xEventGroupSync() function. */
#define ebSET_BIT_TASK_SYNC_BIT			ebBIT_0
#define ebWAIT_BIT_TASK_SYNC_BIT		ebBIT_1
#define ebRENDESVOUS_TASK_1_SYNC_BIT	ebBIT_2
#define ebRENDESVOUS_TASK_2_SYNC_BIT	ebBIT_3
#define ebALL_SYNC_BITS ( ebSET_BIT_TASK_SYNC_BIT | ebWAIT_BIT_TASK_SYNC_BIT | ebRENDESVOUS_TASK_1_SYNC_BIT | ebRENDESVOUS_TASK_2_SYNC_BIT )

/* A block time of zero simply means "don't block". */
#define ebDONT_BLOCK	( 0 )
#define ebONE_TICK		( ( TickType_t ) 1 )

/* A 5ms delay. */
#define ebSHORT_DELAY	pdMS_TO_TICKS( ( TickType_t ) 5 )

/* Used in the selective bits test which checks no, one or both tasks blocked on
event bits in a group are unblocked as appropriate as different bits get set. */
#define ebSELECTIVE_BITS_1		0x03
#define ebSELECTIVE_BITS_2		0x05

#ifndef ebRENDESVOUS_TEST_TASK_STACK_SIZE
	#define ebRENDESVOUS_TEST_TASK_STACK_SIZE configMINIMAL_STACK_SIZE
#endif

#ifndef ebEVENT_GROUP_SET_BITS_TEST_TASK_STACK_SIZE
	#define ebEVENT_GROUP_SET_BITS_TEST_TASK_STACK_SIZE	configMINIMAL_STACK_SIZE
#endif

/*-----------------------------------------------------------*/

/*
 * NOTE:  The tests implemented in this function are informal 'sanity' tests
 * only and are not part of the module tests that make use of the
 * mtCOVERAGE_TEST_MARKER macro within the event groups implementation.
 *
 * The master test task.  This task:
 *
 * 1) Calls prvSelectiveBitsTestMasterFunction() to test the behaviour when two
 *    tasks are blocked on different bits in an event group.  The counterpart of
 *    this test is implemented by the prvSelectiveBitsTestSlaveFunction()
 *    function (which is called by the two tasks that block on the event group).
 *
 * 2) Calls prvBitCombinationTestMasterFunction() to test the behaviour when
 *    just one task is blocked on various combinations of bits within an event
 *    group.  The counterpart of this test is implemented within the 'test
 *    slave' task.
 *
 * 3) Calls prvPerformTaskSyncTests() to test task synchronisation behaviour.
 */
static void prvTestMasterTask( void *pvParameters );

/*
 * A helper task that enables the 'test master' task to perform several
 * behavioural tests.  See the comments above the prvTestMasterTask() prototype
 * above.
 */
static void prvTestSlaveTask( void *pvParameters );

/*
 * The part of the test that is performed between the 'test master' task and the
 * 'test slave' task to test the behaviour when the slave blocks on various
 * event bit combinations.
 */
static BaseType_t prvBitCombinationTestMasterFunction( BaseType_t xError, TaskHandle_t xTestSlaveTaskHandle );

/*
 * The part of the test that uses all the tasks to test the task synchronisation
 * behaviour.
 */
static BaseType_t prvPerformTaskSyncTests( BaseType_t xError, TaskHandle_t xTestSlaveTaskHandle );

/*
 * Two instances of prvSyncTask() are created.  They start by calling
 * prvSelectiveBitsTestSlaveFunction() to act as slaves when the test master is
 * executing the prvSelectiveBitsTestMasterFunction() function.  They then loop
 * to test the task synchronisation (rendezvous) behaviour.
 */
static void prvSyncTask( void *pvParameters );

/*
 * Functions used in a test that blocks two tasks on various different bits
 * within an event group - then sets each bit in turn and checks that the
 * correct tasks unblock at the correct times.
 */
static BaseType_t prvSelectiveBitsTestMasterFunction( void );
static void prvSelectiveBitsTestSlaveFunction( void );

/*-----------------------------------------------------------*/

/* Variables that are incremented by the tasks on each cycle provided no errors
have been found.  Used to detect an error or stall in the test cycling. */
static volatile uint32_t ulTestMasterCycles = 0, ulTestSlaveCycles = 0, ulISRCycles = 0;

/* The event group used by all the task based tests. */
static EventGroupHandle_t xEventGroup = NULL;

/* The event group used by the interrupt based tests. */
static EventGroupHandle_t xISREventGroup = NULL;

/* Handles to the tasks that only take part in the synchronisation calls. */
static TaskHandle_t xSyncTask1 = NULL, xSyncTask2 = NULL;

/*-----------------------------------------------------------*/

void vStartEventGroupTasks( void )
{
TaskHandle_t xTestSlaveTaskHandle;

	/*
	 * This file contains fairly comprehensive checks on the behaviour of event
	 * groups.  It is not intended to be a user friendly demonstration of the
	 * event groups API.
	 *
	 * NOTE:  The tests implemented in this file are informal 'sanity' tests
	 * only and are not part of the module tests that make use of the
	 * mtCOVERAGE_TEST_MARKER macro within the event groups implementation.
	 *
	 * Create the test tasks as described at the top of this file.
	 */
	xTaskCreate( prvTestSlaveTask, "WaitO", ebRENDESVOUS_TEST_TASK_STACK_SIZE, NULL, ebWAIT_BIT_TASK_PRIORITY, &xTestSlaveTaskHandle );
	xTaskCreate( prvTestMasterTask, "SetB", ebEVENT_GROUP_SET_BITS_TEST_TASK_STACK_SIZE, ( void * ) xTestSlaveTaskHandle, ebSET_BIT_TASK_PRIORITY, NULL );
	xTaskCreate( prvSyncTask, "Rndv", ebRENDESVOUS_TEST_TASK_STACK_SIZE, ( void * ) ebRENDESVOUS_TASK_1_SYNC_BIT, ebWAIT_BIT_TASK_PRIORITY, &xSyncTask1 );
	xTaskCreate( prvSyncTask, "Rndv", ebRENDESVOUS_TEST_TASK_STACK_SIZE, ( void * ) ebRENDESVOUS_TASK_2_SYNC_BIT, ebWAIT_BIT_TASK_PRIORITY, &xSyncTask2 );

	/* If the last task was created then the others will have been too. */
	configASSERT( xSyncTask2 );

	/* Create the event group used by the ISR tests.  The event group used by
	the tasks is created by the tasks themselves. */
	xISREventGroup = xEventGroupCreate();
	configASSERT( xISREventGroup );
}
/*-----------------------------------------------------------*/

static void prvTestMasterTask( void *pvParameters )
{
BaseType_t xError;

/* The handle to the slave task is passed in as the task parameter. */
TaskHandle_t xTestSlaveTaskHandle = ( TaskHandle_t ) pvParameters;

	/* Avoid compiler warnings. */
	( void ) pvParameters;

	/* Create the event group used by the tasks ready for the initial tests. */
	xEventGroup = xEventGroupCreate();
	configASSERT( xEventGroup );

	/* Perform the tests that block two tasks on different combinations of bits,
	then set each bit in turn and check the correct tasks unblock at the correct
	times. */
	xError = prvSelectiveBitsTestMasterFunction();

	for( ;; )
	{
		/* Recreate the event group ready for the next cycle. */
		xEventGroup = xEventGroupCreate();
		configASSERT( xEventGroup );

		/* Perform the tests that check the behaviour when a single task is
		blocked on various combinations of event bits. */
		xError = prvBitCombinationTestMasterFunction( xError, xTestSlaveTaskHandle );

		/* Perform the task synchronisation tests. */
		xError = prvPerformTaskSyncTests( xError, xTestSlaveTaskHandle );

		/* Delete the event group. */
		vEventGroupDelete( xEventGroup );

		/* Now all the other tasks should have completed and suspended
		themselves ready for the next go around the loop. */
		if( eTaskGetState( xTestSlaveTaskHandle ) != eSuspended )
		{
			xError = pdTRUE;
		}

		if( eTaskGetState( xSyncTask1 ) != eSuspended )
		{
			xError = pdTRUE;
		}

		if( eTaskGetState( xSyncTask2 ) != eSuspended )
		{
			xError = pdTRUE;
		}

		/* Only increment the cycle variable if no errors have been detected. */
		if( xError == pdFALSE )
		{
			ulTestMasterCycles++;
		}

		configASSERT( xError == pdFALSE );
	}
}
/*-----------------------------------------------------------*/

static void prvSyncTask( void *pvParameters )
{
EventBits_t uxSynchronisationBit, uxReturned;

	/* A few tests that check the behaviour when two tasks are blocked on
	various different bits within an event group are performed before this task
	enters its infinite loop to carry out its main demo function. */
	prvSelectiveBitsTestSlaveFunction();

	/* The bit to use to indicate this task is at the synchronisation point is
	passed in as the task parameter. */
	uxSynchronisationBit = ( EventBits_t ) pvParameters;

	for( ;; )
	{
		/* Now this task takes part in a task synchronisation - sometimes known
		as a 'rendezvous'.  Its execution pattern is controlled by the 'test
		master' task, which is responsible for taking this task out of the
		Suspended state when it is time to test the synchronisation behaviour.
		See: http://www.freertos.org/xEventGroupSync.html. */
		vTaskSuspend( NULL );

		/* Set the bit that indicates this task is at the synchronisation
		point.  The first time this is done the 'test master' task has a lower
		priority than this task so this task will get to the sync point before
		the set bits task - test this by first calling xEventGroupSync() with
		a zero block time, and a block time that is too short for the other
		task, before calling again with a max delay - the first two calls should
		return before the rendezvous completes, the third only after the
		rendezvous is complete. */
		uxReturned = xEventGroupSync( xEventGroup,	/* The event group used for the synchronisation. */
									  uxSynchronisationBit, /* The bit to set in the event group to indicate this task is at the sync point. */
									  ebALL_SYNC_BITS,/* The bits to wait for - these bits are set by the other tasks taking part in the sync. */
									  ebDONT_BLOCK ); /* The maximum time to wait for the sync condition to be met before giving up. */

		/* No block time was specified, so as per the comments above, the
		rendezvous is not expected to have completed yet. */
		configASSERT( ( uxReturned & ebALL_SYNC_BITS ) != ebALL_SYNC_BITS );

		uxReturned = xEventGroupSync( xEventGroup,	/* The event group used for the synchronisation. */
									  uxSynchronisationBit, /* The bit to set in the event group to indicate this task is at the sync point. */
									  ebALL_SYNC_BITS, /* The bits to wait for - these bits are set by the other tasks taking part in the sync. */
									  ebONE_TICK ); /* The maximum time to wait for the sync condition to be met before giving up. */

		/* A short block time was specified, so as per the comments above, the
		rendezvous is not expected to have completed yet. */
		configASSERT( ( uxReturned & ebALL_SYNC_BITS ) != ebALL_SYNC_BITS );

		uxReturned = xEventGroupSync( xEventGroup,	/* The event group used for the synchronisation. */
									uxSynchronisationBit, /* The bit to set in the event group to indicate this task is at the sync point. */
									ebALL_SYNC_BITS,/* The bits to wait for - these bits are set by the other tasks taking part in the sync. */
									portMAX_DELAY );/* The maximum time to wait for the sync condition to be met before giving up. */

		/* A max delay was used, so this task should only exit the above
		function call when the sync condition is met.  Check this is the
		case. */
		configASSERT( ( uxReturned & ebALL_SYNC_BITS ) == ebALL_SYNC_BITS );

		/* Remove compiler warning if configASSERT() is not defined. */
		( void ) uxReturned;

		/* Wait until the 'test master' task unsuspends this task again. */
		vTaskSuspend( NULL );

		/* Set the bit that indicates this task is at the synchronisation
		point again.  This time the 'test master' task has a higher priority
		than this task so will get to the sync point before this task. */
		uxReturned = xEventGroupSync( xEventGroup, uxSynchronisationBit, ebALL_SYNC_BITS, portMAX_DELAY );

		/* Again a max delay was used, so this task should only exit the above
		function call when the sync condition is met.  Check this is the
		case. */
		configASSERT( ( uxReturned & ebALL_SYNC_BITS ) == ebALL_SYNC_BITS );

		/* Block on the event group again.  This time the event group is going
		to be deleted while this task is blocked on it so it is expected that 0
		be returned. */
		uxReturned = xEventGroupWaitBits( xEventGroup, ebALL_SYNC_BITS, pdFALSE, pdTRUE, portMAX_DELAY );
		configASSERT( uxReturned == 0 );
	}
}
/*-----------------------------------------------------------*/

static void prvTestSlaveTask( void *pvParameters )
{
EventBits_t uxReturned;
BaseType_t xError = pdFALSE;

	/* Avoid compiler warnings. */
	( void ) pvParameters;

	for( ;; )
	{
		/**********************************************************************
		* Part 1:  This section is the counterpart to the
		* prvBitCombinationTestMasterFunction() function which is called by the
		* test master task.
		***********************************************************************

		This task is controller by the 'test master' task (which is
		implemented by prvTestMasterTask()).  Suspend until resumed by the
		'test master' task. */
		vTaskSuspend( NULL );

		/* Wait indefinitely for one of the bits in ebCOMBINED_BITS to get
		set.  Clear the bit on exit. */
		uxReturned = xEventGroupWaitBits( xEventGroup,	/* The event group that contains the event bits being queried. */
										 ebBIT_1,		/* The bit to wait for. */
										 pdTRUE,		/* Clear the bit on exit. */
										 pdTRUE,		/* Wait for all the bits (only one in this case anyway). */
										 portMAX_DELAY ); /* Block indefinitely to wait for the condition to be met. */

		/* The 'test master' task set all the bits defined by ebCOMBINED_BITS,
		only one of which was being waited for by this task.  The return value
		shows the state of the event bits when the task was unblocked, however
		because the task was waiting for ebBIT_1 and 'clear on exit' was set to
		the current state of the event bits will have ebBIT_1 clear.  */
		if( uxReturned != ebCOMBINED_BITS )
		{
			xError = pdTRUE;
		}

		/* Now call xEventGroupWaitBits() again, this time waiting for all the
		bits in ebCOMBINED_BITS to be set.  This call should block until the
		'test master' task sets ebBIT_1 - which was the bit cleared in the call
		to xEventGroupWaitBits() above. */
		uxReturned = xEventGroupWaitBits( xEventGroup,
										 ebCOMBINED_BITS, /* The bits being waited on. */
										 pdFALSE,		  /* Don't clear the bits on exit. */
										 pdTRUE,		  /* All the bits must be set to unblock. */
										 portMAX_DELAY );

		/* Were all the bits set? */
		if( ( uxReturned & ebCOMBINED_BITS ) != ebCOMBINED_BITS )
		{
			xError = pdTRUE;
		}

		/* Suspend again to wait for the 'test master' task. */
		vTaskSuspend( NULL );

		/* Now call xEventGroupWaitBits() again, again waiting for all the bits
		in ebCOMBINED_BITS to be set, but this time clearing the bits when the
		task is unblocked. */
		uxReturned = xEventGroupWaitBits( xEventGroup,
									 ebCOMBINED_BITS, /* The bits being waited on. */
									 pdTRUE,		  /* Clear the bits on exit. */
									 pdTRUE,		  /* All the bits must be set to unblock. */
									 portMAX_DELAY );

		/* The 'test master' task set all the bits in the event group, so that
		is the value that should have been returned.  The bits defined by
		ebCOMBINED_BITS will have been clear again in the current value though
		as 'clear on exit' was set to pdTRUE. */
		if( uxReturned != ebALL_BITS )
		{
			xError = pdTRUE;
		}





		/**********************************************************************
		* Part 2:  This section is the counterpart to the
		* prvPerformTaskSyncTests() function which is called by the
		* test master task.
		***********************************************************************


		Once again wait for the 'test master' task to unsuspend this task
		when it is time for the next test. */
		vTaskSuspend( NULL );

		/* Now peform a synchronisation with all the other tasks.  At this point
		the 'test master' task has the lowest priority so will get to the sync
		point after all the other synchronising tasks. */
		uxReturned = xEventGroupSync( xEventGroup,		/* The event group used for the sync. */
									ebWAIT_BIT_TASK_SYNC_BIT, /* The bit in the event group used to indicate this task is at the sync point. */
									ebALL_SYNC_BITS,	/* The bits to wait for.  These bits are set by the other tasks taking part in the sync. */
									portMAX_DELAY );	/* The maximum time to wait for the sync condition to be met before giving up. */

		/* A sync with a max delay should only exit when all the synchronisation
		bits are set... */
		if( ( uxReturned & ebALL_SYNC_BITS ) != ebALL_SYNC_BITS )
		{
			xError = pdTRUE;
		}

		/* ...but now the synchronisation bits should be clear again.  Read back
		the current value of the bits within the event group to check that is
		the case.  Setting the bits to zero will return the bits previous value
		then leave all the bits clear. */
		if( xEventGroupSetBits( xEventGroup, 0x00 ) != 0 )
		{
			xError = pdTRUE;
		}

		/* Check the bits are indeed 0 now by simply reading then. */
		if( xEventGroupGetBits( xEventGroup ) != 0 )
		{
			xError = pdTRUE;
		}

		if( xError == pdFALSE )
		{
			/* This task is still cycling without finding an error. */
			ulTestSlaveCycles++;
		}

		vTaskSuspend( NULL );

		/* This time sync when the 'test master' task has the highest priority
		at the point where it sets its sync bit - so this time the 'test master'
		task will get to the sync point before this task. */
		uxReturned = xEventGroupSync( xEventGroup, ebWAIT_BIT_TASK_SYNC_BIT, ebALL_SYNC_BITS, portMAX_DELAY );

		/* A sync with a max delay should only exit when all the synchronisation
		bits are set... */
		if( ( uxReturned & ebALL_SYNC_BITS ) != ebALL_SYNC_BITS )
		{
			xError = pdTRUE;
		}

		/* ...but now the sync bits should be clear again. */
		if( xEventGroupSetBits( xEventGroup, 0x00 ) != 0 )
		{
			xError = pdTRUE;
		}

		/* Block on the event group again.  This time the event group is going
		to be deleted while this task is blocked on it, so it is expected that 0
		will be returned. */
		uxReturned = xEventGroupWaitBits( xEventGroup, ebALL_SYNC_BITS, pdFALSE, pdTRUE, portMAX_DELAY );

		if( uxReturned != 0 )
		{
			xError = pdTRUE;
		}

		if( xError == pdFALSE )
		{
			/* This task is still cycling without finding an error. */
			ulTestSlaveCycles++;
		}

		configASSERT( xError == pdFALSE );
	}
}
/*-----------------------------------------------------------*/

static BaseType_t prvPerformTaskSyncTests( BaseType_t xError, TaskHandle_t xTestSlaveTaskHandle )
{
EventBits_t uxBits;

	/* The three tasks that take part in the synchronisation (rendezvous) are
	expected to be in the suspended state at the start of the test. */
	if( eTaskGetState( xTestSlaveTaskHandle ) != eSuspended )
	{
		xError = pdTRUE;
	}

	if( eTaskGetState( xSyncTask1 ) != eSuspended )
	{
		xError = pdTRUE;
	}

	if( eTaskGetState( xSyncTask2 ) != eSuspended )
	{
		xError = pdTRUE;
	}

	/* Try a synch with no other tasks involved.  First set all the bits other
	than this task's bit. */
	xEventGroupSetBits( xEventGroup, ( ebALL_SYNC_BITS & ~ebSET_BIT_TASK_SYNC_BIT ) );

	/* Then wait on just one bit - the bit that is being set. */
	uxBits = xEventGroupSync( xEventGroup,			/* The event group used for the synchronisation. */
							ebSET_BIT_TASK_SYNC_BIT,/* The bit set by this task when it reaches the sync point. */
							ebSET_BIT_TASK_SYNC_BIT,/* The bits to wait for - in this case it is just waiting for itself. */
							portMAX_DELAY );		/* The maximum time to wait for the sync condition to be met. */

	/* A sync with a max delay should only exit when all the synchronise
	bits are set...check that is the case.  In this case there is only one
	sync bit anyway. */
	if( ( uxBits & ebSET_BIT_TASK_SYNC_BIT ) != ebSET_BIT_TASK_SYNC_BIT )
	{
		xError = pdTRUE;
	}

	/* ...but now the sync bits should be clear again, leaving all the other
	bits set (as only one bit was being waited for). */
	if( xEventGroupGetBits( xEventGroup ) != ( ebALL_SYNC_BITS & ~ebSET_BIT_TASK_SYNC_BIT ) )
	{
		xError = pdTRUE;
	}

	/* Clear all the bits to zero again. */
	xEventGroupClearBits( xEventGroup, ( ebALL_SYNC_BITS & ~ebSET_BIT_TASK_SYNC_BIT ) );
	if( xEventGroupGetBits( xEventGroup ) != 0 )
	{
		xError = pdTRUE;
	}

	/* Unsuspend the other tasks then check they have executed up to the
	synchronisation point. */
	vTaskResume( xTestSlaveTaskHandle );
	vTaskResume( xSyncTask1 );
	vTaskResume( xSyncTask2 );

	if( eTaskGetState( xTestSlaveTaskHandle ) != eBlocked )
	{
		xError = pdTRUE;
	}

	if( eTaskGetState( xSyncTask1 ) != eBlocked )
	{
		xError = pdTRUE;
	}

	if( eTaskGetState( xSyncTask2 ) != eBlocked )
	{
		xError = pdTRUE;
	}

	/* Set this task's sync bit. */
	uxBits = xEventGroupSync( xEventGroup,			/* The event group used for the synchronisation. */
							ebSET_BIT_TASK_SYNC_BIT,/* The bit set by this task when it reaches the sync point. */
							ebALL_SYNC_BITS,		/* The bits to wait for - these bits are set by the other tasks that take part in the sync. */
							portMAX_DELAY );		/* The maximum time to wait for the sync condition to be met. */

	/* A sync with a max delay should only exit when all the synchronise
	bits are set...check that is the case. */
	if( ( uxBits & ebALL_SYNC_BITS ) != ebALL_SYNC_BITS )
	{
		xError = pdTRUE;
	}

	/* ...but now the sync bits should be clear again. */
	if( xEventGroupGetBits( xEventGroup ) != 0 )
	{
		xError = pdTRUE;
	}


	/* The other tasks should now all be suspended again, ready for the next
	synchronisation. */
	if( eTaskGetState( xTestSlaveTaskHandle ) != eSuspended )
	{
		xError = pdTRUE;
	}

	if( eTaskGetState( xSyncTask1 ) != eSuspended )
	{
		xError = pdTRUE;
	}

	if( eTaskGetState( xSyncTask2 ) != eSuspended )
	{
		xError = pdTRUE;
	}


	/* Sync again - but this time set the last necessary bit as the
	highest priority task, rather than the lowest priority task.  Unsuspend
	the other tasks then check they have executed up to the	synchronisation
	point. */
	vTaskResume( xTestSlaveTaskHandle );
	vTaskResume( xSyncTask1 );
	vTaskResume( xSyncTask2 );

	if( eTaskGetState( xTestSlaveTaskHandle ) != eBlocked )
	{
		xError = pdTRUE;
	}

	if( eTaskGetState( xSyncTask1 ) != eBlocked )
	{
		xError = pdTRUE;
	}

	if( eTaskGetState( xSyncTask2 ) != eBlocked )
	{
		xError = pdTRUE;
	}

	/* Raise the priority of this task above that of the other tasks. */
	vTaskPrioritySet( NULL, ebWAIT_BIT_TASK_PRIORITY + 1 );

	/* Set this task's sync bit. */
	uxBits = xEventGroupSync( xEventGroup, ebSET_BIT_TASK_SYNC_BIT, ebALL_SYNC_BITS, portMAX_DELAY );

	/* A sync with a max delay should only exit when all the synchronisation
	bits are set... */
	if( ( uxBits & ebALL_SYNC_BITS ) != ebALL_SYNC_BITS )
	{
		xError = pdTRUE;
	}

	/* ...but now the sync bits should be clear again. */
	if( xEventGroupGetBits( xEventGroup ) != 0 )
	{
		xError = pdTRUE;
	}


	/* The other tasks should now all be in the ready state again, but not
	executed yet as this task still has a higher relative priority. */
	if( eTaskGetState( xTestSlaveTaskHandle ) != eReady )
	{
		xError = pdTRUE;
	}

	if( eTaskGetState( xSyncTask1 ) != eReady )
	{
		xError = pdTRUE;
	}

	if( eTaskGetState( xSyncTask2 ) != eReady )
	{
		xError = pdTRUE;
	}


	/* Reset the priority of this task back to its original value. */
	vTaskPrioritySet( NULL, ebSET_BIT_TASK_PRIORITY );

	/* Now all the other tasks should have reblocked on the event bits
	to test the behaviour when the event bits are deleted. */
	if( eTaskGetState( xTestSlaveTaskHandle ) != eBlocked )
	{
		xError = pdTRUE;
	}

	if( eTaskGetState( xSyncTask1 ) != eBlocked )
	{
		xError = pdTRUE;
	}

	if( eTaskGetState( xSyncTask2 ) != eBlocked )
	{
		xError = pdTRUE;
	}

	return xError;
}
/*-----------------------------------------------------------*/

static BaseType_t prvBitCombinationTestMasterFunction( BaseType_t xError, TaskHandle_t xTestSlaveTaskHandle )
{
EventBits_t uxBits;

	/* Resume the other task.  It will block, pending a single bit from
	within ebCOMBINED_BITS. */
	vTaskResume( xTestSlaveTaskHandle );

	/* Ensure the other task is blocked on the task. */
	if( eTaskGetState( xTestSlaveTaskHandle ) != eBlocked )
	{
		xError = pdTRUE;
	}

	/* Set all the bits in ebCOMBINED_BITS - the 'test slave' task is only
	blocked waiting for one of them. */
	xEventGroupSetBits( xEventGroup, ebCOMBINED_BITS );

	/* The 'test slave' task should now have executed, clearing ebBIT_1 (the
	bit it was blocked on), then re-entered the Blocked state to wait for
	all the other bits in ebCOMBINED_BITS to be set again.  First check
	ebBIT_1 is clear. */
	uxBits = xEventGroupWaitBits( xEventGroup, ebALL_BITS, pdFALSE, pdFALSE, ebDONT_BLOCK );

	if( uxBits != ( ebCOMBINED_BITS & ~ebBIT_1 ) )
	{
		xError = pdTRUE;
	}

	/* Ensure the other task is still in the blocked state. */
	if( eTaskGetState( xTestSlaveTaskHandle ) != eBlocked )
	{
		xError = pdTRUE;
	}

	/* Set all the bits other than ebBIT_1 - which is the bit that must be
	set before the other task unblocks. */
	xEventGroupSetBits( xEventGroup, ebALL_BITS & ~ebBIT_1 );

	/* Ensure all the expected bits are still set. */
	uxBits = xEventGroupWaitBits( xEventGroup, ebALL_BITS, pdFALSE, pdFALSE, ebDONT_BLOCK );

	if( uxBits != ( ebALL_BITS & ~ebBIT_1 ) )
	{
		xError = pdTRUE;
	}

	/* Ensure the other task is still in the blocked state. */
	if( eTaskGetState( xTestSlaveTaskHandle ) != eBlocked )
	{
		xError = pdTRUE;
	}

	/* Now also set ebBIT_1, which should unblock the other task, which will
	then suspend itself. */
	xEventGroupSetBits( xEventGroup, ebBIT_1 );

	/* Ensure the other task is suspended. */
	if( eTaskGetState( xTestSlaveTaskHandle ) != eSuspended )
	{
		xError = pdTRUE;
	}

	/* The other task should not have cleared the bits - so all the bits
	should still be set. */
	if( xEventGroupSetBits( xEventGroup, 0x00 ) != ebALL_BITS )
	{
		xError = pdTRUE;
	}

	/* Clear ebBIT_1 again. */
	if( xEventGroupClearBits( xEventGroup, ebBIT_1 ) != ebALL_BITS )
	{
		xError = pdTRUE;
	}

	/* Resume the other task - which will wait on all the ebCOMBINED_BITS
	again - this time clearing the bits when it is unblocked. */
	vTaskResume( xTestSlaveTaskHandle );

	/* Ensure the other task is blocked once again. */
	if( eTaskGetState( xTestSlaveTaskHandle ) != eBlocked )
	{
		xError = pdTRUE;
	}

	/* Set the bit the other task is waiting for. */
	xEventGroupSetBits( xEventGroup, ebBIT_1 );

	/* Ensure the other task is suspended once again. */
	if( eTaskGetState( xTestSlaveTaskHandle ) != eSuspended )
	{
		xError = pdTRUE;
	}

	/* The other task should have cleared the bits in ebCOMBINED_BITS.
	Clear the remaining bits. */
	uxBits = xEventGroupWaitBits( xEventGroup, ebALL_BITS, pdFALSE, pdFALSE, ebDONT_BLOCK );

	if( uxBits != ( ebALL_BITS & ~ebCOMBINED_BITS ) )
	{
		xError = pdTRUE;
	}

	/* Clear all bits ready for the sync with the other three tasks.  The
	value returned is the value prior to the bits being cleared. */
	if( xEventGroupClearBits( xEventGroup, ebALL_BITS ) != ( ebALL_BITS & ~ebCOMBINED_BITS ) )
	{
		xError = pdTRUE;
	}

	/* The bits should be clear now. */
	if( xEventGroupGetBits( xEventGroup ) != 0x00 )
	{
		xError = pdTRUE;
	}

	return xError;
}
/*-----------------------------------------------------------*/

static void prvSelectiveBitsTestSlaveFunction( void )
{
EventBits_t uxPendBits, uxReturned;

	/* Used in a test that blocks two tasks on various different bits within an
	event group - then sets each bit in turn and checks that the correct tasks
	unblock at the correct times.

	This function is called by two different tasks - each of which will use a
	different bit.  Check the task handle to see which task the function was
	called by. */
	if( xTaskGetCurrentTaskHandle() == xSyncTask1 )
	{
		uxPendBits = ebSELECTIVE_BITS_1;
	}
	else
	{
		uxPendBits = ebSELECTIVE_BITS_2;
	}

	for( ;; )
	{
		/* Wait until it is time to perform the next cycle of the test.  The
		task is unsuspended by the tests implemented in the
		prvSelectiveBitsTestMasterFunction() function. */
		vTaskSuspend( NULL );
		uxReturned = xEventGroupWaitBits( xEventGroup, uxPendBits, pdTRUE, pdFALSE, portMAX_DELAY );

		if( uxReturned == ( EventBits_t ) 0 )
		{
			break;
		}
	}
}
/*-----------------------------------------------------------*/

static BaseType_t prvSelectiveBitsTestMasterFunction( void )
{
BaseType_t xError = pdFALSE;
EventBits_t uxBit;

	/* Used in a test that blocks two tasks on various different bits within an
	event group - then sets each bit in turn and checks that the correct tasks
	unblock at the correct times.  The two other tasks (xSyncTask1 and
	xSyncTask2) call prvSelectiveBitsTestSlaveFunction() to perform their parts in
	this test.

	Both other tasks should start in the suspended state. */
	if( eTaskGetState( xSyncTask1 ) != eSuspended )
	{
		xError = pdTRUE;
	}

	if( eTaskGetState( xSyncTask2 ) != eSuspended )
	{
		xError = pdTRUE;
	}

	/* Test each bit in the byte individually. */
	for( uxBit = 0x01; uxBit < 0x100; uxBit <<= 1 )
	{
		/* Resume both tasks. */
		vTaskResume( xSyncTask1 );
		vTaskResume( xSyncTask2 );

		/* Now both tasks should be blocked on the event group. */
		if( eTaskGetState( xSyncTask1 ) != eBlocked )
		{
			xError = pdTRUE;
		}

		if( eTaskGetState( xSyncTask2 ) != eBlocked )
		{
			xError = pdTRUE;
		}

		/* Set one bit. */
		xEventGroupSetBits( xEventGroup, uxBit );

		/* Is the bit set in the first set of selective bits?  If so the first
		sync task should have unblocked and returned to the suspended state. */
		if( ( uxBit & ebSELECTIVE_BITS_1 ) == 0 )
		{
			/* Task should not have unblocked. */
			if( eTaskGetState( xSyncTask1 ) != eBlocked )
			{
				xError = pdTRUE;
			}
		}
		else
		{
			/* Task should have unblocked and returned to the suspended state. */
			if( eTaskGetState( xSyncTask1 ) != eSuspended )
			{
				xError = pdTRUE;
			}
		}

		/* Same checks for the second sync task. */
		if( ( uxBit & ebSELECTIVE_BITS_2 ) == 0 )
		{
			/* Task should not have unblocked. */
			if( eTaskGetState( xSyncTask2 ) != eBlocked )
			{
				xError = pdTRUE;
			}
		}
		else
		{
			/* Task should have unblocked and returned to the suspended state. */
			if( eTaskGetState( xSyncTask2 ) != eSuspended )
			{
				xError = pdTRUE;
			}
		}
	}

	/* Ensure both tasks are blocked on the event group again, then delete the
	event group so the other tasks leave this portion of the test. */
	vTaskResume( xSyncTask1 );
	vTaskResume( xSyncTask2 );

	/* Deleting the event group is the signal that the two other tasks should
	leave the prvSelectiveBitsTestSlaveFunction() function and continue to the main
	part of their functionality. */
	vEventGroupDelete( xEventGroup );

	return xError;
}
/*-----------------------------------------------------------*/

void vPeriodicEventGroupsProcessing( void )
{
static BaseType_t xCallCount = 0, xISRTestError = pdFALSE;
const BaseType_t xSetBitCount = 100, xGetBitsCount = 200, xClearBitsCount = 300;
const EventBits_t uxBitsToSet = 0x12U;
EventBits_t uxReturned;
BaseType_t xMessagePosted;

	/* Called periodically from the tick hook to exercise the "FromISR"
	functions. */

	xCallCount++;

	if( xCallCount == xSetBitCount )
	{
		/* All the event bits should start clear. */
		uxReturned = xEventGroupGetBitsFromISR( xISREventGroup );
		if( uxReturned != 0x00 )
		{
			xISRTestError = pdTRUE;
		}
		else
		{
			/* Set the bits.  This is called from the tick hook so it is not
			necessary to use the last parameter to ensure a context switch
			occurs immediately. */
			xMessagePosted = xEventGroupSetBitsFromISR( xISREventGroup, uxBitsToSet, NULL );
			if( xMessagePosted != pdPASS )
			{
				xISRTestError = pdTRUE;
			}
		}
	}
	else if( xCallCount == xGetBitsCount )
	{
		/* Check the bits were set as expected. */
		uxReturned = xEventGroupGetBitsFromISR( xISREventGroup );
		if( uxReturned != uxBitsToSet )
		{
			xISRTestError = pdTRUE;
		}
	}
	else if( xCallCount == xClearBitsCount )
	{
		/* Clear the bits again. */
		uxReturned = ( EventBits_t ) xEventGroupClearBitsFromISR( xISREventGroup, uxBitsToSet );

		/* Check the message was posted. */
		if( uxReturned != pdPASS )
		{
			xISRTestError = pdTRUE;
		}

		/* Go back to the start. */
		xCallCount = 0;

		/* If no errors have been detected then increment the count of test
		cycles. */
		if( xISRTestError == pdFALSE )
		{
			ulISRCycles++;
		}
	}
	else
	{
		/* Nothing else to do. */
	}
}

/*-----------------------------------------------------------*/
/* This is called to check that all the created tasks are still running. */
BaseType_t xAreEventGroupTasksStillRunning( void )
{
static uint32_t ulPreviousWaitBitCycles = 0, ulPreviousSetBitCycles = 0, ulPreviousISRCycles = 0;
BaseType_t xStatus = pdPASS;

	/* Check the tasks are still cycling without finding any errors. */
	if( ulPreviousSetBitCycles == ulTestMasterCycles )
	{
		xStatus = pdFAIL;
	}
	ulPreviousSetBitCycles = ulTestMasterCycles;

	if( ulPreviousWaitBitCycles == ulTestSlaveCycles )
	{
		xStatus = pdFAIL;
	}
	ulPreviousWaitBitCycles = ulTestSlaveCycles;

	if( ulPreviousISRCycles == ulISRCycles )
	{
		xStatus = pdFAIL;
	}
	ulPreviousISRCycles = ulISRCycles;

	return xStatus;
}



