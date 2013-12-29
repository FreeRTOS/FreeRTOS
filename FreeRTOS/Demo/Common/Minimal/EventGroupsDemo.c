/*
    FreeRTOS V7.6.0 - Copyright (C) 2013 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that has become a de facto standard.             *
     *                                                                       *
     *    Help yourself get started quickly and support the FreeRTOS         *
     *    project by purchasing a FreeRTOS tutorial book, reference          *
     *    manual, or both from: http://www.FreeRTOS.org/Documentation        *
     *                                                                       *
     *    Thank you!                                                         *
     *                                                                       *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    >>! NOTE: The modification to the GPL is included to allow you to distribute
    >>! a combined work that includes FreeRTOS without being obliged to provide
    >>! the source code for proprietary components outside of the FreeRTOS
    >>! kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available from the following
    link: http://www.freertos.org/a00114.html

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org - Documentation, books, training, latest versions,
    license and Real Time Engineers Ltd. contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/



/*
 * This file contains fairly comprehensive checks on the behaviour of event
 * groups.  It is not intended to be a user friendly demonstration of the event
 * groups API.
 */



/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "event_groups.h"

/* Priorities used by the tasks. */
#define ebSET_BIT_TASK_PRIORITY		( tskIDLE_PRIORITY )
#define ebWAIT_BIT_TASK_PRIORITY	( tskIDLE_PRIORITY + 1 )

/* Generic bit definitions. */
#define ebBIT_0		( 0x01UL )
#define ebBIT_1		( 0x02UL )
#define ebBIT_2		( 0x04UL )
#define ebBIT_3		( 0x08UL )
#define ebBIT_4		( 0x10UL )
#define ebBIT_5		( 0x20UL )
#define ebBIT_6		( 0x40UL )
#define ebBIT_7		( 0x80UL )

/* Combinations of bits used in the tests. */
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

/* A 5ms delay. */
#define ebSHORT_DELAY	( 5 / portTICK_RATE_MS )

/* Used in the selective bits test which checks no, one or both tasks blocked on
event bits in a group are unblocked as appropriate as different bits get set. */
#define ebSELECTIVE_BITS_1		0x03
#define ebSELECTIVE_BITS_2		0x05

/*-----------------------------------------------------------*/

/*
 * The primary task that manages and controls all the behavioural tests.
 */
static void prvSetBitsTask( void *pvParameters );

/*
 * The task that participates in most of the non 'single task' tests performed
 * by prvSetBitsTask().
 */
static void prvWaitBitsTask( void *pvParameters );

/*
 * Two instances of prvSyncTask() are created.  Their only purpose is to
 * participate in synchronisations and test the behaviour when an event group on
 * which they are blocked is deleted.
 */
static void prvSyncTask( void *pvParameters );

/*
 * Functions used in a test that blocks two tasks on various different bits
 * within an event group - then sets each bit in turn and checks that the 
 * correct tasks unblock at the correct times.
 */
static portBASE_TYPE prvTestSelectiveBits( void );
static void prvPreSyncSelectiveWakeTest( void );

/*-----------------------------------------------------------*/

/* Variables that are incremented by the tasks on each cycle provided no errors
have been found.  Used to detect an error or stall in the test cycling. */
static volatile unsigned long ulSetBitCycles = 0, ulWaitBitCycles = 0;

/* The event group used by all the tests. */
static EventGroupHandle_t xEventBits = NULL;

/* Handles to the tasks that only take part in the synchronisation calls. */
static xTaskHandle xSyncTask1 = NULL, xSyncTask2 = NULL;

/*-----------------------------------------------------------*/

void vStartEventGroupTasks( void )
{
xTaskHandle xWaitBitsTaskHandle;

	/*
	 * This file contains fairly comprehensive checks on the behaviour of event
	 * groups.  It is not intended to be a user friendly demonstration of the
	 * event groups API.
	 */

	xTaskCreate( prvWaitBitsTask, "WaitO", configMINIMAL_STACK_SIZE, NULL, ebWAIT_BIT_TASK_PRIORITY, &xWaitBitsTaskHandle );
	xTaskCreate( prvSetBitsTask, "SetB", configMINIMAL_STACK_SIZE, ( void * ) xWaitBitsTaskHandle, ebSET_BIT_TASK_PRIORITY, NULL );
	xTaskCreate( prvSyncTask, "Rndv", configMINIMAL_STACK_SIZE, ( void * ) ebRENDESVOUS_TASK_1_SYNC_BIT, ebWAIT_BIT_TASK_PRIORITY, &xSyncTask1 );
	xTaskCreate( prvSyncTask, "Rndv", configMINIMAL_STACK_SIZE, ( void * ) ebRENDESVOUS_TASK_2_SYNC_BIT, ebWAIT_BIT_TASK_PRIORITY, &xSyncTask2 );

	/* If the last task was created then the others will have been too. */
	configASSERT( xSyncTask2 );
}
/*-----------------------------------------------------------*/

static void prvSyncTask( void *pvParameters )
{
EventBits_t uxSynchronisationBit, uxReturned;

	/* The bit to use to indicate this task is at the synchronisation point is
	passed in as the task parameter. */
	uxSynchronisationBit = ( EventBits_t ) pvParameters;

	/* A few tests are performed before entering the main demo loop. */
	prvPreSyncSelectiveWakeTest();

	for( ;; )
	{
		/* Wait until the 'set bit' task unsuspends this task. */
		vTaskSuspend( NULL );

		/* Set the bit that indicates this task is at the synchronisation
		point.  The first time this is done the 'set bit' task has a lower
		priority than this task. */
		uxReturned = xEventGroupSync( xEventBits, uxSynchronisationBit, ebALL_SYNC_BITS, portMAX_DELAY );
		configASSERT( ( uxReturned & ebALL_SYNC_BITS ) == ebALL_SYNC_BITS );

		/* Wait until the 'set bit' task unsuspends this task again. */
		vTaskSuspend( NULL );

		/* Set the bit that indicates this task is at the synchronisation
		point again.  This time the 'set bit' task has a higher priority than
		this task. */
		uxReturned = xEventGroupSync( xEventBits, uxSynchronisationBit, ebALL_SYNC_BITS, portMAX_DELAY );
		configASSERT( ( uxReturned & ebALL_SYNC_BITS ) == ebALL_SYNC_BITS );

		/* Block on the event group again.  This time the event group is going
		to be deleted, so 0 should be returned. */
		uxReturned = xEventGroupWaitBits( xEventBits, ebALL_SYNC_BITS, pdFALSE, pdTRUE, portMAX_DELAY );
		configASSERT( uxReturned == 0 );
	}
}
/*-----------------------------------------------------------*/

static void prvWaitBitsTask( void *pvParameters )
{
EventBits_t uxReturned;
portBASE_TYPE xError = pdFALSE;

	/* Avoid compiler warnings. */
	( void ) pvParameters;

	for( ;; )
	{
		/* This task is controller by the prvSetBitsTask().  Suspend until resumed
		by prvSetBitsTask(). */
		vTaskSuspend( NULL );

		/* Wait indefinitely for one of the bits in ebCOMBINED_BITS to get
		set.  Clear the bit on exit. */
		uxReturned = xEventGroupWaitBits( xEventBits,	/* The event bits being queried. */
									 ebBIT_1,		/* The bit to wait for. */
									 pdTRUE,		/* Clear the bit on exit. */
									 pdTRUE,		/* Wait for all the bits (only one in this case anyway. */
									 portMAX_DELAY );

		/* Should unblock after the 'set bit' task has set all the bits in the
		ebCOMBINED_BITS constant, therefore ebCOMBINED_BITS is what should have
		been returned. */
		if( uxReturned != ebCOMBINED_BITS )
		{
			xError = pdTRUE;
		}

		/* Now call xEventGroupWaitBits() again, this time waiting for all the bits
		in ebCOMBINED_BITS to be set.  This call should block until the 'set
		bits' task sets ebBIT_1 - which was the bit cleared in the call to
		xEventGroupWaitBits() above. */
		uxReturned = xEventGroupWaitBits( xEventBits,
									 ebCOMBINED_BITS, /* The bits being waited on. */
									 pdFALSE,		  /* Don't clear the bits on exit. */
									 pdTRUE,		  /* All the bits must be set to unblock. */
									 portMAX_DELAY );

		/* Were all the bits set? */
		if( ( uxReturned & ebCOMBINED_BITS ) != ebCOMBINED_BITS )
		{
			xError = pdTRUE;
		}

		/* Suspend again to wait for the 'set bit' task. */
		vTaskSuspend( NULL );

		/* Now call xEventGroupWaitBits() again, again waiting for all the bits in
		ebCOMBINED_BITS to be set, but this time clearing the bits when the task
		is unblocked. */
		uxReturned = xEventGroupWaitBits( xEventBits,
									 ebCOMBINED_BITS, /* The bits being waited on. */
									 pdTRUE,		  /* Clear the bits on exit. */
									 pdTRUE,		  /* All the bits must be set to unblock. */
									 portMAX_DELAY );


		if( uxReturned != ebALL_BITS )
		{
			xError = pdTRUE;
		}

		vTaskSuspend( NULL );

		/* Now to synchronise with when 'set bit' task has the lowest
		priority. */
		uxReturned = xEventGroupSync( xEventBits, ebWAIT_BIT_TASK_SYNC_BIT, ebALL_SYNC_BITS, portMAX_DELAY );

		/* A sync with a max delay should only exit when all the synchronisation
		bits are set... */
		if( ( uxReturned & ebALL_SYNC_BITS ) != ebALL_SYNC_BITS )
		{
			xError = pdTRUE;
		}

		/* ...but now the synchronisation bits should be clear again. */
		if( xEventGroupSetBits( xEventBits, 0x00 ) != 0 )
		{
			xError = pdTRUE;
		}

		if( xError == pdFALSE )
		{
			/* This task is still cycling without finding an error. */
			ulWaitBitCycles++;
		}

		vTaskSuspend( NULL );

		/* This time sync when the 'set bit' task has the highest priority
		at the point where it sets its sync bit. */
		uxReturned = xEventGroupSync( xEventBits, ebWAIT_BIT_TASK_SYNC_BIT, ebALL_SYNC_BITS, portMAX_DELAY );

		/* A sync with a max delay should only exit when all the synchronisation
		bits are set... */
		if( ( uxReturned & ebALL_SYNC_BITS ) != ebALL_SYNC_BITS )
		{
			xError = pdTRUE;
		}

		/* ...but now the sync bits should be clear again. */
		if( xEventGroupSetBits( xEventBits, 0x00 ) != 0 )
		{
			xError = pdTRUE;
		}

		/* Block on the event group again.  This time the event group is going
		to be deleted, so 0 should be returned. */
		uxReturned = xEventGroupWaitBits( xEventBits, ebALL_SYNC_BITS, pdFALSE, pdTRUE, portMAX_DELAY );

		if( uxReturned != 0 )
		{
			xError = pdTRUE;
		}

		if( xError == pdFALSE )
		{
			/* This task is still cycling without finding an error. */
			ulWaitBitCycles++;
		}

		configASSERT( xError == pdFALSE );
	}
}
/*-----------------------------------------------------------*/

static void prvSetBitsTask( void *pvParameters )
{
EventBits_t uxBits;
portBASE_TYPE xError;

/* The handle to the other task is passed in as the task parameter. */
xTaskHandle xWaitBitsTaskHandle = ( xTaskHandle ) pvParameters;

	/* Avoid compiler warnings. */
	( void ) pvParameters;

	/* Create the event group ready for the initial tests. */
	xEventBits = xEventGroupCreate();
	configASSERT( xEventBits );

	/* Perform the tests that block two tasks on different combinations of bits, 
	then set each bit in turn and check the correct tasks unblock at the correct 
	times. */
	xError = prvTestSelectiveBits();

	for( ;; )
	{
		/* Recreate the event group ready for the next cycle. */
		xEventBits = xEventGroupCreate();
		configASSERT( xEventBits );

		/* Resume the other task.  It will block, pending a single bit from
		within ebCOMBINED_BITS. */
		vTaskResume( xWaitBitsTaskHandle );

		/* Ensure the other task is blocked on the task. */
		if( eTaskGetState( xWaitBitsTaskHandle ) != eBlocked )
		{
			xError = pdTRUE;
		}

		/* Set all the bits in ebCOMBINED_BITS - the 'wait bits' task is only
		blocked waiting for one of them. */
		xEventGroupSetBits( xEventBits, ebCOMBINED_BITS );

		/* The 'wait bits' task should now have executed, clearing ebBIT_1 (the
		bit it was blocked on), then re-entered the Blocked state to wait for
		all the other bits in ebCOMBINED_BITS to be set again.  First check
		ebBIT_1 is clear. */
		uxBits = xEventGroupWaitBits( xEventBits, ebALL_BITS, pdFALSE, pdFALSE, ebDONT_BLOCK );

		if( uxBits != ( ebCOMBINED_BITS & ~ebBIT_1 ) )
		{
			xError = pdTRUE;
		}

		/* Ensure the other task is still in the blocked state. */
		if( eTaskGetState( xWaitBitsTaskHandle ) != eBlocked )
		{
			xError = pdTRUE;
		}

		/* Set all the bits other than ebBIT_1 - which is the bit that must be
		set before the other task unblocks. */
		xEventGroupSetBits( xEventBits, ebALL_BITS & ~ebBIT_1 );

		/* Ensure all the expected bits are still set. */
		uxBits = xEventGroupWaitBits( xEventBits, ebALL_BITS, pdFALSE, pdFALSE, ebDONT_BLOCK );

		if( uxBits != ( ebALL_BITS & ~ebBIT_1 ) )
		{
			xError = pdTRUE;
		}

		/* Ensure the other task is still in the blocked state. */
		if( eTaskGetState( xWaitBitsTaskHandle ) != eBlocked )
		{
			xError = pdTRUE;
		}

		/* Now also set ebBIT_1, which should unblock the other task, which will
		then suspend itself. */
		xEventGroupSetBits( xEventBits, ebBIT_1 );

		/* Ensure the other task is suspended. */
		if( eTaskGetState( xWaitBitsTaskHandle ) != eSuspended )
		{
			xError = pdTRUE;
		}

		/* The other task should not have cleared the bits - so all the bits
		should still be set. */
		if( xEventGroupSetBits( xEventBits, 0x00 ) != ebALL_BITS )
		{
			xError = pdTRUE;
		}

		/* Clear ebBIT_1 again. */
		if( xEventGroupClearBits( xEventBits, ebBIT_1 ) != ebALL_BITS )
		{
			xError = pdTRUE;
		}

		/* Resume the other task - which will wait on all the ebCOMBINED_BITS
		again - this time clearing the bits when it is unblocked. */
		vTaskResume( xWaitBitsTaskHandle );

		/* Ensure the other task is blocked once again. */
		if( eTaskGetState( xWaitBitsTaskHandle ) != eBlocked )
		{
			xError = pdTRUE;
		}

		/* Set the bit the other task is waiting for. */
		xEventGroupSetBits( xEventBits, ebBIT_1 );

		/* Ensure the other task is suspended once again. */
		if( eTaskGetState( xWaitBitsTaskHandle ) != eSuspended )
		{
			xError = pdTRUE;
		}

		/* The other task should have cleared the bits in ebCOMBINED_BITS.
		Clear the remaining bits. */
		uxBits = xEventGroupWaitBits( xEventBits, ebALL_BITS, pdFALSE, pdFALSE, ebDONT_BLOCK );

		if( uxBits != ( ebALL_BITS & ~ebCOMBINED_BITS ) )
		{
			xError = pdTRUE;
		}

		/* Clear all bits ready for the sync with the other three tasks.  The
		value returned is the value prior to the bits being cleared. */
		if( xEventGroupClearBits( xEventBits, ebALL_BITS ) != ( ebALL_BITS & ~ebCOMBINED_BITS ) )
		{
			xError = pdTRUE;
		}

		/* The bits should be clear now. */
		if( xEventGroupGetBits( xEventBits ) != 0x00 )
		{
			xError = pdTRUE;
		}

		/* Check the other three tasks are suspended. */
		if( eTaskGetState( xWaitBitsTaskHandle ) != eSuspended )
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

		/* Unsuspend the other tasks then check they have executed up to the
		synchronisation point. */
		vTaskResume( xWaitBitsTaskHandle );
		vTaskResume( xSyncTask1 );
		vTaskResume( xSyncTask2 );

		if( eTaskGetState( xWaitBitsTaskHandle ) != eBlocked )
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
		uxBits = xEventGroupSync( xEventBits, ebSET_BIT_TASK_SYNC_BIT, ebALL_SYNC_BITS, portMAX_DELAY );

		/* A sync with a max delay should only exit when all the synchronise
		bits are set... */
		if( ( uxBits & ebALL_SYNC_BITS ) != ebALL_SYNC_BITS )
		{
			xError = pdTRUE;
		}

		/* ...but now the sync bits should be clear again. */
		if( xEventGroupSetBits( xEventBits, 0x00 ) != 0 )
		{
			xError = pdTRUE;
		}


		/* The other tasks should now all be suspended again, ready for the next
		synchronisation. */
		if( eTaskGetState( xWaitBitsTaskHandle ) != eSuspended )
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
		vTaskResume( xWaitBitsTaskHandle );
		vTaskResume( xSyncTask1 );
		vTaskResume( xSyncTask2 );

		if( eTaskGetState( xWaitBitsTaskHandle ) != eBlocked )
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
		uxBits = xEventGroupSync( xEventBits, ebSET_BIT_TASK_SYNC_BIT, ebALL_SYNC_BITS, portMAX_DELAY );

		/* A sync with a max delay should only exit when all the synchronisation
		bits are set... */
		if( ( uxBits & ebALL_SYNC_BITS ) != ebALL_SYNC_BITS )
		{
			xError = pdTRUE;
		}

		/* ...but now the sync bits should be clear again. */
		if( xEventGroupSetBits( xEventBits, 0x00 ) != 0 )
		{
			xError = pdTRUE;
		}


		/* The other tasks should now all be in the ready state again, but not
		executed yet as this task still has a higher relative priority. */
		if( eTaskGetState( xWaitBitsTaskHandle ) != eReady )
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
		if( eTaskGetState( xWaitBitsTaskHandle ) != eBlocked )
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

		/* Delete the event group. */
		vEventGroupDelete( xEventBits );

		/* Now all the other tasks should have completed and suspended
		themselves ready for the next go around the loop. */
		if( eTaskGetState( xWaitBitsTaskHandle ) != eSuspended )
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


		if( xError == pdFALSE )
		{
			ulSetBitCycles++;
		}

		configASSERT( xError == pdFALSE );
	}
}
/*-----------------------------------------------------------*/

static void prvPreSyncSelectiveWakeTest( void )
{
EventBits_t uxPendBits, uxReturned;

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
		vTaskSuspend( NULL );
		uxReturned = xEventGroupWaitBits( xEventBits, uxPendBits, pdTRUE, pdFALSE, portMAX_DELAY );

		if( uxReturned == ( EventBits_t ) 0 )
		{
			break;
		}
	}
}
/*-----------------------------------------------------------*/

static portBASE_TYPE prvTestSelectiveBits( void )
{
portBASE_TYPE xError = pdFALSE;
EventBits_t uxBit;

	/* Both tasks should start in the suspended state. */
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
		xEventGroupSetBits( xEventBits, uxBit );

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

	vEventGroupDelete( xEventBits );

	return xError;
}
/*-----------------------------------------------------------*/

/* This is called to check that all the created tasks are still running. */
portBASE_TYPE xAreEventGroupTasksStillRunning( void )
{
static unsigned long ulPreviousWaitBitCycles = 0, ulPreviousSetBitCycles = 0;
portBASE_TYPE xStatus = pdPASS;

	/* Check the tasks are still cycling without finding any errors. */
	if( ulPreviousSetBitCycles == ulSetBitCycles )
	{
		xStatus = pdFAIL;
	}
	ulPreviousSetBitCycles = ulSetBitCycles;

	if( ulPreviousWaitBitCycles == ulWaitBitCycles )
	{
		xStatus = pdFAIL;
	}
	ulPreviousWaitBitCycles = ulWaitBitCycles;

	return xStatus;
}



