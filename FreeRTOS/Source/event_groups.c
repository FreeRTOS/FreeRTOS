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

/* Standard includes. */
#include <stdlib.h>

/* Defining MPU_WRAPPERS_INCLUDED_FROM_API_FILE prevents task.h from redefining
all the API functions to use the MPU wrappers.  That should only be done when
task.h is included from an application file. */
#define MPU_WRAPPERS_INCLUDED_FROM_API_FILE

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "timers.h"
#include "event_groups.h"

/* Lint e961 and e750 are suppressed as a MISRA exception justified because the
MPU ports require MPU_WRAPPERS_INCLUDED_FROM_API_FILE to be defined for the
header files above, but not in this file, in order to generate the correct
privileged Vs unprivileged linkage and placement. */
#undef MPU_WRAPPERS_INCLUDED_FROM_API_FILE /*lint !e961 !e750. */

#if ( INCLUDE_xEventGroupSetBitFromISR == 1 ) && ( configUSE_TIMERS == 0 )
	#error configUSE_TIMERS must be set to 1 to make the xEventGroupSetBitFromISR() function available.
#endif

#if ( INCLUDE_xEventGroupSetBitFromISR == 1 ) && ( INCLUDE_xTimerPendCallbackFromISR == 0 )
	#error INCLUDE_xTimerPendCallbackFromISR must also be set to one to make the xEventGroupSetBitFromISR() function available.
#endif


#if configUSE_16_BIT_TICKS == 1
	#define taskCLEAR_EVENTS_ON_EXIT_BIT	0x0100U
	#define taskUNBLOCKED_DUE_TO_BIT_SET	0x0200U
	#define taskWAIT_FOR_ALL_BITS			0x0400U
	#define taskEVENT_BITS_CONTROL_BYTES	0xff00U
#else
	#define taskCLEAR_EVENTS_ON_EXIT_BIT	0x01000000UL
	#define taskUNBLOCKED_DUE_TO_BIT_SET	0x02000000UL
	#define taskWAIT_FOR_ALL_BITS			0x04000000UL
	#define taskEVENT_BITS_CONTROL_BYTES	0xff000000UL
#endif

typedef struct EventBitsDefinition
{
	xEventBitsType uxEventBits;
	xList xTasksWaitingForBits;		/*< List of tasks waiting for a bit to be set. */
} xEVENT_BITS;

/* Used internally only. */
typedef struct EVENT_GROUP_CALLBACK_PARAMTERS
{
	xEventGroupHandle xTargetEventGroup;
	xEventBitsType xBitsToSet;
} xEventGroupCallbackParameters;

/*-----------------------------------------------------------*/

xEventGroupHandle xEventGroupCreate( void )
{
xEVENT_BITS *pxEventBits;

	pxEventBits = pvPortMalloc( sizeof( xEVENT_BITS ) );
	if( pxEventBits != NULL )
	{
		pxEventBits->uxEventBits = 0;
		vListInitialise( &( pxEventBits->xTasksWaitingForBits ) );
	}

	return ( xEventGroupHandle ) pxEventBits;
}
/*-----------------------------------------------------------*/

xEventBitsType xEventGroupSync( xEventGroupHandle xEventGroup, xEventBitsType uxBitsToSet, xEventBitsType uxBitsToWaitFor, portTickType xTicksToWait )
{
xEventBitsType uxOriginalBitValue, uxReturn;
xEVENT_BITS *pxEventBits = ( xEVENT_BITS * ) xEventGroup;
portBASE_TYPE xYieldedAlready;

	#if ( ( INCLUDE_xTaskGetSchedulerState == 1 ) || ( configUSE_TIMERS == 1 ) )
	{
		configASSERT( !( ( xTaskGetSchedulerState() == taskSCHEDULER_SUSPENDED ) && ( xTicksToWait != 0 ) ) );
	}
	#endif

	vTaskSuspendAll();
	{
		uxOriginalBitValue = pxEventBits->uxEventBits;

		( void ) xEventGroupSetBits( xEventGroup, uxBitsToSet );

		if( ( ( uxOriginalBitValue | uxBitsToSet ) & uxBitsToWaitFor ) == uxBitsToWaitFor )
		{
			/* All the rendezvous bits will have been set once this task set
			its bits - no need to block. */
			uxReturn = ( uxOriginalBitValue | uxBitsToSet );

			/* Rendezvous always clear the bits.  They will have been cleared
			already unless this is the only task in the rendezvous. */
			pxEventBits->uxEventBits &= uxBitsToWaitFor;

			xTicksToWait = 0;
		}
		else
		{
			if( xTicksToWait != ( portTickType ) 0 )
			{
				/* Store the bits that the calling task is waiting for in the
				task's event list item so the kernel knows when a match is
				found.  Then enter the blocked state. */
				vTaskPlaceOnUnorderedEventList( &( pxEventBits->xTasksWaitingForBits ), ( uxBitsToWaitFor | taskCLEAR_EVENTS_ON_EXIT_BIT | taskWAIT_FOR_ALL_BITS ), xTicksToWait );
			}
			else
			{
				/* The rendezvous bits were not set, but no block time was
				specified - just return the current event bit value. */
				uxReturn = pxEventBits->uxEventBits;
			}
		}
	}
	xYieldedAlready = xTaskResumeAll();

	if( xTicksToWait != ( portTickType ) 0 )
	{
		if( xYieldedAlready == pdFALSE )
		{
			portYIELD_WITHIN_API();
		}

		/* The task blocked to wait for its required bits to be set - at this
		point either the required bits were set or the block time expired.  If
		the required bits were set they will have been stored in the task's
		event list item, and they should now be retrieved then cleared. */
		uxReturn = uxTaskResetEventItemValue();

		if( ( uxReturn & taskUNBLOCKED_DUE_TO_BIT_SET ) == ( xEventBitsType ) 0 )
		{
			/* The task timed out, just return the current event bit value. */
			uxReturn = pxEventBits->uxEventBits;
		}
		else
		{
			/* The task unblocked because the bits were set.  Clear the control
			bits before returning the value. */
			uxReturn &= ~taskEVENT_BITS_CONTROL_BYTES;
		}
	}

	return uxReturn;
}
/*-----------------------------------------------------------*/

xEventBitsType xEventGroupWaitBits( xEventGroupHandle xEventGroup, xEventBitsType uxBitsToWaitFor, portBASE_TYPE xClearOnExit, portBASE_TYPE xWaitForAllBits, portTickType xTicksToWait )
{
xEVENT_BITS *pxEventBits = ( xEVENT_BITS * ) xEventGroup;
const xEventBitsType uxCurrentEventBits = pxEventBits->uxEventBits;
xEventBitsType uxReturn, uxControlBits = 0;

	/* Check the user is not attempting to wait on the bits used by the kernel
	itself, and that at least one bit is being requested. */
	configASSERT( ( uxBitsToWaitFor & taskEVENT_BITS_CONTROL_BYTES ) == 0 );
	configASSERT( uxBitsToWaitFor != 0 );
	#if ( ( INCLUDE_xTaskGetSchedulerState == 1 ) || ( configUSE_TIMERS == 1 ) )
	{
		configASSERT( !( ( xTaskGetSchedulerState() == taskSCHEDULER_SUSPENDED ) && ( xTicksToWait != 0 ) ) );
	}
	#endif

	taskENTER_CRITICAL();
	{
		if( xWaitForAllBits == pdFALSE )
		{
			/* Task only has to wait for one bit within uxBitsToWaitFor to be set.  Is
			one already set? */
			if( ( uxCurrentEventBits & uxBitsToWaitFor ) != ( xEventBitsType ) 0 )
			{
				/* At least one of the bits was set.  No need to block. */
				xTicksToWait = 0;
			}
		}
		else
		{
			/* Task has to wait for all the bits in uxBitsToWaitFor to be set.  Are they
			set already? */
			if( ( uxCurrentEventBits & uxBitsToWaitFor ) == uxBitsToWaitFor )
			{
				/* All the bits were set, no need to block. */
				xTicksToWait = 0;
			}
		}

		/* The task can return now if either its wait condition is already met
		or the requested block time is 0. */
		if( xTicksToWait == ( portTickType ) 0 )
		{
			/* No need to block, just set the return value. */
			uxReturn = uxCurrentEventBits;

			if( xClearOnExit != pdFALSE )
			{
				/* The user requested the bits be cleared again prior to exiting
				this function. */
				pxEventBits->uxEventBits &= ~uxBitsToWaitFor;
			}
		}
		else
		{
			/* The task is going to block to wait for its required bits to be
			set.  uxControlBits are used to remember the specified behaviour of
			this call to xEventGroupWaitBits() - for use when the event bits
			unblock the task. */
			if( xClearOnExit != pdFALSE )
			{
				uxControlBits |= taskCLEAR_EVENTS_ON_EXIT_BIT;
			}

			if( xWaitForAllBits != pdFALSE )
			{
				uxControlBits |= taskWAIT_FOR_ALL_BITS;
			}

			/* Store the bits that the calling task is waiting for in the
			task's event list item so the kernel knows when a match is
			found.  Then enter the blocked state. */
			vTaskPlaceOnUnorderedEventList( &( pxEventBits->xTasksWaitingForBits ), ( uxBitsToWaitFor | uxControlBits ), xTicksToWait );
			portYIELD_WITHIN_API();
		}
	}
	taskEXIT_CRITICAL();

	if( xTicksToWait != ( portTickType ) 0 )
	{
		/* The task blocked to wait for its required bits to be set - at this
		point either the required bits were set or the block time expired.  If
		the required bits were set they will have been stored in the task's
		event list item, and they should now be retrieved then cleared. */
		uxReturn = uxTaskResetEventItemValue();

		if( ( uxReturn & taskUNBLOCKED_DUE_TO_BIT_SET ) == ( xEventBitsType ) 0 )
		{
			/* The task timed out, just return the current event bit value. */
			uxReturn = pxEventBits->uxEventBits;
		}
		else
		{
			/* The task unblocked because the bits were set.  Clear the control
			bits before returning the value. */
			uxReturn &= ~taskEVENT_BITS_CONTROL_BYTES;
		}
	}

	return uxReturn;
}
/*-----------------------------------------------------------*/

xEventBitsType xEventGroupClearBits( xEventGroupHandle xEventGroup, xEventBitsType uxBitsToClear )
{
xEVENT_BITS *pxEventBits = ( xEVENT_BITS * ) xEventGroup;
xEventBitsType uxReturn;

	/* Check the user is not attempting to clear the bits used by the kernel
	itself. */
	configASSERT( ( uxBitsToClear & taskEVENT_BITS_CONTROL_BYTES ) == 0 );

	uxBitsToClear = ~uxBitsToClear;
	taskENTER_CRITICAL();
	{
		/* The value returned is the event group value prior to the bits being
		cleared. */
		uxReturn = pxEventBits->uxEventBits;

		/* Clear the bits. */
		pxEventBits->uxEventBits &= uxBitsToClear;
	}
	taskEXIT_CRITICAL();

	return uxReturn;
}
/*-----------------------------------------------------------*/

xEventBitsType xEventGroupSetBits( xEventGroupHandle xEventGroup, xEventBitsType uxBitsToSet )
{
xListItem *pxListItem, *pxNext;
xListItem const *pxListEnd;
xList *pxList;
xEventBitsType uxBitsToClear = 0, uxBitsWaitedFor, uxControlBits;
xEVENT_BITS *pxEventBits = ( xEVENT_BITS * ) xEventGroup;
portBASE_TYPE xMatchFound = pdFALSE;

	/* Check the user is not attempting to set the bits used by the kernel
	itself. */
	configASSERT( ( uxBitsToSet & taskEVENT_BITS_CONTROL_BYTES ) == 0 );

	pxList = &( pxEventBits->xTasksWaitingForBits );
	pxListEnd = listGET_END_MARKER( pxList ); /*lint !e826 !e740 The mini list structure is used as the list end to save RAM.  This is checked and valid. */
	vTaskSuspendAll();
	{
		pxListItem = listGET_HEAD_ENTRY( pxList );

		/* Set the bits. */
		pxEventBits->uxEventBits |= uxBitsToSet;

		/* See if the new bit value should unblock any tasks. */
		while( pxListItem != pxListEnd )
		{
			pxNext = listGET_NEXT( pxListItem );
			uxBitsWaitedFor = listGET_LIST_ITEM_VALUE( pxListItem );
			xMatchFound = pdFALSE;

			/* Split the bits waited for from the control bits. */
			uxControlBits = uxBitsWaitedFor & taskEVENT_BITS_CONTROL_BYTES;
			uxBitsWaitedFor &= ~taskEVENT_BITS_CONTROL_BYTES;

			if( ( uxControlBits & taskWAIT_FOR_ALL_BITS ) == ( xEventBitsType ) 0 )
			{
				/* Just looking for single bit being set. */
				if( ( uxBitsWaitedFor & pxEventBits->uxEventBits ) != ( xEventBitsType ) 0 )
				{
					xMatchFound = pdTRUE;
				}
			}
			else if( ( uxBitsWaitedFor & pxEventBits->uxEventBits ) == uxBitsWaitedFor )
			{
				/* All bits are set. */
				xMatchFound = pdTRUE;
			}
			else
			{
				/* Need all bits to be set, but not all the bits were set. */
			}

			if( xMatchFound != pdFALSE )
			{
				/* The bits match.  Should the bits be cleared on exit? */
				if( ( uxControlBits & taskCLEAR_EVENTS_ON_EXIT_BIT ) != ( xEventBitsType ) 0 )
				{
					uxBitsToClear |= uxBitsWaitedFor;
				}

				/* Store the actual event flag value in the task's event list
				item before removing the task from the event list.  The
				taskUNBLOCKED_DUE_TO_BIT_SET bit is set so the task knows
				that is was unblocked due to its required bits matching, rather
				than because it timed out. */
				( void ) xTaskRemoveFromUnorderedEventList( pxListItem, pxEventBits->uxEventBits | taskUNBLOCKED_DUE_TO_BIT_SET );
			}

			/* Move onto the next list item.  Note pxListItem->pxNext is not
			used here as the list item may have been removed from the event list
			and inserted into the ready/pending reading list. */
			pxListItem = pxNext;
		}

		/* Clear any bits that matched when the taskCLEAR_EVENTS_ON_EXIT_BIT
		bit was set in the control word. */
		pxEventBits->uxEventBits &= ~uxBitsToClear;
	}
	( void ) xTaskResumeAll();

	return pxEventBits->uxEventBits;
}
/*-----------------------------------------------------------*/

void vEventGroupDelete( xEventGroupHandle xEventGroup )
{
xEVENT_BITS *pxEventBits = ( xEVENT_BITS * ) xEventGroup;
const xList *pxTasksWaitingForBits = &( pxEventBits->xTasksWaitingForBits );

	vTaskSuspendAll();
	{
		while( listCURRENT_LIST_LENGTH( pxTasksWaitingForBits ) > ( unsigned portBASE_TYPE ) 0 )
		{
			/* Unblock the task, returning 0 as the event list is being deleted
			and	cannot therefore have any bits set. */
			configASSERT( pxTasksWaitingForBits->xListEnd.pxNext != ( xListItem * ) &( pxTasksWaitingForBits->xListEnd ) );
			( void ) xTaskRemoveFromUnorderedEventList( pxTasksWaitingForBits->xListEnd.pxNext, ( portTickType ) taskUNBLOCKED_DUE_TO_BIT_SET );
		}

		vPortFree( pxEventBits );
	}
	( void ) xTaskResumeAll();
}
/*-----------------------------------------------------------*/

/* For internal use only - execute a 'set bits' command that was pended from
an interrupt. */
void vEventGroupSetBitsCallback( void *pvEventGroup, unsigned long ulBitsToSet )
{
	( void ) xEventGroupSetBits( pvEventGroup, ( xEventBitsType ) ulBitsToSet );
}


