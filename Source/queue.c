/*
	FreeRTOS.org V4.0.5 - Copyright (C) 2003-2006 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation; either version 2 of the License, or
	(at your option) any later version.

	FreeRTOS.org is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with FreeRTOS.org; if not, write to the Free Software
	Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

	A special exception to the GPL can be applied should you wish to distribute
	a combined work that includes FreeRTOS.org, without being obliged to provide
	the source code for any proprietary components.  See the licensing section
	of http://www.FreeRTOS.org for full details of how and when the exception
	can be applied.

	***************************************************************************
	See http://www.FreeRTOS.org for documentation, latest information, license
	and contact details.  Please ensure to read the configuration and relevant
	port sections of the online documentation.
	***************************************************************************
*/

/*
Changes from V1.01

	+ More use of 8bit data types.
	+ Function name prefixes changed where the data type returned has changed.

Changed from V2.0.0

	+ Added the queue locking mechanism and make more use of the scheduler
	  suspension feature to minimise the time interrupts have to be disabled
	  when accessing a queue.

Changed from V2.2.0

	+ Explicit use of 'signed' qualifier on portCHAR types added.

Changes from V3.0.0

	+ API changes as described on the FreeRTOS.org WEB site.

Changes from V3.2.3

	+ Added the queue functions that can be used from co-routines.

*/

#include <stdlib.h>
#include <string.h>
#include "FreeRTOS.h"
#include "task.h"
#include "croutine.h"

/*-----------------------------------------------------------
 * PUBLIC LIST API documented in list.h
 *----------------------------------------------------------*/

/* Constants used with the cRxLock and cTxLock structure members. */
#define queueUNLOCKED	( ( signed portBASE_TYPE ) -1 )

/*
 * Definition of the queue used by the scheduler.
 * Items are queued by copy, not reference.
 */
typedef struct QueueDefinition
{
	signed portCHAR *pcHead;				/*< Points to the beginning of the queue storage area. */
	signed portCHAR *pcTail;				/*< Points to the byte at the end of the queue storage area.  Once more byte is allocated than necessary to store the queue items, this is used as a marker. */

	signed portCHAR *pcWriteTo;				/*< Points to the free next place in the storage area. */
	signed portCHAR *pcReadFrom;			/*< Points to the last place that a queued item was read from. */

	xList xTasksWaitingToSend;				/*< List of tasks that are blocked waiting to post onto this queue.  Stored in priority order. */
	xList xTasksWaitingToReceive;			/*< List of tasks that are blocked waiting to read from this queue.  Stored in priority order. */

	unsigned portBASE_TYPE uxMessagesWaiting;/*< The number of items currently in the queue. */
	unsigned portBASE_TYPE uxLength;		/*< The length of the queue defined as the number of items it will hold, not the number of bytes. */
	unsigned portBASE_TYPE uxItemSize;		/*< The size of each items that the queue will hold. */

	signed portBASE_TYPE xRxLock;				/*< Stores the number of items received from the queue (removed from the queue) while the queue was locked.  Set to queueUNLOCKED when the queue is not locked. */
	signed portBASE_TYPE xTxLock;				/*< Stores the number of items transmitted to the queue (added to the queue) while the queue was locked.  Set to queueUNLOCKED when the queue is not locked. */
} xQUEUE;
/*-----------------------------------------------------------*/

/*
 * Inside this file xQueueHandle is a pointer to a xQUEUE structure.
 * To keep the definition private the API header file defines it as a
 * pointer to void.
 */
typedef xQUEUE * xQueueHandle;

/*
 * Prototypes for public functions are included here so we don't have to
 * include the API header file (as it defines xQueueHandle differently).  These
 * functions are documented in the API header file.
 */
xQueueHandle xQueueCreate( unsigned portBASE_TYPE uxQueueLength, unsigned portBASE_TYPE uxItemSize );
signed portBASE_TYPE xQueueSend( xQueueHandle xQueue, const void * pvItemToQueue, portTickType xTicksToWait );
unsigned portBASE_TYPE uxQueueMessagesWaiting( xQueueHandle pxQueue );
void vQueueDelete( xQueueHandle xQueue );
signed portBASE_TYPE xQueueSendFromISR( xQueueHandle pxQueue, const void *pvItemToQueue, signed portBASE_TYPE xTaskPreviouslyWoken );
signed portBASE_TYPE xQueueReceive( xQueueHandle pxQueue, void *pvBuffer, portTickType xTicksToWait );
signed portBASE_TYPE xQueueReceiveFromISR( xQueueHandle pxQueue, void *pvBuffer, signed portBASE_TYPE *pxTaskWoken );

#if configUSE_CO_ROUTINES == 1
	signed portBASE_TYPE xQueueCRSendFromISR( xQueueHandle pxQueue, const void *pvItemToQueue, signed portBASE_TYPE xCoRoutinePreviouslyWoken );
	signed portBASE_TYPE xQueueCRReceiveFromISR( xQueueHandle pxQueue, void *pvBuffer, signed portBASE_TYPE *pxTaskWoken );
	signed portBASE_TYPE xQueueCRSend( xQueueHandle pxQueue, const void *pvItemToQueue, portTickType xTicksToWait );
	signed portBASE_TYPE xQueueCRReceive( xQueueHandle pxQueue, void *pvBuffer, portTickType xTicksToWait );
#endif

/*
 * Unlocks a queue locked by a call to prvLockQueue.  Locking a queue does not
 * prevent an ISR from adding or removing items to the queue, but does prevent
 * an ISR from removing tasks from the queue event lists.  If an ISR finds a
 * queue is locked it will instead increment the appropriate queue lock count
 * to indicate that a task may require unblocking.  When the queue in unlocked
 * these lock counts are inspected, and the appropriate action taken.
 */
static signed portBASE_TYPE prvUnlockQueue( xQueueHandle pxQueue );

/*
 * Uses a critical section to determine if there is any data in a queue.
 *
 * @return pdTRUE if the queue contains no items, otherwise pdFALSE.
 */
static signed portBASE_TYPE prvIsQueueEmpty( const xQueueHandle pxQueue );

/*
 * Uses a critical section to determine if there is any space in a queue.
 *
 * @return pdTRUE if there is no space, otherwise pdFALSE;
 */
static signed portBASE_TYPE prvIsQueueFull( const xQueueHandle pxQueue );

/*
 * Macro that copies an item into the queue.  This is done by copying the item
 * byte for byte, not by reference.  Updates the queue state to ensure it's
 * integrity after the copy.
 */
#define prvCopyQueueData( pxQueue, pvItemToQueue )												\
{																								\
	memcpy( ( void * ) pxQueue->pcWriteTo, pvItemToQueue, ( unsigned ) pxQueue->uxItemSize );	\
	++( pxQueue->uxMessagesWaiting );															\
	pxQueue->pcWriteTo += pxQueue->uxItemSize;													\
	if( pxQueue->pcWriteTo >= pxQueue->pcTail )													\
	{																							\
		pxQueue->pcWriteTo = pxQueue->pcHead;													\
	}																							\
}
/*-----------------------------------------------------------*/

/*
 * Macro to mark a queue as locked.  Locking a queue prevents an ISR from
 * accessing the queue event lists.
 */
#define prvLockQueue( pxQueue )			\
{										\
	taskENTER_CRITICAL();				\
		++( pxQueue->xRxLock );			\
		++( pxQueue->xTxLock );			\
	taskEXIT_CRITICAL();				\
}
/*-----------------------------------------------------------*/


/*-----------------------------------------------------------
 * PUBLIC QUEUE MANAGEMENT API documented in queue.h
 *----------------------------------------------------------*/

xQueueHandle xQueueCreate( unsigned portBASE_TYPE uxQueueLength, unsigned portBASE_TYPE uxItemSize )
{
xQUEUE *pxNewQueue;
size_t xQueueSizeInBytes;

	/* Allocate the new queue structure. */
	if( uxQueueLength > ( unsigned portBASE_TYPE ) 0 )
	{
		pxNewQueue = ( xQUEUE * ) pvPortMalloc( sizeof( xQUEUE ) );
		if( pxNewQueue != NULL )
		{
			/* Create the list of pointers to queue items.  The queue is one byte
			longer than asked for to make wrap checking easier/faster. */
			xQueueSizeInBytes = ( size_t ) ( uxQueueLength * uxItemSize ) + ( size_t ) 1;

			pxNewQueue->pcHead = ( signed portCHAR * ) pvPortMalloc( xQueueSizeInBytes );
			if( pxNewQueue->pcHead != NULL )
			{
				/* Initialise the queue members as described above where the
				queue type is defined. */
				pxNewQueue->pcTail = pxNewQueue->pcHead + ( uxQueueLength * uxItemSize );
				pxNewQueue->uxMessagesWaiting = 0;
				pxNewQueue->pcWriteTo = pxNewQueue->pcHead;
				pxNewQueue->pcReadFrom = pxNewQueue->pcHead + ( ( uxQueueLength - 1 ) * uxItemSize );
				pxNewQueue->uxLength = uxQueueLength;
				pxNewQueue->uxItemSize = uxItemSize;
				pxNewQueue->xRxLock = queueUNLOCKED;
				pxNewQueue->xTxLock = queueUNLOCKED;

				/* Likewise ensure the event queues start with the correct state. */
				vListInitialise( &( pxNewQueue->xTasksWaitingToSend ) );
				vListInitialise( &( pxNewQueue->xTasksWaitingToReceive ) );

				return  pxNewQueue;
			}
			else
			{
				vPortFree( pxNewQueue );
			}
		}
	}

	/* Will only reach here if we could not allocate enough memory or no memory
	was required. */
	return NULL;
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xQueueSend( xQueueHandle pxQueue, const void *pvItemToQueue, portTickType xTicksToWait )
{
signed portBASE_TYPE xReturn;

	/* Make sure other tasks do not access the queue. */
	vTaskSuspendAll();

	/* It is important that this is the only thread/ISR that modifies the
	ready or delayed lists until xTaskResumeAll() is called.  Places where
	the ready/delayed lists are modified include:

		+ vTaskDelay() -  Nothing can call vTaskDelay as the scheduler is
		  suspended, vTaskDelay() cannot be called from an ISR.
		+ vTaskPrioritySet() - Has a critical section around the access.
		+ vTaskSwitchContext() - This will not get executed while the scheduler
		  is suspended.
		+ prvCheckDelayedTasks() - This will not get executed while the
		  scheduler is suspended.
		+ xTaskCreate() - Has a critical section around the access.
		+ vTaskResume() - Has a critical section around the access.
		+ xTaskResumeAll() - Has a critical section around the access.
		+ xTaskRemoveFromEventList - Checks to see if the scheduler is
		  suspended.  If so then the TCB being removed from the event is
		  removed from the event and added to the xPendingReadyList.
	*/

	/* Make sure interrupts do not access the queue event list. */
	prvLockQueue( pxQueue );

	/* It is important that interrupts to not access the event list of the
	queue being modified here.  Places where the event list is modified
	include:

		+ xQueueSendFromISR().  This checks the lock on the queue to see if
		  it has access.  If the queue is locked then the Tx lock count is
		  incremented to signify that a task waiting for data can be made ready
		  once the queue lock is removed.  If the queue is not locked then
		  a task can be moved from the event list, but will not be removed
		  from the delayed list or placed in the ready list until the scheduler
		  is unlocked.

		+ xQueueReceiveFromISR().  As per xQueueSendFromISR().
	*/
		
	/* If the queue is already full we may have to block. */
	if( prvIsQueueFull( pxQueue ) )
	{
		/* The queue is full - do we want to block or just leave without
		posting? */
		if( xTicksToWait > ( portTickType ) 0 )
		{
			/* We are going to place ourselves on the xTasksWaitingToSend event
			list, and will get woken should the delay expire, or space become
			available on the queue.
			
			As detailed above we do not require mutual exclusion on the event
			list as nothing else can modify it or the ready lists while we
			have the scheduler suspended and queue locked.
			
			It is possible that an ISR has removed data from the queue since we
			checked if any was available.  If this is the case then the data
			will have been copied from the queue, and the queue variables
			updated, but the event list will not yet have been checked to see if
			anything is waiting as the queue is locked. */
			vTaskPlaceOnEventList( &( pxQueue->xTasksWaitingToSend ), xTicksToWait );

			/* Force a context switch now as we are blocked.  We can do
			this from within a critical section as the task we are
			switching to has its own context.  When we return here (i.e. we
			unblock) we will leave the critical section as normal.
			
			It is possible that an ISR has caused an event on an unrelated and
			unlocked queue.  If this was the case then the event list for that
			queue will have been updated but the ready lists left unchanged -
			instead the readied task will have been added to the pending ready
			list. */
			taskENTER_CRITICAL();
			{
				/* We can safely unlock the queue and scheduler here as
				interrupts are disabled.  We must not yield with anything
				locked, but we can yield from within a critical section.
				
				Tasks that have been placed on the pending ready list cannot
				be tasks that are waiting for events on this queue.  See
				in comment xTaskRemoveFromEventList(). */
				prvUnlockQueue( pxQueue );

				/* Resuming the scheduler may cause a yield.  If so then there
				is no point yielding again here. */
				if( !xTaskResumeAll() )
				{
					taskYIELD();
				}

				/* Before leaving the critical section we have to ensure
				exclusive access again. */
				vTaskSuspendAll();
				prvLockQueue( pxQueue );				
			}
			taskEXIT_CRITICAL();
		}
	}
		
	/* When we are here it is possible that we unblocked as space became
	available on the queue.  It is also possible that an ISR posted to the
	queue since we left the critical section, so it may be that again there
	is no space.  This would only happen if a task and ISR post onto the
	same queue. */
	taskENTER_CRITICAL();
	{
		if( pxQueue->uxMessagesWaiting < pxQueue->uxLength )
		{
			/* There is room in the queue, copy the data into the queue. */			
			prvCopyQueueData( pxQueue, pvItemToQueue );		
			xReturn = pdPASS;

			/* Update the TxLock count so prvUnlockQueue knows to check for
			tasks waiting for data to become available in the queue. */
			++( pxQueue->xTxLock );
		}
		else
		{
			xReturn = errQUEUE_FULL;
		}
	}
	taskEXIT_CRITICAL();

	/* We no longer require exclusive access to the queue.  prvUnlockQueue
	will remove any tasks suspended on a receive if either this function
	or an ISR has posted onto the queue. */
	if( prvUnlockQueue( pxQueue ) )
	{
		/* Resume the scheduler - making ready any tasks that were woken
		by an event while the scheduler was locked.  Resuming the
		scheduler may cause a yield, in which case there is no point
		yielding again here. */
		if( !xTaskResumeAll() )
		{
			taskYIELD();
		}
	}
	else
	{
		/* Resume the scheduler - making ready any tasks that were woken
		by an event while the scheduler was locked. */
		xTaskResumeAll();
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xQueueSendFromISR( xQueueHandle pxQueue, const void *pvItemToQueue, signed portBASE_TYPE xTaskPreviouslyWoken )
{
	/* Similar to xQueueSend, except we don't block if there is no room in the
	queue.  Also we don't directly wake a task that was blocked on a queue
	read, instead we return a flag to say whether a context switch is required
	or not (i.e. has a task with a higher priority than us been woken by this
	post). */
	if( pxQueue->uxMessagesWaiting < pxQueue->uxLength )
	{
		prvCopyQueueData( pxQueue, pvItemToQueue );

		/* If the queue is locked we do not alter the event list.  This will
		be done when the queue is unlocked later. */
		if( pxQueue->xTxLock == queueUNLOCKED )
		{
			/* We only want to wake one task per ISR, so check that a task has
			not already been woken. */
			if( !xTaskPreviouslyWoken )		
			{
				if( !listLIST_IS_EMPTY( &( pxQueue->xTasksWaitingToReceive ) ) )
				{
					if( xTaskRemoveFromEventList( &( pxQueue->xTasksWaitingToReceive ) ) != pdFALSE )
					{
						/* The task waiting has a higher priority so record that a
						context	switch is required. */
						return pdTRUE;
					}
				}
			}
		}
		else
		{
			/* Increment the lock count so the task that unlocks the queue
			knows that data was posted while it was locked. */
			++( pxQueue->xTxLock );
		}
	}

	return xTaskPreviouslyWoken;
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xQueueReceive( xQueueHandle pxQueue, void *pvBuffer, portTickType xTicksToWait )
{
signed portBASE_TYPE xReturn;

	/* This function is very similar to xQueueSend().  See comments within
	xQueueSend() for a more detailed explanation.

	Make sure other tasks do not access the queue. */
	vTaskSuspendAll();

	/* Make sure interrupts do not access the queue. */
	prvLockQueue( pxQueue );

	/* If there are no messages in the queue we may have to block. */
	if( prvIsQueueEmpty( pxQueue ) )
	{
		/* There are no messages in the queue, do we want to block or just
		leave with nothing? */			
		if( xTicksToWait > ( portTickType ) 0 )
		{
			vTaskPlaceOnEventList( &( pxQueue->xTasksWaitingToReceive ), xTicksToWait );
			taskENTER_CRITICAL();
			{
				prvUnlockQueue( pxQueue );
				if( !xTaskResumeAll() )
				{
					taskYIELD();
				}

				vTaskSuspendAll();
				prvLockQueue( pxQueue );
			}
			taskEXIT_CRITICAL();
		}
	}

	taskENTER_CRITICAL();
	{
		if( pxQueue->uxMessagesWaiting > ( unsigned portBASE_TYPE ) 0 )
		{
			pxQueue->pcReadFrom += pxQueue->uxItemSize;
			if( pxQueue->pcReadFrom >= pxQueue->pcTail )
			{
				pxQueue->pcReadFrom = pxQueue->pcHead;
			}
			--( pxQueue->uxMessagesWaiting );
			memcpy( ( void * ) pvBuffer, ( void * ) pxQueue->pcReadFrom, ( unsigned ) pxQueue->uxItemSize );

			/* Increment the lock count so prvUnlockQueue knows to check for
			tasks waiting for space to become available on the queue. */
			++( pxQueue->xRxLock );
			xReturn = pdPASS;
		}
		else
		{
			xReturn = pdFAIL;
		}
	}
	taskEXIT_CRITICAL();

	/* We no longer require exclusive access to the queue. */
	if( prvUnlockQueue( pxQueue ) )
	{
		if( !xTaskResumeAll() )
		{
			taskYIELD();
		}
	}
	else
	{
		xTaskResumeAll();
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xQueueReceiveFromISR( xQueueHandle pxQueue, void *pvBuffer, signed portBASE_TYPE *pxTaskWoken )
{
signed portBASE_TYPE xReturn;

	/* We cannot block from an ISR, so check there is data available. */
	if( pxQueue->uxMessagesWaiting > ( unsigned portBASE_TYPE ) 0 )
	{
		/* Copy the data from the queue. */
		pxQueue->pcReadFrom += pxQueue->uxItemSize;
		if( pxQueue->pcReadFrom >= pxQueue->pcTail )
		{
			pxQueue->pcReadFrom = pxQueue->pcHead;
		}
		--( pxQueue->uxMessagesWaiting );
		memcpy( ( void * ) pvBuffer, ( void * ) pxQueue->pcReadFrom, ( unsigned ) pxQueue->uxItemSize );

		/* If the queue is locked we will not modify the event list.  Instead
		we update the lock count so the task that unlocks the queue will know
		that an ISR has removed data while the queue was locked. */
		if( pxQueue->xRxLock == queueUNLOCKED )
		{
			/* We only want to wake one task per ISR, so check that a task has
			not already been woken. */
			if( !( *pxTaskWoken ) )
			{
				if( !listLIST_IS_EMPTY( &( pxQueue->xTasksWaitingToSend ) ) )
				{
					if( xTaskRemoveFromEventList( &( pxQueue->xTasksWaitingToSend ) ) != pdFALSE )
					{
						/* The task waiting has a higher priority than us so
						force a context switch. */
						*pxTaskWoken = pdTRUE;
					}
				}
			}
		}
		else
		{
			/* Increment the lock count so the task that unlocks the queue
			knows that data was removed while it was locked. */
			++( pxQueue->xRxLock );
		}

		xReturn = pdPASS;
	}
	else
	{
		xReturn = pdFAIL;
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

unsigned portBASE_TYPE uxQueueMessagesWaiting( xQueueHandle pxQueue )
{
unsigned portBASE_TYPE uxReturn;

	taskENTER_CRITICAL();
		uxReturn = pxQueue->uxMessagesWaiting;
	taskEXIT_CRITICAL();

	return uxReturn;
}
/*-----------------------------------------------------------*/

void vQueueDelete( xQueueHandle pxQueue )
{
	vPortFree( pxQueue->pcHead );
	vPortFree( pxQueue );
}
/*-----------------------------------------------------------*/

static signed portBASE_TYPE prvUnlockQueue( xQueueHandle pxQueue )
{
signed portBASE_TYPE xYieldRequired = pdFALSE;

	/* THIS FUNCTION MUST BE CALLED WITH THE SCHEDULER SUSPENDED. */

	/* The lock counts contains the number of extra data items placed or
	removed from the queue while the queue was locked.  When a queue is
	locked items can be added or removed, but the event lists cannot be
	updated. */
	taskENTER_CRITICAL();
	{
		--( pxQueue->xTxLock );

		/* See if data was added to the queue while it was locked. */
		if( pxQueue->xTxLock > queueUNLOCKED )
		{
			pxQueue->xTxLock = queueUNLOCKED;

			/* Data was posted while the queue was locked.  Are any tasks
			blocked waiting for data to become available? */
			if( !listLIST_IS_EMPTY( &( pxQueue->xTasksWaitingToReceive ) ) )
			{
				/* Tasks that are removed from the event list will get added to
				the pending ready list as the scheduler is still suspended. */
				if( xTaskRemoveFromEventList( &( pxQueue->xTasksWaitingToReceive ) ) != pdFALSE )
				{
					/* The task waiting has a higher priority so record that a
					context	switch is required. */
					xYieldRequired = pdTRUE;
				}
			}			
		}
	}
	taskEXIT_CRITICAL();

	/* Do the same for the Rx lock. */
	taskENTER_CRITICAL();
	{
		--( pxQueue->xRxLock );

		if( pxQueue->xRxLock > queueUNLOCKED )
		{
			pxQueue->xRxLock = queueUNLOCKED;

			if( !listLIST_IS_EMPTY( &( pxQueue->xTasksWaitingToSend ) ) )
			{
				if( xTaskRemoveFromEventList( &( pxQueue->xTasksWaitingToSend ) ) != pdFALSE )
				{
					xYieldRequired = pdTRUE;
				}
			}			
		}
	}
	taskEXIT_CRITICAL();

	return xYieldRequired;
}
/*-----------------------------------------------------------*/

static signed portBASE_TYPE prvIsQueueEmpty( const xQueueHandle pxQueue )
{
signed portBASE_TYPE xReturn;

	taskENTER_CRITICAL();
		xReturn = ( pxQueue->uxMessagesWaiting == ( unsigned portBASE_TYPE ) 0 );
	taskEXIT_CRITICAL();

	return xReturn;
}
/*-----------------------------------------------------------*/

static signed portBASE_TYPE prvIsQueueFull( const xQueueHandle pxQueue )
{
signed portBASE_TYPE xReturn;

	taskENTER_CRITICAL();
		xReturn = ( pxQueue->uxMessagesWaiting == pxQueue->uxLength );
	taskEXIT_CRITICAL();

	return xReturn;
}
/*-----------------------------------------------------------*/

#if configUSE_CO_ROUTINES == 1
signed portBASE_TYPE xQueueCRSend( xQueueHandle pxQueue, const void *pvItemToQueue, portTickType xTicksToWait )
{
signed portBASE_TYPE xReturn;
		
	/* If the queue is already full we may have to block.  A critical section
	is required to prevent an interrupt removing something from the queue 
	between the check to see if the queue is full and blocking on the queue. */
	portDISABLE_INTERRUPTS();
	{
		if( prvIsQueueFull( pxQueue ) )
		{
			/* The queue is full - do we want to block or just leave without
			posting? */
			if( xTicksToWait > ( portTickType ) 0 )
			{
				/* As this is called from a coroutine we cannot block directly, but
				return indicating that we need to block. */
				vCoRoutineAddToDelayedList( xTicksToWait, &( pxQueue->xTasksWaitingToSend ) );				
				portENABLE_INTERRUPTS();
				return errQUEUE_BLOCKED;
			}
			else
			{
				portENABLE_INTERRUPTS();
				return errQUEUE_FULL;
			}
		}
	}
	portENABLE_INTERRUPTS();
		
	portNOP();

	portDISABLE_INTERRUPTS();
	{
		if( pxQueue->uxMessagesWaiting < pxQueue->uxLength )
		{
			/* There is room in the queue, copy the data into the queue. */			
			prvCopyQueueData( pxQueue, pvItemToQueue );		
			xReturn = pdPASS;

			/* Were any co-routines waiting for data to become available? */
			if( !listLIST_IS_EMPTY( &( pxQueue->xTasksWaitingToReceive ) ) )
			{
				/* In this instance the co-routine could be placed directly 
				into the ready list as we are within a critical section.  
				Instead the same pending ready list mechansim is used as if
				the event were caused from within an interrupt. */
				if( xCoRoutineRemoveFromEventList( &( pxQueue->xTasksWaitingToReceive ) ) != pdFALSE )
				{
					/* The co-routine waiting has a higher priority so record 
					that a yield might be appropriate. */
					xReturn = errQUEUE_YIELD;
				}
			}
		}
		else
		{
			xReturn = errQUEUE_FULL;
		}
	}
	portENABLE_INTERRUPTS();

	return xReturn;
}
#endif
/*-----------------------------------------------------------*/

#if configUSE_CO_ROUTINES == 1
signed portBASE_TYPE xQueueCRReceive( xQueueHandle pxQueue, void *pvBuffer, portTickType xTicksToWait )
{
signed portBASE_TYPE xReturn;

	/* If the queue is already empty we may have to block.  A critical section
	is required to prevent an interrupt adding something to the queue 
	between the check to see if the queue is empty and blocking on the queue. */
	portDISABLE_INTERRUPTS();
	{
		if( prvIsQueueEmpty( pxQueue ) )
		{
			/* There are no messages in the queue, do we want to block or just
			leave with nothing? */			
			if( xTicksToWait > ( portTickType ) 0 )
			{
				/* As this is a co-routine we cannot block directly, but return
				indicating that we need to block. */
				vCoRoutineAddToDelayedList( xTicksToWait, &( pxQueue->xTasksWaitingToReceive ) );
				portENABLE_INTERRUPTS();
				return errQUEUE_BLOCKED;
			}
			else
			{
				portENABLE_INTERRUPTS();
				return errQUEUE_FULL;
			}
		}
	}
	portENABLE_INTERRUPTS();

	portNOP();

	portDISABLE_INTERRUPTS();
	{
		if( pxQueue->uxMessagesWaiting > ( unsigned portBASE_TYPE ) 0 )
		{
			/* Data is available from the queue. */
			pxQueue->pcReadFrom += pxQueue->uxItemSize;
			if( pxQueue->pcReadFrom >= pxQueue->pcTail )
			{
				pxQueue->pcReadFrom = pxQueue->pcHead;
			}
			--( pxQueue->uxMessagesWaiting );
			memcpy( ( void * ) pvBuffer, ( void * ) pxQueue->pcReadFrom, ( unsigned ) pxQueue->uxItemSize );

			xReturn = pdPASS;

			/* Were any co-routines waiting for space to become available? */
			if( !listLIST_IS_EMPTY( &( pxQueue->xTasksWaitingToSend ) ) )
			{
				/* In this instance the co-routine could be placed directly 
				into the ready list as we are within a critical section.  
				Instead the same pending ready list mechansim is used as if
				the event were caused from within an interrupt. */
				if( xCoRoutineRemoveFromEventList( &( pxQueue->xTasksWaitingToSend ) ) != pdFALSE )
				{
					xReturn = errQUEUE_YIELD;
				}
			}	
		}
		else
		{
			xReturn = pdFAIL;
		}
	}
	portENABLE_INTERRUPTS();

	return xReturn;
}
#endif
/*-----------------------------------------------------------*/



#if configUSE_CO_ROUTINES == 1
signed portBASE_TYPE xQueueCRSendFromISR( xQueueHandle pxQueue, const void *pvItemToQueue, signed portBASE_TYPE xCoRoutinePreviouslyWoken )
{
	/* Cannot block within an ISR so if there is no space on the queue then
	exit without doing anything. */
	if( pxQueue->uxMessagesWaiting < pxQueue->uxLength )
	{
		prvCopyQueueData( pxQueue, pvItemToQueue );

		/* We only want to wake one co-routine per ISR, so check that a 
		co-routine has not already been woken. */
		if( !xCoRoutinePreviouslyWoken )		
		{
			if( !listLIST_IS_EMPTY( &( pxQueue->xTasksWaitingToReceive ) ) )
			{
				if( xCoRoutineRemoveFromEventList( &( pxQueue->xTasksWaitingToReceive ) ) != pdFALSE )
				{
					return pdTRUE;
				}
			}
		}
	}

	return xCoRoutinePreviouslyWoken;
}
#endif
/*-----------------------------------------------------------*/

#if configUSE_CO_ROUTINES == 1
signed portBASE_TYPE xQueueCRReceiveFromISR( xQueueHandle pxQueue, void *pvBuffer, signed portBASE_TYPE *pxCoRoutineWoken )
{
signed portBASE_TYPE xReturn;

	/* We cannot block from an ISR, so check there is data available. If
	not then just leave without doing anything. */
	if( pxQueue->uxMessagesWaiting > ( unsigned portBASE_TYPE ) 0 )
	{
		/* Copy the data from the queue. */
		pxQueue->pcReadFrom += pxQueue->uxItemSize;
		if( pxQueue->pcReadFrom >= pxQueue->pcTail )
		{
			pxQueue->pcReadFrom = pxQueue->pcHead;
		}
		--( pxQueue->uxMessagesWaiting );
		memcpy( ( void * ) pvBuffer, ( void * ) pxQueue->pcReadFrom, ( unsigned ) pxQueue->uxItemSize );

		if( !( *pxCoRoutineWoken ) )
		{
			if( !listLIST_IS_EMPTY( &( pxQueue->xTasksWaitingToSend ) ) )
			{
				if( xCoRoutineRemoveFromEventList( &( pxQueue->xTasksWaitingToSend ) ) != pdFALSE )
				{
					*pxCoRoutineWoken = pdTRUE;
				}
			}
		}

		xReturn = pdPASS;
	}
	else
	{
		xReturn = pdFAIL;
	}

	return xReturn;
}
#endif
/*-----------------------------------------------------------*/

