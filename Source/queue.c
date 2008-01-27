/*
	FreeRTOS.org V4.7.0 - Copyright (C) 2003-2007 Richard Barry.

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

	Also see http://www.SafeRTOS.com a version that has been certified for use
	in safety critical systems, plus commercial licensing, development and
	support options.
	***************************************************************************
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
#define queueERRONEOUS_UNBLOCK					( -1 )

/* For internal use only. */
#define	queueSEND_TO_BACK	( 0 )
#define	queueSEND_TO_FRONT	( 1 )

/* Effectively make a union out of the xQUEUE structure. */
#define pxMutexHolder				pcTail
#define uxQueueType					pcHead
#define uxRecursiveCallCount		pcReadFrom
#define queueQUEUE_IS_MUTEX			NULL

/* Semaphores do not actually store or copy data, so have an items size of
zero. */
#define queueSEMAPHORE_QUEUE_ITEM_LENGTH ( 0 )
#define queueDONT_BLOCK					 ( ( portTickType ) 0 )
#define queueMUTEX_GIVE_BLOCK_TIME		 ( ( portTickType ) 0 )
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

	volatile unsigned portBASE_TYPE uxMessagesWaiting;/*< The number of items currently in the queue. */
	unsigned portBASE_TYPE uxLength;		/*< The length of the queue defined as the number of items it will hold, not the number of bytes. */
	unsigned portBASE_TYPE uxItemSize;		/*< The size of each items that the queue will hold. */

	signed portBASE_TYPE xRxLock;			/*< Stores the number of items received from the queue (removed from the queue) while the queue was locked.  Set to queueUNLOCKED when the queue is not locked. */
	signed portBASE_TYPE xTxLock;			/*< Stores the number of items transmitted to the queue (added to the queue) while the queue was locked.  Set to queueUNLOCKED when the queue is not locked. */
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
signed portBASE_TYPE xQueueGenericSend( xQueueHandle xQueue, const void * const pvItemToQueue, portTickType xTicksToWait, portBASE_TYPE xCopyPosition );
unsigned portBASE_TYPE uxQueueMessagesWaiting( const xQueueHandle pxQueue );
void vQueueDelete( xQueueHandle xQueue );
signed portBASE_TYPE xQueueGenericSendFromISR( xQueueHandle pxQueue, const void * const pvItemToQueue, signed portBASE_TYPE xTaskPreviouslyWoken, portBASE_TYPE xCopyPosition );
signed portBASE_TYPE xQueueGenericReceive( xQueueHandle pxQueue, const void * const pvBuffer, portTickType xTicksToWait, portBASE_TYPE xJustPeeking );
signed portBASE_TYPE xQueueReceiveFromISR( xQueueHandle pxQueue, const void * const pvBuffer, signed portBASE_TYPE *pxTaskWoken );
xQueueHandle xQueueCreateMutex( void );
xQueueHandle xQueueCreateCountingSemaphore( unsigned portBASE_TYPE uxCountValue, unsigned portBASE_TYPE uxInitialCount );
portBASE_TYPE xQueueTakeMutexRecursive( xQueueHandle xMutex, portTickType xBlockTime );
portBASE_TYPE xQueueGiveMutexRecursive( xQueueHandle xMutex );
signed portBASE_TYPE xQueueAltGenericSend( xQueueHandle pxQueue, const void * const pvItemToQueue, portTickType xTicksToWait, portBASE_TYPE xCopyPosition );
signed portBASE_TYPE xQueueAltGenericReceive( xQueueHandle pxQueue, const void * const pvBuffer, portTickType xTicksToWait, portBASE_TYPE xJustPeeking );

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
static void prvUnlockQueue( xQueueHandle pxQueue );

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
 * Copies an item into the queue, either at the front of the queue or the
 * back of the queue.
 */
static void prvCopyDataToQueue( xQUEUE *pxQueue, const void *pvItemToQueue, portBASE_TYPE xPosition );

/*
 * Copies an item out of a queue.
 */
static void prvCopyDataFromQueue( xQUEUE * const pxQueue, const void *pvBuffer );
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

#if ( configUSE_MUTEXES == 1 )

	xQueueHandle xQueueCreateMutex( void )
	{
	xQUEUE *pxNewQueue;
	
		/* Allocate the new queue structure. */
		pxNewQueue = ( xQUEUE * ) pvPortMalloc( sizeof( xQUEUE ) );
		if( pxNewQueue != NULL )
		{
			/* Information required for priority inheritance. */
			pxNewQueue->pxMutexHolder = NULL;
			pxNewQueue->uxQueueType = queueQUEUE_IS_MUTEX;
	
			/* Queues used as a mutex no data is actually copied into or out
			of the queue. */
			pxNewQueue->pcWriteTo = NULL;
			pxNewQueue->pcReadFrom = NULL;
			
			/* Each mutex has a length of 1 (like a binary semaphore) and
			an item size of 0 as nothing is actually copied into or out
			of the mutex. */
			pxNewQueue->uxMessagesWaiting = 0;
			pxNewQueue->uxLength = 1;
			pxNewQueue->uxItemSize = 0;
			pxNewQueue->xRxLock = queueUNLOCKED;
			pxNewQueue->xTxLock = queueUNLOCKED;
	
			/* Ensure the event queues start with the correct state. */
			vListInitialise( &( pxNewQueue->xTasksWaitingToSend ) );
			vListInitialise( &( pxNewQueue->xTasksWaitingToReceive ) );

			/* Start with the semaphore in the expected state. */
			xQueueGenericSend( pxNewQueue, NULL, 0, queueSEND_TO_BACK );
		}
	
		return pxNewQueue;
	}

#endif /* configUSE_MUTEXES */
/*-----------------------------------------------------------*/

#if configUSE_RECURSIVE_MUTEXES == 1

	portBASE_TYPE xQueueGiveMutexRecursive( xQueueHandle pxMutex )
	{
	portBASE_TYPE xReturn;

		/* If this is the task that holds the mutex then pxMutexHolder will not 
		change outside of this task.  If this task does not hold the mutex then
		pxMutexHolder can never coincidentally equal the tasks handle, and as
		this is the only condition we are interested in it does not matter if
		pxMutexHolder is accessed simultaneously by another task.  Therefore no
		mutual exclusion is required to test the pxMutexHolder variable. */
		if( pxMutex->pxMutexHolder == xTaskGetCurrentTaskHandle() )
		{
			/* uxRecursiveCallCount cannot be zero if pxMutexHolder is equal to
			the task handle, therefore no underflow check is required.  Also, 
			uxRecursiveCallCount is only modified by the mutex holder, and as
			there can only be one, no mutual exclusion is required to modify the
			uxRecursiveCallCount member. */
			( pxMutex->uxRecursiveCallCount )--;

			/* Have we unwound the call count? */
			if( pxMutex->uxRecursiveCallCount == 0 )
			{
				/* Return the mutex.  This will automatically unblock any other
				task that might be waiting to access the mutex. */
                xQueueGenericSend( pxMutex, NULL, queueMUTEX_GIVE_BLOCK_TIME, queueSEND_TO_BACK );
			}

			xReturn = pdPASS;
		}
		else
		{
			/* We cannot give the mutex because we are not the holder. */
			xReturn = pdFAIL;
		}

		return xReturn;
	}

#endif /* configUSE_RECURSIVE_MUTEXES */
/*-----------------------------------------------------------*/

#if configUSE_RECURSIVE_MUTEXES == 1

	portBASE_TYPE xQueueTakeMutexRecursive( xQueueHandle pxMutex, portTickType xBlockTime )
	{
	portBASE_TYPE xReturn;

		/* Comments regarding mutual exclusion as per those within 
		xQueueGiveMutexRecursive(). */

		if( pxMutex->pxMutexHolder == xTaskGetCurrentTaskHandle() )
		{
			( pxMutex->uxRecursiveCallCount )++;
			xReturn = pdPASS;
		}
		else
		{
            xReturn = xQueueGenericReceive( pxMutex, NULL, xBlockTime, pdFALSE );

			/* pdPASS will only be returned if we successfully obtained the mutex,
			we may have blocked to reach here. */
			if( xReturn == pdPASS )
			{
				( pxMutex->uxRecursiveCallCount )++;
			}
		}

		return xReturn;
	}

#endif /* configUSE_RECURSIVE_MUTEXES */
/*-----------------------------------------------------------*/

#if configUSE_COUNTING_SEMAPHORES == 1

	xQueueHandle xQueueCreateCountingSemaphore( unsigned portBASE_TYPE uxCountValue, unsigned portBASE_TYPE uxInitialCount )
	{
	xQueueHandle pxHandle;
	
		pxHandle = xQueueCreate( ( unsigned portBASE_TYPE ) uxCountValue, queueSEMAPHORE_QUEUE_ITEM_LENGTH );

		if( pxHandle != NULL )
		{
			pxHandle->uxMessagesWaiting = uxInitialCount;
		}

		return pxHandle;
	}

#endif /* configUSE_COUNTING_SEMAPHORES */
/*-----------------------------------------------------------*/

signed portBASE_TYPE xQueueGenericSend( xQueueHandle pxQueue, const void * const pvItemToQueue, portTickType xTicksToWait, portBASE_TYPE xCopyPosition )
{
signed portBASE_TYPE xReturn = pdPASS;
xTimeOutType xTimeOut;

	/* Make sure other tasks do not access the queue. */
	vTaskSuspendAll();

	/* Capture the current time status for future reference. */
	vTaskSetTimeOutState( &xTimeOut );

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

		+ xQueueGenericSendFromISR().  This checks the lock on the queue to see
		  if it has access.  If the queue is locked then the Tx lock count is
		  incremented to signify that a task waiting for data can be made ready
		  once the queue lock is removed.  If the queue is not locked then
		  a task can be moved from the event list, but will not be removed
		  from the delayed list or placed in the ready list until the scheduler
		  is unlocked.

		+ xQueueReceiveFromISR().  As per xQueueGenericSendFromISR().
	*/
		
	/* If the queue is already full we may have to block. */
	do
	{
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

					/* We want to check to see if the queue is still full
					before leaving the critical section.  This is to prevent
					this task placing an item into the queue due to an
					interrupt making space on the queue between critical
					sections (when there might be a higher priority task
					blocked on the queue that cannot run yet because the
					scheduler gets suspended). */
					if( pxQueue->uxMessagesWaiting == pxQueue->uxLength )
					{
						/* We unblocked but there is no space in the queue,
						we probably timed out. */
						xReturn = errQUEUE_FULL;
					}
	
					/* Before leaving the critical section we have to ensure
					exclusive access again. */
					vTaskSuspendAll();
					prvLockQueue( pxQueue );				
				}
				taskEXIT_CRITICAL();
			}
		}
			
		/* If xReturn is errQUEUE_FULL then we unblocked when the queue
		was still full.  Don't check it again now as it is possible that
		an interrupt has removed an item from the queue since we left the
		critical section and we don't want to write to the queue in case
		there is a task of higher priority blocked waiting for space to
		be available on the queue.  If this is the case the higher priority
		task will execute when the scheduler is unsupended. */
		if( xReturn != errQUEUE_FULL )
		{
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
					prvCopyDataToQueue( pxQueue, pvItemToQueue, xCopyPosition );
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
		}

		if( xReturn == errQUEUE_FULL )
		{
			if( xTicksToWait > 0 )
			{
				if( xTaskCheckForTimeOut( &xTimeOut, &xTicksToWait ) == pdFALSE )
				{
					xReturn = queueERRONEOUS_UNBLOCK;
				}
			}
		}
	}
	while( xReturn == queueERRONEOUS_UNBLOCK );

	prvUnlockQueue( pxQueue );
	xTaskResumeAll();

	return xReturn;
}
/*-----------------------------------------------------------*/

#if configUSE_ALTERNATIVE_API == 1

	signed portBASE_TYPE xQueueAltGenericSend( xQueueHandle pxQueue, const void * const pvItemToQueue, portTickType xTicksToWait, portBASE_TYPE xCopyPosition )
	{
	signed portBASE_TYPE xReturn;
	xTimeOutType xTimeOut;

		/* The source code that implements the alternative (Alt) API is much 
		simpler	because it executes everything from within a critical section.  
		This is	the approach taken by many other RTOSes, but FreeRTOS.org has the 
		preferred fully featured API too.  The fully featured API has more 
		complex	code that takes longer to execute, but makes much less use of 
		critical sections.  Therefore the alternative API sacrifices interrupt 
		responsiveness to gain execution speed, whereas the fully featured API
		sacrifices execution speed to ensure better interrupt responsiveness.  */

		taskENTER_CRITICAL();
		{
			/* Capture the current time status for future reference. */
			vTaskSetTimeOutState( &xTimeOut );

			/* If the queue is already full we may have to block. */
			do
			{
				if( pxQueue->uxMessagesWaiting == pxQueue->uxLength )
				{
					/* The queue is full - do we want to block or just leave without
					posting? */
					if( xTicksToWait > ( portTickType ) 0 )
					{
						/* We are going to place ourselves on the xTasksWaitingToSend 
						event list, and will get woken should the delay expire, or 
						space become available on the queue. */
						vTaskPlaceOnEventList( &( pxQueue->xTasksWaitingToSend ), xTicksToWait );
			
						/* Force a context switch now as we are blocked.  We can do
						this from within a critical section as the task we are
						switching to has its own context.  When we return here (i.e.
						we unblock) we will leave the critical section as normal. */
						taskYIELD();
					}
				}
					
				if( pxQueue->uxMessagesWaiting < pxQueue->uxLength )
				{
					/* There is room in the queue, copy the data into the queue. */			
					prvCopyDataToQueue( pxQueue, pvItemToQueue, xCopyPosition );
					xReturn = pdPASS;

					if( !listLIST_IS_EMPTY( &( pxQueue->xTasksWaitingToReceive ) ) )
					{
						if( xTaskRemoveFromEventList( &( pxQueue->xTasksWaitingToReceive ) ) != pdFALSE )
						{
							/* The task waiting has a higher priority. */
							taskYIELD();
						}
					}			
				}
				else
				{
					xReturn = errQUEUE_FULL;

					if( xTicksToWait > 0 )
					{					
						if( xTaskCheckForTimeOut( &xTimeOut, &xTicksToWait ) == pdFALSE )
						{
							/* Another task must have accessed the queue between 
							this task unblocking and actually executing. */
							xReturn = queueERRONEOUS_UNBLOCK;
						}
					}
				}
			}
			while( xReturn == queueERRONEOUS_UNBLOCK );
		}
		taskEXIT_CRITICAL();

		return xReturn;
	}

#endif /* configUSE_ALTERNATIVE_API */
/*-----------------------------------------------------------*/

#if configUSE_ALTERNATIVE_API == 1

	signed portBASE_TYPE xQueueAltGenericReceive( xQueueHandle pxQueue, const void * const pvBuffer, portTickType xTicksToWait, portBASE_TYPE xJustPeeking )
	{
	signed portBASE_TYPE xReturn = pdTRUE;
	xTimeOutType xTimeOut;
	signed portCHAR *pcOriginalReadPosition;

		/* The source code that implements the alternative (Alt) API is much 
		simpler	because it executes everything from within a critical section.  
		This is	the approach taken by many other RTOSes, but FreeRTOS.org has the 
		preferred fully featured API too.  The fully featured API has more 
		complex	code that takes longer to execute, but makes much less use of 
		critical sections.  Therefore the alternative API sacrifices interrupt 
		responsiveness to gain execution speed, whereas the fully featured API
		sacrifices execution speed to ensure better interrupt responsiveness.  */

		taskENTER_CRITICAL();
		{
			/* Capture the current time status for future reference. */
			vTaskSetTimeOutState( &xTimeOut );

			do
			{
				/* If there are no messages in the queue we may have to block. */
				if( pxQueue->uxMessagesWaiting == ( unsigned portBASE_TYPE ) 0 )
				{
					/* There are no messages in the queue, do we want to block or just
					leave with nothing? */			
					if( xTicksToWait > ( portTickType ) 0 )
					{
						#if ( configUSE_MUTEXES == 1 )
						{
							if( pxQueue->uxQueueType == queueQUEUE_IS_MUTEX )
							{
								vTaskPriorityInherit( ( void * const ) pxQueue->pxMutexHolder );
							}
						}
						#endif
						
						vTaskPlaceOnEventList( &( pxQueue->xTasksWaitingToReceive ), xTicksToWait );
						taskYIELD();
					}
				}
			
				if( pxQueue->uxMessagesWaiting > ( unsigned portBASE_TYPE ) 0 )
				{
					/* Remember our read position in case we are just peeking. */
					pcOriginalReadPosition = pxQueue->pcReadFrom;

					prvCopyDataFromQueue( pxQueue, pvBuffer );

					if( xJustPeeking == pdFALSE )
					{
						/* We are actually removing data. */
						--( pxQueue->uxMessagesWaiting );
							
						#if ( configUSE_MUTEXES == 1 )
						{
							if( pxQueue->uxQueueType == queueQUEUE_IS_MUTEX )
							{
								/* Record the information required to implement
								priority inheritance should it become necessary. */
								pxQueue->pxMutexHolder = xTaskGetCurrentTaskHandle();
							}
						}
						#endif

						if( !listLIST_IS_EMPTY( &( pxQueue->xTasksWaitingToSend ) ) )
						{
							if( xTaskRemoveFromEventList( &( pxQueue->xTasksWaitingToSend ) ) != pdFALSE )
							{
								/* The task waiting has a higher priority. */
								taskYIELD();
							}
						}
					}
					else
					{
						/* We are not removing the data, so reset our read
						pointer. */
						pxQueue->pcReadFrom = pcOriginalReadPosition;
					}
					
					xReturn = pdPASS;					
				}
				else
				{
					xReturn = errQUEUE_EMPTY;

					if( xTicksToWait > 0 )
					{
						if( xTaskCheckForTimeOut( &xTimeOut, &xTicksToWait ) == pdFALSE )
						{
							xReturn = queueERRONEOUS_UNBLOCK;
						}
					}
				}

			} while( xReturn == queueERRONEOUS_UNBLOCK );
		}
		taskEXIT_CRITICAL();

		return xReturn;
	}

#endif /* configUSE_ALTERNATIVE_API */
/*-----------------------------------------------------------*/

signed portBASE_TYPE xQueueGenericSendFromISR( xQueueHandle pxQueue, const void * const pvItemToQueue, signed portBASE_TYPE xTaskPreviouslyWoken, portBASE_TYPE xCopyPosition )
{
	/* Similar to xQueueGenericSend, except we don't block if there is no room
	in the queue.  Also we don't directly wake a task that was blocked on a
	queue read, instead we return a flag to say whether a context switch is
	required or not (i.e. has a task with a higher priority than us been woken
	by this	post). */
	if( pxQueue->uxMessagesWaiting < pxQueue->uxLength )
	{
		prvCopyDataToQueue( pxQueue, pvItemToQueue, xCopyPosition );

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

signed portBASE_TYPE xQueueGenericReceive( xQueueHandle pxQueue, const void * const pvBuffer, portTickType xTicksToWait, portBASE_TYPE xJustPeeking )
{
signed portBASE_TYPE xReturn = pdTRUE;
xTimeOutType xTimeOut;
signed portCHAR *pcOriginalReadPosition;

	/* This function is very similar to xQueueGenericSend().  See comments
	within xQueueGenericSend() for a more detailed explanation.

	Make sure other tasks do not access the queue. */
	vTaskSuspendAll();

	/* Capture the current time status for future reference. */
	vTaskSetTimeOutState( &xTimeOut );

	/* Make sure interrupts do not access the queue. */
	prvLockQueue( pxQueue );

	do
	{
		/* If there are no messages in the queue we may have to block. */
		if( prvIsQueueEmpty( pxQueue ) )
		{
			/* There are no messages in the queue, do we want to block or just
			leave with nothing? */			
			if( xTicksToWait > ( portTickType ) 0 )
			{
				#if ( configUSE_MUTEXES == 1 )
				{
					if( pxQueue->uxQueueType == queueQUEUE_IS_MUTEX )
					{
						portENTER_CRITICAL();
							vTaskPriorityInherit( ( void * const ) pxQueue->pxMutexHolder );
						portEXIT_CRITICAL();
					}
				}
				#endif
				
				vTaskPlaceOnEventList( &( pxQueue->xTasksWaitingToReceive ), xTicksToWait );
				taskENTER_CRITICAL();
				{
					prvUnlockQueue( pxQueue );
					if( !xTaskResumeAll() )
					{
						taskYIELD();
					}

					if( pxQueue->uxMessagesWaiting == ( unsigned portBASE_TYPE ) 0 )
					{
						/* We unblocked but the queue is empty.  We probably
						timed out. */
						xReturn = errQUEUE_EMPTY;
					}
	
					vTaskSuspendAll();
					prvLockQueue( pxQueue );
				}
				taskEXIT_CRITICAL();
			}
		}
	
		if( xReturn != errQUEUE_EMPTY )
		{
			taskENTER_CRITICAL();
			{
				if( pxQueue->uxMessagesWaiting > ( unsigned portBASE_TYPE ) 0 )
				{
					/* Remember our read position in case we are just peeking. */
					pcOriginalReadPosition = pxQueue->pcReadFrom;

					prvCopyDataFromQueue( pxQueue, pvBuffer );

					if( xJustPeeking == pdFALSE )
					{
						/* We are actually removing data. */
						--( pxQueue->uxMessagesWaiting );
							
						/* Increment the lock count so prvUnlockQueue knows to check for
						tasks waiting for space to become available on the queue. */
						++( pxQueue->xRxLock );
						
						#if ( configUSE_MUTEXES == 1 )
						{
							if( pxQueue->uxQueueType == queueQUEUE_IS_MUTEX )
							{
								/* Record the information required to implement
								priority inheritance should it become necessary. */
								pxQueue->pxMutexHolder = xTaskGetCurrentTaskHandle();
							}
						}
						#endif
					}
					else
					{
						/* We are not removing the data, so reset our read
						pointer. */
						pxQueue->pcReadFrom = pcOriginalReadPosition;

						/* The data is being left in the queue, so increment the
						lock count so prvUnlockQueue knows to check for other
						tasks waiting for the data to be available. */
						++( pxQueue->xTxLock );						
					}
					
					xReturn = pdPASS;					
				}
				else
				{
					xReturn = errQUEUE_EMPTY;
				}
			}
			taskEXIT_CRITICAL();
		}

		if( xReturn == errQUEUE_EMPTY )
		{
			if( xTicksToWait > 0 )
			{
				if( xTaskCheckForTimeOut( &xTimeOut, &xTicksToWait ) == pdFALSE )
				{
					xReturn = queueERRONEOUS_UNBLOCK;
				}
			}
		}
	} while( xReturn == queueERRONEOUS_UNBLOCK );

	/* We no longer require exclusive access to the queue. */
	prvUnlockQueue( pxQueue );
	xTaskResumeAll();

	return xReturn;
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xQueueReceiveFromISR( xQueueHandle pxQueue, const void * const pvBuffer, signed portBASE_TYPE *pxTaskWoken )
{
signed portBASE_TYPE xReturn;

	/* We cannot block from an ISR, so check there is data available. */
	if( pxQueue->uxMessagesWaiting > ( unsigned portBASE_TYPE ) 0 )
	{
		prvCopyDataFromQueue( pxQueue, pvBuffer );
		--( pxQueue->uxMessagesWaiting );

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

unsigned portBASE_TYPE uxQueueMessagesWaiting( const xQueueHandle pxQueue )
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

static void prvCopyDataToQueue( xQUEUE *pxQueue, const void *pvItemToQueue, portBASE_TYPE xPosition )
{
	if( pxQueue->uxItemSize == 0 )
	{
		#if ( configUSE_MUTEXES == 1 )
		{
			if( pxQueue->uxQueueType == queueQUEUE_IS_MUTEX )
			{
				/* The mutex is no longer being held. */
				vTaskPriorityDisinherit( ( void * const ) pxQueue->pxMutexHolder );
                pxQueue->pxMutexHolder = NULL;
			}
		}
		#endif
	}
	else if( xPosition == queueSEND_TO_BACK )
	{
		memcpy( ( void * ) pxQueue->pcWriteTo, pvItemToQueue, ( unsigned ) pxQueue->uxItemSize );
		pxQueue->pcWriteTo += pxQueue->uxItemSize;
		if( pxQueue->pcWriteTo >= pxQueue->pcTail )
		{
			pxQueue->pcWriteTo = pxQueue->pcHead;
		}
	}
	else
	{
		memcpy( ( void * ) pxQueue->pcReadFrom, pvItemToQueue, ( unsigned ) pxQueue->uxItemSize );
		pxQueue->pcReadFrom -= pxQueue->uxItemSize;
		if( pxQueue->pcReadFrom < pxQueue->pcHead )
		{
			pxQueue->pcReadFrom = ( pxQueue->pcTail - pxQueue->uxItemSize );
		}		
	}

	++( pxQueue->uxMessagesWaiting );
}
/*-----------------------------------------------------------*/

static void prvCopyDataFromQueue( xQUEUE * const pxQueue, const void *pvBuffer )
{
	if( pxQueue->uxQueueType != queueQUEUE_IS_MUTEX )
	{
		pxQueue->pcReadFrom += pxQueue->uxItemSize;
		if( pxQueue->pcReadFrom >= pxQueue->pcTail )
		{
			pxQueue->pcReadFrom = pxQueue->pcHead;
		}
		memcpy( ( void * ) pvBuffer, ( void * ) pxQueue->pcReadFrom, ( unsigned ) pxQueue->uxItemSize );
	}	
}
/*-----------------------------------------------------------*/

static void prvUnlockQueue( xQueueHandle pxQueue )
{
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
					vTaskMissedYield();
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
					vTaskMissedYield();
				}
			}			
		}
	}
	taskEXIT_CRITICAL();
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
			prvCopyDataToQueue( pxQueue, pvItemToQueue, queueSEND_TO_BACK );
			xReturn = pdPASS;

			/* Were any co-routines waiting for data to become available? */
			if( !listLIST_IS_EMPTY( &( pxQueue->xTasksWaitingToReceive ) ) )
			{
				/* In this instance the co-routine could be placed directly
				into the ready list as we are within a critical section.
				Instead the same pending ready list mechanism is used as if
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
		if( pxQueue->uxMessagesWaiting == ( unsigned portBASE_TYPE ) 0 )
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
				Instead the same pending ready list mechanism is used as if
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
		prvCopyDataToQueue( pxQueue, pvItemToQueue, queueSEND_TO_BACK );

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

