/*
	FreeRTOS.org V4.2.0 - Copyright (C) 2003-2007 Richard Barry.

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

#include "FreeRTOS.h"
#include "task.h"
#include "croutine.h"

/* Lists for ready and blocked co-routines. --------------------*/
static xList pxReadyCoRoutineLists[ configMAX_CO_ROUTINE_PRIORITIES ];	/*< Prioritised ready co-routines. */
static xList xDelayedCoRoutineList1;									/*< Delayed co-routines. */
static xList xDelayedCoRoutineList2;									/*< Delayed co-routines (two lists are used - one for delays that have overflowed the current tick count. */
static xList * pxDelayedCoRoutineList;									/*< Points to the delayed co-routine list currently being used. */
static xList * pxOverflowDelayedCoRoutineList;							/*< Points to the delayed co-routine list currently being used to hold co-routines that have overflowed the current tick count. */
static xList xPendingReadyList;											/*< Holds co-routines that have been readied by an external event.  They cannot be added directly to the ready lists as the ready lists cannot be accessed by interrupts. */

/* Other file private variables. --------------------------------*/
corCRCB * pxCurrentCoRoutine = NULL;
static unsigned portBASE_TYPE uxTopCoRoutineReadyPriority = 0;
static portTickType xCoRoutineTickCount = 0;

/* The initial state of the co-routine when it is created. */
#define corINITIAL_STATE	( 0 )

/*
 * Place the co-routine represented by pxCRCB into the appropriate ready queue
 * for the priority.  It is inserted at the end of the list.
 *
 * This macro accesses the co-routine ready lists and therefore must not be
 * used from within an ISR.
 */
#define prvAddCoRoutineToReadyQueue( pxCRCB )																		\
{																													\
	if( pxCRCB->uxPriority > uxTopCoRoutineReadyPriority )															\
	{																												\
		uxTopCoRoutineReadyPriority = pxCRCB->uxPriority;															\
	}																												\
	vListInsertEnd( ( xList * ) &( pxReadyCoRoutineLists[ pxCRCB->uxPriority ] ), &( pxCRCB->xGenericListItem ) );	\
}	

/*
 * Utility to ready all the lists used by the scheduler.  This is called
 * automatically upon the creation of the first co-routine.
 */
static void prvInitialiseCoRoutineLists( void );

/*
 * Co-routines that are readied by an interrupt cannot be placed directly into
 * the ready lists (there is no mutual exclusion).  Instead they are placed in
 * in the pending ready list in order that they can later be moved to the ready
 * list by the co-routine scheduler.
 */
static inline void prvCheckPendingReadyList( void );

/*
 * Macro that looks at the list of co-routines that are currently delayed to
 * see if any require waking.
 *
 * Co-routines are stored in the queue in the order of their wake time -
 * meaning once one co-routine has been found whose timer has not expired
 * we need not look any further down the list.
 */
static inline void prvCheckDelayedList( void );

/*-----------------------------------------------------------*/

signed portBASE_TYPE xCoRoutineCreate( crCOROUTINE_CODE pxCoRoutineCode, unsigned portBASE_TYPE uxPriority, unsigned portBASE_TYPE uxIndex )
{
signed portBASE_TYPE xReturn;
corCRCB *pxCoRoutine;

	/* Allocate the memory that will store the co-routine control block. */
	pxCoRoutine = ( corCRCB * ) pvPortMalloc( sizeof( corCRCB ) );
	if( pxCoRoutine )
	{
		/* If pxCurrentCoRoutine is NULL then this is the first co-routine to
		be created and the co-routine data structures need initialising. */
		if( pxCurrentCoRoutine == NULL )
		{
			pxCurrentCoRoutine = pxCoRoutine;
			prvInitialiseCoRoutineLists();
		}

		/* Check the priority is within limits. */
		if( uxPriority >= configMAX_CO_ROUTINE_PRIORITIES )
		{
			uxPriority = configMAX_CO_ROUTINE_PRIORITIES - 1;
		}

		/* Fill out the co-routine control block from the function parameters. */
		pxCoRoutine->uxState = corINITIAL_STATE;
		pxCoRoutine->uxPriority = uxPriority;
		pxCoRoutine->uxIndex = uxIndex;
		pxCoRoutine->pxCoRoutineFunction = pxCoRoutineCode;

		/* Initialise all the other co-routine control block parameters. */
		vListInitialiseItem( &( pxCoRoutine->xGenericListItem ) );
		vListInitialiseItem( &( pxCoRoutine->xEventListItem ) );

		/* Set the co-routine control block as a link back from the xListItem.
		This is so we can get back to the containing CRCB from a generic item
		in a list. */
		listSET_LIST_ITEM_OWNER( &( pxCoRoutine->xGenericListItem ), pxCoRoutine );
		listSET_LIST_ITEM_OWNER( &( pxCoRoutine->xEventListItem ), pxCoRoutine );
	
		/* Event lists are always in priority order. */
		listSET_LIST_ITEM_VALUE( &( pxCoRoutine->xEventListItem ), configMAX_PRIORITIES - ( portTickType ) uxPriority );
		
		/* Now the co-routine has been initialised it can be added to the ready
		list at the correct priority. */
		prvAddCoRoutineToReadyQueue( pxCoRoutine );

		xReturn = pdPASS;
	}
	else
	{		
		xReturn = errCOULD_NOT_ALLOCATE_REQUIRED_MEMORY;
	}
	
	return xReturn;	
}
/*-----------------------------------------------------------*/

void vCoRoutineAddToDelayedList( portTickType xTicksToDelay, xList *pxEventList )
{
portTickType xTimeToWake;

	/* Calculate the time to wake - this may overflow but this is
	not a problem. */
	xTimeToWake = xCoRoutineTickCount + xTicksToDelay;

	/* We must remove ourselves from the ready list before adding
	ourselves to the blocked list as the same list item is used for
	both lists. */
	vListRemove( ( xListItem * ) &( pxCurrentCoRoutine->xGenericListItem ) );

	/* The list item will be inserted in wake time order. */
	listSET_LIST_ITEM_VALUE( &( pxCurrentCoRoutine->xGenericListItem ), xTimeToWake );

	if( xTimeToWake < xCoRoutineTickCount )
	{
		/* Wake time has overflowed.  Place this item in the
		overflow list. */
		vListInsert( ( xList * ) pxOverflowDelayedCoRoutineList, ( xListItem * ) &( pxCurrentCoRoutine->xGenericListItem ) );
	}
	else
	{
		/* The wake time has not overflowed, so we can use the
		current block list. */
		vListInsert( ( xList * ) pxDelayedCoRoutineList, ( xListItem * ) &( pxCurrentCoRoutine->xGenericListItem ) );
	}

	if( pxEventList )
	{
		/* Also add the co-routine to an event list.  If this is done then the
		function must be called with interrupts disabled. */
		vListInsert( pxEventList, &( pxCurrentCoRoutine->xEventListItem ) );
	}
}
/*-----------------------------------------------------------*/

static inline void prvCheckPendingReadyList( void )
{
	/* Are there any co-routines waiting to get moved to the ready list?  These
	are co-routines that have been readied by an ISR.  The ISR cannot access
	the	ready lists itself. */
	while( !listLIST_IS_EMPTY( &xPendingReadyList ) )
	{
		corCRCB *pxUnblockedCRCB;

		/* The pending ready list can be accessed by an ISR. */
		portDISABLE_INTERRUPTS();
		{	
			pxUnblockedCRCB = ( corCRCB * ) listGET_OWNER_OF_HEAD_ENTRY( (&xPendingReadyList) );			
			vListRemove( &( pxUnblockedCRCB->xEventListItem ) );
		}
		portENABLE_INTERRUPTS();

		vListRemove( &( pxUnblockedCRCB->xGenericListItem ) );
		prvAddCoRoutineToReadyQueue( pxUnblockedCRCB );	
	}
}
/*-----------------------------------------------------------*/

static inline void prvCheckDelayedList( void )
{
static portTickType xLastTickCount, xPassedTicks;
corCRCB *pxCRCB;

	xPassedTicks = xTaskGetTickCount() - xLastTickCount;
	while( xPassedTicks )
	{
		xCoRoutineTickCount++;
		xPassedTicks--;

		/* If the tick count has overflowed we need to swap the ready lists. */
		if( xCoRoutineTickCount == 0 )
		{
			xList * pxTemp;

			/* Tick count has overflowed so we need to swap the delay lists.  If there are
			any items in pxDelayedCoRoutineList here then there is an error! */
			pxTemp = pxDelayedCoRoutineList;
			pxDelayedCoRoutineList = pxOverflowDelayedCoRoutineList;
			pxOverflowDelayedCoRoutineList = pxTemp;
		}

		/* See if this tick has made a timeout expire. */
		while( ( pxCRCB = ( corCRCB * ) listGET_OWNER_OF_HEAD_ENTRY( pxDelayedCoRoutineList ) ) != NULL )
		{	
			if( xCoRoutineTickCount < listGET_LIST_ITEM_VALUE( &( pxCRCB->xGenericListItem ) ) )				
			{			
				/* Timeout not yet expired. */																			
				break;																				
			}																						

			portDISABLE_INTERRUPTS();
			{
				/* The event could have occurred just before this critical
				section.  If this is the case then the generic list item will
				have been moved to the pending ready list and the following
				line is still valid.  Also the pvContainer parameter will have
				been set to NULL so the following lines are also valid. */
				vListRemove( &( pxCRCB->xGenericListItem ) );											

				/* Is the co-routine waiting on an event also? */												
				if( pxCRCB->xEventListItem.pvContainer )													
				{															
					vListRemove( &( pxCRCB->xEventListItem ) );											
				}
			}
			portENABLE_INTERRUPTS();

			prvAddCoRoutineToReadyQueue( pxCRCB );													
		}																									
	}

	xLastTickCount = xCoRoutineTickCount;
}
/*-----------------------------------------------------------*/

void vCoRoutineSchedule( void )
{
	/* See if any co-routines readied by events need moving to the ready lists. */
	prvCheckPendingReadyList();

	/* See if any delayed co-routines have timed out. */
	prvCheckDelayedList();

	/* Find the highest priority queue that contains ready co-routines. */
	while( listLIST_IS_EMPTY( &( pxReadyCoRoutineLists[ uxTopCoRoutineReadyPriority ] ) ) )
	{
		if( uxTopCoRoutineReadyPriority == 0 )
		{
			/* No more co-routines to check. */
			return;
		}
		--uxTopCoRoutineReadyPriority;
	}

	/* listGET_OWNER_OF_NEXT_ENTRY walks through the list, so the co-routines
	 of the	same priority get an equal share of the processor time. */
	listGET_OWNER_OF_NEXT_ENTRY( pxCurrentCoRoutine, &( pxReadyCoRoutineLists[ uxTopCoRoutineReadyPriority ] ) );

	/* Call the co-routine. */
	( pxCurrentCoRoutine->pxCoRoutineFunction )( pxCurrentCoRoutine, pxCurrentCoRoutine->uxIndex );

	return;
}
/*-----------------------------------------------------------*/

static void prvInitialiseCoRoutineLists( void )
{
unsigned portBASE_TYPE uxPriority;

	for( uxPriority = 0; uxPriority < configMAX_CO_ROUTINE_PRIORITIES; uxPriority++ )
	{
		vListInitialise( ( xList * ) &( pxReadyCoRoutineLists[ uxPriority ] ) );
	}

	vListInitialise( ( xList * ) &xDelayedCoRoutineList1 );
	vListInitialise( ( xList * ) &xDelayedCoRoutineList2 );
	vListInitialise( ( xList * ) &xPendingReadyList );

	/* Start with pxDelayedCoRoutineList using list1 and the
	pxOverflowDelayedCoRoutineList using list2. */
	pxDelayedCoRoutineList = &xDelayedCoRoutineList1;
	pxOverflowDelayedCoRoutineList = &xDelayedCoRoutineList2;
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xCoRoutineRemoveFromEventList( const xList *pxEventList )
{
corCRCB *pxUnblockedCRCB;
signed portBASE_TYPE xReturn;

	/* This function is called from within an interrupt.  It can only access
	event lists and the pending ready list. */
	pxUnblockedCRCB = ( corCRCB * ) listGET_OWNER_OF_HEAD_ENTRY( pxEventList );
	vListRemove( &( pxUnblockedCRCB->xEventListItem ) );
	vListInsertEnd( ( xList * ) &( xPendingReadyList ), &( pxUnblockedCRCB->xEventListItem ) );

	if( pxUnblockedCRCB->uxPriority >= pxCurrentCoRoutine->uxPriority )
	{
		xReturn = pdTRUE;
	}
	else
	{
		xReturn = pdFALSE;
	}

	return xReturn;
}

