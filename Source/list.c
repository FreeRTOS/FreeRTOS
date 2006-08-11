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
Changes from V1.2.0

	+ Removed the volatile modifier from the function parameters.  This was
	  only ever included to prevent compiler warnings.  Now warnings are
	  removed by casting parameters where the calls are made.

	+ prvListGetOwnerOfNextEntry() and prvListGetOwnerOfHeadEntry() have been
	  removed from the c file and added as macros to the h file.

	+ uxNumberOfItems has been added to the list structure.  This removes the
	  need for a pointer comparison when checking if a list is empty, and so
	  is slightly faster.

	+ Removed the NULL check in vListRemove().  This makes the call faster but
	  necessitates any application code utilising the list implementation to
	  ensure NULL pointers are not passed.

Changes from V2.0.0

	+ Double linked the lists to allow faster removal item removal.

Changes from V2.6.1

	+ Make use of the new portBASE_TYPE definition where ever appropriate.

Changes from V3.0.0

	+ API changes as described on the FreeRTOS.org WEB site.

Changes from V3.2.4

	+ Removed the pxHead member of the xList structure.  This always pointed
	  to the same place so has been removed to free a few bytes of RAM.

	+ Introduced the xMiniListItem structure that does not include the 
	  xListItem members that are not required by the xListEnd member of a list.
	  Again this was done to reduce RAM usage.

	+ Changed the volatile definitions of some structure members to clean up
	  the code where the list structures are used.

Changes from V4.0.4

	+ Optimised vListInsert() in the case when the wake time is the maximum 
	  tick count value.
*/

#include <stdlib.h>
#include "FreeRTOS.h"
#include "list.h"

/*-----------------------------------------------------------
 * PUBLIC LIST API documented in list.h
 *----------------------------------------------------------*/

void vListInitialise( xList *pxList )
{
	/* The list structure contains a list item which is used to mark the
	end of the list.  To initialise the list the list end is inserted
	as the only list entry. */
	pxList->pxIndex = ( xListItem * ) &( pxList->xListEnd );

	/* The list end value is the highest possible value in the list to
	ensure it remains at the end of the list. */
	pxList->xListEnd.xItemValue = portMAX_DELAY;

	/* The list end next and previous pointers point to itself so we know
	when the list is empty. */
	pxList->xListEnd.pxNext = ( xListItem * ) &( pxList->xListEnd );
	pxList->xListEnd.pxPrevious = ( xListItem * ) &( pxList->xListEnd );

	pxList->uxNumberOfItems = 0;
}
/*-----------------------------------------------------------*/

void vListInitialiseItem( xListItem *pxItem )
{
	/* Make sure the list item is not recorded as being on a list. */
	pxItem->pvContainer = NULL;
}
/*-----------------------------------------------------------*/

void vListInsertEnd( xList *pxList, xListItem *pxNewListItem )
{
volatile xListItem * pxIndex;

	/* Insert a new list item into pxList, but rather than sort the list,
	makes the new list item the last item to be removed by a call to
	pvListGetOwnerOfNextEntry.  This means it has to be the item pointed to by
	the pxIndex member. */
	pxIndex = pxList->pxIndex;

	pxNewListItem->pxNext = pxIndex->pxNext;
	pxNewListItem->pxPrevious = pxList->pxIndex;
	pxIndex->pxNext->pxPrevious = ( volatile xListItem * ) pxNewListItem;
	pxIndex->pxNext = ( volatile xListItem * ) pxNewListItem;
	pxList->pxIndex = ( volatile xListItem * ) pxNewListItem;

	/* Remember which list the item is in. */
	pxNewListItem->pvContainer = ( void * ) pxList;

	( pxList->uxNumberOfItems )++;
}
/*-----------------------------------------------------------*/

void vListInsert( xList *pxList, xListItem *pxNewListItem )
{
volatile xListItem *pxIterator;
portTickType xValueOfInsertion;

	/* Insert the new list item into the list, sorted in ulListItem order. */
	xValueOfInsertion = pxNewListItem->xItemValue;

	/* If the list already contains a list item with the same item value then
	the new list item should be placed after it.  This ensures that TCB's which
	are stored in ready lists (all of which have the same ulListItem value)
	get an equal share of the CPU.  However, if the xItemValue is the same as 
	the back marker the iteration loop below will not end.  This means we need
	to guard against this by checking the value first and modifying the 
	algorithm slightly if necessary. */
	if( xValueOfInsertion == portMAX_DELAY )
	{
		pxIterator = pxList->xListEnd.pxPrevious;
	}
	else
	{
		for( pxIterator = ( xListItem * ) &( pxList->xListEnd ); pxIterator->pxNext->xItemValue <= xValueOfInsertion; pxIterator = pxIterator->pxNext )
		{
			/* There is nothing to do here, we are just iterating to the
			wanted insertion position. */
		}
	}

	pxNewListItem->pxNext = pxIterator->pxNext;
	pxNewListItem->pxNext->pxPrevious = ( volatile xListItem * ) pxNewListItem;
	pxNewListItem->pxPrevious = pxIterator;
	pxIterator->pxNext = ( volatile xListItem * ) pxNewListItem;

	/* Remember which list the item is in.  This allows fast removal of the
	item later. */
	pxNewListItem->pvContainer = ( void * ) pxList;

	( pxList->uxNumberOfItems )++;
}
/*-----------------------------------------------------------*/

void vListRemove( xListItem *pxItemToRemove )
{
xList * pxList;

	pxItemToRemove->pxNext->pxPrevious = pxItemToRemove->pxPrevious;
	pxItemToRemove->pxPrevious->pxNext = pxItemToRemove->pxNext;
	
	/* The list item knows which list it is in.  Obtain the list from the list
	item. */
	pxList = ( xList * ) pxItemToRemove->pvContainer;

	/* Make sure the index is left pointing to a valid item. */
	if( pxList->pxIndex == pxItemToRemove )
	{
		pxList->pxIndex = pxItemToRemove->pxPrevious;
	}

	pxItemToRemove->pvContainer = NULL;
	( pxList->uxNumberOfItems )--;
}
/*-----------------------------------------------------------*/

