/*
 * FreeRTOS memory safety proofs with CBMC.
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use, copy,
 * modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
 * BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
 * ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 *
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

#include "cbmc.h"

/*
 * We allocate a TCB and set some members to basic values
 */
TaskHandle_t xUnconstrainedTCB( void )
{
	TCB_t * pxTCB = pvPortMalloc(sizeof(TCB_t));

	if ( pxTCB == NULL )
		return NULL;

	__CPROVER_assume( pxTCB->uxPriority < configMAX_PRIORITIES );

	vListInitialiseItem( &( pxTCB->xStateListItem ) );
	vListInitialiseItem( &( pxTCB->xEventListItem ) );

	listSET_LIST_ITEM_OWNER( &( pxTCB->xStateListItem ), pxTCB );
	listSET_LIST_ITEM_OWNER( &( pxTCB->xEventListItem ), pxTCB );

	if ( nondet_bool() )
	{
		listSET_LIST_ITEM_VALUE( &( pxTCB->xStateListItem ), pxTCB->uxPriority );
	}
	else
	{
		listSET_LIST_ITEM_VALUE( &( pxTCB->xStateListItem ), portMAX_DELAY );
	}

	if ( nondet_bool() )
	{
		listSET_LIST_ITEM_VALUE( &( pxTCB->xEventListItem ), ( TickType_t ) configMAX_PRIORITIES - ( TickType_t ) pxTCB->uxPriority );
	}
	else
	{
		listSET_LIST_ITEM_VALUE( &( pxTCB->xEventListItem ), portMAX_DELAY );
	}
	return pxTCB;
}

/*
 * We set xPendedTicks since __CPROVER_assume does not work
 * well with statically initialised variables
 */
void vSetGlobalVariables( void ) {
	UBaseType_t uxNonZeroValue;

	__CPROVER_assume( uxNonZeroValue != 0 );

	uxSchedulerSuspended = uxNonZeroValue;
	xPendedTicks = nondet_bool() ? PENDED_TICKS : 0;
	uxCurrentNumberOfTasks = nondet_ubasetype();
	xTickCount = nondet_ticktype();
}

/*
 * We initialise and fill the task lists so coverage is optimal.
 * This initialization is not guaranteed to be minimal, but it
 * is quite efficient and it serves the same purpose
 */
BaseType_t xPrepareTaskLists( void )
{
	TCB_t * pxTCB = NULL;

	__CPROVER_assert_zero_allocation();

	prvInitialiseTaskLists();

	/* This task will be moved to a ready list, granting coverage
	 * on lines 2780-2786 (tasks.c) */
	pxTCB = xUnconstrainedTCB();
	if ( pxTCB == NULL )
	{
		return pdFAIL;
	}
	vListInsert( pxOverflowDelayedTaskList, &( pxTCB->xStateListItem ) );

	/* Use of this macro ensures coverage on line 185 (list.c) */
	listGET_OWNER_OF_NEXT_ENTRY( pxTCB , pxOverflowDelayedTaskList );

	pxTCB = xUnconstrainedTCB();
	if ( pxTCB == NULL )
	{
		return pdFAIL;
	}
	vListInsert( &xPendingReadyList, &( pxTCB->xStateListItem ) );
	vListInsert( pxOverflowDelayedTaskList, &( pxTCB->xEventListItem ) );

	pxTCB = xUnconstrainedTCB();
	if ( pxTCB == NULL )
	{
		return pdFAIL;
	}
	vListInsert( pxOverflowDelayedTaskList, &( pxTCB->xStateListItem ) );

	/* This nondeterministic choice ensure coverage in line 2746 (tasks.c) */
	if ( nondet_bool() )
	{
		vListInsert( pxOverflowDelayedTaskList, &( pxTCB->xEventListItem ) );
	}

	pxCurrentTCB = xUnconstrainedTCB();
	if ( pxCurrentTCB == NULL )
	{
		return pdFAIL;
	}
	vListInsert( &pxReadyTasksLists[ pxCurrentTCB->uxPriority ], &( pxCurrentTCB->xStateListItem ) );

	return pdPASS;
}
