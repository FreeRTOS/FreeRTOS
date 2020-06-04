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
	uint8_t ucStaticAllocationFlag;

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

	pxTCB->pxStack = ( StackType_t * ) pvPortMalloc( ( ( ( size_t ) STACK_DEPTH ) * sizeof( StackType_t ) ) );
	if ( pxTCB->pxStack == NULL )
	{
		vPortFree( pxTCB );
		return NULL;
	}

	__CPROVER_assume( ucStaticAllocationFlag <= tskSTATICALLY_ALLOCATED_STACK_AND_TCB );
	__CPROVER_assume( ucStaticAllocationFlag >= tskDYNAMICALLY_ALLOCATED_STACK_AND_TCB );
	pxTCB->ucStaticallyAllocated = ucStaticAllocationFlag;

	return pxTCB;
}

/*
 * We set the values of relevant global
 * variables to nondeterministic values
 */
void vSetGlobalVariables()
{
	xSchedulerRunning = nondet_basetype();
}

/*
 * We initialise and fill the task lists so coverage is optimal.
 * This initialization is not guaranteed to be minimal, but it
 * is quite efficient and it serves the same purpose
 */
BaseType_t xPrepareTaskLists( TaskHandle_t * xTask )
{
	TCB_t * pxTCB = NULL;

	__CPROVER_assert_zero_allocation();

	prvInitialiseTaskLists();

	/*
	 * The task handle passed to TaskDelete can be NULL. In that case, the
	 * task to delete is the one in `pxCurrentTCB`, see the macro `prvGetTCBFromHandle`
	 * in line 1165 (tasks.c) for reference. For that reason, we provide a similar
	 * initialization for an arbitrary task `pxTCB` and `pxCurrentTCB`.
	 */

	pxTCB = xUnconstrainedTCB();
	if ( pxTCB != NULL )
	{
		if ( nondet_bool() )
		{
			TCB_t * pxOtherTCB;
			pxOtherTCB = xUnconstrainedTCB();
			/*
			 * Nondeterministic insertion of another TCB in the same list
			 * to guarantee coverage in line 1174 (tasks.c)
			 */
			if ( pxOtherTCB != NULL )
			{
				vListInsert( &xPendingReadyList, &( pxOtherTCB->xStateListItem ) );
			}
		}
		vListInsert( &xPendingReadyList, &( pxTCB->xStateListItem ) );

		/*
		 * Nondeterministic insertion of an event list item to guarantee
		 * coverage in lines 1180-1184 (tasks.c)
		 */
		if ( nondet_bool() )
		{
			vListInsert( pxDelayedTaskList, &( pxTCB->xEventListItem ) );
		}
	}

	/* Note that `*xTask = NULL` can happen here, but this is fine -- `pxCurrentTCB` will be used instead */
	*xTask = pxTCB;

	/*
	 * `pxCurrentTCB` must be initialized the same way as the previous task, but an
	 * allocation failure cannot happen in this case (i.e., if the previous task is NULL)
	 */
	pxCurrentTCB = xUnconstrainedTCB();
	if ( pxCurrentTCB == NULL )
	{
		return pdFAIL;
	}

	if ( nondet_bool() )
	{
		TCB_t * pxOtherTCB;
		pxOtherTCB = xUnconstrainedTCB();
		if ( pxOtherTCB != NULL )
		{
			vListInsert( &pxReadyTasksLists[ pxOtherTCB->uxPriority ], &( pxOtherTCB->xStateListItem ) );
		}
	}
	vListInsert( &pxReadyTasksLists[ pxCurrentTCB->uxPriority ], &( pxCurrentTCB->xStateListItem ) );

	/* Use of this macro ensures coverage on line 185 (list.c) */
	listGET_OWNER_OF_NEXT_ENTRY( pxCurrentTCB , &pxReadyTasksLists[ pxCurrentTCB->uxPriority ] );

	if ( nondet_bool() )
	{
		vListInsert( pxDelayedTaskList, &( pxCurrentTCB->xEventListItem ) );
	}

	return pdPASS;
}
