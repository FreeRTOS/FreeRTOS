/*
 * FreeRTOS V202212.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

#include "cbmc.h"

/*
 * We allocate a TCB and set some members to basic values
 */
TaskHandle_t xUnconstrainedTCB( void )
{
    TCB_t * pxTCB = pvPortMalloc( sizeof( TCB_t ) );

    if( pxTCB == NULL )
    {
        return NULL;
    }

    __CPROVER_assume( pxTCB->uxPriority < configMAX_PRIORITIES );

    vListInitialiseItem( &( pxTCB->xStateListItem ) );
    vListInitialiseItem( &( pxTCB->xEventListItem ) );

    listSET_LIST_ITEM_OWNER( &( pxTCB->xStateListItem ), pxTCB );
    listSET_LIST_ITEM_OWNER( &( pxTCB->xEventListItem ), pxTCB );

    if( nondet_bool() )
    {
        listSET_LIST_ITEM_VALUE( &( pxTCB->xStateListItem ), pxTCB->uxPriority );
    }
    else
    {
        listSET_LIST_ITEM_VALUE( &( pxTCB->xStateListItem ), portMAX_DELAY );
    }

    if( nondet_bool() )
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
 * We set the values of relevant global
 * variables to nondeterministic values
 */
void vSetGlobalVariables()
{
    xPendedTicks = nondet_ubasetype();
    uxSchedulerSuspended = nondet_ubasetype();
    xYieldPendings[ 0 ] = nondet_basetype();
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

    /* Needed for coverage: This task will be moved to a ready list */
    pxTCB = xUnconstrainedTCB();

    if( pxTCB == NULL )
    {
        return pdFAIL;
    }

    vListInsert( pxOverflowDelayedTaskList, &( pxTCB->xStateListItem ) );

    /* Needed for coverage. */
    listGET_OWNER_OF_NEXT_ENTRY( pxTCB, pxOverflowDelayedTaskList );

    pxTCB = xUnconstrainedTCB();

    if( pxTCB == NULL )
    {
        return pdFAIL;
    }

    vListInsert( &xPendingReadyList, &( pxTCB->xStateListItem ) );

    /* Needed for coverage: A nondeterministic choice */
    if( nondet_bool() )
    {
        vListInsert( pxOverflowDelayedTaskList, &( pxTCB->xEventListItem ) );
    }

    pxCurrentTCB = xUnconstrainedTCB();

    if( pxCurrentTCB == NULL )
    {
        return pdFAIL;
    }

    vListInsert( &pxReadyTasksLists[ pxCurrentTCB->uxPriority ], &( pxCurrentTCB->xStateListItem ) );

    return pdPASS;
}
