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
 * https://aws.amazon.com/freertos
 * https://www.FreeRTOS.org
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
        exit(1);
    }

    __CPROVER_assume( pxTCB->uxPriority < configMAX_PRIORITIES );

    listSET_LIST_ITEM_OWNER( &( pxTCB->xStateListItem ), pxTCB );
    pxTCB->xEventListItem.pxContainer = NULL;
    
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
    xYieldPending = nondet_basetype();
    xTickCount = nondet_ticktype();
}

/* 
 * An unbounded proof requires non-deterministic list sizes.
 * Since we make no assumptions about the contents of these lists,
 * we don't need to populate them with anything.
*/
void vSetNonDeterministicListSize( List_t * list, UBaseType_t size)
{
    list->uxNumberOfItems = nondet_ubasetype();
    __CPROVER_assume(list->uxNumberOfItems <= size );

    if (list->uxNumberOfItems == 0){
        list->pxIndex = 0;
    }
    else{
        list->pxIndex = nondet_ubasetype();
        __CPROVER_assume(list->pxIndex < list->uxNumberOfItems );
    }
}

void vMallocElements(List_t * list)
{
    for (UBaseType_t i = 0; i < configLIST_SIZE; i++)
    {
        if (i < list->uxNumberOfItems){
            // malloc the whole TCB instead of the list-item,
            // since the TCB fields get accessed.
            TCB_t * pxTCB = xUnconstrainedTCB();
            list->xListData[i] = &(pxTCB->xStateListItem);
            list->xListData[i]->pxContainer = list;
        }
    }
}

/*
 * We initialise and fill the task lists so coverage is optimal.
 * This initialization is not guaranteed to be minimal, but it
 * is quite efficient and it serves the same purpose
 */
BaseType_t xPrepareTaskLists( void )
{
    __CPROVER_assert_zero_allocation();
    prvInitialiseTaskLists();
    
    // Set non-deterministic size for the delayed task-list. 
    // But we also need to malloc their elements.
    vSetNonDeterministicListSize(pxDelayedTaskList, configLIST_SIZE);
    vMallocElements(pxDelayedTaskList);
    
    // Also allocate the current tcb
    pxCurrentTCB = xUnconstrainedTCB();
    return pdPASS;
}
