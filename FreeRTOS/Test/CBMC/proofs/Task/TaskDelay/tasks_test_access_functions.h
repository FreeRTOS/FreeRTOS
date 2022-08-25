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
 * We set the values of relevant global variables to
 * nondeterministic values, except for `uxSchedulerSuspended`
 * which is set to 0 (to pass through the assertion)
 */

void vSetGlobalVariables( void )
{
    uxSchedulerSuspended = pdFALSE;
    xTickCount = nondet_ticktype();
    xNextTaskUnblockTime = nondet_ticktype();
}


/* 
 * An unbounded proof requires non-deterministic list sizes.
 * Since we make no assumptions about the contents of these lists,
 * we don't need to populate them with anything.
*/
void vSetNonDeterministicListSize( List_t * list)
{
    list->uxNumberOfItems = nondet_ubasetype();
    __CPROVER_assume(list->uxNumberOfItems <= configLIST_SIZE );

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
    ListItem_t * elements = pvPortMalloc((configLIST_SIZE - 1) * sizeof(ListItem_t));
    if (elements == NULL){
        exit(1);
    }
    for (UBaseType_t i = 0; i < configLIST_SIZE - 1; i++)
    {
        if (i < list->uxNumberOfItems){
            list->xListData[i] = &(elements[i]);
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

    // allot the current TCB 
    pxCurrentTCB = xUnconstrainedTCB();
    if( pxCurrentTCB == NULL )
    {
        return pdFAIL;
    }

    // set sizes for the task lists.
    vSetNonDeterministicListSize(&pxReadyTasksLists[pxCurrentTCB->uxPriority]);
    vSetNonDeterministicListSize(pxDelayedTaskList);
    vSetNonDeterministicListSize(pxOverflowDelayedTaskList);

    // malloc elements for the delayed and overflow-delayed lists.
    vMallocElements(pxDelayedTaskList);
    vMallocElements(pxOverflowDelayedTaskList);

    // add current TCB to the ready tasks list.
    UBaseType_t currentTCBindex;
    __CPROVER_assume(currentTCBindex < pxReadyTasksLists[pxCurrentTCB->uxPriority].uxNumberOfItems);
    pxReadyTasksLists[pxCurrentTCB->uxPriority].xListData[currentTCBindex] = &(pxCurrentTCB->xStateListItem);
    pxCurrentTCB->xStateListItem.pxContainer = &pxReadyTasksLists[pxCurrentTCB->uxPriority];

    return pdPASS;
}

/*
 * We stub out `xTaskResumeAll` including the assertion and change on
 * variables `uxSchedulerSuspended`. We assume that `xPendingReadyList`
 * is empty to avoid the first loop, and xPendedTicks to avoid the second
 * one. Finally, we return a nondeterministic value (overapproximation)
 */
BaseType_t xTaskResumeAllStub( void )
{
    BaseType_t xAlreadyYielded;

    configASSERT( uxSchedulerSuspended );

    taskENTER_CRITICAL();
    {
        --uxSchedulerSuspended;
        __CPROVER_assert( listLIST_IS_EMPTY( &xPendingReadyList ), "Pending ready tasks list not empty." );
        // TODO: For the pendedTicks assert -> Shouldn't this be an assume?
        //__CPROVER_assert( xPendedTicks == 0, "xPendedTicks is not equal to zero." ); 
    }
    taskEXIT_CRITICAL();

    return xAlreadyYielded;
}
