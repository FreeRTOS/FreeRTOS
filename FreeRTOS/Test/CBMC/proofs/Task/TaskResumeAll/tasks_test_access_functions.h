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
 * We set xPendedTicks since __CPROVER_assume does not work
 * well with statically initialised variables
 */
void vSetGlobalVariables( void )
{
    UBaseType_t uxNonZeroValue;

    __CPROVER_assume( uxNonZeroValue != 0 );

    uxSchedulerSuspended = uxNonZeroValue;
    xPendedTicks = nondet_bool() ? 1 : 0;
    uxCurrentNumberOfTasks = nondet_ubasetype();
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

BaseType_t xPrepareTaskLists( void )
{
    __CPROVER_assert_zero_allocation();
    prvInitialiseTaskLists();
    
    // An auxillary list. It's purpose is to add elements that don't
    // get added to the pxDelayedTaskList.
    List_t * extraList = pvPortMalloc(sizeof(List_t));
    List_t * extraList2 = pvPortMalloc(sizeof(List_t));
    if (extraList == NULL || extraList2 == NULL){
        return pdFAIL;
    }
    vListInitialise(extraList);
    vListInitialise(extraList2);

    // Set non-deterministic sizes for the two lists used. 
    vSetNonDeterministicListSize(pxDelayedTaskList, configLIST_SIZE);  
    vSetNonDeterministicListSize(&xPendingReadyList, configLIST_SIZE);

    // Malloc a set of TCBs. We need to malloc the whole TCB instead of 
    // just the list-item, since the TCB fields get accessed.
    TCB_t ** TCBs = pvPortMalloc(configLIST_SIZE * sizeof(TCB_t*));
    if (TCBs == NULL){
        return pdFAIL;
    }
    for (UBaseType_t i = 0; i < configLIST_SIZE; i++)
    {
        TCBs[i] = xUnconstrainedTCB();
        if (TCBs[i] == NULL){
            return pdFAIL;
        }
    }

    // Each stateListItem needs to be part of some list.
    // Put it in either the delayed-task-list or the extra-list.
    for (UBaseType_t i = 0; i < configLIST_SIZE; i++)
    {
        if (i < pxDelayedTaskList->uxNumberOfItems)
        {
            pxDelayedTaskList->xListData[i] = &(TCBs[i]->xStateListItem);
            pxDelayedTaskList->xListData[i]->pxContainer = pxDelayedTaskList;
        } 
        else 
        {
            extraList->xListData[extraList->uxNumberOfItems] = &(TCBs[i]->xStateListItem);
            extraList->xListData[extraList->uxNumberOfItems]->pxContainer = extraList;
            extraList->uxNumberOfItems++;
        }
    }

    // Each eventListItem can be in the pending-ready list.
    for (UBaseType_t i = 0; i < configLIST_SIZE; i++)
    {
        if (i < xPendingReadyList.uxNumberOfItems){
            xPendingReadyList.xListData[i] = &(TCBs[i]->xEventListItem);
            xPendingReadyList.xListData[i]->pxContainer = &xPendingReadyList;
        }
        else{
            if (nondet_bool()){
                extraList2->xListData[extraList2->uxNumberOfItems] = &(TCBs[i]->xEventListItem);
                extraList2->xListData[extraList2->uxNumberOfItems]->pxContainer = extraList2;
                extraList2->uxNumberOfItems++;
            }
        }
    }

    // Also allocate the current tcb
    pxCurrentTCB = xUnconstrainedTCB();
    if (pxCurrentTCB == NULL){
        return pdFAIL;
    }
    return pdPASS;
}
