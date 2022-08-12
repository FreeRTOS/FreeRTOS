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
    uint8_t ucStaticAllocationFlag;

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
 * An unbounded proof requires non-deterministic list sizes.
 * Since we make no assumptions about the contents of these lists,
 * we don't need to populate them with anything.
*/
void vSetNonDeterministicListSize( List_t * list)
{
    list->uxNumberOfItems = nondet_ubasetype();
    __CPROVER_assume(list->uxNumberOfItems <= configLIST_SIZE);

    if (list->uxNumberOfItems == 0){
        list->pxIndex = 0;
    }
    else{
        list->pxIndex = nondet_ubasetype();
        __CPROVER_assume(list->pxIndex < list->uxNumberOfItems );
    }
}



/*
 * Creates a new TCB and optionally adds it to non-deterministic indices
 * in various task-lists.
 * Also prepares a task-list
*/
BaseType_t xPrepareTaskLists( TaskHandle_t * xTask )
{
    __CPROVER_assert_zero_allocation();
    prvInitialiseTaskLists();
    for( UBaseType_t uxPriority = ( UBaseType_t ) 0U; uxPriority < ( UBaseType_t ) configMAX_PRIORITIES; uxPriority++ )
    {
        vSetNonDeterministicListSize(&pxReadyTasksLists[uxPriority]);
    }

    // we only need to malloc the one TCB that we intend on setting a priority for,
    // and the current TCB. This saves us from having to make multiple mallocs
    TaskHandle_t newTCB = xUnconstrainedTCB();
    pxCurrentTCB = xUnconstrainedTCB();
    if (newTCB == NULL || pxCurrentTCB == NULL){
        return pdFAIL;
    }

    // Add the new TCB to the ready list that it is supposed to be a part of.
    if (nondet_bool()){   // needed for 100% coverage
        UBaseType_t newTCBlistIndex;
        __CPROVER_assume(newTCBlistIndex < pxReadyTasksLists[newTCB->uxPriority].uxNumberOfItems);
        pxReadyTasksLists[newTCB->uxPriority].xListData[newTCBlistIndex] = &(newTCB->xStateListItem);
        newTCB->xStateListItem.pxContainer = &pxReadyTasksLists[newTCB->uxPriority];
    }

    /*
     * The task handle passed to TaskPrioritySet can be NULL. 
     * In that case, the task to delete is the one in `pxCurrentTCB`, 
     * see the macro `prvGetTCBFromHandle` for reference. 
     * Hence we either set 'xTask' to the newly created TCB, 
     * or assign it to null.
     */
    if (notdet_bool()){
        *xTask = newTCB;
    } 
    else
    {
        *xTask = NULL;
    }

    return pdPASS;
}



