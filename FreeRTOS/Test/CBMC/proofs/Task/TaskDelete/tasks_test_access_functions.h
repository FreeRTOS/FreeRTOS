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
    // Allocate TCB
    TCB_t * pxTCB = (TCB_t *) pvPortMalloc( sizeof( TCB_t ) );
    if( pxTCB == NULL )
    {
        return NULL;
    }

    // Set some members
    __CPROVER_assume( pxTCB->uxPriority < configMAX_PRIORITIES ); // necessary?

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

    // allocate stack
    // make stack depth unbounded?
    pxTCB->pxStack = ( StackType_t * ) pvPortMalloc( ( ( ( size_t ) STACK_DEPTH ) * sizeof( StackType_t ) ) );
    if( pxTCB->pxStack == NULL )
    {
        vPortFree( pxTCB );
        return NULL;
    }

    // set static allocation flag
    uint8_t ucStaticAllocationFlag;
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
    uxCurrentNumberOfTasks = nondet_ubasetype();
}

/* 
 * An unbounded proof requires non-deterministic list sizes.
 * Since we make no assumptions about the contents of these lists,
 * we don't need to populate them with anything.
*/
void vSetNonDeterministicListSize( List_t * list, UBaseType_t minSize)
{
    list->uxNumberOfItems = nondet_ubasetype();
    // Needed?
    __CPROVER_assume(list->uxNumberOfItems <= configLIST_SIZE && list->uxNumberOfItems >= minSize);
    if (list->uxNumberOfItems == 0){
        list->pxIndex = 0;
    }
    else{
        list->pxIndex = nondet_ubasetype();
        __CPROVER_assume(list->pxIndex < list->uxNumberOfItems );
    }
}


void vPrepareTaskLists(){
    __CPROVER_assert_zero_allocation();
    prvInitialiseTaskLists();

    // Set non-deterministic sizes for all the different lists we may need.
    for( UBaseType_t uxPriority = ( UBaseType_t ) 0U; uxPriority < ( UBaseType_t ) configMAX_PRIORITIES; uxPriority++ )
    {
        vSetNonDeterministicListSize(&pxReadyTasksLists[uxPriority],0);
    }
    vSetNonDeterministicListSize(&xTasksWaitingTermination,0);
    vSetNonDeterministicListSize(&xPendingReadyList,1);
    vSetNonDeterministicListSize(pxDelayedTaskList,0);
}

/*
 * So we only need to malloc the one TCB that we intend on 
 * deleting. This saves us from having to make multiple malloc
 * statements. 
*/
TaskHandle_t xAddTaskToLists()
{
    // Create a new TCB and assume that it's at a particular index
    TaskHandle_t newTCB = xUnconstrainedTCB();
    if (newTCB == NULL){
        exit(1); // is this necessary?
    }
    // Add the TCB's xStateListItem to the pending task list
    UBaseType_t pendingListIndex;
    __CPROVER_assume(pendingListIndex < xPendingReadyList.uxNumberOfItems);
    xPendingReadyList.xListData[pendingListIndex] = &(newTCB->xStateListItem);
    newTCB->xStateListItem.pxContainer = &xPendingReadyList;
    
    // Optionally, add the TCB's xEventListItem to the delayed task list
    if (nondet_bool()){
            UBaseType_t delayedListIndex;
            __CPROVER_assume(delayedListIndex < pxDelayedTaskList->uxNumberOfItems);
            pxDelayedTaskList->xListData[delayedListIndex] = &(newTCB->xEventListItem);
            newTCB->xEventListItem.pxContainer = pxDelayedTaskList;
    }
    
    // If the pxDelayedTaskList size is non-zero, we may access the head element.
    // after a deletion. Hence we need to allocate 2 objects
    if (pxDelayedTaskList->uxNumberOfItems > 0){
        pxDelayedTaskList->xListData[0] = (ListItem_t *) pvPortMalloc( sizeof( ListItem_t ) );
        if (pxDelayedTaskList->xListData[0] == NULL){
            exit(1);
        }
    }
    if (pxDelayedTaskList->uxNumberOfItems > 1){
        pxDelayedTaskList->xListData[1] = (ListItem_t *) pvPortMalloc( sizeof( ListItem_t ) );
        if (pxDelayedTaskList->xListData[1] == NULL){
            exit(1);
        }
    }

    /*
     * The task handle passed to TaskDelete can be NULL. In that case, the
     * task to delete is the one in `pxCurrentTCB`, 
     * see the macro `prvGetTCBFromHandle` for reference. 
     * Hence we either return the newly created TCB, or assign it to 
     * `pxCurrentTCB` and return null.
     */
    if (notdet_bool()){
        return newTCB;
    } 
    else
    {
        pxCurrentTCB = newTCB;
        return NULL;
    }
}

BaseType_t old_PrepareTaskLists( TaskHandle_t * xTask )
{
    /*
     * The task handle passed to TaskDelete can be NULL. In that case, the
     * task to delete is the one in `pxCurrentTCB`, see the macro `prvGetTCBFromHandle`
     * in line 1165 (tasks.c) for reference. For that reason, we provide a similar
     * initialization for an arbitrary task `pxTCB` and `pxCurrentTCB`.
     */

    TCB_t * pxTCB = xUnconstrainedTCB();

    if( pxTCB != NULL )
    {
        if( nondet_bool() )
        {
            TCB_t * pxOtherTCB;
            pxOtherTCB = xUnconstrainedTCB();

            /*
             * Nondeterministic insertion of another TCB in the same list
             * to guarantee coverage in line 1174 (tasks.c)
             */
            if( pxOtherTCB != NULL )
            {
                vListInsert( &xPendingReadyList, &( pxOtherTCB->xStateListItem ) );
            }
        }

        vListInsert( &xPendingReadyList, &( pxTCB->xStateListItem ) );

        /*
         * Nondeterministic insertion of an event list item to guarantee
         * coverage in lines 1180-1184 (tasks.c)
         */
        if( nondet_bool() )
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

    if( pxCurrentTCB == NULL )
    {
        return pdFAIL;
    }

    if( nondet_bool() )
    {
        TCB_t * pxOtherTCB;
        pxOtherTCB = xUnconstrainedTCB();

        if( pxOtherTCB != NULL )
        {
            vListInsert( &pxReadyTasksLists[ pxOtherTCB->uxPriority ], &( pxOtherTCB->xStateListItem ) );
        }
    }

    vListInsert( &pxReadyTasksLists[ pxCurrentTCB->uxPriority ], &( pxCurrentTCB->xStateListItem ) );

    /* Use of this macro ensures coverage on line 185 (list.c) */
    listGET_OWNER_OF_NEXT_ENTRY( pxCurrentTCB, &pxReadyTasksLists[ pxCurrentTCB->uxPriority ] );

    if( nondet_bool() )
    {
        vListInsert( pxDelayedTaskList, &( pxCurrentTCB->xEventListItem ) );
    }

    return pdPASS;
}
