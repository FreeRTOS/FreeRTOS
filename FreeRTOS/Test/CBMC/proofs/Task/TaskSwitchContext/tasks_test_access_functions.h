
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
TaskHandle_t xUnconstrainedTCB()
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
void vSetGlobalVariables( void )
{
    uxSchedulerSuspended = nondet_ubasetype();
    uxTopReadyPriority = configMAX_PRIORITIES - 1;
}


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

// Initialize the list to non-deterministic sizes and malloc
// the one element that we are going to access.
BaseType_t xPrepareTaskLists( void )
{
    // Allocate new TCB
    __CPROVER_assert_zero_allocation();
    TCB_t * newTCB = xUnconstrainedTCB();
    if( newTCB == NULL )
    {
        return pdFAIL;
    }

    // Set non-deterministic list sizes.
    prvInitialiseTaskLists();
    for( UBaseType_t uxPriority = ( UBaseType_t ) 0U; uxPriority < ( UBaseType_t ) configMAX_PRIORITIES; uxPriority++ )
    {
        vSetNonDeterministicListSize(&pxReadyTasksLists[uxPriority]);
    }

    // Assumption: The idle task is always in the ready list with 0 priority.
    // Hence the list should have at least 1 element.
    // TODO: Is this a reasonable assumption?
    __CPROVER_assume(pxReadyTasksLists[0].uxNumberOfItems > 0);
    
    // Set the top ready priority to the highest non-empty priority.
    UBaseType_t topReadyPriority = configMAX_PRIORITIES - 1;
    while( listLIST_IS_EMPTY( &( pxReadyTasksLists[ topReadyPriority ] ) ) )
    {
        --topReadyPriority;
    }            

    // Set the new TCB to the one element that is going to be accessed.
    // This saves proof time by avoiding allocating additional unnecessary tasks  
    // (is an overapproximation, and hence sufficient to prove memory safety) 
    UBaseType_t indexToBeAccessed = pxReadyTasksLists[topReadyPriority].pxIndex + 1;                                                            \
    if( indexToBeAccessed == (pxReadyTasksLists[ topReadyPriority ]).uxNumberOfItems)
    {
        indexToBeAccessed = ( UBaseType_t ) 0;
    }
    pxReadyTasksLists[topReadyPriority].xListData[indexToBeAccessed] = &(newTCB->xStateListItem);                         
    
    return pdPASS;
}


