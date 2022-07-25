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
 * Our stub for pvPortMalloc in cbmc.h nondeterministically chooses
 * either to return NULL or to allocate the requested memory.
 */
void vNondetSetCurrentTCB( void )
{
    pxCurrentTCB = pvPortMalloc( sizeof( TCB_t ) );
}

/*
 * We just require task lists to be initialized for this proof
 */
void vPrepareTaskLists( void )
{
    __CPROVER_assert_zero_allocation();

    prvInitialiseTaskLists();
}

/*
 * We set the values of relevant global
 * variables to nondeterministic values
 */
void vSetGlobalVariables( void )
{
    xSchedulerRunning = nondet_basetype();
    uxCurrentNumberOfTasks = nondet_ubasetype();
}

/*
 * For each of the pxReadyTasksLists lists (only kind of list needed for task-create)
 * we could insert into, set a non-deterministic list size and pxIndex.
 */
void vSetNonDeterministicListSizes( void )
{
    for( UBaseType_t uxPriority = ( UBaseType_t ) 0U; uxPriority < ( UBaseType_t ) configMAX_PRIORITIES; uxPriority++ )
    {
        pxReadyTasksLists[uxPriority].uxNumberOfItems = nondet_ubasetype();
        if (pxReadyTasksLists[uxPriority].uxNumberOfItems == 0){
            pxReadyTasksLists[uxPriority].pxIndex = 0;
        }
        else{
            __CPROVER_assume( pxReadyTasksLists[uxPriority].pxIndex < pxReadyTasksLists[uxPriority].uxNumberOfItems );
        }
    }
}
/*
 * pvPortMalloc is nondeterministic by definition, thus we do not need
 * to check for NULL allocation in this function
 */
TaskHandle_t * pxNondetSetTaskHandle( void )
{
    TaskHandle_t * pxNondetTaskHandle = pvPortMalloc( sizeof( TaskHandle_t ) );

    return pxNondetTaskHandle;
}

/*
 * Tries to allocate a string of size xStringLength and sets the string
 * to be terminated using a nondeterministic index if allocation was successful
 */
char * pcNondetSetString( size_t xStringLength )
{
    char * pcName = pvPortMalloc( xStringLength );

    if( pcName != NULL )
    {
        size_t uNondetIndex;
        __CPROVER_assume( uNondetIndex < xStringLength );
        pcName[ uNondetIndex ] = '\0';
    }

    return pcName;
}

/* 
 * Simply creates a new TCB object
 */
TaskHandle_t pxCreateTCB()
{
    TaskHandle_t newTCB = (TCB_t *) pvPortMalloc( sizeof( TCB_t ) );
    return newTCB;
}