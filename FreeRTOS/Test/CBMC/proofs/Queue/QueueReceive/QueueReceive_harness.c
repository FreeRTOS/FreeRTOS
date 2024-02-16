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

#include "FreeRTOS.h"
#include "queue.h"
#include "queue_init.h"
#include "tasksStubs.h"
#include "cbmc.h"

/* prvUnlockQueue is going to decrement this value to 0 in the loop.
* We need a bound for the loop. Using 4 has a reasonable performance resulting
* in 3 unwinding iterations of the loop. The loop is mostly modifying a
* data structure in task.c that is not in the scope of the proof. */
#ifndef LOCK_BOUND
    #define LOCK_BOUND    4
#endif

/* This code checks for time outs. This value is used to bound the time out
 * wait period. The stub function xTaskCheckForTimeOut used to model
 * this wait time will be bounded to this define. */
#ifndef QUEUE_RECEIVE_BOUND
    #define QUEUE_RECEIVE_BOUND    4
#endif

/* If the item size is not bounded, the proof does not finish in a reasonable
 * time due to the involved memcpy commands. */
#ifndef MAX_ITEM_SIZE
    #define MAX_ITEM_SIZE    20
#endif

QueueHandle_t xQueue;

/* This method is used to model side effects of concurrency.
 * The initialization of pxTimeOut is not relevant for this harness. */
void vTaskInternalSetTimeOutState( TimeOut_t * const pxTimeOut )
{
    __CPROVER_assert( __CPROVER_w_ok( &( pxTimeOut->xOverflowCount ), sizeof( BaseType_t ) ), "pxTimeOut should be a valid pointer and xOverflowCount writable" );
    __CPROVER_assert( __CPROVER_w_ok( &( pxTimeOut->xTimeOnEntering ), sizeof( TickType_t ) ), "pxTimeOut should be a valid pointer and xTimeOnEntering writable" );
    xQueue->uxMessagesWaiting = nondet_BaseType_t();
}

void harness()
{
    vInitTaskCheckForTimeOut( 0, QUEUE_RECEIVE_BOUND - 1 );

    xQueue = xUnconstrainedQueueBoundedItemSize( MAX_ITEM_SIZE );


    TickType_t xTicksToWait;

    if( xState == taskSCHEDULER_SUSPENDED )
    {
        xTicksToWait = 0;
    }

    if( xQueue )
    {
        xQueue->cTxLock = LOCK_BOUND - 1;
        xQueue->cRxLock = LOCK_BOUND - 1;

        void * pvBuffer = pvPortMalloc( xQueue->uxItemSize );

        if( !pvBuffer )
        {
            xQueue->uxItemSize = 0;
        }

        xQueueReceive( xQueue, pvBuffer, xTicksToWait );
    }
}
