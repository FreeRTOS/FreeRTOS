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

#include "FreeRTOS.h"
#include "queue.h"
#include "queue_datastructure.h"
#include "cbmc.h"

#ifndef LOCK_BOUND
    #define LOCK_BOUND    4
#endif

BaseType_t prvNotifyQueueSetContainer( const Queue_t * const pxQueue,
                                       const BaseType_t xCopyPosition );

BaseType_t prvCopyDataToQueue( Queue_t * const pxQueue,
                               const void * pvItemToQueue,
                               const BaseType_t xPosition )
{
    if( pxQueue->uxItemSize > ( UBaseType_t ) 0 )
    {
        __CPROVER_assert( __CPROVER_r_ok( pvItemToQueue, ( size_t ) pxQueue->uxItemSize ), "pvItemToQueue region must be readable" );

        if( xPosition == queueSEND_TO_BACK )
        {
            __CPROVER_assert( __CPROVER_w_ok( ( void * ) pxQueue->pcWriteTo, ( size_t ) pxQueue->uxItemSize ), "pxQueue->pcWriteTo region must be writable" );
        }
        else
        {
            __CPROVER_assert( __CPROVER_w_ok( ( void * ) pxQueue->u.xQueue.pcReadFrom, ( size_t ) pxQueue->uxItemSize ), "pxQueue->u.xQueue.pcReadFrom region must be writable" );
        }

        return pdFALSE;
    }
    else
    {
        return nondet_BaseType_t();
    }
}

QueueSetHandle_t xUnconstrainedQueueSet()
{
    UBaseType_t uxEventQueueLength = 2;
    QueueSetHandle_t xSet = xQueueCreateSet( uxEventQueueLength );

    if( xSet )
    {
        xSet->cTxLock = nondet_int8_t();
        __CPROVER_assume( xSet->cTxLock != 127 );
        xSet->cRxLock = nondet_int8_t();
        xSet->uxMessagesWaiting = nondet_UBaseType_t();
        xSet->xTasksWaitingToReceive.uxNumberOfItems = nondet_UBaseType_t();
        xSet->xTasksWaitingToSend.uxNumberOfItems = nondet_UBaseType_t();
    }

    return xSet;
}

void harness()
{
    UBaseType_t uxQueueLength;
    UBaseType_t uxItemSize;
    uint8_t ucQueueType;

    __CPROVER_assume( uxQueueLength > 0 );
    __CPROVER_assume( uxItemSize < 10 );

    /* The implicit assumption for the QueueGenericCreate method is,
     * that there are no overflows in the computation and the inputs are safe.
     * There is no check for this in the code base */
    UBaseType_t upper_bound = portMAX_DELAY - sizeof( Queue_t );
    __CPROVER_assume( uxItemSize < ( upper_bound ) / uxQueueLength );
    QueueHandle_t xQueue =
        xQueueGenericCreate( uxQueueLength, uxItemSize, ucQueueType );

    if( xQueue )
    {
        xQueueAddToSet( xQueue, xUnconstrainedQueueSet() );

        if( xQueue->pxQueueSetContainer )
        {
            __CPROVER_assume( xQueue->pxQueueSetContainer->uxMessagesWaiting < xQueue->pxQueueSetContainer->uxLength );
            BaseType_t xCopyPosition = nondet_BaseType_t();
            prvNotifyQueueSetContainer( xQueue, xCopyPosition );
        }
    }
}
