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

#ifndef LOCK_BOUND
    #define LOCK_BOUND    4
#endif

#ifndef QUEUE_SEND_BOUND
    #define QUEUE_SEND_BOUND    4
#endif

#if ( configUSE_QUEUE_SETS == 0 )
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
#else /* if ( configUSE_QUEUE_SETS == 0 ) */
    BaseType_t prvNotifyQueueSetContainer( const Queue_t * const pxQueue )
    {
        Queue_t * pxQueueSetContainer = pxQueue->pxQueueSetContainer;

        configASSERT( pxQueueSetContainer );
    }

    void prvUnlockQueue( Queue_t * const pxQueue )
    {
        configASSERT( pxQueue );

        if( pxQueue->pxQueueSetContainer != NULL )
        {
            prvNotifyQueueSetContainer( pxQueue );
        }

        listLIST_IS_EMPTY( &( pxQueue->xTasksWaitingToReceive ) );
        pxQueue->cTxLock = queueUNLOCKED;

        listLIST_IS_EMPTY( &( pxQueue->xTasksWaitingToSend ) );
        pxQueue->cRxLock = queueUNLOCKED;
    }

#endif /* if ( configUSE_QUEUE_SETS == 0 ) */

void harness()
{
    /*Initialise the tasksStubs */
    vInitTaskCheckForTimeOut( 0, QUEUE_SEND_BOUND - 1 );
    xState = nondet_basetype();
    QueueHandle_t xQueue =
        xUnconstrainedQueueBoundedItemSize( 2 );

    TickType_t xTicksToWait;

    if( xState == taskSCHEDULER_SUSPENDED )
    {
        xTicksToWait = 0;
    }

    if( xQueue )
    {
        void * pvItemToQueue = pvPortMalloc( xQueue->uxItemSize );
        BaseType_t xCopyPosition;

        if( xCopyPosition == queueOVERWRITE )
        {
            xQueue->uxLength = 1;
        }

        if( xQueue->uxItemSize == 0 )
        {
            /* uxQueue->xQueueType is a pointer to the head of the queue storage area.
             * If an item has a size, this pointer must not be modified after init.
             * Otherwise some of the write statements will fail. */
            xQueue->uxQueueType = nondet_int8_t();
            pvItemToQueue = 0;
        }

        /* This code checks explicitly for violations of the pxQueue->uxMessagesWaiting < pxQueue->uxLength
         * invariant. */
        xQueue->uxMessagesWaiting = nondet_UBaseType_t();

        /* These values are decremented during a while loop interacting with task.c.
         * This interaction is currently abstracted away.*/
        xQueue->cTxLock = LOCK_BOUND - 1;
        xQueue->cRxLock = LOCK_BOUND - 1;

        if( !pvItemToQueue )
        {
            xQueue->uxItemSize = 0;
        }

        xQueueGenericSend( xQueue, pvItemToQueue, xTicksToWait, xCopyPosition );
    }
}
