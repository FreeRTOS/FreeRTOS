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
#include "queue_datastructure.h"

#ifndef CBMC_OBJECT_BITS
    #define CBMC_OBJECT_BITS    7
#endif

#ifndef CBMC_OBJECT_MAX_SIZE
    #define CBMC_OBJECT_MAX_SIZE    ( UINT32_MAX >> ( CBMC_OBJECT_BITS + 1 ) )
#endif

/* Using prvCopyDataToQueue together with prvNotifyQueueSetContainer
 * leads to a problem space explosion. Therefore, we use this stub
 * and a sepearted proof on prvCopyDataToQueue to deal with it.
 * As prvNotifyQueueSetContainer is disabled if configUSE_QUEUE_SETS != 1,
 * in other cases the original implementation should be used. */
#if ( configUSE_QUEUE_SETS == 1 )
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
#endif /* if ( configUSE_QUEUE_SETS == 1 ) */

/* xQueueCreateSet is compiled out if configUSE_QUEUE_SETS != 1.*/
#if ( configUSE_QUEUE_SETS == 1 )
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

            /* This is an invariant checked with a couple of asserts in the code base.
             * If it is false from the beginning, the CBMC proofs are not able to succeed*/
            __CPROVER_assume( xSet->uxMessagesWaiting < xSet->uxLength );
            xSet->xTasksWaitingToSend.uxNumberOfItems = nondet_UBaseType_t();
        }

        return xSet;
    }
#endif /* if ( configUSE_QUEUE_SETS == 1 ) */

/* Create a mostly unconstrained Queue but bound the max item size.
 * This is required for performance reasons in CBMC at the moment. */
QueueHandle_t xUnconstrainedQueueBoundedItemSize( UBaseType_t uxItemSizeBound )
{
    UBaseType_t uxQueueLength;
    UBaseType_t uxItemSize;
    uint8_t ucQueueType;

    __CPROVER_assume( uxQueueLength > 0 );
    __CPROVER_assume( uxItemSize < uxItemSizeBound );

    /* QueueGenericCreate method does not check for multiplication overflow */
    size_t uxQueueStorageSize;
    __CPROVER_assume( uxQueueStorageSize < CBMC_OBJECT_MAX_SIZE );
    __CPROVER_assume( uxItemSize < uxQueueStorageSize / uxQueueLength );

    QueueHandle_t xQueue =
        xQueueGenericCreate( uxQueueLength, uxItemSize, ucQueueType );

    if( xQueue )
    {
        xQueue->cTxLock = nondet_int8_t();
        __CPROVER_assume( xQueue->cTxLock != 127 );
        xQueue->cRxLock = nondet_int8_t();
        __CPROVER_assume( xQueue->cRxLock != 127 );
        xQueue->uxMessagesWaiting = nondet_UBaseType_t();

        /* This is an invariant checked with a couple of asserts in the code base.
         * If it is false from the beginning, the CBMC proofs are not able to succeed*/
        __CPROVER_assume( xQueue->uxMessagesWaiting < xQueue->uxLength );
        xQueue->xTasksWaitingToReceive.uxNumberOfItems = nondet_UBaseType_t();
        xQueue->xTasksWaitingToSend.uxNumberOfItems = nondet_UBaseType_t();
        #if ( configUSE_QUEUE_SETS == 1 )
            xQueueAddToSet( xQueue, xUnconstrainedQueueSet() );
        #endif
    }

    return xQueue;
}

/* Create a mostly unconstrained Queue */
QueueHandle_t xUnconstrainedQueue( void )
{
    UBaseType_t uxQueueLength;
    UBaseType_t uxItemSize;
    uint8_t ucQueueType;

    __CPROVER_assume( uxQueueLength > 0 );

    /* QueueGenericCreate method does not check for multiplication overflow */
    size_t uxQueueStorageSize;
    __CPROVER_assume( uxQueueStorageSize < CBMC_OBJECT_MAX_SIZE );
    __CPROVER_assume( uxItemSize < uxQueueStorageSize / uxQueueLength );

    QueueHandle_t xQueue =
        xQueueGenericCreate( uxQueueLength, uxItemSize, ucQueueType );

    if( xQueue )
    {
        xQueue->cTxLock = nondet_int8_t();
        __CPROVER_assume( xQueue->cTxLock != 127 );
        xQueue->cRxLock = nondet_int8_t();
        xQueue->uxMessagesWaiting = nondet_UBaseType_t();

        /* This is an invariant checked with a couple of asserts in the code base.
         * If it is false from the beginning, the CBMC proofs are not able to succeed*/
        __CPROVER_assume( xQueue->uxMessagesWaiting < xQueue->uxLength );
        xQueue->xTasksWaitingToReceive.uxNumberOfItems = nondet_UBaseType_t();
        xQueue->xTasksWaitingToSend.uxNumberOfItems = nondet_UBaseType_t();
        #if ( configUSE_QUEUE_SETS == 1 )
            xQueueAddToSet( xQueue, xUnconstrainedQueueSet() );
        #endif
    }

    return xQueue;
}

/* Create a mostly unconstrained Mutex */
QueueHandle_t xUnconstrainedMutex( void )
{
    uint8_t ucQueueType;
    QueueHandle_t xQueue =
        xQueueCreateMutex( ucQueueType );

    if( xQueue )
    {
        xQueue->cTxLock = nondet_int8_t();
        __CPROVER_assume( xQueue->cTxLock != 127 );
        xQueue->cRxLock = nondet_int8_t();
        xQueue->uxMessagesWaiting = nondet_UBaseType_t();

        /* This is an invariant checked with a couple of asserts in the code base.
         * If it is false from the beginning, the CBMC proofs are not able to succeed*/
        __CPROVER_assume( xQueue->uxMessagesWaiting < xQueue->uxLength );
        xQueue->xTasksWaitingToReceive.uxNumberOfItems = nondet_UBaseType_t();
        xQueue->xTasksWaitingToSend.uxNumberOfItems = nondet_UBaseType_t();
        #if ( configUSE_QUEUE_SETS == 1 )
            xQueueAddToSet( xQueue, xUnconstrainedQueueSet() );
        #endif
    }

    return xQueue;
}
