/*
 * FreeRTOS V202112.00
 * Copyright (C) Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

#include "proof/queue.h"

/* Simplifying assumption: we do not verify queue initialisation in a
 * concurrent environment. We assume the queue initialization (including reset)
 * happens-before all concurrent send/receives. */
#ifdef VERIFAST /*< ***xQueueGenericReset happens-before concurrent behavior*** */
    #define taskENTER_CRITICAL()
    #define taskEXIT_CRITICAL()
#endif

/* The following intermediate queue predicates summarise states used by queue
 * initialization but not used elsewhere so we confine them to these proofs
 * locally. */

/*@
 * predicate queue_init1(QueueHandle_t q;) =
 *  QUEUE_SHAPE(q, _, _, _, _) &*&
 *  queuelists(q)
 *  ;
 *
 * predicate queue_init2(QueueHandle_t q, int8_t *Storage, size_t N, size_t M;) =
 *  QUEUE_SHAPE(q, Storage, N, M, _) &*&
 *  queuelists(q) &*&
 *  0 < N &*&
 *  chars(Storage, (N*M), _) &*&
 *  malloc_block(Storage, N*M) &*&
 *  Storage + N * M <= (int8_t *)UINTPTR_MAX &*&
 *  true
 *  ;
 * @*/

BaseType_t xQueueGenericReset( QueueHandle_t xQueue,
                               BaseType_t xNewQueue )
/*@requires queue_init2(xQueue, ?Storage, ?N, ?M);@*/

/*@ensures 0 == M
 *  ? freertos_mutex(xQueue, Storage, N, 0)
 *  : queue(xQueue, Storage, N, M, 0, (N-1), 0, false, nil) &*& queuelists(xQueue);@*/
{
    #ifdef VERIFAST /*< const pointer declaration */
        Queue_t * pxQueue = xQueue;
    #else
        Queue_t * const pxQueue = xQueue;
    #endif

    configASSERT( pxQueue );

    taskENTER_CRITICAL();
    {
        pxQueue->u.xQueue.pcTail = pxQueue->pcHead + ( pxQueue->uxLength * pxQueue->uxItemSize ); /*lint !e9016 Pointer arithmetic allowed on char types, especially when it assists conveying intent. */
        pxQueue->uxMessagesWaiting = ( UBaseType_t ) 0U;
        pxQueue->pcWriteTo = pxQueue->pcHead;
        /*@mul_mono_l(0, N-1, M);@*/
        pxQueue->u.xQueue.pcReadFrom = pxQueue->pcHead + ( ( pxQueue->uxLength - 1U ) * pxQueue->uxItemSize ); /*lint !e9016 Pointer arithmetic allowed on char types, especially when it assists conveying intent. */
        pxQueue->cRxLock = queueUNLOCKED;
        pxQueue->cTxLock = queueUNLOCKED;

        if( xNewQueue == pdFALSE )
        {
            /* If there are tasks blocked waiting to read from the queue, then
             * the tasks will remain blocked as after this function exits the queue
             * will still be empty.  If there are tasks blocked waiting to write to
             * the queue, then one should be unblocked as after this function exits
             * it will be possible to write to it. */
            if( listLIST_IS_EMPTY( &( pxQueue->xTasksWaitingToSend ) ) == pdFALSE )
            {
                if( xTaskRemoveFromEventList( &( pxQueue->xTasksWaitingToSend ) ) != pdFALSE )
                {
                    queueYIELD_IF_USING_PREEMPTION();
                }
                else
                {
                    mtCOVERAGE_TEST_MARKER();
                }
            }
            else
            {
                mtCOVERAGE_TEST_MARKER();
            }
        }
        else
        {
            /* Ensure the event queues start in the correct state. */
            vListInitialise( &( pxQueue->xTasksWaitingToSend ) );
            vListInitialise( &( pxQueue->xTasksWaitingToReceive ) );
        }

        /*@if (M != 0) { buffer_from_chars(pxQueue->pcHead, N, M); }@*/
    }
    taskEXIT_CRITICAL();

    /* A value is returned for calling semantic consistency with previous
     * versions. */
    return pdPASS;
}

static void prvInitialiseNewQueue( const UBaseType_t uxQueueLength,
                                   const UBaseType_t uxItemSize,
                                   uint8_t * pucQueueStorage,
                                   const uint8_t ucQueueType,
                                   Queue_t * pxNewQueue )

/*@requires queue_init1(pxNewQueue) &*&
 *  0 < uxQueueLength &*& 0 < uxItemSize &*&
 *  malloc_block(pucQueueStorage, uxQueueLength * uxItemSize) &*&
 *  pucQueueStorage + uxQueueLength * uxItemSize <= (uint8_t *)UINTPTR_MAX &*&
 *  uchars(pucQueueStorage, uxQueueLength * uxItemSize,_);@*/

/*@ensures queue(pxNewQueue, ((int8_t *)(void *)pucQueueStorage), uxQueueLength, uxItemSize, 0, (uxQueueLength-1), 0, false, nil) &*&
 *  queuelists(pxNewQueue);@*/
{
    #ifndef VERIFAST /*< void cast of unused var */

        /* Remove compiler warnings about unused parameters should
         * configUSE_TRACE_FACILITY not be set to 1. */
        ( void ) ucQueueType;
    #endif

    if( uxItemSize == ( UBaseType_t ) 0 )
    {
        /* No RAM was allocated for the queue storage area, but PC head cannot
         * be set to NULL because NULL is used as a key to say the queue is used as
         * a mutex.  Therefore just set pcHead to point to the queue as a benign
         * value that is known to be within the memory map. */
        #ifdef VERIFAST /*< stricter casting */
            pxNewQueue->pcHead = ( int8_t * ) ( void * ) pxNewQueue;
        #else
            pxNewQueue->pcHead = ( int8_t * ) pxNewQueue;
        #endif
    }
    else
    {
        /* Set the head to the start of the queue storage area. */
        #ifdef VERIFAST /*< stricter casting */
            pxNewQueue->pcHead = ( int8_t * ) ( void * ) pucQueueStorage;
        #else
            pxNewQueue->pcHead = ( int8_t * ) pucQueueStorage;
        #endif
    }

    /* Initialise the queue members as described where the queue type is
     * defined. */
    pxNewQueue->uxLength = uxQueueLength;
    pxNewQueue->uxItemSize = uxItemSize;
    /*@close queue_init2(pxNewQueue, _, uxQueueLength, uxItemSize);@*/
    #ifdef VERIFAST /*< void cast of unused return value */
        xQueueGenericReset( pxNewQueue, pdTRUE );
    #else
        ( void ) xQueueGenericReset( pxNewQueue, pdTRUE );
    #endif

    #if ( configUSE_TRACE_FACILITY == 1 )
        {
            pxNewQueue->ucQueueType = ucQueueType;
        }
    #endif /* configUSE_TRACE_FACILITY */

    #if ( configUSE_QUEUE_SETS == 1 )
        {
            pxNewQueue->pxQueueSetContainer = NULL;
        }
    #endif /* configUSE_QUEUE_SETS */

    traceQUEUE_CREATE( pxNewQueue );
}


QueueHandle_t xQueueGenericCreate( const UBaseType_t uxQueueLength,
                                   const UBaseType_t uxItemSize,
                                   const uint8_t ucQueueType )

/*@requires 0 < uxQueueLength &*&
 *  0 < uxItemSize &*&
 *  0 < uxQueueLength * uxItemSize &*&
 *  uxQueueLength * uxItemSize <= UINT_MAX;@*/

/*@ensures result == NULL
 *  ? true
 *  : queue(result, _, uxQueueLength, uxItemSize, 0, (uxQueueLength-1), 0, false, nil) &*&
 *      queuelists(result) &*&
 *      result->irqMask |-> _ &*&
 *      result->schedulerSuspend |-> _ &*&
 *      result->locked |-> _;@*/
{
    Queue_t * pxNewQueue;
    size_t xQueueSizeInBytes;
    uint8_t * pucQueueStorage;

    configASSERT( uxQueueLength > ( UBaseType_t ) 0 );

    /* Allocate enough space to hold the maximum number of items that
     * can be in the queue at any time.  It is valid for uxItemSize to be
     * zero in the case the queue is used as a semaphore. */
    xQueueSizeInBytes = ( size_t ) ( uxQueueLength * uxItemSize ); /*lint !e961 MISRA exception as the casts are only redundant for some ports. */

    /* Check for multiplication overflow. */
    configASSERT( ( uxItemSize == 0 ) || ( uxQueueLength == ( xQueueSizeInBytes / uxItemSize ) ) );

    /* Check for addition overflow. */
    configASSERT( ( sizeof( Queue_t ) + xQueueSizeInBytes ) > xQueueSizeInBytes );

    #ifdef VERIFAST /*< ***model single malloc of struct and buffer*** */
        pxNewQueue = ( Queue_t * ) pvPortMalloc( sizeof( Queue_t ) );
    #else

        /* Allocate the queue and storage area.  Justification for MISRA
         * deviation as follows:  pvPortMalloc() always ensures returned memory
         * blocks are aligned per the requirements of the MCU stack.  In this case
         * pvPortMalloc() must return a pointer that is guaranteed to meet the
         * alignment requirements of the Queue_t structure - which in this case
         * is an int8_t *.  Therefore, whenever the stack alignment requirements
         * are greater than or equal to the pointer to char requirements the cast
         * is safe.  In other cases alignment requirements are not strict (one or
         * two bytes). */
        pxNewQueue = ( Queue_t * ) pvPortMalloc( sizeof( Queue_t ) + xQueueSizeInBytes ); /*lint !e9087 !e9079 see comment above. */
    #endif

    if( pxNewQueue != NULL )
    {
        #ifdef VERIFAST /*< ***model single malloc of struct and buffer*** */
            pucQueueStorage = ( uint8_t * ) pvPortMalloc( xQueueSizeInBytes );

            if( pucQueueStorage == NULL )
            {
                vPortFree( pxNewQueue );
                return NULL;
            }

            /*@malloc_block_limits(pucQueueStorage);@*/
        #else

            /* Jump past the queue structure to find the location of the queue
             * storage area. */
            pucQueueStorage = ( uint8_t * ) pxNewQueue;
            pucQueueStorage += sizeof( Queue_t ); /*lint !e9016 Pointer arithmetic allowed on char types, especially when it assists conveying intent. */
        #endif /* ifdef VERIFAST */

        #if ( configSUPPORT_STATIC_ALLOCATION == 1 )
            {
                /* Queues can be created either statically or dynamically, so
                 * note this task was created dynamically in case it is later
                 * deleted. */
                pxNewQueue->ucStaticallyAllocated = pdFALSE;
            }
        #endif /* configSUPPORT_STATIC_ALLOCATION */

        prvInitialiseNewQueue( uxQueueLength, uxItemSize, pucQueueStorage, ucQueueType, pxNewQueue );
    }
    else
    {
        traceQUEUE_CREATE_FAILED( ucQueueType );
        mtCOVERAGE_TEST_MARKER();
    }

    return pxNewQueue;
}
