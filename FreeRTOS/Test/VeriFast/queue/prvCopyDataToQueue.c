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

/* *INDENT-OFF* */

#include "proof/queue.h"

static BaseType_t prvCopyDataToQueue( Queue_t * const pxQueue,
                                      const void * pvItemToQueue,
                                      const BaseType_t xPosition )
/*@requires queue(pxQueue, ?Storage, ?N, ?M, ?W, ?R, ?K, ?is_locked, ?abs) &*&
    (K < N || xPosition == queueOVERWRITE) &*&
    chars(pvItemToQueue, M, ?x) &*&
    (xPosition == queueSEND_TO_BACK || xPosition == queueSEND_TO_FRONT || (xPosition == queueOVERWRITE && N == 1));@*/
/*@ensures
    (xPosition == queueSEND_TO_BACK
        ? queue(pxQueue, Storage, N, M, (W+1)%N, R, (K+1), is_locked, append(abs, singleton(x)))
        : (xPosition == queueSEND_TO_FRONT
            ? (R == 0
                ? queue(pxQueue, Storage, N, M, W, (N-1), (K+1), is_locked, cons(x, abs))
                : queue(pxQueue, Storage, N, M, W, (R-1), (K+1), is_locked, cons(x, abs)))
            : xPosition == queueOVERWRITE &*& queue(pxQueue, Storage, N, M, W, R, 1, is_locked, singleton(x)))
    ) &*&
    chars(pvItemToQueue, M, x);@*/
{
    BaseType_t xReturn = pdFALSE;
    UBaseType_t uxMessagesWaiting;

    /* This function is called from a critical section. */

    uxMessagesWaiting = pxQueue->uxMessagesWaiting;

    /* The abstract list of list of chars of `Storage` is `contents` */
    /*@assert buffer(Storage, N, M, ?contents);@*/
    if( pxQueue->uxItemSize == ( UBaseType_t ) 0 )
    {
        /* This case is unreachable for queues */
        /*@assert false;@*/
        #if ( configUSE_MUTEXES == 1 )
        {
            if( pxQueue->uxQueueType == queueQUEUE_IS_MUTEX )
            {
                /* The mutex is no longer being held. */
                xReturn = xTaskPriorityDisinherit( pxQueue->u.xSemaphore.xMutexHolder );
                pxQueue->u.xSemaphore.xMutexHolder = NULL;
            }
            else
            {
                mtCOVERAGE_TEST_MARKER();
            }
        }
        #endif /* configUSE_MUTEXES */
    }
    else if( xPosition == queueSEND_TO_BACK )
    {
#ifdef VERIFAST /*< void cast of unused return value */
        /* Now we focus the proof on the logical element of the buffer that
         * will be updated using the following lemma to split the buffer into 3
         * parts: a prefix, the element we want to update, and the suffix. This
         * enables the subsequent memcpy to verify. */
        /*@split_element(Storage, N, M, W);@*/
        /*@assert
            buffer(Storage, W, M, ?prefix) &*&
            chars(Storage + W * M, M, _) &*&
            buffer(Storage + (W + 1) * M, (N-1-W), M, ?suffix);@*/
        memcpy( ( void * ) pxQueue->pcWriteTo, pvItemToQueue, ( size_t ) pxQueue->uxItemSize );
        /* After the update we stitch the buffer back together */
        /*@join_element(Storage, N, M, W);@*/
        /*@combine_list_update(prefix, x, suffix, W, contents);@*/
#else
        ( void ) memcpy( ( void * ) pxQueue->pcWriteTo, pvItemToQueue, ( size_t ) pxQueue->uxItemSize ); /*lint !e961 !e418 !e9087 MISRA exception as the casts are only redundant for some ports, plus previous logic ensures a null pointer can only be passed to memcpy() if the copy size is 0.  Cast to void required by function signature and safe as no alignment requirement and copy length specified in bytes. */
#endif
        /*@mul_mono_l(W, N-1, M);@*/
        pxQueue->pcWriteTo += pxQueue->uxItemSize;                                                       /*lint !e9016 Pointer arithmetic on char types ok, especially in this use case where it is the clearest way of conveying intent. */

        if( pxQueue->pcWriteTo >= pxQueue->u.xQueue.pcTail )                                             /*lint !e946 MISRA exception justified as comparison of pointers is the cleanest solution. */
        {
            /*@div_leq(N, W+1, M);@*/ /* now we know W == N-1 so (W+1)%N == 0 */
            pxQueue->pcWriteTo = pxQueue->pcHead;
        }
        else
        {
            /*@{
                div_lt(W+1, N, M); // now we know W+1 < N
                mod_lt(W+1, N);    // so, W+1 == (W+1)%N
                note(pxQueue->pcWriteTo == Storage + ((W + 1) * M));
                note(                      Storage + ((W + 1) * M) == Storage + (((W + 1) % N) * M));
            }@*/
            mtCOVERAGE_TEST_MARKER();
        }
    }
    else
    {
#ifdef VERIFAST /*< void cast of unused return value */
        /*@split_element(Storage, N, M, R);@*/
        /*@assert
            buffer(Storage, R, M, ?prefix) &*&
            chars(Storage + R * M, M, _) &*&
            buffer(Storage + (R + 1) * M, (N-1-R), M, ?suffix);@*/
        memcpy( ( void * ) pxQueue->u.xQueue.pcReadFrom, pvItemToQueue, ( size_t ) pxQueue->uxItemSize );
        /*@join_element(Storage, N, M, R);@*/
        /*@combine_list_update(prefix, x, suffix, R, contents);@*/
#else
        ( void ) memcpy( ( void * ) pxQueue->u.xQueue.pcReadFrom, pvItemToQueue, ( size_t ) pxQueue->uxItemSize ); /*lint !e961 !e9087 !e418 MISRA exception as the casts are only redundant for some ports.  Cast to void required by function signature and safe as no alignment requirement and copy length specified in bytes.  Assert checks null pointer only used when length is 0. */
#endif
        pxQueue->u.xQueue.pcReadFrom -= pxQueue->uxItemSize;

        if( pxQueue->u.xQueue.pcReadFrom < pxQueue->pcHead ) /*lint !e946 MISRA exception justified as comparison of pointers is the cleanest solution. */
        {
            pxQueue->u.xQueue.pcReadFrom = ( pxQueue->u.xQueue.pcTail - pxQueue->uxItemSize );
            /*@{ div_leq(R-1, 0, M); leq_bound(R, 0); }@*/
            /*@assert R == 0;@*/
            /*@assert pxQueue->u.xQueue.pcReadFrom == Storage + (N-1) * M;@*/
        }
        else
        {
            /*@assert 0 < R;@*/
            /*@assert pxQueue->u.xQueue.pcReadFrom == Storage + (R-1) * M;@*/
            mtCOVERAGE_TEST_MARKER();
        }

        /*@
        if (R == 0)
        {
           mod_plus(N, (K+1), N); mod_same(N); mod_mod(K+1, N);
           assert W == ((N-1) + 1 + (K+1)) % N;
        }
        @*/
        if( xPosition == queueOVERWRITE )
        {
            if( uxMessagesWaiting > ( UBaseType_t ) 0 )
            {
                /* An item is not being added but overwritten, so subtract
                 * one from the recorded number of items in the queue so when
                 * one is added again below the number of recorded items remains
                 * correct. */
                --uxMessagesWaiting;
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

    pxQueue->uxMessagesWaiting = uxMessagesWaiting + ( UBaseType_t ) 1;

    /*@
    if (xPosition == queueSEND_TO_BACK)
    {
        enq_lemma(K, (R+1)%N, contents, abs, x);
        mod_plus_one(W, R + 1 + K, N);
        mod_plus_distr(R+1, K, N);
    }
    else if (xPosition == queueSEND_TO_FRONT)
    {
        front_enq_lemma(K, R, contents, abs, x);
        if (0 < R)
        {
            mod_lt(R, N);
        }
    }
    @*/
    return xReturn;
}

/* *INDENT-ON* */
