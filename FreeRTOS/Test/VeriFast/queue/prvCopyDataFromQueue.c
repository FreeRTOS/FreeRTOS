/*
 * FreeRTOS V202111.00
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

static void prvCopyDataFromQueue( Queue_t * const pxQueue,
                                  void * const pvBuffer )
/*@requires queue(pxQueue, ?Storage, ?N, ?M, ?W, ?R, ?K, ?is_locked, ?abs) &*& 0 < K &*& chars(pvBuffer, M, _);@*/

/*@ensures queue_after_prvCopyDataFromQueue(pxQueue, Storage, N, M, W, (R+1)%N, K, is_locked, abs) &*&
 *  chars(pvBuffer, M, head(abs));@*/
{
    if( pxQueue->uxItemSize != ( UBaseType_t ) 0 )
    {
        /*@assert buffer(Storage, N, M, ?contents);@*/
        /*@mul_mono_l(R, N-1, M);@*/
        pxQueue->u.xQueue.pcReadFrom += pxQueue->uxItemSize;           /*lint !e9016 Pointer arithmetic on char types ok, especially in this use case where it is the clearest way of conveying intent. */

        if( pxQueue->u.xQueue.pcReadFrom >= pxQueue->u.xQueue.pcTail ) /*lint !e946 MISRA exception justified as use of the relational operator is the cleanest solutions. */
        {
            /*@div_leq(N, R+1, M);@*/                                  /* now we know R == N-1 */
            pxQueue->u.xQueue.pcReadFrom = pxQueue->pcHead;
        }
        else
        {
            /*@{
             *  div_lt(R+1, N, M); // now we know R+1 < N
             *  mod_lt(R+1, N);    // so, R+1 == (R+1)%N
             *  note(pxQueue->u.xQueue.pcReadFrom == Storage + ((R + 1) * M));
             *  note(                                Storage + ((R + 1) * M) == Storage + (((R + 1) % N) * M));
             * }@*/
            mtCOVERAGE_TEST_MARKER();
        }

        /*@mod_plus(R+1, K, N);@*/
        /*@mod_mod(R+1, N);@*/
        /*@split_element(Storage, N, M, (R+1)%N);@*/

        /*@assert
         *  buffer(Storage, (R+1)%N, M, ?prefix) &*&
         *  chars(Storage + ((R+1)%N) * M, M, ?element) &*&
         *  buffer(Storage + ((R+1)%N + 1) * M, (N-1-(R+1)%N), M, ?suffix);@*/
        #ifdef VERIFAST /*< void cast of unused return value */
            memcpy( ( void * ) pvBuffer, ( void * ) pxQueue->u.xQueue.pcReadFrom, ( size_t ) pxQueue->uxItemSize );
        #else
            ( void ) memcpy( ( void * ) pvBuffer, ( void * ) pxQueue->u.xQueue.pcReadFrom, ( size_t ) pxQueue->uxItemSize ); /*lint !e961 !e418 !e9087 MISRA exception as the casts are only redundant for some ports.  Also previous logic ensures a null pointer can only be passed to memcpy() when the count is 0.  Cast to void required by function signature and safe as no alignment requirement and copy length specified in bytes. */
        #endif

        /*@{
         *  combine_list_no_change(prefix, element, suffix, (R+1)%N, contents);
         *  join_element(Storage, N, M, (R+1)%N);
         *  length_take(K, contents);
         *  take_length_eq(K, rotate_left((R+1)%N, contents), abs);
         *  deq_value_lemma(K, (R+1)%N, contents, abs);
         * }@*/
    }
}

void caller_reinstates_queue_predicate( Queue_t * const pxQueue,
                                        void * const pvBuffer )

/*@requires queue(pxQueue, ?Storage, ?N, ?M, ?W, ?R, ?K, ?is_locked, ?abs) &*&
 *  0 < K &*&
 *  chars(pvBuffer, M, _);@*/

/*@ensures
 *  queue(pxQueue, Storage, N, M, W, (R+1)%N, K-1, is_locked, tail(abs)) &*&
 *  chars(pvBuffer, M, head(abs));@*/
{
    prvCopyDataFromQueue( pxQueue, pvBuffer );
    /*@open queue_after_prvCopyDataFromQueue(pxQueue, Storage, N, M, W, (R+1)%N, K, is_locked, abs);@*/
    /*@assert buffer(Storage, N, M, ?contents);@*/
    pxQueue->uxMessagesWaiting = pxQueue->uxMessagesWaiting - 1;
    /*@deq_lemma(K, (R+1)%N, contents, abs, head(abs));@*/
}
