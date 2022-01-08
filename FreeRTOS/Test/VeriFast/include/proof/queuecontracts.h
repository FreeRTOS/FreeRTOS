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

#ifndef QUEUECONTRACTS_H
#define QUEUECONTRACTS_H

#include "queue.h"

void prvCopyDataFromQueue( Queue_t * const pxQueue,
                           void * const pvBuffer );
/*@requires queue(pxQueue, ?Storage, ?N, ?M, ?W, ?R, ?K, ?is_locked, ?abs) &*& 0 < K &*& chars(pvBuffer, M, _);@*/

/*@ensures queue_after_prvCopyDataFromQueue(pxQueue, Storage, N, M, W, (R+1)%N, K, is_locked, abs) &*&
 *  chars(pvBuffer, M, head(abs));@*/

BaseType_t prvCopyDataToQueue( Queue_t * const pxQueue,
                               const void * pvItemToQueue,
                               const BaseType_t xPosition );

/*@requires queue(pxQueue, ?Storage, ?N, ?M, ?W, ?R, ?K, ?is_locked, ?abs) &*&
 *  (K < N || xPosition == queueOVERWRITE) &*&
 *  chars(pvItemToQueue, M, ?x) &*&
 *  (xPosition == queueSEND_TO_BACK || xPosition == queueSEND_TO_FRONT || (xPosition == queueOVERWRITE && N == 1));@*/

/*@ensures
 *  (xPosition == queueSEND_TO_BACK
 *      ? queue(pxQueue, Storage, N, M, (W+1)%N, R, (K+1), is_locked, append(abs, singleton(x)))
 *      : (xPosition == queueSEND_TO_FRONT
 *          ? (R == 0
 *              ? queue(pxQueue, Storage, N, M, W, (N-1), (K+1), is_locked, cons(x, abs))
 *              : queue(pxQueue, Storage, N, M, W, (R-1), (K+1), is_locked, cons(x, abs)))
 *          : xPosition == queueOVERWRITE &*& queue(pxQueue, Storage, N, M, W, R, 1, is_locked, singleton(x)))
 *  ) &*&
 *  chars(pvItemToQueue, M, x);@*/

BaseType_t prvIsQueueEmpty( Queue_t * pxQueue );
/*@requires [1/2]queuehandle(pxQueue, ?N, ?M, ?is_isr) &*& is_isr == false;@*/
/*@ensures [1/2]queuehandle(pxQueue, N, M, is_isr);@*/

BaseType_t prvIsQueueFull( Queue_t * pxQueue );
/*@requires [1/2]queuehandle(pxQueue, ?N, ?M, ?is_isr) &*& is_isr == false;@*/
/*@ensures [1/2]queuehandle(pxQueue, N, M, is_isr);@*/

#endif /* QUEUECONTRACTS_H */
