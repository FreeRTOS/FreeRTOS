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

/* In this case we cannot wrap the macro in a function call to give a function
 * contract because we require annotations within the macro body, which is not
 * supported by VeriFast */
#define prvLockQueue( pxQueue )                            \
    taskENTER_CRITICAL();                                  \
    {                                                      \
        if( ( pxQueue )->cRxLock == queueUNLOCKED )        \
        {                                                  \
            ( pxQueue )->cRxLock = queueLOCKED_UNMODIFIED; \
        }                                                  \
        if( ( pxQueue )->cTxLock == queueUNLOCKED )        \
        {                                                  \
            ( pxQueue )->cTxLock = queueLOCKED_UNMODIFIED; \
        }                                                  \
    }                                                      \
    taskEXIT_CRITICAL()

void wrapper_prvLockQueue( QueueHandle_t xQueue )

/*@requires [1/2]queuehandle(xQueue, ?N, ?M, ?is_isr) &*& is_isr == false &*&
 *  [1/2]queuelock(xQueue);@*/

/*@ensures [1/2]queuehandle(xQueue, N, M, is_isr) &*&
 *  [1/2]xQueue->locked |-> ?m &*&
 *  mutex_held(m, queue_locked_invariant(xQueue), currentThread, 1/2) &*&
 *  queue_locked_invariant(xQueue)();@*/
{
    taskENTER_CRITICAL();
    /*@open queue(xQueue, ?Storage, N, M, ?W, ?R, ?K, ?is_locked, ?abs);@*/
    {
        if( ( xQueue )->cRxLock == queueUNLOCKED )
        {
            ( xQueue )->cRxLock = queueLOCKED_UNMODIFIED;
        }

        if( ( xQueue )->cTxLock == queueUNLOCKED )
        {
            ( xQueue )->cTxLock = queueLOCKED_UNMODIFIED;
        }
    }
    /*@close queue(xQueue, Storage, N, M, W, R, K, true, abs);@*/
    taskEXIT_CRITICAL();
    #ifdef VERIFAST /*< ghost action */
        mutex_acquire( xQueue->locked );
    #endif
}
