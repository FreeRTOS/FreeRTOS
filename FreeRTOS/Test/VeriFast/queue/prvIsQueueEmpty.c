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
#define taskENTER_CRITICAL()    setInterruptMask( pxQueue )
#define taskEXIT_CRITICAL()     clearInterruptMask( pxQueue )

static BaseType_t prvIsQueueEmpty( const Queue_t * pxQueue )
/*@requires [1/2]queuehandle(pxQueue, ?N, ?M, ?is_isr) &*& is_isr == false;@*/
/*@ensures [1/2]queuehandle(pxQueue, N, M, is_isr);@*/
{
    BaseType_t xReturn;

    taskENTER_CRITICAL();
    /*@assert queue(pxQueue, ?Storage, N, M, ?W, ?R, ?K, ?is_locked, ?abs);@*/
    {
        if( pxQueue->uxMessagesWaiting == ( UBaseType_t ) 0 )
        {
            xReturn = pdTRUE;
        }
        else
        {
            xReturn = pdFALSE;
        }
    }
    /*@close queue(pxQueue, Storage, N, M, W, R, K, is_locked, abs);@*/
    taskEXIT_CRITICAL();

    return xReturn;
}
