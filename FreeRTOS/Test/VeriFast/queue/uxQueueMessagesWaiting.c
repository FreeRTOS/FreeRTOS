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

/* It may seem that the read of `pxQueue->uxMessagesWaiting` is required to be
 * contained in a critical region to be thread-safe. However, it is impossible for
 * this read to be involved in a data race due to the atomicity mechanism used by
 * tasks and ISRs: masking and enabling interrupts. If we assume (1) a
 * uniprocessor system and (2) that higher priority ISRs never call queue API
 * functions then masking interrupts ensures *strong isolation* meaning critical
 * regions protected by interrupt masking/enabling are isolated from other
 * critical regions and code outside of critical regions. */

UBaseType_t uxQueueMessagesWaitingFromISR( const QueueHandle_t xQueue )
/*@requires queue(xQueue, ?Storage, ?N, ?M, ?W, ?R, ?K, ?is_locked, ?abs);@*/
/*@ensures queue(xQueue, Storage, N, M, W, R, K, is_locked, abs) &*& result == K;@*/
{
    UBaseType_t uxReturn;

#ifdef VERIFAST /*< const pointer declaration */
    Queue_t * pxQueue = xQueue;
#else
    Queue_t * const pxQueue = xQueue;
#endif

    configASSERT( pxQueue );
    uxReturn = pxQueue->uxMessagesWaiting;

    return uxReturn;
}

UBaseType_t uxQueueMessagesWaiting( const QueueHandle_t xQueue )
/*@requires [1/2]queuehandle(xQueue, ?N, ?M, ?is_isr) &*& is_isr == false;@*/
/*@ensures [1/2]queuehandle(xQueue, N, M, is_isr);@*/
{
    UBaseType_t uxReturn;

    configASSERT( xQueue );

    taskENTER_CRITICAL();
    {
        /*@assert queue(xQueue, ?Storage, N, M, ?W, ?R, ?K, ?is_locked, ?abs);@*/
        uxReturn = ( ( Queue_t * ) xQueue )->uxMessagesWaiting;
        /*@close queue(xQueue, Storage, N, M, W, R, K, is_locked, abs);@*/
    }
    taskEXIT_CRITICAL();

    return uxReturn;
} /*lint !e818 Pointer cannot be declared const as xQueue is a typedef not pointer. */

/* *INDENT-ON* */
