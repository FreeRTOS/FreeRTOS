/*
 * FreeRTOS V202012.00
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
 */

#include "proof/queue.h"
#define configSUPPORT_DYNAMIC_ALLOCATION    1
#define configSUPPORT_STATIC_ALLOCATION     0

void vQueueDelete( QueueHandle_t xQueue )
/*@requires queue(xQueue, ?Storage, ?N, ?M, ?W, ?R, ?K, ?is_locked, ?abs) &*&
    queuelists(xQueue) &*&
    xQueue->irqMask |-> _ &*&
    xQueue->schedulerSuspend |-> _ &*&
    xQueue->locked |-> _;@*/
/*@ensures true;@*/
{
#ifdef VERIFAST /*< const pointer declaration */
    Queue_t * pxQueue = xQueue;
#else
    Queue_t * const pxQueue = xQueue;
#endif

    configASSERT( pxQueue );
    traceQUEUE_DELETE( pxQueue );

    #if ( configQUEUE_REGISTRY_SIZE > 0 )
        {
            vQueueUnregisterQueue( pxQueue );
        }
    #endif

    #if ( ( configSUPPORT_DYNAMIC_ALLOCATION == 1 ) && ( configSUPPORT_STATIC_ALLOCATION == 0 ) )
        {
            /* The queue can only have been allocated dynamically - free it
             * again. */
            vPortFree( pxQueue );
#ifdef VERIFAST /*< leak ghost state on deletion */
            /*@leak buffer(_, _, _, _);@*/
            /*@leak malloc_block(_, _);@*/
#endif
        }
    #elif ( ( configSUPPORT_DYNAMIC_ALLOCATION == 1 ) && ( configSUPPORT_STATIC_ALLOCATION == 1 ) )
        {
            /* The queue could have been allocated statically or dynamically, so
             * check before attempting to free the memory. */
            if( pxQueue->ucStaticallyAllocated == ( uint8_t ) pdFALSE )
            {
                vPortFree( pxQueue );
            }
            else
            {
                mtCOVERAGE_TEST_MARKER();
            }
        }
    #else /* if ( ( configSUPPORT_DYNAMIC_ALLOCATION == 1 ) && ( configSUPPORT_STATIC_ALLOCATION == 0 ) ) */
        {
            /* The queue must have been statically allocated, so is not going to be
             * deleted.  Avoid compiler warnings about the unused parameter. */
            ( void ) pxQueue;
        }
    #endif /* configSUPPORT_DYNAMIC_ALLOCATION */
}
