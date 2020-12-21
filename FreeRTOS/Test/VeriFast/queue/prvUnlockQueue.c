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
#define taskENTER_CRITICAL()    setInterruptMask( pxQueue )
#define taskEXIT_CRITICAL()     clearInterruptMask( pxQueue )

/* VeriFast: we make one major change. We merge the critical regions for
 * decrementing `cTxLock` and `cRxLock`. */

static void prvUnlockQueue( Queue_t * const pxQueue )
/*@requires [1/2]queuehandle(pxQueue, ?N, ?M, ?is_isr) &*& is_isr == false &*&
    [1/2]pxQueue->locked |-> ?m &*&
    mutex_held(m, queue_locked_invariant(pxQueue), currentThread, 1/2) &*&
    queue_locked_invariant(pxQueue)();@*/
/*@ensures [1/2]queuehandle(pxQueue, N, M, is_isr) &*&
    [1/2]queuelock(pxQueue);@*/
{
    /* THIS FUNCTION MUST BE CALLED WITH THE SCHEDULER SUSPENDED. */

    /* The lock counts contains the number of extra data items placed or
     * removed from the queue while the queue was locked.  When a queue is
     * locked items can be added or removed, but the event lists cannot be
     * updated. */
    taskENTER_CRITICAL();
    /*@open queue(pxQueue, ?Storage, N, M, ?W, ?R, ?K, _, ?abs);@*/
    {
        int8_t cTxLock = pxQueue->cTxLock;

        /* See if data was added to the queue while it was locked. */
        while( cTxLock > queueLOCKED_UNMODIFIED )
        /*@invariant queuelists(pxQueue);@*/
        {
            /* Data was posted while the queue was locked.  Are any tasks
             * blocked waiting for data to become available? */
            #if ( configUSE_QUEUE_SETS == 1 )
                {
                    if( pxQueue->pxQueueSetContainer != NULL )
                    {
                        if( prvNotifyQueueSetContainer( pxQueue ) != pdFALSE )
                        {
                            /* The queue is a member of a queue set, and posting to
                             * the queue set caused a higher priority task to unblock.
                             * A context switch is required. */
                            vTaskMissedYield();
                        }
                        else
                        {
                            mtCOVERAGE_TEST_MARKER();
                        }
                    }
                    else
                    {
                        /* Tasks that are removed from the event list will get
                         * added to the pending ready list as the scheduler is still
                         * suspended. */
                        if( listLIST_IS_EMPTY( &( pxQueue->xTasksWaitingToReceive ) ) == pdFALSE )
                        {
                            if( xTaskRemoveFromEventList( &( pxQueue->xTasksWaitingToReceive ) ) != pdFALSE )
                            {
                                /* The task waiting has a higher priority so record that a
                                 * context switch is required. */
                                vTaskMissedYield();
                            }
                            else
                            {
                                mtCOVERAGE_TEST_MARKER();
                            }
                        }
                        else
                        {
                            break;
                        }
                    }
                }
            #else /* configUSE_QUEUE_SETS */
                {
                    /* Tasks that are removed from the event list will get added to
                     * the pending ready list as the scheduler is still suspended. */
                    if( listLIST_IS_EMPTY( &( pxQueue->xTasksWaitingToReceive ) ) == pdFALSE )
                    {
                        if( xTaskRemoveFromEventList( &( pxQueue->xTasksWaitingToReceive ) ) != pdFALSE )
                        {
                            /* The task waiting has a higher priority so record that
                             * a context switch is required. */
                            vTaskMissedYield();
                        }
                        else
                        {
                            mtCOVERAGE_TEST_MARKER();
                        }
                    }
                    else
                    {
                        break;
                    }
                }
            #endif /* configUSE_QUEUE_SETS */

            --cTxLock;
        }

        pxQueue->cTxLock = queueUNLOCKED;
    }
#ifndef VERIFAST /*< ***merge cTxLock and cRxLock critical regions*** */
    taskEXIT_CRITICAL();

    /* Do the same for the Rx lock. */
    taskENTER_CRITICAL();
#endif
    {
        int8_t cRxLock = pxQueue->cRxLock;

        while( cRxLock > queueLOCKED_UNMODIFIED )
        /*@invariant queuelists(pxQueue);@*/
        {
            if( listLIST_IS_EMPTY( &( pxQueue->xTasksWaitingToSend ) ) == pdFALSE )
            {
                if( xTaskRemoveFromEventList( &( pxQueue->xTasksWaitingToSend ) ) != pdFALSE )
                {
                    vTaskMissedYield();
                }
                else
                {
                    mtCOVERAGE_TEST_MARKER();
                }

                --cRxLock;
            }
            else
            {
                break;
            }
        }

        pxQueue->cRxLock = queueUNLOCKED;
    }
    /*@close queue(pxQueue, Storage, N, M, W, R, K, false, abs);@*/
    taskEXIT_CRITICAL();
#ifdef VERIFAST /*< ghost action */
    mutex_release( pxQueue->locked );
#endif
}
