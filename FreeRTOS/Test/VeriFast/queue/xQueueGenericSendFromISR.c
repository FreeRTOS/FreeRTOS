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
#include "proof/queuecontracts.h"

BaseType_t xQueueGenericSendFromISR( QueueHandle_t xQueue,
                                     const void * const pvItemToQueue,
                                     BaseType_t * const pxHigherPriorityTaskWoken,
                                     const BaseType_t xCopyPosition )
/*@requires
    [1/2]queuehandle(xQueue, ?N, ?M, ?is_isr) &*& is_isr == true &*&
    chars(pvItemToQueue, M, ?x) &*&
    integer(pxHigherPriorityTaskWoken, _) &*&
    (xCopyPosition == queueSEND_TO_BACK || xCopyPosition == queueSEND_TO_FRONT || (xCopyPosition == queueOVERWRITE && N == 1));@*/
/*@ensures
    [1/2]queuehandle(xQueue, N, M, is_isr) &*&
    chars(pvItemToQueue, M, x) &*&
    integer(pxHigherPriorityTaskWoken, _);@*/
{
    BaseType_t xReturn;
    UBaseType_t uxSavedInterruptStatus;

#ifdef VERIFAST /*< const pointer declaration */
    Queue_t * pxQueue = xQueue;
#else
    Queue_t * const pxQueue = xQueue;

    configASSERT( pxQueue );
    configASSERT( !( ( pvItemToQueue == NULL ) && ( pxQueue->uxItemSize != ( UBaseType_t ) 0U ) ) );
    configASSERT( !( ( xCopyPosition == queueOVERWRITE ) && ( pxQueue->uxLength != 1 ) ) );
#endif

    /* RTOS ports that support interrupt nesting have the concept of a maximum
     * system call (or maximum API call) interrupt priority.  Interrupts that are
     * above the maximum system call priority are kept permanently enabled, even
     * when the RTOS kernel is in a critical section, but cannot make any calls to
     * FreeRTOS API functions.  If configASSERT() is defined in FreeRTOSConfig.h
     * then portASSERT_IF_INTERRUPT_PRIORITY_INVALID() will result in an assertion
     * failure if a FreeRTOS API function is called from an interrupt that has been
     * assigned a priority above the configured maximum system call priority.
     * Only FreeRTOS functions that end in FromISR can be called from interrupts
     * that have been assigned a priority at or (logically) below the maximum
     * system call interrupt priority.  FreeRTOS maintains a separate interrupt
     * safe API to ensure interrupt entry is as fast and as simple as possible.
     * More information (albeit Cortex-M specific) is provided on the following
     * link: https://www.FreeRTOS.org/RTOS-Cortex-M3-M4.html */
    portASSERT_IF_INTERRUPT_PRIORITY_INVALID();

    /* Similar to xQueueGenericSend, except without blocking if there is no room
     * in the queue.  Also don't directly wake a task that was blocked on a queue
     * read, instead return a flag to say whether a context switch is required or
     * not (i.e. has a task with a higher priority than us been woken by this
     * post). */
    uxSavedInterruptStatus = portSET_INTERRUPT_MASK_FROM_ISR();
    /*@assert queue(pxQueue, ?Storage, N, M, ?W, ?R, ?K, ?is_locked, ?abs);@*/
    {
        if( ( pxQueue->uxMessagesWaiting < pxQueue->uxLength ) || ( xCopyPosition == queueOVERWRITE ) )
        {
            const int8_t cTxLock = pxQueue->cTxLock;
            const UBaseType_t uxPreviousMessagesWaiting = pxQueue->uxMessagesWaiting;

            traceQUEUE_SEND_FROM_ISR( pxQueue );

            /* Semaphores use xQueueGiveFromISR(), so pxQueue will not be a
             *  semaphore or mutex.  That means prvCopyDataToQueue() cannot result
             *  in a task disinheriting a priority and prvCopyDataToQueue() can be
             *  called here even though the disinherit function does not check if
             *  the scheduler is suspended before accessing the ready lists. */
#ifdef VERIFAST /*< void cast of unused return value */
            /*@close queue(pxQueue, Storage, N, M, W, R, K, is_locked, abs);@*/
            prvCopyDataToQueue( pxQueue, pvItemToQueue, xCopyPosition );
#else
            ( void ) prvCopyDataToQueue( pxQueue, pvItemToQueue, xCopyPosition );
#endif
            /*@open queue(pxQueue, _, N, M, _, _, _, _, _);@*/

            /* The event list is not altered if the queue is locked.  This will
             * be done when the queue is unlocked later. */
            if( cTxLock == queueUNLOCKED )
            {
                /* VeriFast: we do not verify this configuration option */
                #if ( configUSE_QUEUE_SETS == 1 )
                    {
                        if( pxQueue->pxQueueSetContainer != NULL )
                        {
                            if( ( xCopyPosition == queueOVERWRITE ) && ( uxPreviousMessagesWaiting != ( UBaseType_t ) 0 ) )
                            {
                                /* Do not notify the queue set as an existing item
                                 * was overwritten in the queue so the number of items
                                 * in the queue has not changed. */
                                mtCOVERAGE_TEST_MARKER();
                            }
                            else if( prvNotifyQueueSetContainer( pxQueue ) != pdFALSE )
                            {
                                /* The queue is a member of a queue set, and posting
                                 * to the queue set caused a higher priority task to
                                 * unblock.  A context switch is required. */
                                if( pxHigherPriorityTaskWoken != NULL )
                                {
                                    *pxHigherPriorityTaskWoken = pdTRUE;
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
                            if( listLIST_IS_EMPTY( &( pxQueue->xTasksWaitingToReceive ) ) == pdFALSE )
                            {
                                if( xTaskRemoveFromEventList( &( pxQueue->xTasksWaitingToReceive ) ) != pdFALSE )
                                {
                                    /* The task waiting has a higher priority so
                                     *  record that a context switch is required. */
                                    if( pxHigherPriorityTaskWoken != NULL )
                                    {
                                        *pxHigherPriorityTaskWoken = pdTRUE;
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
                                mtCOVERAGE_TEST_MARKER();
                            }
                        }
                    }
                #else /* configUSE_QUEUE_SETS */
                    {
                        if( listLIST_IS_EMPTY( &( pxQueue->xTasksWaitingToReceive ) ) == pdFALSE )
                        {
                            if( xTaskRemoveFromEventList( &( pxQueue->xTasksWaitingToReceive ) ) != pdFALSE )
                            {
                                /* The task waiting has a higher priority so record that a
                                 * context switch is required. */
                                if( pxHigherPriorityTaskWoken != NULL )
                                {
                                    *pxHigherPriorityTaskWoken = pdTRUE;
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
                            mtCOVERAGE_TEST_MARKER();
                        }

                        /* Not used in this path. */
#ifndef VERIFAST /*< void cast of unused var */
                        ( void ) uxPreviousMessagesWaiting;
#endif
                    }
                #endif /* configUSE_QUEUE_SETS */
            }
            else
            {
                /* Increment the lock count so the task that unlocks the queue
                 * knows that data was posted while it was locked. */
                configASSERT( cTxLock != queueINT8_MAX );

                pxQueue->cTxLock = ( int8_t ) ( cTxLock + 1 );
            }

            xReturn = pdPASS;
            /*@
            if (xCopyPosition == queueSEND_TO_BACK)
            {
                close queue(pxQueue, Storage, N, M, (W+1)%N, R, (K+1), is_locked, append(abs, singleton(x)));
            }
            else if (xCopyPosition == queueSEND_TO_FRONT)
            {
                if (R == 0)
                {
                    close queue(pxQueue, Storage, N, M, W, (N-1), (K+1), is_locked, cons(x, abs));
                }
                else
                {
                    close queue(pxQueue, Storage, N, M, W, (R-1), (K+1), is_locked, cons(x, abs));
                }
            } else if (xCopyPosition == queueOVERWRITE)
            {
                close queue(pxQueue, Storage, N, M, W, R, 1, is_locked, singleton(x));
            }
            @*/
        }
        else
        {
            traceQUEUE_SEND_FROM_ISR_FAILED( pxQueue );
            xReturn = errQUEUE_FULL;
            /*@close queue(pxQueue, Storage, N, M, W, R, K, is_locked, abs);@*/
        }
    }
    portCLEAR_INTERRUPT_MASK_FROM_ISR( uxSavedInterruptStatus );

    return xReturn;
}
