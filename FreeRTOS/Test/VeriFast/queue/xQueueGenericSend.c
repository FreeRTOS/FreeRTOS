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
#include "proof/queuecontracts.h"

BaseType_t xQueueGenericSend( QueueHandle_t xQueue,
                              const void * const pvItemToQueue,
                              TickType_t xTicksToWait,
                              const BaseType_t xCopyPosition )

/*@requires [1/2]queuehandle(xQueue, ?N, ?M, ?is_isr) &*& is_isr == false &*&
 *  [1/2]queuesuspend(xQueue) &*&
 *  chars(pvItemToQueue, M, ?x) &*&
 *  (xCopyPosition == queueSEND_TO_BACK || xCopyPosition == queueSEND_TO_FRONT || (xCopyPosition == queueOVERWRITE && N == 1));@*/

/*@ensures [1/2]queuehandle(xQueue, N, M, is_isr) &*&
 *  [1/2]queuesuspend(xQueue) &*&
 *  chars(pvItemToQueue, M, x);@*/
{
    BaseType_t xEntryTimeSet = pdFALSE, xYieldRequired;
    TimeOut_t xTimeOut;

    #ifdef VERIFAST /*< const pointer declaration */
        Queue_t * pxQueue = xQueue;
    #else
        Queue_t * const pxQueue = xQueue;

        configASSERT( pxQueue );
        configASSERT( !( ( pvItemToQueue == NULL ) && ( pxQueue->uxItemSize != ( UBaseType_t ) 0U ) ) );
        configASSERT( !( ( xCopyPosition == queueOVERWRITE ) && ( pxQueue->uxLength != 1 ) ) );
        #if ( ( INCLUDE_xTaskGetSchedulerState == 1 ) || ( configUSE_TIMERS == 1 ) )
            {
                configASSERT( !( ( xTaskGetSchedulerState() == taskSCHEDULER_SUSPENDED ) && ( xTicksToWait != 0 ) ) );
            }
        #endif
    #endif /* ifdef VERIFAST */

    /*lint -save -e904 This function relaxes the coding standard somewhat to
     * allow return statements within the function itself.  This is done in the
     * interest of execution time efficiency. */
    for( ; ; )

    /*@invariant [1/2]queuehandle(xQueue, N, M, is_isr) &*&
     *  [1/2]queuesuspend(xQueue) &*&
     *  chars(pvItemToQueue, M, x) &*&
     *  u_integer(&xTicksToWait, _) &*&
     *  (xCopyPosition == queueSEND_TO_BACK || xCopyPosition == queueSEND_TO_FRONT || (xCopyPosition == queueOVERWRITE && N == 1)) &*&
     *  xTIME_OUT(&xTimeOut);@*/
    {
        taskENTER_CRITICAL();
        {
            /*@assert queue(pxQueue, ?Storage, N, M, ?W, ?R, ?K, ?is_locked, ?abs);@*/

            /* Is there room on the queue now?  The running task must be the
             * highest priority task wanting to access the queue.  If the head item
             * in the queue is to be overwritten then it does not matter if the
             * queue is full. */
            if( ( pxQueue->uxMessagesWaiting < pxQueue->uxLength ) || ( xCopyPosition == queueOVERWRITE ) )
            {
                traceQUEUE_SEND( pxQueue );

                /* VeriFast: we do not verify this configuration option */
                #if ( configUSE_QUEUE_SETS == 1 )
                    {
                        const UBaseType_t uxPreviousMessagesWaiting = pxQueue->uxMessagesWaiting;

                        xYieldRequired = prvCopyDataToQueue( pxQueue, pvItemToQueue, xCopyPosition );

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
                                 * unblock. A context switch is required. */
                                queueYIELD_IF_USING_PREEMPTION();
                            }
                            else
                            {
                                mtCOVERAGE_TEST_MARKER();
                            }
                        }
                        else
                        {
                            /* If there was a task waiting for data to arrive on the
                             * queue then unblock it now. */
                            if( listLIST_IS_EMPTY( &( pxQueue->xTasksWaitingToReceive ) ) == pdFALSE )
                            {
                                if( xTaskRemoveFromEventList( &( pxQueue->xTasksWaitingToReceive ) ) != pdFALSE )
                                {
                                    /* The unblocked task has a priority higher than
                                     * our own so yield immediately.  Yes it is ok to
                                     * do this from within the critical section - the
                                     * kernel takes care of that. */
                                    queueYIELD_IF_USING_PREEMPTION();
                                }
                                else
                                {
                                    mtCOVERAGE_TEST_MARKER();
                                }
                            }
                            else if( xYieldRequired != pdFALSE )
                            {
                                /* This path is a special case that will only get
                                 * executed if the task was holding multiple mutexes
                                 * and the mutexes were given back in an order that is
                                 * different to that in which they were taken. */
                                queueYIELD_IF_USING_PREEMPTION();
                            }
                            else
                            {
                                mtCOVERAGE_TEST_MARKER();
                            }
                        }
                    }
                #else /* configUSE_QUEUE_SETS */
                    {
                        /*@close queue(pxQueue, Storage, N, M, W, R, K, is_locked, abs);@*/
                        xYieldRequired = prvCopyDataToQueue( pxQueue, pvItemToQueue, xCopyPosition );

                        /* If there was a task waiting for data to arrive on the
                         * queue then unblock it now. */
                        if( listLIST_IS_EMPTY( &( pxQueue->xTasksWaitingToReceive ) ) == pdFALSE )
                        {
                            if( xTaskRemoveFromEventList( &( pxQueue->xTasksWaitingToReceive ) ) != pdFALSE )
                            {
                                /* The unblocked task has a priority higher than
                                 * our own so yield immediately.  Yes it is ok to do
                                 * this from within the critical section - the kernel
                                 * takes care of that. */
                                queueYIELD_IF_USING_PREEMPTION();
                            }
                            else
                            {
                                mtCOVERAGE_TEST_MARKER();
                            }
                        }
                        else if( xYieldRequired != pdFALSE )
                        {
                            /* This path is a special case that will only get
                             * executed if the task was holding multiple mutexes and
                             * the mutexes were given back in an order that is
                             * different to that in which they were taken. */
                            queueYIELD_IF_USING_PREEMPTION();
                        }
                        else
                        {
                            mtCOVERAGE_TEST_MARKER();
                        }
                    }
                #endif /* configUSE_QUEUE_SETS */

                /*@
                 * if (xCopyPosition == queueSEND_TO_BACK)
                 * {
                 *  close queue(pxQueue, Storage, N, M, (W+1)%N, R, (K+1), is_locked, append(abs, singleton(x)));
                 * }
                 * else if (xCopyPosition == queueSEND_TO_FRONT)
                 * {
                 *  close queue(pxQueue, Storage, N, M, W, (R == 0 ? (N-1) : (R-1)), (K+1), is_locked, cons(x, abs));
                 * }
                 * else if (xCopyPosition == queueOVERWRITE)
                 * {
                 *  close queue(pxQueue, Storage, N, M, W, R, 1, is_locked, singleton(x));
                 * }
                 * @*/
                taskEXIT_CRITICAL();
                return pdPASS;
            }
            else
            {
                if( xTicksToWait == ( TickType_t ) 0 )
                {
                    /*@close queue(pxQueue, Storage, N, M, W, R, K, is_locked, abs);@*/

                    /* The queue was full and no block time is specified (or
                     * the block time has expired) so leave now. */
                    taskEXIT_CRITICAL();

                    /* Return to the original privilege level before exiting
                     * the function. */
                    traceQUEUE_SEND_FAILED( pxQueue );
                    return errQUEUE_FULL;
                }
                else if( xEntryTimeSet == pdFALSE )
                {
                    /* The queue was full and a block time was specified so
                     * configure the timeout structure. */
                    vTaskInternalSetTimeOutState( &xTimeOut );
                    xEntryTimeSet = pdTRUE;
                }
                else
                {
                    /* Entry time was already set. */
                    mtCOVERAGE_TEST_MARKER();
                }
            }

            /*@close queue(pxQueue, Storage, N, M, W, R, K, is_locked, abs);@*/
        }
        taskEXIT_CRITICAL();

        /* Interrupts and other tasks can send to and receive from the queue
         * now the critical section has been exited. */

        /*@close exists(pxQueue);@*/
        vTaskSuspendAll();
        prvLockQueue( pxQueue );

        /* Update the timeout state to see if it has expired yet. */
        if( xTaskCheckForTimeOut( &xTimeOut, &xTicksToWait ) == pdFALSE )
        {
            if( prvIsQueueFull( pxQueue ) != pdFALSE )
            {
                traceBLOCKING_ON_QUEUE_SEND( pxQueue );
                /*@open queue_locked_invariant(xQueue)();@*/
                vTaskPlaceOnEventList( &( pxQueue->xTasksWaitingToSend ), xTicksToWait );

                /* Unlocking the queue means queue events can effect the
                 * event list.  It is possible that interrupts occurring now
                 * remove this task from the event list again - but as the
                 * scheduler is suspended the task will go onto the pending
                 * ready last instead of the actual ready list. */
                /*@close queue_locked_invariant(xQueue)();@*/
                prvUnlockQueue( pxQueue );

                /* Resuming the scheduler will move tasks from the pending
                 * ready list into the ready list - so it is feasible that this
                 * task is already in a ready list before it yields - in which
                 * case the yield will not cause a context switch unless there
                 * is also a higher priority task in the pending ready list. */
                /*@close exists(pxQueue);@*/
                if( xTaskResumeAll() == pdFALSE )
                {
                    portYIELD_WITHIN_API();
                }
            }
            else
            {
                /* Try again. */
                prvUnlockQueue( pxQueue );
                #ifdef VERIFAST /*< void cast of unused return value */
                    /*@close exists(pxQueue);@*/
                    xTaskResumeAll();
                #else
                    ( void ) xTaskResumeAll();
                #endif
            }
        }
        else
        {
            /* The timeout has expired. */
            prvUnlockQueue( pxQueue );
            #ifdef VERIFAST /*< void cast of unused return value */
                /*@close exists(pxQueue);@*/
                xTaskResumeAll();
            #else
                ( void ) xTaskResumeAll();
            #endif

            traceQUEUE_SEND_FAILED( pxQueue );
            return errQUEUE_FULL;
        }
    } /*lint -restore */
}
