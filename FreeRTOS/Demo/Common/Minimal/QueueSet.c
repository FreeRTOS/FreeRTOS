/*
 * FreeRTOS V202112.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

/*
 * Tests the use of queue sets.
 *
 * A receive task creates a number of queues and adds them to a queue set before
 * blocking on the queue set receive.  A transmit task and (optionally) an
 * interrupt repeatedly unblocks the receive task by sending messages to the
 * queues in a pseudo random order.  The receive task removes the messages from
 * the queues and flags an error if the received message does not match that
 * expected.  The task sends values in the range 0 to
 * queuesetINITIAL_ISR_TX_VALUE, and the ISR sends value in the range
 * queuesetINITIAL_ISR_TX_VALUE to ULONG_MAX.
 */


/* Standard includes. */
#include <stdlib.h>
#include <limits.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/* Demo includes. */
#include "QueueSet.h"


#if ( configUSE_QUEUE_SETS == 1 ) /* Remove the tests if queue sets are not defined. */


/* The number of queues that are created and added to the queue set. */
    #define queuesetNUM_QUEUES_IN_SET         3

/* The length of each created queue. */
    #define queuesetQUEUE_LENGTH              3

/* Block times used in this demo.  A block time or 0 means "don't block". */
    #define queuesetSHORT_DELAY               200
    #define queuesetDONT_BLOCK                0

/* Messages are sent in incrementing order from both a task and an interrupt.
 * The task sends values in the range 0 to 0xfffe, and the interrupt sends values
 * in the range of 0xffff to ULONG_MAX. */
    #define queuesetINITIAL_ISR_TX_VALUE      0xffffUL

/* The priorities used in this demo. */
    #define queuesetLOW_PRIORITY              ( tskIDLE_PRIORITY )
    #define queuesetMEDIUM_PRIORITY           ( queuesetLOW_PRIORITY + 1 )

/* For test purposes the priority of the sending task is changed after every
 * queuesetPRIORITY_CHANGE_LOOPS number of values are sent to a queue. */
    #define queuesetPRIORITY_CHANGE_LOOPS     ( ( queuesetNUM_QUEUES_IN_SET * queuesetQUEUE_LENGTH ) * 2 )

/* The ISR sends to the queue every queuesetISR_TX_PERIOD ticks. */
    #define queuesetISR_TX_PERIOD             ( 100UL )

/* A delay inserted when the Tx task changes its priority to be above the idle
 * task priority to ensure the idle priority tasks get some CPU time before the
 * next iteration of the queue set Tx task. */
    #define queuesetTX_LOOP_DELAY             pdMS_TO_TICKS( ( TickType_t ) 200 )

/* The allowable maximum deviation between a received value and the expected
 * received value.  A deviation will occur when data is received from a queue
 * inside an ISR in between a task receiving from a queue and the task checking
 * the received value. */
    #define queuesetALLOWABLE_RX_DEVIATION    3

/* Ignore values that are at the boundaries of allowable values to make the
 * testing of limits easier (don't have to deal with wrapping values). */
    #define queuesetIGNORED_BOUNDARY          ( queuesetALLOWABLE_RX_DEVIATION * 2 )

    typedef enum
    {
        eEqualPriority = 0, /* Tx and Rx tasks have the same priority. */
        eTxHigherPriority,  /* The priority of the Tx task is above that of the Rx task. */
        eTxLowerPriority    /* The priority of the Tx task is below that of the Rx task. */
    } eRelativePriorities;

/*
 * The task that periodically sends to the queue set.
 */
    static void prvQueueSetSendingTask( void * pvParameters );

/*
 * The task that reads from the queue set.
 */
    static void prvQueueSetReceivingTask( void * pvParameters );

/*
 * Check the value received from a queue is the expected value.  Some values
 * originate from the send task, some values originate from the ISR, with the
 * range of the value being used to distinguish between the two message
 * sources.
 */
    static void prvCheckReceivedValue( uint32_t ulReceived );

/*
 * For purposes of test coverage, functions that read from and write to a
 * queue set from an ISR respectively.
 */
    static void prvReceiveFromQueueInSetFromISR( void );
    static void prvSendToQueueInSetFromISR( void );

/*
 * Create the queues and add them to a queue set before resuming the Tx
 * task.
 */
    static void prvSetupTest( void );

/*
 * Checks a value received from a queue falls within the range of expected
 * values.
 */
    static BaseType_t prvCheckReceivedValueWithinExpectedRange( uint32_t ulReceived,
                                                                uint32_t ulExpectedReceived );

/*
 * Increase test coverage by occasionally change the priorities of the two tasks
 * relative to each other.
 */
    static void prvChangeRelativePriorities( void );

/*
 * Queue overwrites can only be performed on queues of length of one, requiring
 * a special test function so a queue of length 1 can temporarily be added to a
 * set.
 */
    static void prvTestQueueOverwriteWithQueueSet( void );

/*
 * Test the case where two queues within a set are written to with
 * xQueueOverwrite().
 */
    static void prvTestQueueOverwriteOnTwoQueusInQueueSet( void );
    static void prvTestQueueOverwriteFromISROnTwoQueusInQueueSet( void );

/*
 * Local pseudo random number seed and return functions.  Used to avoid calls
 * to the standard library.
 */
    static size_t prvRand( void );
    static void prvSRand( size_t uxSeed );

/*-----------------------------------------------------------*/

/* The queues that are added to the set. */
    static QueueHandle_t xQueues[ queuesetNUM_QUEUES_IN_SET ] = { 0 };

/* Counts how many times each queue in the set is used to ensure all the
 * queues are used. */
    static uint32_t ulQueueUsedCounter[ queuesetNUM_QUEUES_IN_SET ] = { 0 };

/* The handle of the queue set to which the queues are added. */
    static QueueSetHandle_t xQueueSet;

/* If the prvQueueSetReceivingTask() task has not detected any errors then
 * it increments ulCycleCounter on each iteration.
 * xAreQueueSetTasksStillRunning() returns pdPASS if the value of
 * ulCycleCounter has changed between consecutive calls, and pdFALSE if
 * ulCycleCounter has stopped incrementing (indicating an error condition). */
    static volatile uint32_t ulCycleCounter = 0UL;

/* Set to pdFAIL if an error is detected by any queue set task.
 * ulCycleCounter will only be incremented if xQueueSetTasksSatus equals pdPASS. */
    static volatile BaseType_t xQueueSetTasksStatus = pdPASS;

/* Just a flag to let the function that writes to a queue from an ISR know that
 * the queues are setup and can be used. */
    static volatile BaseType_t xSetupComplete = pdFALSE;

/* The value sent to the queue from the ISR is file scope so the
 * xAreQueeuSetTasksStillRunning() function can check it is incrementing as
 * expected. */
    static volatile uint32_t ulISRTxValue = queuesetINITIAL_ISR_TX_VALUE;

/* Used by the pseudo random number generator. */
    static size_t uxNextRand = 0;

/* The task handles are stored so their priorities can be changed. */
    TaskHandle_t xQueueSetSendingTask, xQueueSetReceivingTask;

/*-----------------------------------------------------------*/

    void vStartQueueSetTasks( void )
    {
        /* Create the tasks. */
        xTaskCreate( prvQueueSetSendingTask, "SetTx", configMINIMAL_STACK_SIZE, NULL, queuesetMEDIUM_PRIORITY, &xQueueSetSendingTask );

        if( xQueueSetSendingTask != NULL )
        {
            xTaskCreate( prvQueueSetReceivingTask, "SetRx", configMINIMAL_STACK_SIZE, ( void * ) xQueueSetSendingTask, queuesetMEDIUM_PRIORITY, &xQueueSetReceivingTask );

            /* It is important that the sending task does not attempt to write to a
             * queue before the queue has been created.  It is therefore placed into
             * the suspended state before the scheduler has started.  It is resumed by
             * the receiving task after the receiving task has created the queues and
             * added the queues to the queue set. */
            vTaskSuspend( xQueueSetSendingTask );
        }
    }
/*-----------------------------------------------------------*/

    BaseType_t xAreQueueSetTasksStillRunning( void )
    {
        static uint32_t ulLastCycleCounter, ulLastISRTxValue = 0;
        static uint32_t ulLastQueueUsedCounter[ queuesetNUM_QUEUES_IN_SET ] = { 0 };
        BaseType_t xReturn = pdPASS, x;

        if( ulLastCycleCounter == ulCycleCounter )
        {
            /* The cycle counter is no longer being incremented.  Either one of the
             * tasks is stalled or an error has been detected. */
            xReturn = pdFAIL;
        }

        ulLastCycleCounter = ulCycleCounter;

        /* Ensure that all the queues in the set have been used.  This ensures the
         * test is working as intended and guards against the rand() in the Tx task
         * missing some values. */
        for( x = 0; x < queuesetNUM_QUEUES_IN_SET; x++ )
        {
            if( ulLastQueueUsedCounter[ x ] == ulQueueUsedCounter[ x ] )
            {
                xReturn = pdFAIL;
            }

            ulLastQueueUsedCounter[ x ] = ulQueueUsedCounter[ x ];
        }

        /* Check the global status flag. */
        if( xQueueSetTasksStatus != pdPASS )
        {
            xReturn = pdFAIL;
        }

        /* Check that the ISR is still sending values to the queues too. */
        if( ulISRTxValue == ulLastISRTxValue )
        {
            xReturn = pdFAIL;
        }
        else
        {
            ulLastISRTxValue = ulISRTxValue;
        }

        return xReturn;
    }
/*-----------------------------------------------------------*/

    static void prvQueueSetSendingTask( void * pvParameters )
    {
        uint32_t ulTaskTxValue = 0;
        size_t uxQueueToWriteTo;
        QueueHandle_t xQueueInUse;

        /* Remove compiler warning about the unused parameter. */
        ( void ) pvParameters;

        /* Seed mini pseudo random number generator. */
        prvSRand( ( size_t ) &ulTaskTxValue );

        for( ; ; )
        {
            /* Generate the index for the queue to which a value is to be sent. */
            uxQueueToWriteTo = prvRand() % queuesetNUM_QUEUES_IN_SET;
            xQueueInUse = xQueues[ uxQueueToWriteTo ];

            /* Note which index is being written to to ensure all the queues are
             * used. */
            ( ulQueueUsedCounter[ uxQueueToWriteTo ] )++;

            /* Send to the queue to unblock the task that is waiting for data to
             * arrive on a queue within the queue set to which this queue belongs. */
            if( xQueueSendToBack( xQueueInUse, &ulTaskTxValue, portMAX_DELAY ) != pdPASS )
            {
                /* The send should always pass as an infinite block time was
                 * used. */
                xQueueSetTasksStatus = pdFAIL;
            }

            #if ( configUSE_PREEMPTION == 0 )
                taskYIELD();
            #endif

            ulTaskTxValue++;

            /* If the Tx value has reached the range used by the ISR then set it
             * back to 0. */
            if( ulTaskTxValue == queuesetINITIAL_ISR_TX_VALUE )
            {
                ulTaskTxValue = 0;
            }

            /* Increase test coverage by occasionally change the priorities of the
             * two tasks relative to each other. */
            prvChangeRelativePriorities();
        }
    }
/*-----------------------------------------------------------*/

    static void prvChangeRelativePriorities( void )
    {
        static UBaseType_t ulLoops = 0;
        static eRelativePriorities ePriorities = eEqualPriority;

        /* Occasionally change the task priority relative to the priority of
         * the receiving task. */
        ulLoops++;

        if( ulLoops >= queuesetPRIORITY_CHANGE_LOOPS )
        {
            ulLoops = 0;

            switch( ePriorities )
            {
                case eEqualPriority:

                    /* Both tasks are running with medium priority.  Now lower the
                     * priority of the receiving task so the Tx task has the higher
                     * relative priority. */
                    vTaskPrioritySet( xQueueSetReceivingTask, queuesetLOW_PRIORITY );
                    ePriorities = eTxHigherPriority;
                    break;

                case eTxHigherPriority:

                    /* The Tx task is running with a higher priority than the Rx
                     * task.  Switch the priorities around so the Rx task has the
                     * higher relative priority. */
                    vTaskPrioritySet( xQueueSetReceivingTask, queuesetMEDIUM_PRIORITY );
                    vTaskPrioritySet( xQueueSetSendingTask, queuesetLOW_PRIORITY );
                    ePriorities = eTxLowerPriority;
                    break;

                case eTxLowerPriority:

                    /* The Tx task is running with a lower priority than the Rx
                     * task.  Make the priorities equal again. */
                    vTaskPrioritySet( xQueueSetSendingTask, queuesetMEDIUM_PRIORITY );
                    ePriorities = eEqualPriority;

                    /* When both tasks are using a non-idle priority the queue set
                     * tasks will starve idle priority tasks of execution time - so
                     * relax a bit before the next iteration to minimise the impact. */
                    vTaskDelay( queuesetTX_LOOP_DELAY );

                    break;
            }
        }
    }
/*-----------------------------------------------------------*/

    static void prvQueueSetReceivingTask( void * pvParameters )
    {
        uint32_t ulReceived;
        QueueHandle_t xActivatedQueue;
        TickType_t xBlockTime;

        /* Remove compiler warnings. */
        ( void ) pvParameters;

        /* Create the queues and add them to the queue set before resuming the Tx
         * task. */
        prvSetupTest();

        for( ; ; )
        {
            /* For test coverage reasons, the block time is dependent on the
             * priority of this task - which changes during the test.  When the task
             * is at the idle priority it polls the queue set. */
            if( uxTaskPriorityGet( NULL ) == tskIDLE_PRIORITY )
            {
                xBlockTime = 0;
            }
            else
            {
                xBlockTime = portMAX_DELAY;
            }

            /* Wait for a message to arrive on one of the queues in the set. */
            xActivatedQueue = xQueueSelectFromSet( xQueueSet, portMAX_DELAY );

            if( xActivatedQueue == NULL )
            {
                if( xBlockTime != 0 )
                {
                    /* This should not happen as an infinite delay was used. */
                    xQueueSetTasksStatus = pdFAIL;
                }
            }
            else
            {
                /* Reading from the queue should pass with a zero block time as
                 * this task will only run when something has been posted to a task
                 * in the queue set. */
                if( xQueueReceive( xActivatedQueue, &ulReceived, queuesetDONT_BLOCK ) != pdPASS )
                {
                    xQueueSetTasksStatus = pdFAIL;
                }

                /* Ensure the value received was the value expected.  This function
                 * manipulates file scope data and is also called from an ISR, hence
                 * the critical section. */
                taskENTER_CRITICAL();
                {
                    prvCheckReceivedValue( ulReceived );
                }
                taskEXIT_CRITICAL();

                if( xQueueSetTasksStatus == pdPASS )
                {
                    ulCycleCounter++;
                }
            }
        }
    }
/*-----------------------------------------------------------*/

    void vQueueSetAccessQueueSetFromISR( void )
    {
        static uint32_t ulCallCount = 0;

        /* xSetupComplete is set to pdTRUE when the queues have been created and
         * are available for use. */
        if( xSetupComplete == pdTRUE )
        {
            /* It is intended that this function is called from the tick hook
             * function, so each call is one tick period apart. */
            ulCallCount++;

            if( ulCallCount > queuesetISR_TX_PERIOD )
            {
                ulCallCount = 0;

                /* First attempt to read from the queue set. */
                prvReceiveFromQueueInSetFromISR();

                /* Then write to the queue set. */
                prvSendToQueueInSetFromISR();
            }
        }
    }
/*-----------------------------------------------------------*/

    static void prvCheckReceivedValue( uint32_t ulReceived )
    {
        static uint32_t ulExpectedReceivedFromTask = 0, ulExpectedReceivedFromISR = queuesetINITIAL_ISR_TX_VALUE;

        /* Values are received in tasks and interrupts.  It is likely that the
         * receiving task will sometimes get preempted by the receiving interrupt
         * between reading a value from the queue and calling this function.  When
         * that happens, if the receiving interrupt calls this function the values
         * will get passed into this function slightly out of order.  For that
         * reason the value passed in is tested against a small range of expected
         * values, rather than a single absolute value.  To make the range testing
         * easier values in the range limits are ignored. */

        /* If the received value is equal to or greater than
         * queuesetINITIAL_ISR_TX_VALUE then it was sent by an ISR. */
        if( ulReceived >= queuesetINITIAL_ISR_TX_VALUE )
        {
            /* The value was sent from the ISR. */
            if( ( ulReceived - queuesetINITIAL_ISR_TX_VALUE ) < queuesetIGNORED_BOUNDARY )
            {
                /* The value received is at the lower limit of the expected range.
                 * Don't test it and expect to receive one higher next time. */
            }
            else if( ( ULONG_MAX - ulReceived ) <= queuesetIGNORED_BOUNDARY )
            {
                /* The value received is at the higher limit of the expected range.
                 * Don't test it and expect to wrap soon. */
            }
            else
            {
                /* Check the value against its expected value range. */
                if( prvCheckReceivedValueWithinExpectedRange( ulReceived, ulExpectedReceivedFromISR ) != pdPASS )
                {
                    xQueueSetTasksStatus = pdFAIL;
                }
            }

            configASSERT( xQueueSetTasksStatus );

            /* It is expected to receive an incrementing number. */
            ulExpectedReceivedFromISR++;

            if( ulExpectedReceivedFromISR == 0 )
            {
                ulExpectedReceivedFromISR = queuesetINITIAL_ISR_TX_VALUE;
            }
        }
        else
        {
            /* The value was sent from the Tx task. */
            if( ulReceived < queuesetIGNORED_BOUNDARY )
            {
                /* The value received is at the lower limit of the expected range.
                 * Don't test it, and expect to receive one higher next time. */
            }
            else if( ( ( queuesetINITIAL_ISR_TX_VALUE - 1 ) - ulReceived ) <= queuesetIGNORED_BOUNDARY )
            {
                /* The value received is at the higher limit of the expected range.
                 * Don't test it and expect to wrap soon. */
            }
            else
            {
                /* Check the value against its expected value range. */
                if( prvCheckReceivedValueWithinExpectedRange( ulReceived, ulExpectedReceivedFromTask ) != pdPASS )
                {
                    xQueueSetTasksStatus = pdFAIL;
                }
            }

            configASSERT( xQueueSetTasksStatus );

            /* It is expected to receive an incrementing number. */
            ulExpectedReceivedFromTask++;

            if( ulExpectedReceivedFromTask >= queuesetINITIAL_ISR_TX_VALUE )
            {
                ulExpectedReceivedFromTask = 0;
            }
        }
    }
/*-----------------------------------------------------------*/

    static BaseType_t prvCheckReceivedValueWithinExpectedRange( uint32_t ulReceived,
                                                                uint32_t ulExpectedReceived )
    {
        BaseType_t xReturn = pdPASS;

        if( ulReceived > ulExpectedReceived )
        {
            configASSERT( ( ulReceived - ulExpectedReceived ) <= queuesetALLOWABLE_RX_DEVIATION );

            if( ( ulReceived - ulExpectedReceived ) > queuesetALLOWABLE_RX_DEVIATION )
            {
                xReturn = pdFALSE;
            }
        }
        else
        {
            configASSERT( ( ulExpectedReceived - ulReceived ) <= queuesetALLOWABLE_RX_DEVIATION );

            if( ( ulExpectedReceived - ulReceived ) > queuesetALLOWABLE_RX_DEVIATION )
            {
                xReturn = pdFALSE;
            }
        }

        return xReturn;
    }
/*-----------------------------------------------------------*/

    static void prvReceiveFromQueueInSetFromISR( void )
    {
        QueueSetMemberHandle_t xActivatedQueue;
        uint32_t ulReceived;

        /* See if any of the queues in the set contain data. */
        xActivatedQueue = xQueueSelectFromSetFromISR( xQueueSet );

        if( xActivatedQueue != NULL )
        {
            /* Reading from the queue for test purposes only. */
            if( xQueueReceiveFromISR( xActivatedQueue, &ulReceived, NULL ) != pdPASS )
            {
                /* Data should have been available as the handle was returned from
                 * xQueueSelectFromSetFromISR(). */
                xQueueSetTasksStatus = pdFAIL;
            }

            /* Ensure the value received was the value expected. */
            prvCheckReceivedValue( ulReceived );
        }
    }
/*-----------------------------------------------------------*/

    static void prvSendToQueueInSetFromISR( void )
    {
        static BaseType_t xQueueToWriteTo = 0;
        uint32_t ulTxValueSnapshot = ulISRTxValue;

        if( xQueueSendFromISR( xQueues[ xQueueToWriteTo ], ( void * ) &ulTxValueSnapshot, NULL ) == pdPASS )
        {
            ulISRTxValue++;

            /* If the Tx value has wrapped then set it back to its initial value. */
            if( ulISRTxValue == 0UL )
            {
                ulISRTxValue = queuesetINITIAL_ISR_TX_VALUE;
            }

            /* Use a different queue next time. */
            xQueueToWriteTo++;

            if( xQueueToWriteTo >= queuesetNUM_QUEUES_IN_SET )
            {
                xQueueToWriteTo = 0;
            }
        }
    }
/*-----------------------------------------------------------*/

    static void prvTestQueueOverwriteWithQueueSet( void )
    {
        uint32_t ulValueToSend = 0, ulValueReceived = 0;
        QueueHandle_t xQueueHandle = NULL, xReceivedHandle = NULL;
        const UBaseType_t xLengthOfOne = ( UBaseType_t ) 1;

        /* Create a queue that has a length of one - a requirement in order to call
         * xQueueOverwrite.  This will get deleted again when this test completes. */
        xQueueHandle = xQueueCreate( xLengthOfOne, sizeof( uint32_t ) );
        configASSERT( xQueueHandle );

        if( xQueueHandle != NULL )
        {
            xQueueAddToSet( xQueueHandle, xQueueSet );

            /* Add an item to the queue then ensure the queue set correctly
             * indicates that one item is available, and that item is indeed the
             * queue written to. */
            xQueueOverwrite( xQueueHandle, ( void * ) &ulValueToSend );

            if( uxQueueMessagesWaiting( xQueueSet ) != ( UBaseType_t ) 1 )
            {
                /* Expected one item in the queue set. */
                xQueueSetTasksStatus = pdFAIL;
            }

            xQueuePeek( xQueueSet, &xReceivedHandle, queuesetDONT_BLOCK );

            if( xReceivedHandle != xQueueHandle )
            {
                /* Wrote to xQueueHandle so expected xQueueHandle to be the handle
                 * held in the queue set. */
                xQueueSetTasksStatus = pdFAIL;
            }

            /* Now overwrite the value in the queue and ensure the queue set state
             * doesn't change as the number of items in the queues within the set have
             * not changed. */
            ulValueToSend++;
            xQueueOverwrite( xQueueHandle, ( void * ) &ulValueToSend );

            if( uxQueueMessagesWaiting( xQueueSet ) != ( UBaseType_t ) 1 )
            {
                /* Still expected one item in the queue set. */
                xQueueSetTasksStatus = pdFAIL;
            }

            xReceivedHandle = xQueueSelectFromSet( xQueueSet, queuesetDONT_BLOCK );

            if( xReceivedHandle != xQueueHandle )
            {
                /* Wrote to xQueueHandle so expected xQueueHandle to be the handle
                 * held in the queue set. */
                xQueueSetTasksStatus = pdFAIL;
            }

            /* Also ensure the value received from the queue is the overwritten
             * value, not the value originally written. */
            xQueueReceive( xQueueHandle, &ulValueReceived, queuesetDONT_BLOCK );

            if( ulValueReceived != ulValueToSend )
            {
                /* Unexpected value received from the queue. */
                xQueueSetTasksStatus = pdFAIL;
            }

            /* Should be anything in the queue set now. */
            if( uxQueueMessagesWaiting( xQueueSet ) != ( UBaseType_t ) 0 )
            {
                xQueueSetTasksStatus = pdFAIL;
            }

            xReceivedHandle = xQueueSelectFromSet( xQueueSet, queuesetDONT_BLOCK );

            if( xReceivedHandle != NULL )
            {
                xQueueSetTasksStatus = pdFAIL;
            }

            /* Clean up. */
            xQueueRemoveFromSet( xQueueHandle, xQueueSet );
            vQueueDelete( xQueueHandle );
        }
    }
/*-----------------------------------------------------------*/

    static void prvTestQueueOverwriteOnTwoQueusInQueueSet( void )
    {
        uint32_t ulValueToSend1 = 1, ulValueToSend2 = 2UL, ulValueReceived = 0;
        QueueHandle_t xQueueHandle1 = NULL, xQueueHandle2 = NULL, xReceivedHandle = NULL;
        const UBaseType_t xLengthOfOne = ( UBaseType_t ) 1;

        /* Create two queues that have a length of one - a requirement in order to call
         * xQueueOverwrite.  These will get deleted again when this test completes. */
        xQueueHandle1 = xQueueCreate( xLengthOfOne, sizeof( uint32_t ) );
        configASSERT( xQueueHandle1 );
        xQueueHandle2 = xQueueCreate( xLengthOfOne, sizeof( uint32_t ) );
        configASSERT( xQueueHandle2 );

        if( ( xQueueHandle1 != NULL ) && ( xQueueHandle2 != NULL ) )
        {
            /* Add both queues to the queue set. */
            xQueueAddToSet( xQueueHandle1, xQueueSet );
            xQueueAddToSet( xQueueHandle2, xQueueSet );

            /* Add an item using the first queue. */
            xQueueOverwrite( xQueueHandle1, ( void * ) &ulValueToSend1 );

            if( uxQueueMessagesWaiting( xQueueSet ) != ( UBaseType_t ) 1 )
            {
                /* Expected one item in the queue set. */
                xQueueSetTasksStatus = pdFAIL;
            }

            xQueuePeek( xQueueSet, &xReceivedHandle, queuesetDONT_BLOCK );

            if( xReceivedHandle != xQueueHandle1 )
            {
                /* Wrote to xQueueHandle so expected xQueueHandle to be the handle
                 * held in the queue set. */
                xQueueSetTasksStatus = pdFAIL;
            }

            /* Next add an item to the second queue. */
            xQueueOverwrite( xQueueHandle2, ( void * ) &ulValueToSend2 );

            if( uxQueueMessagesWaiting( xQueueSet ) != ( UBaseType_t ) 2 )
            {
                /* Expected two items in the queue set. */
                xQueueSetTasksStatus = pdFAIL;
            }

            /* The head of the queue set should not have changed though. */
            xQueuePeek( xQueueSet, &xReceivedHandle, queuesetDONT_BLOCK );

            if( xReceivedHandle != xQueueHandle1 )
            {
                /* Wrote to xQueueHandle so expected xQueueHandle to be the handle
                 * held in the queue set. */
                xQueueSetTasksStatus = pdFAIL;
            }

            /* Now overwrite the value in the queue and ensure the queue set state
             * doesn't change as the number of items in the queues within the set have
             * not changed.  NOTE:  after this queue 1 should hold ulValueToSend2 and queue
             * 2 should hold the value ulValueToSend1. */
            xQueueOverwrite( xQueueHandle1, ( void * ) &ulValueToSend2 );

            if( uxQueueMessagesWaiting( xQueueSet ) != ( UBaseType_t ) 2 )
            {
                /* Still expected two items in the queue set. */
                xQueueSetTasksStatus = pdFAIL;
            }

            xQueueOverwrite( xQueueHandle2, ( void * ) &ulValueToSend1 );

            if( uxQueueMessagesWaiting( xQueueSet ) != ( UBaseType_t ) 2 )
            {
                /* Still expected two items in the queue set. */
                xQueueSetTasksStatus = pdFAIL;
            }

            /* Repeat the above to ensure the queue set state doesn't change. */
            xQueueOverwrite( xQueueHandle1, ( void * ) &ulValueToSend2 );

            if( uxQueueMessagesWaiting( xQueueSet ) != ( UBaseType_t ) 2 )
            {
                /* Still expected two items in the queue set. */
                xQueueSetTasksStatus = pdFAIL;
            }

            xQueueOverwrite( xQueueHandle2, ( void * ) &ulValueToSend1 );

            if( uxQueueMessagesWaiting( xQueueSet ) != ( UBaseType_t ) 2 )
            {
                /* Still expected two items in the queue set. */
                xQueueSetTasksStatus = pdFAIL;
            }

            /* Now when reading from the queue set we expect the handle to the first
             * queue to be received first, and for that queue to hold ulValueToSend2 as the
             * originally written value was overwritten.  Likewise the second handle received
             * from the set should be that of the second queue, and that queue should hold
             * ulValueToSend1 as the originally written value was overwritten. */
            xReceivedHandle = xQueueSelectFromSet( xQueueSet, queuesetDONT_BLOCK );

            if( xReceivedHandle != xQueueHandle1 )
            {
                /* Wrote to xQueueHandle1 first so expected that handle to be read from
                 * the set first. */
                xQueueSetTasksStatus = pdFAIL;
            }

            if( uxQueueMessagesWaiting( xQueueSet ) != ( UBaseType_t ) 1 )
            {
                /* One value was read from the set, so now only expect a single value
                 * in the set. */
                xQueueSetTasksStatus = pdFAIL;
            }

            xQueueReceive( xReceivedHandle, &ulValueReceived, queuesetDONT_BLOCK );

            if( ulValueReceived != ulValueToSend2 )
            {
                /* Unexpected value received from the queue.  ulValueToSend1 was written
                 * first, but then overwritten with ulValueToSend2; */
                xQueueSetTasksStatus = pdFAIL;
            }

            xReceivedHandle = xQueueSelectFromSet( xQueueSet, queuesetDONT_BLOCK );

            if( xReceivedHandle != xQueueHandle2 )
            {
                /* xQueueHandle1 has already been removed from the set so expect only
                 * xQueueHandle2 to be left. */
                xQueueSetTasksStatus = pdFAIL;
            }

            if( uxQueueMessagesWaiting( xQueueSet ) != ( UBaseType_t ) 0 )
            {
                /* The last value was read from the set so don't expect any more. */
                xQueueSetTasksStatus = pdFAIL;
            }

            xQueueReceive( xReceivedHandle, &ulValueReceived, queuesetDONT_BLOCK );

            if( ulValueReceived != ulValueToSend1 )
            {
                /* Unexpected value received from the queue.  ulValueToSend2 was written
                 * first, but then overwritten with ulValueToSend1. */
                xQueueSetTasksStatus = pdFAIL;
            }

            /* Should be anything in the queue set now. */
            xReceivedHandle = xQueueSelectFromSet( xQueueSet, queuesetDONT_BLOCK );

            if( xReceivedHandle != NULL )
            {
                xQueueSetTasksStatus = pdFAIL;
            }

            /* Clean up. */
            xQueueRemoveFromSet( xQueueHandle1, xQueueSet );
            xQueueRemoveFromSet( xQueueHandle2, xQueueSet );
            vQueueDelete( xQueueHandle1 );
            vQueueDelete( xQueueHandle2 );
        }
    }
/*-----------------------------------------------------------*/

    static void prvTestQueueOverwriteFromISROnTwoQueusInQueueSet( void )
    {
        uint32_t ulValueToSend1 = 1, ulValueToSend2 = 2UL, ulValueReceived = 0;
        QueueHandle_t xQueueHandle1 = NULL, xQueueHandle2 = NULL, xReceivedHandle = NULL;
        const UBaseType_t xLengthOfOne = ( UBaseType_t ) 1;

        /* Create two queues that have a length of one - a requirement in order to call
         * xQueueOverwrite.  These will get deleted again when this test completes. */
        xQueueHandle1 = xQueueCreate( xLengthOfOne, sizeof( uint32_t ) );
        configASSERT( xQueueHandle1 );
        xQueueHandle2 = xQueueCreate( xLengthOfOne, sizeof( uint32_t ) );
        configASSERT( xQueueHandle2 );

        if( ( xQueueHandle1 != NULL ) && ( xQueueHandle2 != NULL ) )
        {
            /* Add both queues to the queue set. */
            xQueueAddToSet( xQueueHandle1, xQueueSet );
            xQueueAddToSet( xQueueHandle2, xQueueSet );

            /* Add an item using the first queue using the 'FromISR' version of the
             * overwrite function. */
            xQueueOverwriteFromISR( xQueueHandle1, ( void * ) &ulValueToSend1, NULL );

            if( uxQueueMessagesWaiting( xQueueSet ) != ( UBaseType_t ) 1 )
            {
                /* Expected one item in the queue set. */
                xQueueSetTasksStatus = pdFAIL;
            }

            xQueuePeek( xQueueSet, &xReceivedHandle, queuesetDONT_BLOCK );

            if( xReceivedHandle != xQueueHandle1 )
            {
                /* Wrote to xQueueHandle so expected xQueueHandle to be the handle
                 * held in the queue set. */
                xQueueSetTasksStatus = pdFAIL;
            }

            /* Next add an item to the second queue using the 'FromISR' version of the
             * overwrite function. */
            xQueueOverwriteFromISR( xQueueHandle2, ( void * ) &ulValueToSend2, NULL );

            if( uxQueueMessagesWaiting( xQueueSet ) != ( UBaseType_t ) 2 )
            {
                /* Expected two items in the queue set. */
                xQueueSetTasksStatus = pdFAIL;
            }

            /* The head of the queue set should not have changed though. */
            xQueuePeek( xQueueSet, &xReceivedHandle, queuesetDONT_BLOCK );

            if( xReceivedHandle != xQueueHandle1 )
            {
                /* Wrote to xQueueHandle so expected xQueueHandle to be the handle
                 * held in the queue set. */
                xQueueSetTasksStatus = pdFAIL;
            }

            /* Now overwrite the value in the queue and ensure the queue set state
             * doesn't change as the number of items in the queues within the set have
             * not changed.  NOTE:  after this queue 1 should hold ulValueToSend2 and queue
             * 2 should hold the value ulValueToSend1. */
            xQueueOverwriteFromISR( xQueueHandle1, ( void * ) &ulValueToSend2, NULL );

            if( uxQueueMessagesWaiting( xQueueSet ) != ( UBaseType_t ) 2 )
            {
                /* Still expected two items in the queue set. */
                xQueueSetTasksStatus = pdFAIL;
            }

            xQueueOverwriteFromISR( xQueueHandle2, ( void * ) &ulValueToSend1, NULL );

            if( uxQueueMessagesWaiting( xQueueSet ) != ( UBaseType_t ) 2 )
            {
                /* Still expected two items in the queue set. */
                xQueueSetTasksStatus = pdFAIL;
            }

            /* Repeat the above to ensure the queue set state doesn't change. */
            xQueueOverwriteFromISR( xQueueHandle1, ( void * ) &ulValueToSend2, NULL );

            if( uxQueueMessagesWaiting( xQueueSet ) != ( UBaseType_t ) 2 )
            {
                /* Still expected two items in the queue set. */
                xQueueSetTasksStatus = pdFAIL;
            }

            xQueueOverwriteFromISR( xQueueHandle2, ( void * ) &ulValueToSend1, NULL );

            if( uxQueueMessagesWaiting( xQueueSet ) != ( UBaseType_t ) 2 )
            {
                /* Still expected two items in the queue set. */
                xQueueSetTasksStatus = pdFAIL;
            }

            /* Now when reading from the queue set we expect the handle to the first
             * queue to be received first, and for that queue to hold ulValueToSend2 as the
             * originally written value was overwritten.  Likewise the second handle received
             * from the set should be that of the second queue, and that queue should hold
             * ulValueToSend1 as the originally written value was overwritten. */
            xReceivedHandle = xQueueSelectFromSet( xQueueSet, queuesetDONT_BLOCK );

            if( xReceivedHandle != xQueueHandle1 )
            {
                /* Wrote to xQueueHandle1 first so expected that handle to be read from
                 * the set first. */
                xQueueSetTasksStatus = pdFAIL;
            }

            if( uxQueueMessagesWaiting( xQueueSet ) != ( UBaseType_t ) 1 )
            {
                /* One value was read from the set, so now only expect a single value
                 * in the set. */
                xQueueSetTasksStatus = pdFAIL;
            }

            xQueueReceive( xReceivedHandle, &ulValueReceived, queuesetDONT_BLOCK );

            if( ulValueReceived != ulValueToSend2 )
            {
                /* Unexpected value received from the queue.  ulValueToSend1 was written
                 * first, but then overwritten with ulValueToSend2; */
                xQueueSetTasksStatus = pdFAIL;
            }

            xReceivedHandle = xQueueSelectFromSet( xQueueSet, queuesetDONT_BLOCK );

            if( xReceivedHandle != xQueueHandle2 )
            {
                /* xQueueHandle1 has already been removed from the set so expect only
                 * xQueueHandle2 to be left. */
                xQueueSetTasksStatus = pdFAIL;
            }

            if( uxQueueMessagesWaiting( xQueueSet ) != ( UBaseType_t ) 0 )
            {
                /* The last value was read from the set so don't expect any more. */
                xQueueSetTasksStatus = pdFAIL;
            }

            xQueueReceive( xReceivedHandle, &ulValueReceived, queuesetDONT_BLOCK );

            if( ulValueReceived != ulValueToSend1 )
            {
                /* Unexpected value received from the queue.  ulValueToSend2 was written
                 * first, but then overwritten with ulValueToSend1. */
                xQueueSetTasksStatus = pdFAIL;
            }

            /* Should be anything in the queue set now. */
            xReceivedHandle = xQueueSelectFromSet( xQueueSet, queuesetDONT_BLOCK );

            if( xReceivedHandle != NULL )
            {
                xQueueSetTasksStatus = pdFAIL;
            }

            /* Clean up. */
            xQueueRemoveFromSet( xQueueHandle1, xQueueSet );
            xQueueRemoveFromSet( xQueueHandle2, xQueueSet );
            vQueueDelete( xQueueHandle1 );
            vQueueDelete( xQueueHandle2 );
        }
    }
/*-----------------------------------------------------------*/

    static void prvSetupTest( void )
    {
        BaseType_t x;
        uint32_t ulValueToSend = 0;

        /* Ensure the queues are created and the queue set configured before the
         * sending task is unsuspended.
         *
         * First Create the queue set such that it will be able to hold a message for
         * every space in every queue in the set. */
        xQueueSet = xQueueCreateSet( queuesetNUM_QUEUES_IN_SET * queuesetQUEUE_LENGTH );

        for( x = 0; x < queuesetNUM_QUEUES_IN_SET; x++ )
        {
            /* Create the queue and add it to the set.  The queue is just holding
             * uint32_t value. */
            xQueues[ x ] = xQueueCreate( queuesetQUEUE_LENGTH, sizeof( uint32_t ) );
            configASSERT( xQueues[ x ] );

            if( xQueueAddToSet( xQueues[ x ], xQueueSet ) != pdPASS )
            {
                xQueueSetTasksStatus = pdFAIL;
            }
            else
            {
                /* The queue has now been added to the queue set and cannot be added to
                 * another. */
                if( xQueueAddToSet( xQueues[ x ], xQueueSet ) != pdFAIL )
                {
                    xQueueSetTasksStatus = pdFAIL;
                }
            }
        }

        /* Attempt to remove a queue from a queue set it does not belong
         * to (NULL being passed as the queue set in this case). */
        if( xQueueRemoveFromSet( xQueues[ 0 ], NULL ) != pdFAIL )
        {
            /* It is not possible to successfully remove a queue from a queue
             * set it does not belong to. */
            xQueueSetTasksStatus = pdFAIL;
        }

        /* Attempt to remove a queue from the queue set it does belong to. */
        if( xQueueRemoveFromSet( xQueues[ 0 ], xQueueSet ) != pdPASS )
        {
            /* It should be possible to remove the queue from the queue set it
             * does belong to. */
            xQueueSetTasksStatus = pdFAIL;
        }

        /* Add an item to the queue before attempting to add it back into the
         * set. */
        xQueueSend( xQueues[ 0 ], ( void * ) &ulValueToSend, 0 );

        if( xQueueAddToSet( xQueues[ 0 ], xQueueSet ) != pdFAIL )
        {
            /* Should not be able to add a non-empty queue to a set. */
            xQueueSetTasksStatus = pdFAIL;
        }

        /* Remove the item from the queue before adding the queue back into the
         * set so the dynamic tests can begin. */
        xQueueReceive( xQueues[ 0 ], &ulValueToSend, 0 );

        if( xQueueAddToSet( xQueues[ 0 ], xQueueSet ) != pdPASS )
        {
            /* If the queue was successfully removed from the queue set then it
             * should be possible to add it back in again. */
            xQueueSetTasksStatus = pdFAIL;
        }

        /* The task that sends to the queues is not running yet, so attempting to
         * read from the queue set should fail. */
        if( xQueueSelectFromSet( xQueueSet, queuesetSHORT_DELAY ) != NULL )
        {
            xQueueSetTasksStatus = pdFAIL;
        }

        /* Testing the behaviour of queue sets when a queue overwrite operation is
         * performed on a set member requires a special test as overwrites can only
         * be performed on queues that have a length of 1. */
        prvTestQueueOverwriteWithQueueSet();

        /* Test the case where two queues within a set are written to with
         * xQueueOverwrite(). */
        prvTestQueueOverwriteOnTwoQueusInQueueSet();
        prvTestQueueOverwriteFromISROnTwoQueusInQueueSet();

        /* In case any of the above have already indicated a failure. */
        configASSERT( xQueueSetTasksStatus != pdFAIL );

        /* Resume the task that writes to the queues. */
        vTaskResume( xQueueSetSendingTask );

        /* Let the ISR access the queues also. */
        xSetupComplete = pdTRUE;
    }
/*-----------------------------------------------------------*/

    static size_t prvRand( void )
    {
        uxNextRand = ( uxNextRand * ( size_t ) 1103515245 ) + ( size_t ) 12345;
        return ( uxNextRand / ( size_t ) 65536 ) % ( size_t ) 32768;
    }
/*-----------------------------------------------------------*/

    static void prvSRand( size_t uxSeed )
    {
        uxNextRand = uxSeed;
    }

#endif /* ( configUSE_QUEUE_SETS == 1 ) */
