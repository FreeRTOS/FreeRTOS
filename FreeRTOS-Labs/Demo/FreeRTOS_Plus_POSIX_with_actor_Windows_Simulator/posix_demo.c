/*
 * FreeRTOS POSIX Demo V1.0.0
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

/**
 * @brief Demo intro: job distribution with actor model.
 *
 * This demo simulates job distribution with actor model.
 * https://en.wikipedia.org/wiki/Actor_model
 *
 * In this demo, vStartPOSIXDemo() first creates all mailboxes
 * which will be used by actors to send and receive messages.
 * Then it spins up two types of actors -- Dispatcher and Workers.
 *
 * Dispatcher -- Distributing sub-tasks to workers.
 *               Distribution is done by putting messages into each worker's inbox,
 *               which is essentially an mqueue. Dispatcher keeps distributing tasks
 *               until all intended tasks are distributed.
 *
 * Workers -- Take sub-tasks and perform predefined routine for each type of tasks.
 *
 * Upon finishing distributing all tasks, Dispatcher will send a "terminate" message to
 * each worker. vStartPOSIXDemo() will then join all actor threads and clean up mailboxes.
 *
 * @note A few assumptions are made in this demo, which a user might have to alter
 * if to adopt this model in a new application:
 *
 *  - The upper limit for MQUEUE_NUMBER_OF_WORKERS is set to 10.
 *    This is not due to physical constraint (e.g. memory), rather to make queue
 *    names end with a single digit number.
 *
 *  - Message enum is cast to char/uint8_t directly, with the assumption that
 *    the system is not going to have more than 254 messages, which is often true
 *    in practice. Could extend bits used in a message to either have more messages
 *    or include additional arguments for a message. Proper typecasting is needed
 *    in that case.
 *
 *  - The philosophy is "failure is expected". It is shown in both the way dispatcher
 *    delivers messages (i.e. messages can be dropped by worker(s)), and also the
 *    way workers process messages (i.e. workers do not inform dispatcher success or
 *    failure).
 *
 *  - Following the philosophy, dispatcher shall never use blocking calls to distribute
 *    tasks. The only exception made here is that dispatcher needs to make sure the
 *    successful delivery of "terminate" messages. So that, main thread could join
 *    all actor threads and finish the demo.
 */

/* FreeRTOS includes. */
#include "FreeRTOS_POSIX.h"

/* System headers. */
#include <stdbool.h>
#include <string.h>
#include <stdio.h>

/* Demo includes. */
#include "posix_demo.h"

/* FreeRTOS+POSIX. */
#include "FreeRTOS_POSIX/pthread.h"
#include "FreeRTOS_POSIX/mqueue.h"
#include "FreeRTOS_POSIX/time.h"
#include "FreeRTOS_POSIX/fcntl.h"
#include "FreeRTOS_POSIX/errno.h"

/* Constants. */
#define LINE_BREAK    "\r\n"

/**
 * @brief Control messages.
 *
 * uint8_t is sufficient for this enum, that we are going to cast to char directly.
 * If ever needed, implement a function to properly typecast.
 */
/**@{ */
typedef enum ControlMessage
{
    eMSG_LOWER_INAVLID = 0x00,        /**< Guard, let's not use 0x00 for messages. */
    eWORKER_CTRL_MSG_CONTINUE = 0x01, /**< Dispatcher to worker, distributing another job. */
    eWORKER_CTRL_MSG_EXIT = 0x02,     /**< Dispatcher to worker, all jobs are finished and the worker receiving such can exit. */

    /* define additional messages here */

    eMSG_UPPER_INVALID = 0xFF /**< Guard, additional tasks shall be defined above. */
} eControlMessage;
/**@} */

/**
 * @defgroup Configuration constants for the dispatcher-worker demo.
 */
/**@{ */
#define MQUEUE_NUMBER_OF_WORKERS    ( 4 )                        /**< The number of worker threads, each thread has one queue which is used as income box. */

#if ( MQUEUE_NUMBER_OF_WORKERS > 10 )
    #error "Please keep MQUEUE_NUMBER_OF_WORKERS < 10."
#endif

#define MQUEUE_WORKER_QNAME_BASE                "/qNode0"         /**< Queue name base. */
#define MQUEUE_WORKER_QNAME_BASE_LEN            ( 6 )             /** Queue name base length. */

#define MQUEUE_TIMEOUT_SECONDS                  ( 1 )             /**< Relative timeout for mqueue functions. */
#define MQUEUE_MAX_NUMBER_OF_MESSAGES_WORKER    ( 1 )             /**< Maximum number of messages in a queue. */

#define MQUEUE_MSG_WORKER_CTRL_MSG_SIZE         sizeof( uint8_t ) /**< Control message size. */
#define DEMO_ERROR                              ( -1 )            /**< Any non-zero value would work. */
/**@} */

/**
 * @brief Structure used by Worker thread.
 */
/**@{ */
typedef struct WorkerThreadResources
{
    pthread_t pxID; /**< thread ID. */
    mqd_t xInboxID; /**< mqueue inbox ID. */
} WorkerThreadResources_t;
/**@} */

/**
 * @brief Structure used by Dispatcher thread.
 */
/**@{ */
typedef struct DispatcherThreadResources
{
    pthread_t pxID;    /**< thread ID. */
    mqd_t * pOutboxID; /**< a list of mqueue outbox ID. */
} DispatcherThreadResources_t;
/**@} */

/*-----------------------------------------------------------*/

static void * prvWorkerThread( void * pvArgs )
{
    WorkerThreadResources_t pArgList = *( WorkerThreadResources_t * ) pvArgs;

    printf( "Worker thread #[%d] - start %s", ( int ) pArgList.pxID, LINE_BREAK );

    struct timespec xReceiveTimeout = { 0 };

    ssize_t xMessageSize = 0;
    char pcReceiveBuffer[ MQUEUE_MSG_WORKER_CTRL_MSG_SIZE ] = { 0 };

    /* This is a worker thread that reacts based on what is sent to its inbox (mqueue). */
    while( true )
    {
        clock_gettime( CLOCK_REALTIME, &xReceiveTimeout );
        xReceiveTimeout.tv_sec += MQUEUE_TIMEOUT_SECONDS;

        xMessageSize = mq_receive( pArgList.xInboxID,
                                   pcReceiveBuffer,
                                   MQUEUE_MSG_WORKER_CTRL_MSG_SIZE,
                                   0 );

        /* Parse messages */
        if( xMessageSize == MQUEUE_MSG_WORKER_CTRL_MSG_SIZE )
        {
            switch( ( int ) pcReceiveBuffer[ 0 ] )
            {
                case eWORKER_CTRL_MSG_CONTINUE:
                    /* Task branch, currently only prints message to screen. */
                    /* Could perform tasks here. Could also notify dispatcher upon completion, if desired. */
                    printf( "Worker thread #[%d] -- Received eWORKER_CTRL_MSG_CONTINUE %s", ( int ) pArgList.pxID, LINE_BREAK );
                    break;

                case eWORKER_CTRL_MSG_EXIT:
                    printf( "Worker thread #[%d] -- Finished. Exit now. %s", ( int ) pArgList.pxID, LINE_BREAK );

                    return NULL;

                default:
                    /* Received a message that we don't care or not defined. */
                    break;
            }
        }
        else
        {
            /* Invalid message. Error handling can be done here, if desired. */
        }
    }

    /* You should never hit here. */
    /* return NULL; */
}

/*-----------------------------------------------------------*/

static void * prvDispatcherThread( void * pvArgs )
{
    DispatcherThreadResources_t pArgList = *( DispatcherThreadResources_t * ) pvArgs;

    printf( "Dispatcher thread - start %s", LINE_BREAK );

    struct timespec xSendTimeout = { 0 };

    ssize_t xMessageSize = 0;
    char pcSendBuffer[ MQUEUE_MSG_WORKER_CTRL_MSG_SIZE ] = { 0 };

    /* Just for fun, let threads do a total of 100 independent tasks. */
    int i = 0;
    const int totalNumOfJobsPerThread = 100;

    /* Distribute 1000 independent tasks to workers, in round-robin fashion. */
    pcSendBuffer[ 0 ] = ( char ) eWORKER_CTRL_MSG_CONTINUE;

    for( i = 0; i < totalNumOfJobsPerThread; i++ )
    {
        clock_gettime( CLOCK_REALTIME, &xSendTimeout );
        xSendTimeout.tv_sec += MQUEUE_TIMEOUT_SECONDS;

        printf( "Dispatcher iteration #[%d] -- Sending msg to worker thread #[%d]. %s", i, ( int ) pArgList.pOutboxID[ i % MQUEUE_NUMBER_OF_WORKERS ], LINE_BREAK );

        xMessageSize = mq_timedsend( pArgList.pOutboxID[ i % MQUEUE_NUMBER_OF_WORKERS ],
                                     pcSendBuffer,
                                     MQUEUE_MSG_WORKER_CTRL_MSG_SIZE,
                                     0,
                                     &xSendTimeout );

        if( xMessageSize != 0 )
        {
            /* This error is acceptable in our setup.
             * Since inbox for each thread fits only one message.
             * In reality, balance inbox size, message arrival rate, and message drop rate. */
            printf( "An acceptable failure -- dispatcher failed to send eWORKER_CTRL_MSG_CONTINUE to outbox ID: %x. errno %d %s",
                    ( int ) pArgList.pOutboxID[ i % MQUEUE_NUMBER_OF_WORKERS ], errno, LINE_BREAK );
        }
    }

    /* Control thread is now done with distributing jobs. Tell workers they are done. */
    pcSendBuffer[ 0 ] = ( char ) eWORKER_CTRL_MSG_EXIT;

    for( i = 0; i < MQUEUE_NUMBER_OF_WORKERS; i++ )
    {
        printf( "Dispatcher [%d] -- Sending eWORKER_CTRL_MSG_EXIT to worker thread #[%d]. %s", i, ( int ) pArgList.pOutboxID[ i % MQUEUE_NUMBER_OF_WORKERS ], LINE_BREAK );

        /* This is a blocking call, to guarantee worker thread exits. */
        xMessageSize = mq_send( pArgList.pOutboxID[ i % MQUEUE_NUMBER_OF_WORKERS ],
                                pcSendBuffer,
                                MQUEUE_MSG_WORKER_CTRL_MSG_SIZE,
                                0 );
    }

    return NULL;
}

/*-----------------------------------------------------------*/

/**
 * @brief Job distribution with actor model.
 *
 * See the top of this file for detailed description.
 */
void vStartPOSIXDemo( void *pvParameters )
{
    int i = 0;
    int iStatus = 0;

	/* Remove warnings about unused parameters. */
    ( void ) pvParameters;

    /* Handles of the threads and related resources. */
    DispatcherThreadResources_t pxDispatcher = { 0 };
    WorkerThreadResources_t pxWorkers[ MQUEUE_NUMBER_OF_WORKERS ] = { { 0 } };
    mqd_t workerMqueues[ MQUEUE_NUMBER_OF_WORKERS ] = { 0 };

    struct mq_attr xQueueAttributesWorker =
    {
        .mq_flags   = 0,
        .mq_maxmsg  = MQUEUE_MAX_NUMBER_OF_MESSAGES_WORKER,
        .mq_msgsize = MQUEUE_MSG_WORKER_CTRL_MSG_SIZE,
        .mq_curmsgs = 0
    };

    pxDispatcher.pOutboxID = workerMqueues;

    /* Create message queues for each worker thread. */
    for( i = 0; i < MQUEUE_NUMBER_OF_WORKERS; i++ )
    {
        /* Prepare a unique queue name for each worker. */
        char qName[] = MQUEUE_WORKER_QNAME_BASE;
        qName[ MQUEUE_WORKER_QNAME_BASE_LEN - 1 ] = qName[ MQUEUE_WORKER_QNAME_BASE_LEN - 1 ] + i;

        /* Open a queue with --
         * O_CREAT -- create a message queue.
         * O_RDWR -- both receiving and sending messages.
         */
        pxWorkers[ i ].xInboxID = mq_open( qName,
                                           O_CREAT | O_RDWR,
                                           ( mode_t ) 0,
                                           &xQueueAttributesWorker );

        if( pxWorkers[ i ].xInboxID == ( mqd_t ) -1 )
        {
            printf( "Invalid inbox (mqueue) for worker. %s", LINE_BREAK );
            iStatus = DEMO_ERROR;
            break;
        }

        /* Outboxes of dispatcher thread is the inboxes of all worker threads. */
        pxDispatcher.pOutboxID[ i ] = pxWorkers[ i ].xInboxID;
    }

    /* Create and start Worker threads. */
    if( iStatus == 0 )
    {
        for( i = 0; i < MQUEUE_NUMBER_OF_WORKERS; i++ )
        {
            ( void ) pthread_create( &( pxWorkers[ i ].pxID ), NULL, prvWorkerThread, &pxWorkers[ i ] );
        }

        /* Create and start dispatcher thread. */
        ( void ) pthread_create( &( pxDispatcher.pxID ), NULL, prvDispatcherThread, &pxDispatcher );

        /* Actors will do predefined tasks in threads. Current implementation is that
         * dispatcher actor notifies worker actors to terminate upon finishing distributing tasks. */

        /* Wait for worker threads to join. */
        for( i = 0; i < MQUEUE_NUMBER_OF_WORKERS; i++ )
        {
            ( void ) pthread_join( pxWorkers[ i ].pxID, NULL );
        }

        /* Wait for dispatcher thread to join. */
        ( void ) pthread_join( pxDispatcher.pxID, NULL );
    }

    /* Close and unlink worker message queues. */
    for( i = 0; i < MQUEUE_NUMBER_OF_WORKERS; i++ )
    {
        char qName[] = MQUEUE_WORKER_QNAME_BASE;
        qName[ MQUEUE_WORKER_QNAME_BASE_LEN - 1 ] = qName[ MQUEUE_WORKER_QNAME_BASE_LEN - 1 ] + i;

        if( pxWorkers[ i ].xInboxID != NULL )
        {
            ( void ) mq_close( pxWorkers[ i ].xInboxID );
            ( void ) mq_unlink( qName );
        }
    }

    /* Have something on console. */
    if( iStatus == 0 )
    {
        printf( "All threads finished. %s", LINE_BREAK );
    }
    else
    {
        printf( "Queues did not get initialized properly. Did not run demo. %s", LINE_BREAK );
    }

	/* This task was created with the native xTaskCreate() API function, so
	must not run off the end of its implementing thread. */
	vTaskDelete( NULL );
}
