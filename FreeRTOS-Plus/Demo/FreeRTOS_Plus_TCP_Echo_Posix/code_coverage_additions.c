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

/*
 * Contains sundry tests to exercise code that is not touched by the standard
 * demo tasks (which are predominantly test tasks).  Some tests are included
 * here because they can only be executed when configASSERT() is not defined.
 */

#include <string.h>

#include "FreeRTOS.h"
#include "task.h"
#include "timers.h"
#include "event_groups.h"
#include "semphr.h"
#include "stream_buffer.h"
#include "message_buffer.h"

/*-----------------------------------------------------------*/

/*
 * Try creating static objects with one of the mandatory parameters set to NULL.
 * This can't be done in the standard demos as asserts() will get hit.
 */
static BaseType_t prvStaticAllocationsWithNullBuffers( void );

/*
 * Code coverage analysis is performed with tracing turned off, so this
 * function executes the trace specific utility functions that would not
 * otherwise be executed..
 */
static BaseType_t prvTraceUtils( void );

/*
 * The queue peek standard demo does not cover the case where an attempt to peek
 * times out, so test that case.
 */
static BaseType_t prvPeekTimeout( void );

/*
 * Calls various interrupt safe functions designed to query the state of a
 * queue.
 */
static BaseType_t prvQueueQueryFromISR( void );

/*
 * Hits a few paths in tasks state and status query functions not otherwise hit
 * by standard demo and test files.
 */
static BaseType_t prvTaskQueryFunctions( void );

/*
 * None of the standard demo tasks use the task tags - exercise them here.
 */
static BaseType_t prvTaskTags( void );

/*
 * Exercises a few of the query functions that are not otherwise exercised in
 * the standard demo and test functions.
 */
static BaseType_t prvTimerQuery( void );

/*-----------------------------------------------------------*/

static BaseType_t prvStaticAllocationsWithNullBuffers( void )
{
    uintptr_t ulReturned = 0;
    BaseType_t xReturn = pdPASS;
    UBaseType_t uxDummy = 10;

    /* Don't expect to create any of the objects as a NULL parameter is always
     * passed in place of a required buffer.  Hence if all passes then none of the
     |= will be against 0, and ulReturned will still be zero at the end of this
     * function. */
    ulReturned |= ( uintptr_t ) xEventGroupCreateStatic( NULL );

    /* Try creating a task twice, once with puxStackBuffer NULL, and once with
     * pxTaskBuffer NULL. */
    ulReturned |= ( uintptr_t ) xTaskCreateStatic( NULL,    /* Task to run, not needed as the task is not created. */
                                                   "Dummy", /* Task name. */
                                                   configMINIMAL_STACK_SIZE,
                                                   NULL,
                                                   tskIDLE_PRIORITY,
                                                   NULL,
                                                   ( StaticTask_t * ) &xReturn ); /* Dummy value just to pass a non NULL value in - won't get used. */

    ulReturned |= ( uintptr_t ) xTaskCreateStatic( NULL,                          /* Task to run, not needed as the task is not created. */
                                                   "Dummy",                       /* Task name. */
                                                   configMINIMAL_STACK_SIZE,
                                                   NULL,
                                                   tskIDLE_PRIORITY,
                                                   ( StackType_t * ) &xReturn, /* Dummy value just to pass a non NULL value in - won't get used. */
                                                   NULL );

    ulReturned |= ( uintptr_t ) xQueueCreateStatic( uxDummy,
                                                    uxDummy,
                                                    ( uint8_t * ) &xReturn, /* Dummy value just to pass a non NULL value in - won't get used. */
                                                    NULL );

    /* Try creating a stream buffer twice, once with pucStreamBufferStorageArea
     * set to NULL, and once with pxStaticStreamBuffer set to NULL. */
    ulReturned |= ( uintptr_t ) xStreamBufferCreateStatic( uxDummy,
                                                           uxDummy,
                                                           NULL,
                                                           ( StaticStreamBuffer_t * ) &xReturn ); /* Dummy value just to pass a non NULL value in - won't get used. */

    ulReturned |= ( uintptr_t ) xStreamBufferCreateStatic( uxDummy,
                                                           uxDummy,
                                                           ( uint8_t * ) &xReturn, /* Dummy value just to pass a non NULL value in - won't get used. */
                                                           NULL );

    if( ulReturned != 0 )
    {
        /* Something returned a non-NULL value. */
        xReturn = pdFAIL;
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

static BaseType_t prvTraceUtils( void )
{
    EventGroupHandle_t xEventGroup;
    QueueHandle_t xQueue;
    BaseType_t xReturn = pdPASS;
    const UBaseType_t xNumber = ( UBaseType_t ) 100, xQueueLength = ( UBaseType_t ) 1;
    UBaseType_t uxValue;
    TaskHandle_t xTaskHandle;
    StreamBufferHandle_t xStreamBuffer;
    MessageBufferHandle_t xMessageBuffer;

    /* Exercise the event group trace utilities. */
    xEventGroup = xEventGroupCreate();

    if( xEventGroup != NULL )
    {
        vEventGroupSetNumber( xEventGroup, xNumber );

        if( uxEventGroupGetNumber( NULL ) != 0 )
        {
            xReturn = pdFAIL;
        }

        if( uxEventGroupGetNumber( xEventGroup ) != xNumber )
        {
            xReturn = pdFAIL;
        }

        vEventGroupDelete( xEventGroup );
    }
    else
    {
        xReturn = pdFAIL;
    }

    /* Exercise the queue trace utilities. */
    xQueue = xQueueCreate( xQueueLength, ( UBaseType_t ) sizeof( uxValue ) );

    if( xQueue != NULL )
    {
        vQueueSetQueueNumber( xQueue, xNumber );

        if( uxQueueGetQueueNumber( xQueue ) != xNumber )
        {
            xReturn = pdFAIL;
        }

        if( ucQueueGetQueueType( xQueue ) != queueQUEUE_TYPE_BASE )
        {
            xReturn = pdFAIL;
        }

        vQueueDelete( xQueue );
    }
    else
    {
        xReturn = pdFAIL;
    }

    /* Exercise the task trace utilities.  Value of 100 is arbitrary, just want
     * to check the value that is set is also read back. */
    uxValue = 100;
    xTaskHandle = xTaskGetCurrentTaskHandle();
    vTaskSetTaskNumber( xTaskHandle, uxValue );

    if( uxTaskGetTaskNumber( xTaskHandle ) != uxValue )
    {
        xReturn = pdFAIL;
    }

    if( uxTaskGetTaskNumber( NULL ) != 0 )
    {
        xReturn = pdFAIL;
    }

    /* Timer trace util functions are exercised in prvTimerQuery(). */


    /* Exercise the stream buffer utilities.  Try creating with a trigger level
     * of 0, it should then get capped to 1. */
    xStreamBuffer = xStreamBufferCreate( sizeof( uint32_t ), 0 );

    if( xStreamBuffer != NULL )
    {
        vStreamBufferSetStreamBufferNumber( xStreamBuffer, uxValue );

        if( uxStreamBufferGetStreamBufferNumber( xStreamBuffer ) != uxValue )
        {
            xReturn = pdFALSE;
        }

        if( ucStreamBufferGetStreamBufferType( xStreamBuffer ) != 0 )
        {
            /* "Is Message Buffer" flag should have been 0. */
            xReturn = pdFALSE;
        }

        vStreamBufferDelete( xStreamBuffer );
    }
    else
    {
        xReturn = pdFALSE;
    }

    xMessageBuffer = xMessageBufferCreate( sizeof( uint32_t ) );

    if( xMessageBuffer != NULL )
    {
        if( ucStreamBufferGetStreamBufferType( xMessageBuffer ) == 0 )
        {
            /* "Is Message Buffer" flag should have been 1. */
            xReturn = pdFALSE;
        }

        vMessageBufferDelete( xMessageBuffer );
    }
    else
    {
        xReturn = pdFALSE;
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

static BaseType_t prvPeekTimeout( void )
{
    QueueHandle_t xHandle;
    const UBaseType_t xQueueLength = 1;
    BaseType_t xReturn = pdPASS;
    TickType_t xBlockTime = ( TickType_t ) 2;
    UBaseType_t uxReceived;

    /* Create the queue just to try peeking it while it is empty. */
    xHandle = xQueueCreate( xQueueLength, ( UBaseType_t ) sizeof( xQueueLength ) );

    if( xHandle != NULL )
    {
        if( uxQueueMessagesWaiting( xHandle ) != 0 )
        {
            xReturn = pdFAIL;
        }

        /* Ensure peeking from the queue times out as the queue is empty. */
        if( xQueuePeek( xHandle, &uxReceived, xBlockTime ) != pdFALSE )
        {
            xReturn = pdFAIL;
        }

        vQueueDelete( xHandle );
    }
    else
    {
        xReturn = pdFAIL;
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

static BaseType_t prvQueueQueryFromISR( void )
{
    BaseType_t xReturn = pdPASS, xValue = 1;
    const UBaseType_t xISRQueueLength = ( UBaseType_t ) 1;
    const char * pcISRQueueName = "ISRQueue";
    QueueHandle_t xISRQueue = NULL;

    xISRQueue = xQueueCreate( xISRQueueLength, ( UBaseType_t ) sizeof( BaseType_t ) );

    if( xISRQueue != NULL )
    {
        vQueueAddToRegistry( xISRQueue, pcISRQueueName );

        if( strcmp( pcQueueGetName( xISRQueue ), pcISRQueueName ) )
        {
            xReturn = pdFAIL;
        }

        /* Expect the queue to be empty here. */
        if( uxQueueMessagesWaitingFromISR( xISRQueue ) != 0 )
        {
            xReturn = pdFAIL;
        }

        if( xQueueIsQueueEmptyFromISR( xISRQueue ) != pdTRUE )
        {
            xReturn = pdFAIL;
        }

        if( xQueueIsQueueFullFromISR( xISRQueue ) != pdFALSE )
        {
            xReturn = pdFAIL;
        }

        /* Now fill the queue - it only has one space. */
        if( xQueueSendFromISR( xISRQueue, &xValue, NULL ) != pdPASS )
        {
            xReturn = pdFAIL;
        }

        /* Check it now reports as full. */
        if( uxQueueMessagesWaitingFromISR( xISRQueue ) != 1 )
        {
            xReturn = pdFAIL;
        }

        if( xQueueIsQueueEmptyFromISR( xISRQueue ) != pdFALSE )
        {
            xReturn = pdFAIL;
        }

        if( xQueueIsQueueFullFromISR( xISRQueue ) != pdTRUE )
        {
            xReturn = pdFAIL;
        }

        vQueueDelete( xISRQueue );
    }
    else
    {
        xReturn = pdFAIL;
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

static BaseType_t prvTaskQueryFunctions( void )
{
    static TaskStatus_t xStatus, * pxStatusArray;
    TaskHandle_t xTimerTask, xIdleTask;
    BaseType_t xReturn = pdPASS;
    UBaseType_t uxNumberOfTasks, uxReturned, ux;
    uint32_t ulTotalRunTime1, ulTotalRunTime2;
    const uint32_t ulRunTimeTolerance = ( uint32_t ) 0xfff;

    /* Obtain task status with the stack high water mark and without the
     * state. */
    vTaskGetInfo( NULL, &xStatus, pdTRUE, eRunning );

    if( uxTaskGetStackHighWaterMark( NULL ) != xStatus.usStackHighWaterMark )
    {
        xReturn = pdFAIL;
    }

    if( uxTaskGetStackHighWaterMark2( NULL ) != ( configSTACK_DEPTH_TYPE ) xStatus.usStackHighWaterMark )
    {
        xReturn = pdFAIL;
    }

    /* Now obtain a task status without the high water mark but with the state,
     * which in the case of the idle task should be Read. */
    xTimerTask = xTimerGetTimerDaemonTaskHandle();
    vTaskSuspend( xTimerTask ); /* Should never suspend Timer task normally!. */
    vTaskGetInfo( xTimerTask, &xStatus, pdFALSE, eInvalid );

    if( xStatus.eCurrentState != eSuspended )
    {
        xReturn = pdFAIL;
    }

    if( xStatus.uxBasePriority != uxTaskPriorityGetFromISR( xTimerTask ) )
    {
        xReturn = pdFAIL;
    }

    if( xStatus.uxBasePriority != ( configMAX_PRIORITIES - 1 ) )
    {
        xReturn = pdFAIL;
    }

    xTaskResumeFromISR( xTimerTask );
    vTaskGetInfo( xTimerTask, &xStatus, pdTRUE, eInvalid );

    if( ( xStatus.eCurrentState != eReady ) && ( xStatus.eCurrentState != eBlocked ) )
    {
        xReturn = pdFAIL;
    }

    if( uxTaskGetStackHighWaterMark( xTimerTask ) != xStatus.usStackHighWaterMark )
    {
        xReturn = pdFAIL;
    }

    if( uxTaskGetStackHighWaterMark2( xTimerTask ) != ( configSTACK_DEPTH_TYPE ) xStatus.usStackHighWaterMark )
    {
        xReturn = pdFAIL;
    }

    /* Attempting to abort a delay in the idle task should be guaranteed to
     * fail as the idle task should never block. */
    xIdleTask = xTaskGetIdleTaskHandle();

    if( xTaskAbortDelay( xIdleTask ) != pdFAIL )
    {
        xReturn = pdFAIL;
    }

    /* Create an array of task status objects large enough to hold information
     * on the number of tasks at this time - note this may change at any time if
     * higher priority tasks are executing and creating tasks. */
    uxNumberOfTasks = uxTaskGetNumberOfTasks();
    pxStatusArray = ( TaskStatus_t * ) pvPortMalloc( uxNumberOfTasks * sizeof( TaskStatus_t ) );

    if( pxStatusArray != NULL )
    {
        /* Pass part of the array into uxTaskGetSystemState() to ensure it doesn't
         * try using more space than there is available. */
        uxReturned = uxTaskGetSystemState( pxStatusArray, uxNumberOfTasks / ( UBaseType_t ) 2, NULL );

        if( uxReturned != ( UBaseType_t ) 0 )
        {
            xReturn = pdFAIL;
        }

        /* Now do the same but passing in the complete array size, this is done
         * twice to check for a difference in the total run time. */
        uxTaskGetSystemState( pxStatusArray, uxNumberOfTasks, &ulTotalRunTime1 );
        memset( ( void * ) pxStatusArray, 0xaa, uxNumberOfTasks * sizeof( TaskStatus_t ) );
        uxReturned = uxTaskGetSystemState( pxStatusArray, uxNumberOfTasks, &ulTotalRunTime2 );

        if( ( ulTotalRunTime2 - ulTotalRunTime1 ) > ulRunTimeTolerance )
        {
            xReturn = pdFAIL;
        }

        /* Basic sanity check of array contents. */
        for( ux = 0; ux < uxReturned; ux++ )
        {
            if( pxStatusArray[ ux ].eCurrentState >= ( UBaseType_t ) eInvalid )
            {
                xReturn = pdFAIL;
            }

            if( pxStatusArray[ ux ].uxCurrentPriority >= ( UBaseType_t ) configMAX_PRIORITIES )
            {
                xReturn = pdFAIL;
            }
        }

        vPortFree( pxStatusArray );
    }
    else
    {
        xReturn = pdFAIL;
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

static BaseType_t prvDummyTagFunction( void * pvParameter )
{
    return ( BaseType_t ) pvParameter;
}
/*-----------------------------------------------------------*/

static BaseType_t prvTaskTags( void )
{
    BaseType_t xReturn = pdPASS, xParameter = ( BaseType_t ) 0xDEADBEEF;
    TaskHandle_t xTask;

    /* First try with the handle of a different task.  Use the timer task for
     * convenience. */
    xTask = xTimerGetTimerDaemonTaskHandle();

    vTaskSetApplicationTaskTag( xTask, prvDummyTagFunction );

    if( xTaskGetApplicationTaskTag( xTask ) != prvDummyTagFunction )
    {
        xReturn = pdFAIL;
    }
    else
    {
        if( xTaskCallApplicationTaskHook( xTask, ( void * ) xParameter ) != xParameter )
        {
            xReturn = pdFAIL;
        }

        if( xTaskCallApplicationTaskHook( xTask, ( void * ) NULL ) != pdFAIL )
        {
            xReturn = pdFAIL;
        }
    }

    /* Try FromISR version too. */
    if( xTaskGetApplicationTaskTagFromISR( xTask ) != prvDummyTagFunction )
    {
        xReturn = pdFAIL;
    }

    /* Now try with a NULL handle, so using this task. */
    vTaskSetApplicationTaskTag( NULL, NULL );

    if( xTaskGetApplicationTaskTag( NULL ) != NULL )
    {
        xReturn = pdFAIL;
    }

    if( xTaskGetApplicationTaskTagFromISR( NULL ) != NULL )
    {
        xReturn = pdFAIL;
    }

    vTaskSetApplicationTaskTag( NULL, prvDummyTagFunction );

    if( xTaskGetApplicationTaskTag( NULL ) != prvDummyTagFunction )
    {
        xReturn = pdFAIL;
    }
    else
    {
        if( xTaskCallApplicationTaskHook( NULL, ( void * ) xParameter ) != xParameter )
        {
            xReturn = pdFAIL;
        }

        if( xTaskCallApplicationTaskHook( NULL, ( void * ) NULL ) != pdFAIL )
        {
            xReturn = pdFAIL;
        }
    }

    /* Try FromISR version too. */
    if( xTaskGetApplicationTaskTagFromISR( NULL ) != prvDummyTagFunction )
    {
        xReturn = pdFAIL;
    }

    vTaskSetApplicationTaskTag( NULL, NULL );

    if( xTaskGetApplicationTaskTag( NULL ) != NULL )
    {
        xReturn = pdFAIL;
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

static BaseType_t prvTimerQuery( void )
{
    TimerHandle_t xTimer;
    BaseType_t xReturn = pdPASS;
    const char * pcTimerName = "TestTimer";
    const TickType_t xTimerPeriod = ( TickType_t ) 100;
    const UBaseType_t uxTimerNumber = ( UBaseType_t ) 55;

    xTimer = xTimerCreate( pcTimerName,
                           xTimerPeriod,
                           pdFALSE,
                           ( void * ) xTimerPeriod,
                           NULL ); /* Not actually going to start timer so NULL callback is ok. */

    if( xTimer != NULL )
    {
        if( xTimerGetPeriod( xTimer ) != xTimerPeriod )
        {
            xReturn = pdFAIL;
        }

        if( strcmp( pcTimerGetName( xTimer ), pcTimerName ) != 0 )
        {
            xReturn = pdFAIL;
        }

        vTimerSetTimerNumber( xTimer, uxTimerNumber );

        if( uxTimerGetTimerNumber( xTimer ) != uxTimerNumber )
        {
            xReturn = pdFAIL;
        }

        xTimerDelete( xTimer, portMAX_DELAY );
    }
    else
    {
        xReturn = pdFAIL;
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

BaseType_t xRunCodeCoverageTestAdditions( void )
{
    BaseType_t xReturn = pdPASS;

    xReturn &= prvStaticAllocationsWithNullBuffers();
    xReturn &= prvTraceUtils();
    xReturn &= prvPeekTimeout();
    xReturn &= prvQueueQueryFromISR();
    xReturn &= prvTaskQueryFunctions();
    xReturn &= prvTaskTags();
    xReturn &= prvTimerQuery();

    return xReturn;
}
/*-----------------------------------------------------------*/
