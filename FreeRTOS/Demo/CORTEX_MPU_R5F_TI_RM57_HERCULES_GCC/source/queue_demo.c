/*
 * FreeRTOS V202212.00
 * Copyright (C) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

/**
 * @file queue_demo.c
 * @brief Use the Queue APIs to send data from a sender task to a receiver task.
 */

/* Standard includes. */
#include <stdio.h>

/* Kernel includes. */
#include "FreeRTOSConfig.h"
#include "FreeRTOS.h"
#include "task.h"
#include "timers.h"
#include "queue.h"

/* Board Support Package Includes */
#include "sci.h"
#include "reg_system.h"

/* Demo Specific Includes */
#include "demo_tasks.h"

#if( mainDEMO_TYPE & QUEUE_DEMO )

    /* ------------------------------ Demo Task Configs ------------------------------ */

    /** @brief The rate at which data is sent to the queue from the send task.
     * @note Ticks are converted to milliseconds using pdMS_TO_TICKS(). */
    #define queueTASK_SEND_FREQUENCY_MS  pdMS_TO_TICKS( 200UL )

    /** @brief The rate at which data is sent to the queue from the timer.
     * @note Ticks are converted to milliseconds using pdMS_TO_TICKS(). */
    #define queueTIMER_SEND_FREQUENCY_MS pdMS_TO_TICKS( 2000UL )

    /** @brief The number of items the queue can hold at once. */
    #define queueQUEUE_LENGTH            ( 2 )

    /** @brief Value sent from the send task to the receive task */
    #define queueVALUE_SENT_FROM_TASK    ( 0x1234UL )

    /** @brief Value sent from the timer to the receive task */
    #define queueVALUE_SENT_FROM_TIMER   ( 0x4321UL )

/* --------------------- Task Function Declaration --------------------- */

/** @brief Function run by the task that receives data from the queue.
 * @note
 * The queue receive task is implemented by the prvQueueReceiveTask()
 * function in this file. prvQueueReceiveTask() waits for data to arrive on
 * the queue. When data is received, the task checks the value of the data,
 * then outputs a message to indicate if the data came from the queue send
 * task or the queue send software timer. */
static void prvQueueReceiveTask( void * pvParameters );

/** @brief Function run by the task that sends data to a queue.
 * @note
 * The queue send task is implemented by the prvQueueSendTask() function in
 * this file. It uses vTaskDelayUntil() to create a periodic task that
 * sends queueVALUE_SENT_FROM_TASK to the queue every 200 milliseconds. */
static void prvQueueSendTask( void * pvParameters );

/** @brief The callback function executed when the timer expires.
 * @note
 * The timer is an auto-reload timer with a period of two seconds. Its
 * callback function sends the value queueVALUE_SENT_FROM_TIMER to the
 * queue. The callback function is implemented by prvQueueSendTimerCallback().
 */
static void prvQueueSendTimerCallback( TimerHandle_t xTimerHandle );

/*-------------------- Static Task Memory Allocation ------------------- */

/** @brief Statically allocated, and MPU aligned, Queue object */
static StaticQueue_t xStaticQueue __attribute__( ( aligned( 0x80 ) ) );

/** @brief Statically allocated, and MPU aligned, Storage for the Queue */
static uint8_t xQueueStorage[ 0x20 ] __attribute__( ( aligned( 0x80 ) ) );

/** @brief Statically allocated, and MPU aligned, QueueHandle */
static QueueHandle_t xQueue __attribute__( ( aligned( 0x20 ) ) );

/* Each task needs to know the other tasks handle so they can send signals to
 * each other. The handle is obtained from the task's name. */

/** @brief Task name for the queue send task. */
static const char * pcSendTaskName = "SendTaskName";

/** @brief Task name for the queue receive task. */
static const char * pcReceiveTaskName = "ReceiveTaskName";

/** @brief Static MPU aligned stack used by the Queue Send Task */
static StackType_t xQueueSendTaskStack[ configMINIMAL_STACK_SIZE / 2U ]
    __attribute__( ( aligned( configMINIMAL_STACK_SIZE * 0x2U ) ) );

/** @brief Static TCB Used by the Queue Send Task */
PRIVILEGED_DATA static StaticTask_t xQueueSendTaskTCB;

/** @brief Static MPU aligned stack used by the Queue Receive Task */
static StackType_t xQueueReceiveTaskStack[ configMINIMAL_STACK_SIZE / 2U ]
    __attribute__( ( aligned( configMINIMAL_STACK_SIZE * 0x2U ) ) );

/** @brief Static TCB Used by the Queue Receive Task */
PRIVILEGED_DATA static StaticTask_t xQueueReceiveTaskTCB;

/** @brief A software timer that is started from the tick hook. */
static TimerHandle_t xTimer = NULL;

/** @brief Statically allocated timer object. */
static StaticTimer_t xStaticTimer;

/** @brief Statically allocated task handle for the queue receive task. */
static TaskHandle_t xReceiveTaskHandle;

/** @brief Statically allocated task handle for the queue send task. */
static TaskHandle_t xSendTaskHandle;

/* ------------------------------------------------------------------------------------ */

BaseType_t prvCreateQueueTasks( void )
{
    /* Declaration when these variable are exported from linker scripts. */
    extern uint32_t __peripherals_start__[];
    extern uint32_t __peripherals_end__[];

    uint32_t ulPeriphRegionStart = ( uint32_t ) __peripherals_start__;
    uint32_t ulPeriphRegionSize = ( uint32_t ) __peripherals_end__ - ulPeriphRegionStart;
    uint32_t ulPeriphRegionAttr = portMPU_REGION_PRIV_RW_USER_RW_NOEXEC | portMPU_REGION_DEVICE_SHAREABLE;

    BaseType_t xReturn = pdPASS;

    uint32_t ulRegionAttr = portMPU_REGION_PRIV_RW_USER_RW_NOEXEC
                          | portMPU_REGION_NORMAL_OIWTNOWA_SHARED;

    /* Start the two tasks as described in the comments at the top of this file. */
    TaskParameters_t
        xQueueReceiveTaskParameters = { .pvTaskCode = prvQueueReceiveTask,
                                        .pcName = pcReceiveTaskName,
                                        .usStackDepth = configMINIMAL_STACK_SIZE / 2U,
                                        .pvParameters = NULL,
                                        .uxPriority = demoQUEUE_RECEIVE_TASK_PRIORITY,
                                        .puxStackBuffer = xQueueReceiveTaskStack,
                                        .pxTaskBuffer = &xQueueReceiveTaskTCB,
                                        .xRegions = {
                                            /* First Configurable Region 0 */
                                            { ( void * ) &xStaticQueue,
                                              ( uint32_t ) sizeof( StaticQueue_t ),
                                              ulRegionAttr },
                                            /* Region 1 */
                                            { ( void * ) &xQueueStorage,
                                              ( uint32_t ) sizeof( xQueueStorage ),
                                              ulRegionAttr },
                                            /* Region 2 */
                                            { ( void * ) &xQueue,
                                              ( uint32_t ) sizeof( QueueHandle_t ),
                                              ulRegionAttr },
                                            /* Region 3 */
                                            { 0, 0, 0 },
                                            /* Region 4 */
                                            { 0, 0, 0 },
                                            /* Region 5 */
                                            { 0, 0, 0 },
                                            /* Region 6 */
                                            { 0, 0, 0 },
    #if( configTOTAL_MPU_REGIONS == 16 )
                                            /* Region 7 */
                                            { 0, 0, 0 },
                                            /* Region 8 */
                                            { 0, 0, 0 },
                                            /* Region 9 */
                                            { 0, 0, 0 },
                                            /* Region 10 */
                                            { 0, 0, 0 },
    #endif /* configTOTAL_MPU_REGIONS == 16 */
                                            /* Last Configurable MPU Region */
                                            { ( void * ) ulPeriphRegionStart,
                                              ulPeriphRegionSize,
                                              ulPeriphRegionAttr },
                                        } };

    TaskParameters_t
        xQueueSendTaskParameters = { .pvTaskCode = prvQueueSendTask,
                                     .pcName = pcSendTaskName,
                                     .usStackDepth = configMINIMAL_STACK_SIZE / 2U,
                                     .pvParameters = NULL,
                                     .uxPriority = demoQUEUE_SEND_TASK_PRIORITY,
                                     .puxStackBuffer = xQueueSendTaskStack,
                                     .pxTaskBuffer = &xQueueSendTaskTCB,
                                     .xRegions = {
                                         /* First Configurable Region 0 */
                                         { ( void * ) &xStaticQueue,
                                           ( uint32_t ) sizeof( StaticQueue_t ),
                                           ulRegionAttr },
                                         /* Region 1 */
                                         { ( void * ) &xQueueStorage,
                                           ( uint32_t ) sizeof( xQueueStorage ),
                                           ulRegionAttr },
                                         /* Region 2 */
                                         { ( void * ) &xQueue,
                                           ( uint32_t ) sizeof( QueueHandle_t ),
                                           ulRegionAttr },
                                         /* Region 3 */
                                         { 0, 0, 0 },
                                         /* Region 4 */
                                         { 0, 0, 5 },
                                         /* Region 5 */
                                         { 0, 0, 0 },
                                         /* Region 6 */
                                         { 0, 0, 0 },
    #if( configTOTAL_MPU_REGIONS == 16 )
                                         /* Region 7 */
                                         { 0, 0, 0 },
                                         /* Region 8 */
                                         { 0, 0, 0 },
                                         /* Region 9 */
                                         { 0, 0, 0 },
                                         /* Region 10 */
                                         { 0, 0, 0 },
    #endif /* configTOTAL_MPU_REGIONS == 16 */
                                         /* Last Configurable MPU Region */
                                         { ( void * ) ulPeriphRegionStart,
                                           ulPeriphRegionSize,
                                           ulPeriphRegionAttr },
                                     } };

    /* Create an unprivileged task with RO access to ucSharedMemory. */
    xReturn = xTaskCreateRestrictedStatic( &( xQueueReceiveTaskParameters ),
                                           &( xReceiveTaskHandle ) );

    if( pdPASS == xReturn )
    {
        sci_print( "Created the Queue Receive Task\r\n" );
        /* Create an unprivileged task with RW access to ucSharedMemory. */
        xReturn = xTaskCreateRestrictedStatic( &( xQueueSendTaskParameters ),
                                               &xSendTaskHandle );
        if( pdPASS == xReturn )
        {
            sci_print( "Created the Queue Send Task\r\n" );
        }
        else
        {
            sci_print( "Failed to create the Queue Receive Task\r\n" );
            xReturn = pdFAIL;
        }
    }
    else
    {
        sci_print( "Failed to create the Queue Receive Task\r\n" );
        xReturn = pdFAIL;
    }
    return xReturn;
}

BaseType_t xCreateQueueTasks( void )
{
    BaseType_t xReturn = pdPASS;

    /* The Receive Task MUST be a higher priority than the send task. */
    configASSERT( demoQUEUE_RECEIVE_TASK_PRIORITY > demoQUEUE_SEND_TASK_PRIORITY );

    /* Create the queue used by the queue tasks . */
    xQueue = xQueueCreateStatic( queueQUEUE_LENGTH,
                                 sizeof( uint32_t ),
                                 xQueueStorage,
                                 &xStaticQueue );

    if( xQueue != NULL )
    {
        sci_print( "Created the Queue for the tasks\r\n" );

        /** @brief The debugging text name for the timer */
        const char * pcTimerName = "Timer";
        /** @brief Mark that this is an auto-reload timer. */
        const BaseType_t xAutoReload = ( BaseType_t ) pdTRUE;
        /** @brief Timer ID that is not used in this demo. */
        void * const pvTimerID = NULL;
        /** @brief Callback function for the timer */
        TimerCallbackFunction_t pxCallbackFunction = prvQueueSendTimerCallback;

        /* Create a statically allocated timer */
        xTimer = xTimerCreateStatic( pcTimerName,
                                     ( const TickType_t ) queueTIMER_SEND_FREQUENCY_MS,
                                     xAutoReload,
                                     pvTimerID,
                                     pxCallbackFunction,
                                     &( xStaticTimer ) );
    }
    else
    {
        sci_print( "Failed to create the Queue for the tasks\r\n" );
        xReturn = pdFAIL;
    }

    if( NULL != xTimer )
    {
        sci_print( "Created the Queue Timer\r\n" );
    }
    else
    {
        sci_print( "Failed to create the Queue Timer\r\n" );
        xReturn = pdFAIL;
    }

    if( pdPASS == xReturn )
    {
        xReturn = prvCreateQueueTasks();
    }
    else
    {
        xReturn = pdFAIL;
    }

    if( pdPASS == xReturn )
    {
        /* Use an Access Control List to allow the tasks to use this queue */
        vGrantAccessToQueue( xReceiveTaskHandle, xQueue );
        vGrantAccessToQueue( xSendTaskHandle, xQueue );

        /* The scheduler has not started so use a block time of 0. */
        xReturn = xTimerStart( xTimer, 0 );
    }
    else
    {
        xReturn = pdFAIL;
    }

    if( pdPASS == xReturn )
    {
        sci_print( "Started the Timer\r\n" );
    }
    else
    {
        sci_print( "Failed to start the Queue Timer\r\n" );
    }

    return xReturn;
}

/*-----------------------------------------------------------------------*/

static void prvQueueSendTask( void * pvParameters )
{
    TickType_t xNextWakeTime;
    const TickType_t xBlockTime = queueTASK_SEND_FREQUENCY_MS;
    const uint32_t ulValueToSend = queueVALUE_SENT_FROM_TASK;
    /* Prevent the compiler warning about the unused parameter. */
    ( void ) pvParameters;

    /* Initialise xNextWakeTime - this only needs to be done once. */
    xNextWakeTime = xTaskGetTickCount();

    for( ;; )
    {
        /* Move this task to the blocked state for xBlockTime milliseconds.
         * The block time is specified in ticks, pdMS_TO_TICKS() was used to
         * convert a time specified in milliseconds into a time specified in
         * ticks. While in the Blocked state this task will not consume any
         * CPU time. */
        xTaskDelayUntil( &xNextWakeTime, xBlockTime );

        /* Send to the queue - causing the queue receive task to unblock
         * and write to the console. 0 is used as the block time so the send
         * operation will not block. It shouldn't need to block as the queue
         * should always have at least one space at this point in the code.
         */
        xQueueSend( xQueue, &ulValueToSend, 0U );
    }
}

/*-----------------------------------------------------------------------*/

static void prvQueueSendTimerCallback( TimerHandle_t xTimerHandle )
{
    const uint32_t ulValueToSend = queueVALUE_SENT_FROM_TIMER;

    /* This is the software timer callback function. The software timer has
     * a period of two seconds. This callback function will execute if the
     * timer expires, which will happen every two seconds. */

    /* Avoid compiler warnings resulting from the unused parameter. */
    ( void ) xTimerHandle;

    /* Send to the queue - causing the queue receive task to unblock and
     * write out a message. This function is called from the timer/daemon
     * task, so must not block. Hence the block time is set to 0. */
    xQueueSend( xQueue, &ulValueToSend, 0U );
}

/*-----------------------------------------------------------------------*/

static void prvQueueReceiveTask( void * pvParameters )
{
    uint32_t ulReceivedValue = 0;
    /* Prevent the compiler warning about the unused parameter. */
    ( void ) pvParameters;

    for( ;; )
    {
        /* Wait until something arrives in the queue - this task will block
         * indefinitely provided INCLUDE_vTaskSuspend is set to 1 in
         * FreeRTOSConfig.h. It will not use any CPU time while it is in the
         * Blocked state. */
        xQueueReceive( xQueue, &ulReceivedValue, portMAX_DELAY );

        /* To get here something must have been received from the queue,
         * but is it an expected value? */
        if( ulReceivedValue == queueVALUE_SENT_FROM_TASK )
        {
            vToggleLED( 0x0 );
        }
        else if( ulReceivedValue == queueVALUE_SENT_FROM_TIMER )
        {
            vToggleLED( 0x1 );
        }
        else
        {
            /* Invalid value received. Force an assert. */
            configASSERT( ulReceivedValue == !ulReceivedValue );
        }
    }
}
/* --------------------------------------------------------------------- */

#endif /* ( mainDEMO_TYPE & QUEUE_DEMO ) */
