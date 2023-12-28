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
 * This file contains some test scenarios that ensure tasks respond correctly
 * to xTaskAbortDelay() calls.  It also ensures tasks return the correct state
 * of eBlocked when blocked indefinitely in both the case where a task is
 * blocked on an object and when a task is blocked on a notification.
 */

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"
#include "event_groups.h"

/* Board Includes */
#include "sci.h"

/* Demo includes */
#include "demo_tasks.h"

/* This file can only be used if the functionality it tests is included in the
 * build.  Remove the whole file if this is not the case. */
#if( INCLUDE_xTaskAbortDelay == 1 )

    #if( INCLUDE_xTaskGetHandle != 1 )
        #error This test file uses the xTaskGetHandle() API function so INCLUDE_xTaskGetHandle must be set to 1 in FreeRTOSConfig.h.
    #endif

/* Task priorities.  Allow these to be overridden. */
    #ifndef abtCONTROLLING_PRIORITY
        #define abtCONTROLLING_PRIORITY ( configMAX_PRIORITIES - 3 )
    #endif

    #ifndef abtBLOCKING_PRIORITY
        #define abtBLOCKING_PRIORITY ( configMAX_PRIORITIES - 2 )
    #endif

/* The tests that are performed. */
    #define abtNOTIFY_WAIT_ABORTS    0
    #define abtNOTIFY_TAKE_ABORTS    1
    #define abtDELAY_ABORTS          2
    #define abtDELAY_UNTIL_ABORTS    3
    #define abtSEMAPHORE_TAKE_ABORTS 4
    #define abtEVENT_GROUP_ABORTS    5
    #define abtQUEUE_SEND_ABORTS     6
    #define abtSTREAM_BUFFER_RECEIVE 7
    #define abtMAX_TESTS             8

/*-----------------------------------------------------------*/

/*
 * The two test tasks.  The controlling task specifies which test to executed.
 * More information is provided in the comments within the tasks.
 */
static void prvControllingTask( void * pvParameters );
static void prvBlockingTask( void * pvParameters );

/*
 * Test functions called by the blocking task.  Each function follows the same
 * pattern, but the way the task blocks is different in each case.
 *
 * In each function three blocking calls are made.  The first and third
 * blocking call is expected to time out, while the middle blocking call is
 * expected to be aborted by the controlling task half way through the block
 * time.
 */
static void prvTestAbortingTaskNotifyWait( void );
static void prvTestAbortingTaskNotifyTake( void );
static void prvTestAbortingTaskDelay( void );
static void prvTestAbortingTaskDelayUntil( void );
static void prvTestAbortingSemaphoreTake( void );
static void prvTestAbortingEventGroupWait( void );
static void prvTestAbortingQueueSend( void );
static void prvTestAbortingStreamBufferReceive( void );

/*
 * Performs a few tests to cover code paths not otherwise covered by the continuous
 * tests.
 */
static void prvPerformSingleTaskTests( void );

/*
 * Checks the amount of time a task spent in the Blocked state is within the
 * expected bounds.
 */
static void prvCheckExpectedTimeIsWithinAnAcceptableMargin(
    TickType_t xStartTime,
    TickType_t xExpectedBlockTime
);

/*-----------------------------------------------------------*/

typedef struct AbortDelayData
{
    /* Used to ensure that tasks are still executing without error. */
    volatile BaseType_t xControllingCycles;
    volatile BaseType_t xBlockingCycles;
    volatile BaseType_t xErrorOccurred;

    /* Each task needs to know the other tasks handle so they can send signals to
     * each other.  The handle is obtained from the task's name. */
    const char pcControllingTaskName[ configMAX_TASK_NAME_LEN ];
    const char pcBlockingTaskName[ configMAX_TASK_NAME_LEN ];

    /* The maximum amount of time a task will block for. */
    const TickType_t xMaxBlockTime;
    const TickType_t xHalfMaxBlockTime;

    /* The actual block time is dependent on the priority of other tasks in the
     * system so the actual block time might be greater than that expected, but it
     * should be within an acceptable upper bound. */
    const TickType_t xAllowableMargin;
} AbortDelayData_t;

static AbortDelayData_t AbortData __attribute__( ( aligned( 0x200 ) ) ) = {
    /* Used to ensure that tasks are still executing without error. */
    .xControllingCycles = 0U,
    .xBlockingCycles = 0U,
    .xErrorOccurred = pdFALSE,

    /* Each task needs to know the other tasks handle so they can send signals to
     * each other.  The handle is obtained from the task's name. */
    .pcControllingTaskName = "AbtCtrl",
    .pcBlockingTaskName = "AbtBlk",

    /* The maximum amount of time a task will block for. */
    .xMaxBlockTime = pdMS_TO_TICKS( 100U ),
    .xHalfMaxBlockTime = pdMS_TO_TICKS( 50U ),

    /* The actual block time is dependent on the priority of other tasks in the
     * system so the actual block time might be greater than that expected, but it
     * should be within an acceptable upper bound. */
    .xAllowableMargin = pdMS_TO_TICKS( 7U ),
};

/*---------------------------------------------------------------------------*/

/** Statically declare the TCBs and Stacks for the stacks */
PRIVILEGED_DATA static StaticTask_t xControllingTaskTCB;
static StackType_t xControllingTaskStack[ configMINIMAL_STACK_SIZE ]
    __attribute__( ( aligned( configMINIMAL_STACK_SIZE * 0x4U ) ) );

PRIVILEGED_DATA static StaticTask_t xBlockingTaskTCB;
static StackType_t xBlockingTaskStack[ configMINIMAL_STACK_SIZE ]
    __attribute__( ( aligned( configMINIMAL_STACK_SIZE * 0x4U ) ) );

static TaskHandle_t controllingTaskHandle;

static TaskHandle_t blockingTaskHandle;

/*-----------------------------------------------------------*/

void vCreateAbortDelayTasks( void )
{
    uint32_t retVal = 0U;
    #if 0
    /* Used to ensure that tasks are still executing without error. */
    AbortData.xControllingCycles = 0U;
    AbortData.xBlockingCycles = 0U;
    AbortData.xErrorOccurred = pdFALSE;

/* Each task needs to know the other tasks handle so they can send signals to
 * each other.  The handle is obtained from the task's name. */
    AbortData.pcControllingTaskName = "AbtCtrl";
    AbortData.pcBlockingTaskName = "AbtBlk";

/* The maximum amount of time a task will block for. */
    AbortData.xMaxBlockTime = pdMS_TO_TICKS( 100U );
    AbortData.xHalfMaxBlockTime = pdMS_TO_TICKS( 50U );

/* The actual block time is dependent on the priority of other tasks in the
 * system so the actual block time might be greater than that expected, but it
 * should be within an acceptable upper bound. */
    AbortData.xAllowableMargin = pdMS_TO_TICKS( 7U );
    #endif
    /* Create the two test tasks described above. */
    TaskParameters_t
        xControllingTaskParameters = { .pvTaskCode = prvControllingTask,
                                       .pcName = AbortData.pcControllingTaskName,
                                       .usStackDepth = configMINIMAL_STACK_SIZE,
                                       .pvParameters = NULL,
                                       .uxPriority = abtCONTROLLING_PRIORITY,
                                       .puxStackBuffer = xControllingTaskStack,
                                       .pxTaskBuffer = &xControllingTaskTCB,
                                       .xRegions = {
                                           /* First Configurable Region 5 */
                                           { ( void * ) &AbortData,
                                             ( uint32_t ) sizeof( AbortDelayData_t ),
                                             portMPU_REGION_EXECUTE_NEVER |
                                                 portMPU_REGION_READ_WRITE |
                                                 portMPU_NORMAL_OIWTNOWA_SHARED },
                                           /* Region 6 */
                                           { 0, 0, 0 },
                                           /* Region 7 */
                                           { 0, 0, 0 },
                                           /* Region 8 */
                                           { 0, 0, 0 },
                                           /* Region 9 */
                                           { 0, 0, 0 },
    #if( configTOTAL_MPU_REGIONS == 16 )
                                           /* Region 10 */
                                           { 0, 0, 0 },
                                           /* Region 11 */
                                           { 0, 0, 0 },
                                           /* Region 12 */
                                           { 0, 0, 0 },
                                           /* Region 13 */
                                           { 0, 0, 0 },
    #endif /* configTOTAL_MPU_REGIONS == 16 */
                                           /* Last Configurable Region */
                                           { 0, 0, 0 },
                                       } };
    TaskParameters_t
        xBlockingTaskParameters = { .pvTaskCode = prvBlockingTask,
                                    .pcName = AbortData.pcBlockingTaskName,
                                    .usStackDepth = configMINIMAL_STACK_SIZE,
                                    .pvParameters = NULL,
                                    .uxPriority = abtBLOCKING_PRIORITY,
                                    .puxStackBuffer = xBlockingTaskStack,
                                    .pxTaskBuffer = &xBlockingTaskTCB,
                                    .xRegions = {
                                        /* First Configurable Region 5 */
                                        { ( void * ) &AbortData,
                                          ( uint32_t ) sizeof( AbortDelayData_t ),
                                          portMPU_REGION_EXECUTE_NEVER |
                                              portMPU_REGION_READ_WRITE |
                                              portMPU_NORMAL_OIWTNOWA_SHARED },
                                        /* Region 6 */
                                        { 0, 0, 0 },
                                        /* Region 7 */
                                        { 0, 0, 0 },
                                        /* Region 8 */
                                        { 0, 0, 0 },
                                        /* Region 9 */
                                        { 0, 0, 0 },
    #if( configTOTAL_MPU_REGIONS == 16 )
                                        /* Region 10 */
                                        { 0, 0, 0 },
                                        /* Region 11 */
                                        { 0, 0, 0 },
                                        /* Region 12 */
                                        { 0, 0, 0 },
                                        /* Region 13 */
                                        { 0, 0, 0 },
    #endif /* configTOTAL_MPU_REGIONS == 16 */
                                        /* Last Configurable Region */
                                        { 0, 0, 0 },
                                    } };

    /* Create an unprivileged task with RO access to ucSharedMemory. */
    retVal = xTaskCreateRestrictedStatic(
        &( xControllingTaskParameters ),
        &controllingTaskHandle
    );
    configASSERT( retVal );

    /* Create an unprivileged task with RO access to ucSharedMemory. */
    retVal =
        xTaskCreateRestrictedStatic( &( xBlockingTaskParameters ), &blockingTaskHandle );
    configASSERT( retVal );
}
/*-----------------------------------------------------------*/

static void prvControllingTask( void * pvParameters )
{
    TaskHandle_t xBlockingTask;
    uint32_t ulTestToPerform = abtNOTIFY_WAIT_ABORTS;
    TickType_t xTimeAtStart;
    const TickType_t xStartMargin = 2UL;

    /* Just to remove compiler warnings. */
    ( void ) pvParameters;

    xBlockingTask = xTaskGetHandle( AbortData.pcBlockingTaskName );
    configASSERT( xBlockingTask );

    for( ;; )
    {
        /* Tell the secondary task to perform the next test. */
        xTimeAtStart = xTaskGetTickCount();
        xTaskNotify( xBlockingTask, ulTestToPerform, eSetValueWithOverwrite );

        /* The secondary task has a higher priority, so will now be in the
         * Blocked state to wait for a maximum of xMaxBlockTime.  It expects that
         * period to complete with a timeout.  It will then block for
         * xMaxBlockTimeAgain, but this time it expects to the block time to abort
         * half way through.  Block until it is time to send the abort to the
         * secondary task.  xStartMargin is used because this task takes timing
         * from the beginning of the test, whereas the blocking task takes timing
         * from the entry into the Blocked state - and as the tasks run at
         * different priorities, there may be some discrepancy.  Also, temporarily
         * raise the priority of the controlling task to that of the blocking
         * task to minimise discrepancies. */
        vTaskPrioritySet( NULL, abtBLOCKING_PRIORITY );
        vTaskDelay( AbortData.xMaxBlockTime + AbortData.xHalfMaxBlockTime + xStartMargin );

        if( xTaskAbortDelay( xBlockingTask ) != pdPASS )
        {
            AbortData.xErrorOccurred = pdTRUE;
        }

        /* Reset the priority to the normal controlling priority. */
        vTaskPrioritySet( NULL, abtCONTROLLING_PRIORITY );

        /* Now wait to be notified that the secondary task has completed its
         * test. */
        ulTaskNotifyTake( pdTRUE, portMAX_DELAY );

        /* Did the entire test run for the expected time, which is two full
         * block times plus the half block time caused by calling
         * xTaskAbortDelay()? */
        prvCheckExpectedTimeIsWithinAnAcceptableMargin(
            xTimeAtStart,
            ( AbortData.xMaxBlockTime + AbortData.xMaxBlockTime +
              AbortData.xHalfMaxBlockTime )
        );

        /* Move onto the next test. */
        ulTestToPerform++;

        if( ulTestToPerform >= abtMAX_TESTS )
        {
            ulTestToPerform = 0;
        }

        /* To indicate this task is still executing. */
        AbortData.xControllingCycles++;
    }
}
/*-----------------------------------------------------------*/

static void prvBlockingTask( void * pvParameters )
{
    TaskHandle_t xControllingTask;
    uint32_t ulNotificationValue;
    const uint32_t ulMax = 0xffffffffUL;

    /* Just to remove compiler warnings. */
    ( void ) pvParameters;

    /* Start by performing a few tests to cover code not exercised in the loops
     * below. */
    prvPerformSingleTaskTests();

    xControllingTask = xTaskGetHandle( AbortData.pcControllingTaskName );
    configASSERT( xControllingTask );

    for( ;; )
    {
        /* Wait to be notified of the test that is to be performed next. */
        xTaskNotifyWait( 0, ulMax, &ulNotificationValue, portMAX_DELAY );

        switch( ulNotificationValue )
        {
            case abtNOTIFY_WAIT_ABORTS:
                prvTestAbortingTaskNotifyWait();
                break;

            case abtNOTIFY_TAKE_ABORTS:
                prvTestAbortingTaskNotifyTake();
                break;

            case abtDELAY_ABORTS:
                prvTestAbortingTaskDelay();
                break;

            case abtDELAY_UNTIL_ABORTS:
                prvTestAbortingTaskDelayUntil();
                break;

            case abtSEMAPHORE_TAKE_ABORTS:
                prvTestAbortingSemaphoreTake();
                break;

            case abtEVENT_GROUP_ABORTS:
                prvTestAbortingEventGroupWait();
                break;

            case abtQUEUE_SEND_ABORTS:
                prvTestAbortingQueueSend();
                break;

            case abtSTREAM_BUFFER_RECEIVE:
                prvTestAbortingStreamBufferReceive();
                break;

            default:
                /* Should not get here. */
                break;
        }

        /* Let the primary task know the test is complete. */
        xTaskNotifyGive( xControllingTask );

        /* To indicate this task is still executing. */
        AbortData.xBlockingCycles++;
    }
}
/*-----------------------------------------------------------*/

static void prvPerformSingleTaskTests( void )
{
    TaskHandle_t xThisTask;
    BaseType_t xReturned;

    /* Try unblocking this task using both the task and ISR versions of the API -
     * both should return false as this task is not blocked. */
    xThisTask = xTaskGetCurrentTaskHandle();

    xReturned = xTaskAbortDelay( xThisTask );

    if( xReturned != pdFALSE )
    {
        AbortData.xErrorOccurred = pdTRUE;
    }
}
/*-----------------------------------------------------------*/

static void prvTestAbortingTaskDelayUntil( void )
{
    TickType_t xTimeAtStart, xLastBlockTime;
    BaseType_t xReturned;

    /* Note the time before the delay so the length of the delay is known. */
    xTimeAtStart = xTaskGetTickCount();

    /* Take a copy of the time as it is updated in the call to
     * xTaskDelayUntil() but its original value is needed to determine the actual
     * time spend in the Blocked state. */
    xLastBlockTime = xTimeAtStart;

    /* This first delay should just time out. */
    xReturned = xTaskDelayUntil( &xLastBlockTime, AbortData.xMaxBlockTime );
    prvCheckExpectedTimeIsWithinAnAcceptableMargin(
        xTimeAtStart,
        AbortData.xMaxBlockTime
    );
    configASSERT( xReturned == pdTRUE );

    /* Remove compiler warning about value being set but not used in the case
     * configASSERT() is not defined. */
    ( void ) xReturned;

    /* This second delay should be aborted by the primary task half way
     * through.  Again take a copy of the time as it is updated in the call to
     * vTaskDelayUntil() buts its original value is needed to determine the amount
     * of time actually spent in the Blocked state.  This uses vTaskDelayUntil()
     * in place of xTaskDelayUntil() for test coverage. */
    xTimeAtStart = xTaskGetTickCount();
    xLastBlockTime = xTimeAtStart;
    xTaskDelayUntil( &xLastBlockTime, AbortData.xMaxBlockTime );
    prvCheckExpectedTimeIsWithinAnAcceptableMargin(
        xTimeAtStart,
        AbortData.xHalfMaxBlockTime
    );

    /* As with the other tests, the third block period should not time out. */
    xTimeAtStart = xTaskGetTickCount();
    xLastBlockTime = xTimeAtStart;
    xReturned = xTaskDelayUntil( &xLastBlockTime, AbortData.xMaxBlockTime );
    prvCheckExpectedTimeIsWithinAnAcceptableMargin(
        xTimeAtStart,
        AbortData.xMaxBlockTime
    );
    configASSERT( xReturned == pdTRUE );

    /* Remove compiler warning about value being set but not used in the case
     * configASSERT() is not defined. */
    ( void ) xReturned;
}
/*-----------------------------------------------------------*/

static void prvTestAbortingTaskDelay( void )
{
    TickType_t xTimeAtStart;

    /* Note the time before the delay so the length of the delay is known. */
    xTimeAtStart = xTaskGetTickCount();

    /* This first delay should just time out. */
    vTaskDelay( AbortData.xMaxBlockTime );
    prvCheckExpectedTimeIsWithinAnAcceptableMargin(
        xTimeAtStart,
        AbortData.xMaxBlockTime
    );

    /* Note the time before the delay so the length of the delay is known. */
    xTimeAtStart = xTaskGetTickCount();

    /* This second delay should be aborted by the primary task half way
     * through. */
    vTaskDelay( AbortData.xMaxBlockTime );
    prvCheckExpectedTimeIsWithinAnAcceptableMargin(
        xTimeAtStart,
        AbortData.xHalfMaxBlockTime
    );

    /* Note the time before the delay so the length of the delay is known. */
    xTimeAtStart = xTaskGetTickCount();

    /* This third delay should just time out again. */
    vTaskDelay( AbortData.xMaxBlockTime );
    prvCheckExpectedTimeIsWithinAnAcceptableMargin(
        xTimeAtStart,
        AbortData.xMaxBlockTime
    );
}
/*-----------------------------------------------------------*/

static void prvTestAbortingTaskNotifyTake( void )
{
    TickType_t xTimeAtStart;
    uint32_t ulReturn;

    /* Note the time before the delay so the length of the delay is known. */
    xTimeAtStart = xTaskGetTickCount();

    /* This first delay should just time out. */
    ulReturn = ulTaskNotifyTake( pdFALSE, AbortData.xMaxBlockTime );

    if( ulReturn != 0 )
    {
        AbortData.xErrorOccurred = pdTRUE;
    }

    prvCheckExpectedTimeIsWithinAnAcceptableMargin(
        xTimeAtStart,
        AbortData.xMaxBlockTime
    );

    /* Note the time before the delay so the length of the delay is known. */
    xTimeAtStart = xTaskGetTickCount();

    /* This second delay should be aborted by the primary task half way
     * through. */
    ulReturn = ulTaskNotifyTake( pdFALSE, AbortData.xMaxBlockTime );

    if( ulReturn != 0 )
    {
        AbortData.xErrorOccurred = pdTRUE;
    }

    prvCheckExpectedTimeIsWithinAnAcceptableMargin(
        xTimeAtStart,
        AbortData.xHalfMaxBlockTime
    );

    /* Note the time before the delay so the length of the delay is known. */
    xTimeAtStart = xTaskGetTickCount();

    /* This third delay should just time out again. */
    ulReturn = ulTaskNotifyTake( pdFALSE, AbortData.xMaxBlockTime );

    if( ulReturn != 0 )
    {
        AbortData.xErrorOccurred = pdTRUE;
    }

    prvCheckExpectedTimeIsWithinAnAcceptableMargin(
        xTimeAtStart,
        AbortData.xMaxBlockTime
    );
}
/*-----------------------------------------------------------*/

static void prvTestAbortingEventGroupWait( void )
{
    TickType_t xTimeAtStart;
    EventGroupHandle_t xEventGroup;
    EventBits_t xBitsToWaitFor = ( EventBits_t ) 0x01, xReturn;

    #if( configSUPPORT_STATIC_ALLOCATION == 1 )
    {
        static StaticEventGroup_t xEventGroupBuffer;

        /* Create the event group.  Statically allocated memory is used so the
         * creation cannot fail. */
        xEventGroup = xEventGroupCreateStatic( &xEventGroupBuffer );
    }
    #else
    {
        xEventGroup = xEventGroupCreate();
        configASSERT( xEventGroup );
    }
    #endif /* if ( configSUPPORT_STATIC_ALLOCATION == 1 ) */

    /* Note the time before the delay so the length of the delay is known. */
    xTimeAtStart = xTaskGetTickCount();

    /* This first delay should just time out. */
    xReturn = xEventGroupWaitBits(
        xEventGroup,
        xBitsToWaitFor,
        pdTRUE,
        pdTRUE,
        AbortData.xMaxBlockTime
    );

    if( xReturn != 0x00 )
    {
        AbortData.xErrorOccurred = pdTRUE;
    }

    prvCheckExpectedTimeIsWithinAnAcceptableMargin(
        xTimeAtStart,
        AbortData.xMaxBlockTime
    );

    /* Note the time before the delay so the length of the delay is known. */
    xTimeAtStart = xTaskGetTickCount();

    /* This second delay should be aborted by the primary task half way
     * through. */
    xReturn = xEventGroupWaitBits(
        xEventGroup,
        xBitsToWaitFor,
        pdTRUE,
        pdTRUE,
        AbortData.xMaxBlockTime
    );

    if( xReturn != 0x00 )
    {
        AbortData.xErrorOccurred = pdTRUE;
    }

    prvCheckExpectedTimeIsWithinAnAcceptableMargin(
        xTimeAtStart,
        AbortData.xHalfMaxBlockTime
    );

    /* Note the time before the delay so the length of the delay is known. */
    xTimeAtStart = xTaskGetTickCount();

    /* This third delay should just time out again. */
    xReturn = xEventGroupWaitBits(
        xEventGroup,
        xBitsToWaitFor,
        pdTRUE,
        pdTRUE,
        AbortData.xMaxBlockTime
    );

    if( xReturn != 0x00 )
    {
        AbortData.xErrorOccurred = pdTRUE;
    }

    prvCheckExpectedTimeIsWithinAnAcceptableMargin(
        xTimeAtStart,
        AbortData.xMaxBlockTime
    );

    /* Not really necessary in this case, but for completeness. */
    vEventGroupDelete( xEventGroup );
}
/*-----------------------------------------------------------*/

static void prvTestAbortingStreamBufferReceive( void )
{
    TickType_t xTimeAtStart;
    StreamBufferHandle_t xStreamBuffer;
    size_t xReturn;
    const size_t xTriggerLevelBytes = ( size_t ) 1;
    uint8_t uxRxData;

    #if( configSUPPORT_STATIC_ALLOCATION == 1 )
    {
        /* Defines the memory that will actually hold the streams within the
         * stream buffer. */
        static uint8_t ucStorageBuffer[ sizeof( configMESSAGE_BUFFER_LENGTH_TYPE ) + 1 ];

        /* The variable used to hold the stream buffer structure. */
        StaticStreamBuffer_t xStreamBufferStruct;

        xStreamBuffer = xStreamBufferCreateStatic(
            sizeof( ucStorageBuffer ),
            xTriggerLevelBytes,
            ucStorageBuffer,
            &xStreamBufferStruct
        );
    }
    #else  /* if ( configSUPPORT_STATIC_ALLOCATION == 1 ) */
    {
        xStreamBuffer = xStreamBufferCreate( sizeof( uint8_t ), xTriggerLevelBytes );
        configASSERT( xStreamBuffer );
    }
    #endif /* if ( configSUPPORT_STATIC_ALLOCATION == 1 ) */

    /* Note the time before the delay so the length of the delay is known. */
    xTimeAtStart = xTaskGetTickCount();

    /* This first delay should just time out. */
    xReturn = xStreamBufferReceive(
        xStreamBuffer,
        &uxRxData,
        sizeof( uxRxData ),
        AbortData.xMaxBlockTime
    );

    if( xReturn != 0x00 )
    {
        AbortData.xErrorOccurred = pdTRUE;
    }

    prvCheckExpectedTimeIsWithinAnAcceptableMargin(
        xTimeAtStart,
        AbortData.xMaxBlockTime
    );

    /* Note the time before the delay so the length of the delay is known. */
    xTimeAtStart = xTaskGetTickCount();

    /* This second delay should be aborted by the primary task half way
     * through xMaxBlockTime. */
    xReturn = xStreamBufferReceive(
        xStreamBuffer,
        &uxRxData,
        sizeof( uxRxData ),
        AbortData.xMaxBlockTime
    );

    if( xReturn != 0x00 )
    {
        AbortData.xErrorOccurred = pdTRUE;
    }

    prvCheckExpectedTimeIsWithinAnAcceptableMargin(
        xTimeAtStart,
        AbortData.xHalfMaxBlockTime
    );

    /* Note the time before the delay so the length of the delay is known. */
    xTimeAtStart = xTaskGetTickCount();

    /* This third delay should just time out again. */
    xReturn = xStreamBufferReceive(
        xStreamBuffer,
        &uxRxData,
        sizeof( uxRxData ),
        AbortData.xMaxBlockTime
    );

    if( xReturn != 0x00 )
    {
        AbortData.xErrorOccurred = pdTRUE;
    }

    prvCheckExpectedTimeIsWithinAnAcceptableMargin(
        xTimeAtStart,
        AbortData.xMaxBlockTime
    );

    /* Not really necessary in this case, but for completeness. */
    vStreamBufferDelete( xStreamBuffer );
}
/*-----------------------------------------------------------*/

static void prvTestAbortingQueueSend( void )
{
    TickType_t xTimeAtStart;
    BaseType_t xReturn;
    const UBaseType_t xQueueLength = ( UBaseType_t ) 1;
    QueueHandle_t xQueue;
    uint8_t ucItemToQueue;

    #if( configSUPPORT_STATIC_ALLOCATION == 1 )
    {
        static StaticQueue_t xQueueBuffer;
        static uint8_t ucQueueStorage[ sizeof( uint8_t ) ];

        /* Create the queue.  Statically allocated memory is used so the
         * creation cannot fail. */
        xQueue = xQueueCreateStatic(
            xQueueLength,
            sizeof( uint8_t ),
            ucQueueStorage,
            &xQueueBuffer
        );
    }
    #else
    {
        xQueue = xQueueCreate( xQueueLength, sizeof( uint8_t ) );
        configASSERT( xQueue );
    }
    #endif /* if ( configSUPPORT_STATIC_ALLOCATION == 1 ) */

    /* This function tests aborting when in the blocked state waiting to send,
     * so the queue must be full.  There is only one space in the queue. */
    xReturn = xQueueSend( xQueue, &ucItemToQueue, AbortData.xMaxBlockTime );

    if( xReturn != pdPASS )
    {
        AbortData.xErrorOccurred = pdTRUE;
    }

    /* Note the time before the delay so the length of the delay is known. */
    xTimeAtStart = xTaskGetTickCount();

    /* This first delay should just time out. */
    xReturn = xQueueSend( xQueue, &ucItemToQueue, AbortData.xMaxBlockTime );

    if( xReturn != pdFALSE )
    {
        AbortData.xErrorOccurred = pdTRUE;
    }

    prvCheckExpectedTimeIsWithinAnAcceptableMargin(
        xTimeAtStart,
        AbortData.xMaxBlockTime
    );

    /* Note the time before the delay so the length of the delay is known. */
    xTimeAtStart = xTaskGetTickCount();

    /* This second delay should be aborted by the primary task half way
     * through. */
    xReturn = xQueueSend( xQueue, &ucItemToQueue, AbortData.xMaxBlockTime );

    if( xReturn != pdFALSE )
    {
        AbortData.xErrorOccurred = pdTRUE;
    }

    prvCheckExpectedTimeIsWithinAnAcceptableMargin(
        xTimeAtStart,
        AbortData.xHalfMaxBlockTime
    );

    /* Note the time before the delay so the length of the delay is known. */
    xTimeAtStart = xTaskGetTickCount();

    /* This third delay should just time out again. */
    xReturn = xQueueSend( xQueue, &ucItemToQueue, AbortData.xMaxBlockTime );

    if( xReturn != pdFALSE )
    {
        AbortData.xErrorOccurred = pdTRUE;
    }

    prvCheckExpectedTimeIsWithinAnAcceptableMargin(
        xTimeAtStart,
        AbortData.xMaxBlockTime
    );

    /* Not really necessary in this case, but for completeness. */
    vQueueDelete( xQueue );
}
/*-----------------------------------------------------------*/

static void prvTestAbortingSemaphoreTake( void )
{
    TickType_t xTimeAtStart;
    BaseType_t xReturn;
    SemaphoreHandle_t xSemaphore;

    #if( configSUPPORT_STATIC_ALLOCATION == 1 )
    {
        static StaticSemaphore_t xSemaphoreBuffer;

        /* Create the semaphore.  Statically allocated memory is used so the
         * creation cannot fail. */
        xSemaphore = xSemaphoreCreateBinaryStatic( &xSemaphoreBuffer );
    }
    #else
    {
        xSemaphore = xSemaphoreCreateBinary();
    }
    #endif

    /* Note the time before the delay so the length of the delay is known. */
    xTimeAtStart = xTaskGetTickCount();

    /* This first delay should just time out. */
    xReturn = xSemaphoreTake( xSemaphore, AbortData.xMaxBlockTime );

    if( xReturn != pdFALSE )
    {
        AbortData.xErrorOccurred = pdTRUE;
    }

    prvCheckExpectedTimeIsWithinAnAcceptableMargin(
        xTimeAtStart,
        AbortData.xMaxBlockTime
    );

    /* Note the time before the delay so the length of the delay is known. */
    xTimeAtStart = xTaskGetTickCount();

    /* This second delay should be aborted by the primary task half way
     * through xMaxBlockTime. */
    xReturn = xSemaphoreTake( xSemaphore, portMAX_DELAY );

    if( xReturn != pdFALSE )
    {
        AbortData.xErrorOccurred = pdTRUE;
    }

    prvCheckExpectedTimeIsWithinAnAcceptableMargin(
        xTimeAtStart,
        AbortData.xHalfMaxBlockTime
    );

    /* Note the time before the delay so the length of the delay is known. */
    xTimeAtStart = xTaskGetTickCount();

    /* This third delay should just time out again. */
    xReturn = xSemaphoreTake( xSemaphore, AbortData.xMaxBlockTime );

    if( xReturn != pdFALSE )
    {
        AbortData.xErrorOccurred = pdTRUE;
    }

    prvCheckExpectedTimeIsWithinAnAcceptableMargin(
        xTimeAtStart,
        AbortData.xMaxBlockTime
    );

    /* Not really necessary in this case, but for completeness. */
    vSemaphoreDelete( xSemaphore );
}
/*-----------------------------------------------------------*/

static void prvTestAbortingTaskNotifyWait( void )
{
    TickType_t xTimeAtStart;
    BaseType_t xReturn;

    /* Note the time before the delay so the length of the delay is known. */
    xTimeAtStart = xTaskGetTickCount();

    /* This first delay should just time out. */
    xReturn = xTaskNotifyWait( 0, 0, NULL, AbortData.xMaxBlockTime );

    if( xReturn != pdFALSE )
    {
        AbortData.xErrorOccurred = pdTRUE;
    }

    prvCheckExpectedTimeIsWithinAnAcceptableMargin(
        xTimeAtStart,
        AbortData.xMaxBlockTime
    );

    /* Note the time before the delay so the length of the delay is known. */
    xTimeAtStart = xTaskGetTickCount();

    /* This second delay should be aborted by the primary task half way
     * through xMaxBlockTime. */
    xReturn = xTaskNotifyWait( 0, 0, NULL, portMAX_DELAY );

    if( xReturn != pdFALSE )
    {
        AbortData.xErrorOccurred = pdTRUE;
    }

    prvCheckExpectedTimeIsWithinAnAcceptableMargin(
        xTimeAtStart,
        AbortData.xHalfMaxBlockTime
    );

    /* Note the time before the delay so the length of the delay is known. */
    xTimeAtStart = xTaskGetTickCount();

    /* This third delay should just time out again. */
    xReturn = xTaskNotifyWait( 0, 0, NULL, AbortData.xMaxBlockTime );

    if( xReturn != pdFALSE )
    {
        AbortData.xErrorOccurred = pdTRUE;
    }

    prvCheckExpectedTimeIsWithinAnAcceptableMargin(
        xTimeAtStart,
        AbortData.xMaxBlockTime
    );
}
/*-----------------------------------------------------------*/

static void prvCheckExpectedTimeIsWithinAnAcceptableMargin(
    TickType_t xStartTime,
    TickType_t xExpectedBlockTime
)
{
    TickType_t xTimeNow, xActualBlockTime;

    xTimeNow = xTaskGetTickCount();
    xActualBlockTime = xTimeNow - xStartTime;

    /* The actual block time should not be less than the expected block time. */
    if( xActualBlockTime < xExpectedBlockTime )
    {
        AbortData.xErrorOccurred = pdTRUE;
    }

    /* The actual block time can be greater than the expected block time, as it
     * depends on the priority of the other tasks, but it should be within an
     * acceptable margin. */
    if( xActualBlockTime > ( xExpectedBlockTime + AbortData.xAllowableMargin ) )
    {
        AbortData.xErrorOccurred = pdTRUE;
    }
}
/*-----------------------------------------------------------*/

BaseType_t xAreAbortDelayTestTasksStillRunning( void )
{
    static BaseType_t xLastControllingCycleCount = 0, xLastBlockingCycleCount = 0;
    BaseType_t xReturn = pdPASS;

    /* Have both tasks performed at least one cycle since this function was
     * last called? */
    if( AbortData.xControllingCycles == xLastControllingCycleCount )
    {
        xReturn = pdFAIL;
    }

    if( AbortData.xBlockingCycles == xLastBlockingCycleCount )
    {
        xReturn = pdFAIL;
    }

    if( AbortData.xErrorOccurred == pdTRUE )
    {
        xReturn = pdFAIL;
    }

    xLastBlockingCycleCount = AbortData.xBlockingCycles;
    xLastControllingCycleCount = AbortData.xControllingCycles;

    return xReturn;
}

#endif /* INCLUDE_xTaskAbortDelay == 1 */
