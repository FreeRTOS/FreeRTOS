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

/* Standard includes. */
#include <stdint.h>

/* FreeRTOS includes. */
#include "FreeRTOSConfig.h"
#include "FreeRTOS.h"
#include "task.h"
#include "portmacro.h"

/* HalCoGen includes. */
#include "sci.h"

/* Demo include */
#include "demo_tasks.h"

#if( mainDEMO_TYPE & NOTIFICATION_DEMO )

    /** @brief Parameters that are passed into the notification test task solely
     * for the purpose of ensuring parameters are passed into tasks correctly. */
    #define notificationTASK_PARAMETER ( 0xFEEDBEEFUL )

    /** @brief Value sent back and forth between the tasks */
    #define notificationTEST_VALUE     0x1234UL

/** @brief TCB used by the Notification Test Task */
PRIVILEGED_DATA static StaticTask_t xNotificationTestTaskTCB;

/** @brief MPU Region Aligned Stack used by the Notification Test Task */
static StackType_t uxNotificationTestTaskStack[ configMINIMAL_STACK_SIZE ]
    __attribute__( ( aligned( configMINIMAL_STACK_SIZE * 0x4UL ) ) );

/** @brief Statically allocated task handle for the Notification Test task. */
static TaskHandle_t xNotificationTaskOneHandle;

/* ----------------------------------------------------------------------------------- */

static void prvNotifyCheck( BaseType_t ulRetVal )
{
    if( pdPASS == ulRetVal )
    {
        sci_print( "Notification API Returned a passing value!\r\n" );
    }
    else
    {
        sci_print( "Notification API did not return pdPASS.\r\n" );
        configASSERT( ulRetVal );
    }
}

/** @brief Entry point for the Unprivileged Notification Test Task.
 * @param pvParameters A test value to ensure the task's arguments are correctly set.
 * @note This task sends itself and another task notifications using the
 * cross-task notification APIs.
 */
static void prvNotificationTestTask( void * pvParameters )
{
    BaseType_t xReturned;
    UBaseType_t ulNotificationValue;

    /* Ensure that the correct parameter was passed to the task */
    configASSERT( ( uint32_t ) pvParameters == notificationTEST_VALUE );
    for( ;; )
    {
        /* Clear the notification value each loop */
        ulNotificationValue = 0x0UL;

        /* The task should not yet have a notification pending. */
        xReturned = xTaskNotifyWait( 0x0UL, 0x0UL, &ulNotificationValue, 0x0UL );
        configASSERT( pdFAIL == xReturned );
        configASSERT( 0x0UL == ulNotificationValue );

        /* Tell the task to notify itself twice */
        xReturned = xTaskNotifyGive( xTaskGetCurrentTaskHandle() );
        prvNotifyCheck( xReturned );

        xReturned = xTaskNotifyGive( xTaskGetCurrentTaskHandle() );
        prvNotifyCheck( xReturned );

        /* Perform a non-blocking notification read, should see two "gives" */
        ulNotificationValue = ulTaskNotifyTake( pdTRUE, 0x0 );

        /* Two notifications have been sent to this task by itself */
        configASSERT( 0x2UL == ulNotificationValue );
        sci_print( "Notification Task correctly sent itself two notifications!\r\n" );

        /* Now make the task send itself a notification with a value */
        xReturned = xTaskNotify( xTaskGetCurrentTaskHandle(),
                                 notificationTEST_VALUE,
                                 eSetValueWithOverwrite );
        prvNotifyCheck( xReturned );

        /* Clear ulNotificationValue before using it */
        ulNotificationValue = 0x0UL;

        /* Receive the value sent using xTaskNotify */
        xReturned = xTaskNotifyWait( 0,
                                     ( uint32_t ) 0xFFFFFFFFUL,
                                     &ulNotificationValue,
                                     ( TickType_t ) 0x50UL );
        prvNotifyCheck( xReturned );

        if( notificationTEST_VALUE == ulNotificationValue )
        {
            sci_print( "Notification Task got the expected value!\r\n" );
        }
        else
        {
            sci_print( "Notification Task did NOT get the expected value!\r\n" );
            configASSERT( 0x0UL );
        }

        /* Reset the variable before using it */
        ulNotificationValue = 0x0UL;

        /* There should be no value to receive this time */
        xReturned = xTaskNotifyWait( 0, 0, &ulNotificationValue, ( TickType_t ) 0x0UL );
        if( ( pdPASS == xReturned ) || ( 0x0 != ulNotificationValue ) )
        {
            sci_print( "Notification Task received a value when there should have been "
                       "none" );
            configASSERT( 0x0UL );
        }

        xTaskNotify( xTaskGetCurrentTaskHandle(),
                     ulNotificationValue,
                     eSetValueWithOverwrite );
        xReturned = xTaskNotifyStateClear( NULL );

        /* First time a notification was pending. */
        configASSERT( xReturned == pdTRUE );
        xReturned = xTaskNotifyStateClear( NULL );

        /* Second time the notification was already clear. */
        configASSERT( xReturned == pdFALSE );

        sci_print( "Notification Task sleeping before next loop!\r\n\r\n" );
        /* Sleep for odd number of seconds to schedule at different real-times */
        vTaskDelay( pdMS_TO_TICKS( 2750UL ) );
    }
}

/* ----------------------------------------------------------------------------------- */

BaseType_t xCreateNotificationTestTask( void )
{
    /* Declaration when these variable are exported from linker scripts. */
    extern uint32_t __peripherals_start__[];
    extern uint32_t __peripherals_end__[];

    uint32_t ulPeriphRegionStart = ( uint32_t ) __peripherals_start__;
    uint32_t ulPeriphRegionSize = ( uint32_t ) __peripherals_end__ - ulPeriphRegionStart;
    uint32_t ulPeriphRegionAttr = portMPU_REGION_PRIV_RW_USER_RW_NOEXEC | portMPU_REGION_DEVICE_SHAREABLE;

    BaseType_t xReturn = pdFAIL;
    /* Create the register check tasks, as described at the top of this file. */
    TaskParameters_t  xNotificationTestTaskParameters = {
        /* The function that implements the task. */
        .pvTaskCode = prvNotificationTestTask,
        /* The name of the task. */
        .pcName = "NotificationTestTask",
        /* Size of stack to allocate for the task - in words not bytes!. */
        .usStackDepth = configMINIMAL_STACK_SIZE,
        /* Parameter passed into the task. */
        .pvParameters = ( void * ) notificationTEST_VALUE,
        /* Priority of the task. */
        .uxPriority = ( demoNOTIFICATION_TASK_PRIORITY ),
        .puxStackBuffer = uxNotificationTestTaskStack,
        .pxTaskBuffer = &xNotificationTestTaskTCB,
        .xRegions = {
                    /* MPU Region 0 */
                    { ( void * ) &xNotificationTaskOneHandle,
                      ( uint32_t ) sizeof( TaskHandle_t ),
                        portMPU_REGION_PRIV_RW_USER_RW_NOEXEC |
                        portMPU_REGION_NORMAL_OIWTNOWA_SHARED },
                    /* MPU Region 1 */
                    { 0, 0, 0 },
                    /* MPU Region 2 */
                    { 0, 0, 0 },
                    /* MPU Region 3 */
                    { 0, 0, 0 },
                    /* MPU Region 4 */
                    { 0, 0, 0 },
                    /* MPU Region 5 */
                    { 0, 0, 0 },
                    /* MPU Region 6 */
                    { 0, 0, 0 },
    #if( configTOTAL_MPU_REGIONS == 16 )
                        /* MPU Region 7 */
                        { 0, 0, 0 },
                        /* MPU Region 8 */
                        { 0, 0, 0 },
                        /* MPU Region 9 */
                        { 0, 0, 0 },
                        /* MPU Region 10 */
                        { 0, 0, 0 },
    #endif
                    /* Last Configurable MPU Region */
                    { ( void * ) ulPeriphRegionStart, ulPeriphRegionSize, ulPeriphRegionAttr },
        }
    };

    /* Create the notification test task */
    xReturn = xTaskCreateRestrictedStatic( &( xNotificationTestTaskParameters ),
                                           &( xNotificationTaskOneHandle ) );
    if( pdPASS == xReturn )
    {
        sci_print( "Created the Notification Test Task\r\n" );
    }
    else
    {
        sci_print( "Failed to create the Notification Test Task\r\n" );
    }

    return xReturn;
}
#endif /* ( mainDEMO_TYPE & NOTIFICATION_DEMO ) */
