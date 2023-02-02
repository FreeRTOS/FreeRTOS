/*
 * FreeRTOS V202012.00
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
/*! @file single_core_idle_task_thread_covg_utest */

/* C runtime includes. */
#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>
#include <pthread.h>

/* Task includes */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"
#include "event_groups.h"
#include "queue.h"

/* Test includes. */
#include "unity.h"
#include "unity_memory.h"
#include "../global_vars.h"
#include "../single_covg_utest_common.h"

/* Mock includes. */
#include "mock_timers.h"
#include "mock_fake_assert.h"
#include "mock_fake_port.h"

/* ===========================  EXTERN VARIABLES  =========================== */

extern volatile UBaseType_t uxDeletedTasksWaitingCleanUp;

/* ============================  Unity Fixtures  ============================ */
/*! called before each testcase */
void setUp( void )
{
    commonSetUp();
}

/*! called after each testcase */
void tearDown( void )
{
    commonTearDown();
}

/*! called at the beginning of the whole suite */
void suiteSetUp()
{
}

/*! called at the end of the whole suite */
int suiteTearDown( int numFailures )
{
    return numFailures;
}

/* =============================  HELPER FUNCTIONS  ========================= */
void vApplicationIdleHook( void )
{
    printf( "idle hook called\r\n" );
    pthread_exit( NULL );
}

void vApplicationMinimalIdleHook( void )
{
    printf( "minimal idle hook called\r\n" );
    pthread_exit( NULL );
}

static void vPortYieldWithinAPI_xQueuePeek_Stub( int cmock_num_calls )
{
    vFakePortExitCriticalSection();

    vFakePortEnterCriticalSection();
}

/* =============================  STATIC FUNCTIONS  ========================= */

static void * task_thread_function( void * args )
{
    void * pvParameters = NULL;

    /* Setup */
    portTASK_FUNCTION( prvIdleTask, pvParameters );
    ( void ) fool_static2;/* ignore unused variable warning */
    
    /* API Call */
    prvIdleTask( pvParameters );

    return NULL;
}

/* ==============================  Test Cases  ============================== */

/*
Coverage for: 
        void vTaskSuspend( TaskHandle_t xTaskToSuspend )
        
        covers the following else case when scheduler is not running
            if( xSchedulerRunning != pdFALSE )
            {
                taskENTER_CRITICAL();
                {
                    prvResetNextTaskUnblockTime();
                }
                taskEXIT_CRITICAL();
            }
            else
            {
                mtCOVERAGE_TEST_MARKER();
            }
*/
void test_task_suspend_stopped_scheduler( void )
{
    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES] = { NULL };
    uint32_t i;

    /* Create a high priority task */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[0] );

    /* Create tasks for each remaining CPU core */
    for (i = 1; i < configNUMBER_OF_CORES ; i++) {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[i] );
    }

    /* Suspend task the last task and set core affinity for CPU 0 */
    vTaskSuspend( xTaskHandles[i-1] );

}



/*
Coverage for:
    portTASK_FUNCTION( prvIdleTask );
    
    requires you to create a thread and kill it, for an idle task is eternal.
*/
void test_prvIddleTask_Expected_time( void )
{
    vFakePortYieldWithinAPI_Stub( &vPortYieldWithinAPI_xQueuePeek_Stub );

    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES] = { NULL };
    uint32_t i, retVal ;
    pthread_t thread_id;

    /* Create configNUMBER_OF_CORES tasks of equal priority */
    for (i = 0; i < (configNUMBER_OF_CORES); i++) {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[i] );
    }
    
    vTaskStartScheduler();
    //Necessary to trigger another function with porttask()
    vTaskDelete(xTaskHandles[0]);

    /* API Call */
    pthread_create( &thread_id, NULL, &task_thread_function, NULL );
    pthread_join( thread_id, ( void ** ) &retVal );
    
    for (i = 1; i < (configNUMBER_OF_CORES); i++) {
        vTaskDelete(xTaskHandles[i]);
    }
}


// /*
// Coverage for:
//     portTASK_FUNCTION( prvIdleTask );
    
//     requires you to create a thread and kill it, for an idle task is eternal.
// */
// void test_prvIddleTask_yield( void )
// {
//     vFakePortYieldWithinAPI_Stub( &vPortYieldWithinAPI_xQueuePeek_Stub );

//     TaskHandle_t xTaskHandles[configNUMBER_OF_CORES + 1] = { NULL };
//     uint32_t i, retVal ;
//     pthread_t thread_id;

//     /* Create configNUMBER_OF_CORES tasks of equal priority */
//     for (i = 0; i < (configNUMBER_OF_CORES); i++) {
//         xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[i] );
//     }

//     // /* Create a single equal priority task */   
//     // xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[0] );
    
//     vTaskStartScheduler();
//     vTaskDelete(xTaskHandles[0]);

//     /* API Call */
//     pthread_create( &thread_id, NULL, &task_thread_function, NULL );
//     pthread_join( thread_id, ( void ** ) &retVal );
    
//     for (i = 1; i < (configNUMBER_OF_CORES); i++) {
//         vTaskDelete(xTaskHandles[i]);
//     }
// }