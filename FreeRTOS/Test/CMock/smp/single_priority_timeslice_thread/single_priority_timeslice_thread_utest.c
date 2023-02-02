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
/*! @file single_priority_no_timeslice_utest.c */

/* C runtime includes. */
#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>
#include <pthread.h>

/* Tasl includes */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"
#include "event_groups.h"
#include "queue.h"

/* Test includes. */
#include "unity.h"
#include "unity_memory.h"
#include "../global_vars.h"
#include "../smp_utest_common.h"

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
void vApplicationMinimalIdleHook( void )
{
    printf( "Minimal idle hook called\r\n" );
    pthread_exit( NULL );
}

/* =============================  STATIC FUNCTIONS  ========================= */

static void * task_thread_function( void * args )
{
    void * pvParameters = NULL;

    /* Setup */
    portTASK_FUNCTION( prvMinimalIdleTask, pvParameters );
    
    /* API Call */
    prvMinimalIdleTask( pvParameters );

    return NULL;
}

/* ==============================  Test Cases  ============================== */

/*
Coverage for:
    static portTASK_FUNCTION( prvMinimalIdleTask, pvParameters )
    
    requires you to create a thread and kill it, for an idle task is eternal.
*/
void test_prvIddleTask_Expected_time( void )
{
    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES + 1] = { NULL };
    uint32_t i, retVal ;
    pthread_t thread_id;

    /* Create configNUMBER_OF_CORES tasks of equal priority */
    for (i = 0; i < (configNUMBER_OF_CORES); i++) {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[i] );
    }

    // /* Create a single equal priority task */   
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[0] );
    
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

/*
Coverage for:
    static portTASK_FUNCTION( prvMinimalIdleTask, pvParameters )
    
    for the condition when a task that is sharing the idle priority is 
    ready to run then the idle task is yielded before the end of the timeslice
    
    programmatically:
        if( listCURRENT_LIST_LENGTH( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ) ) > ( UBaseType_t ) configNUMBER_OF_CORES ) = True

*/
void test_prvIddleTask_Expected_time_more_task( void )
{
    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES+1] = { NULL };
    uint32_t retVal ;
    pthread_t thread_id;

    /* As configNUMBER_OF_CORES idle tasks are already created by FreeRTOS kernel 
    *  we only need to create one extra to have additonal equal priorty task */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, &xTaskHandles[configNUMBER_OF_CORES] );
    
    vTaskStartScheduler();

    /* API Call */
    pthread_create( &thread_id, NULL, &task_thread_function, NULL );
    pthread_join( thread_id, ( void ** ) &retVal );
    
    //Only delete the task we created
    vTaskDelete(xTaskHandles[configNUMBER_OF_CORES]);
    
}


