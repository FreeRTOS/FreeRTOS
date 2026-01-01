/* run-eventgroups-test
 *
 * Copyright (C) 2025 Advanced Micro Devices, Inc. or its affiliates. All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
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
 *
 */

#include "FreeRTOS.h"
#include "FreeRTOS_CLI.h"
#include "stdint.h"
#include "string.h"
#include "stdio.h"
#include "cli.h"
#include "task.h"
#include "EventGroupsDemo.h"
#include "register_tests.h"
#include "event_groups.h"


// Define event bits
#define EB_SYNC_BIT_1         (1 << 0)
#define EB_SYNC_BIT_2         (1 << 1)
#define EB_SET_BITS_TEST_BIT  (1 << 2)
// Task priorities
#define ebWAIT_BIT_TASK_PRIORITY       2
#define ebSET_BIT_TASK_PRIORITY        3
#define MAX_ITERATIONS 3

static int test_started = 0;
// Event group handle
EventGroupHandle_t xEventGroup;

/* Test Parameters */
int masterSuccess = 0;
int slaveSuccess = 0;

BaseType_t xReturn= pdFAIL;

// Master task to set event bits
void prvTestMasterTask(void *pvParameters)
{
    TaskHandle_t xSlaveTaskHandle = (TaskHandle_t)pvParameters;
    for (int i = 0; i < MAX_ITERATIONS; i++)
    {
        // Set the event bit to notify the slave task
        xEventGroupSetBits(xEventGroup, EB_SET_BITS_TEST_BIT);

	masterSuccess++;

        // Wait for a bit before setting the event bit again
        vTaskDelay(pdMS_TO_TICKS(500));

        // Set synchronization bits to sync with the slave task
        xEventGroupSetBits(xEventGroup, EB_SYNC_BIT_1 | EB_SYNC_BIT_2);
    }
    vTaskDelete(NULL);
}

// Slave task to wait for event bits
void prvTestSlaveTask(void *pvParameters)
{
    EventBits_t uxsetBits;
    EventBits_t uxBits;
    for (int i = 0; i < MAX_ITERATIONS; i++)
    {
        // Wait for the event bit to be set by the master task
        uxsetBits = xEventGroupWaitBits(xEventGroup, EB_SET_BITS_TEST_BIT, pdFALSE, pdFALSE, portMAX_DELAY);

        // Wait for synchronization events
        uxBits = xEventGroupWaitBits(xEventGroup, EB_SYNC_BIT_1 | EB_SYNC_BIT_2, pdTRUE, pdFALSE, portMAX_DELAY);

        // Ensure both sync bits were received
        if ((uxsetBits & EB_SET_BITS_TEST_BIT) && (uxBits & EB_SYNC_BIT_1) && (uxBits & EB_SYNC_BIT_2))
        {
	    slaveSuccess++;
        }
    }
    vTaskDelete(NULL);

}


int eventgroupsstart()
{
    TaskHandle_t xTestSlaveTaskHandle;

    // Create the event group used for inter-task synchronization
    xEventGroup = xEventGroupCreate();
    configASSERT(xEventGroup);
   
    // Create the slave task to wait for event bits
    xReturn= xTaskCreate(prvTestSlaveTask, "WaitO", configMINIMAL_STACK_SIZE, NULL, ebWAIT_BIT_TASK_PRIORITY, &xTestSlaveTaskHandle);
    configASSERT(xReturn == pdPASS);
    
    // Create the master task to set event bits
    xReturn=    xTaskCreate(prvTestMasterTask, "SetB",configMINIMAL_STACK_SIZE, (void *)xTestSlaveTaskHandle, ebSET_BIT_TASK_PRIORITY, NULL);
    configASSERT(xReturn == pdPASS);

    vTaskDelay(pdMS_TO_TICKS(5000));
    if  ((masterSuccess >=  MAX_ITERATIONS) && (slaveSuccess >=  MAX_ITERATIONS))
    {
        if ((masterSuccess == MAX_ITERATIONS) && (slaveSuccess == MAX_ITERATIONS))
        {
          return pdPASS;  
        }
        else
        {
          return pdFAIL;  
        }
    }
    else{
        return pdFAIL;  
    }

}

static BaseType_t  prvRuneventgroupstest( char * pcWriteBuffer,
                                  size_t xWriteBufferLen,
                                  const char * pcCommandString )
{
    memset(pcWriteBuffer, 0x00, xWriteBufferLen );
    if (test_started == 0)
    {
        if(eventgroupsstart()==pdFAIL){
            snprintf(pcWriteBuffer,xWriteBufferLen,"FAIL: run-eventgroups-test");
	}
	else{
            snprintf(pcWriteBuffer,xWriteBufferLen,"PASS: run-eventgroups-test");
         }
    }

    else {
        snprintf(pcWriteBuffer,xWriteBufferLen,"test Test already run");
        return 0;
    }
    test_started = 1;
    return 0;
}

static const CLI_Command_Definition_t run_eventgroups_test =
{
    "run-eventgroups-test",
    "\r\nrun-eventgroups-test:\r\n Run eventgroups test\r\n\r\n",
    prvRuneventgroupstest, /* The function to run. */
    0
};

void register_eventgroups_test(void) {
    FreeRTOS_CLIRegisterCommand( &run_eventgroups_test );
}


