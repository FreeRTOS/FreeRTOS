/* run-mutex-test
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
#include "register_tests.h"
#include "semphr.h"
#include <stdio.h>

#define MAX_ITERATIONS 3

static int demo_started = 0;

/* Mutex Handle */
SemaphoreHandle_t xMutex;

/* Shared Resource */
int sharedResource = 0;

/* Test Parameters */
int task1Success = 0;
int task2Success = 0;

void vTask1(void *pvParameters)
{
    for (int i = 0; i < MAX_ITERATIONS; i++)
    {
        /* Try to take the mutex */
        if (xSemaphoreTake(xMutex, pdMS_TO_TICKS(1000)) == pdTRUE)
        {
            /* Access the shared resource */
            sharedResource++;

            /* Simulate some work with the resource */
            vTaskDelay(pdMS_TO_TICKS(500));

            /* Release the mutex */
            xSemaphoreGive(xMutex);

            task1Success++;
        }

        /* Delay before retrying */
        vTaskDelay(pdMS_TO_TICKS(1000));
    }
    /* End Task */
    vTaskDelete(NULL);
}

void vTask2(void *pvParameters)
{
    for (int i = 0; i < MAX_ITERATIONS; i++)
    {
        /* Try to take the mutex */
        if (xSemaphoreTake(xMutex, pdMS_TO_TICKS(1000)) == pdTRUE)
        {
            /* Access the shared resource */
            sharedResource += 2;

            /* Simulate some work with the resource */
            vTaskDelay(pdMS_TO_TICKS(500));

            /* Release the mutex */
            xSemaphoreGive(xMutex);

            task2Success++;
        }

        /* Delay before retrying */
        vTaskDelay(pdMS_TO_TICKS(1000));
    }

    vTaskDelete(NULL);
}

/* Main Function */
int mutexstart(void)
{
    BaseType_t taskCreationStatus = pdPASS;

    /* Create the mutex */
    xMutex = xSemaphoreCreateMutex();
    if (xMutex == NULL)
    {
        printf("Failed to create mutex.\n");
        return pdFAIL; // Test failed
    }

    /* Create Task 1 */
    taskCreationStatus = xTaskCreate(vTask1, "Task1", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY + 1, NULL);
    if (taskCreationStatus != pdPASS)
    {
        printf("Failed to create Task 1.\n");
        return pdFAIL;
    }

    /* Create Task 2 */
    taskCreationStatus = xTaskCreate(vTask2, "Task2", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY + 1, NULL);
    if (taskCreationStatus != pdPASS)
    {
        printf("Failed to create Task 2.\n");
        return pdFAIL; 
    }

    vTaskDelay(pdMS_TO_TICKS(5000));

    if ((task1Success + task2Success) >= (2* MAX_ITERATIONS))
    {
        if ((task1Success == MAX_ITERATIONS) && (task2Success == MAX_ITERATIONS))
        {
            return pdPASS;
        }
        else
        {
            return pdFAIL;
        }
    }
    else
    {
       return pdFAIL;
    }

}



static BaseType_t  prvRunmutexTest( char * pcWriteBuffer,
                                  size_t xWriteBufferLen,
                                  const char * pcCommandString )
{
    memset(pcWriteBuffer, 0x00, xWriteBufferLen );
    if (demo_started == 0)
    {
        if(mutexstart()==pdFAIL){
            snprintf(pcWriteBuffer,xWriteBufferLen,"FAIL: run-mutex-test");
	}
	else{ 
            snprintf(pcWriteBuffer,xWriteBufferLen,"PASS: run-mutex-test");
	}
    }
    else {
        snprintf(pcWriteBuffer,xWriteBufferLen," Test already run");
        return 0;
    }
    demo_started = 1;

    return 0;
}

static const CLI_Command_Definition_t run_mutex_test =
{
    "run-mutex-test",
    "\r\nrun-mutex-test:\r\n Run mutex test\r\n\r\n",
    prvRunmutexTest, /* The function to run. */
    0
};

void register_mutex_test(void) {
    FreeRTOS_CLIRegisterCommand( &run_mutex_test );
}


