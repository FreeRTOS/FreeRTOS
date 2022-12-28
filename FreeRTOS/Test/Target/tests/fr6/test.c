/*
 * FreeRTOS Kernel <DEVELOPMENT BRANCH>
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

/**
 * @file test.c
 * @brief Implements FR6 test functions for SMP on target testing.
 */

/* Kernel includes. */
#include "FreeRTOS.h" /* Must come first. */
#include "queue.h"    /* RTOS queue related API prototypes. */
#include "semphr.h"   /* Semaphore related API prototypes. */
#include "task.h"     /* RTOS task related API prototypes. */
#include "timers.h"   /* Software timer related API prototypes. */

#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "bsl.h"
#include "unity.h" /* unit testing support functions */

/* Priorities at which the tasks are created.  The max priority can be specified
as ( configMAX_PRIORITIES - 1 ). */
#define mainTASK_A_PRIORITY (tskIDLE_PRIORITY + 2)
#define mainTASK_B_PRIORITY (tskIDLE_PRIORITY + 2)
#define mainTASK_C_PRIORITY (tskIDLE_PRIORITY + 2)

static void prvTaskA(void *pvParameters);
static void prvTaskB(void *pvParameters);
static void prvTaskC(void *pvParameters);

#if configNUMBER_OF_CORES != 2
#error Require two cores be configured for FreeRTOS
#endif

BaseType_t xTestFailed = pdFALSE;
BaseType_t xTestPassed = pdFALSE;
BaseType_t xTaskAState = 0;
BaseType_t xTaskBState = 0;

void test_fr6TASK_SWITCHED_IN(void) {
  UBaseType_t uxIdx, uxNumTasksRunning;
  TaskStatus_t taskStatus[16];
  UBaseType_t uxTaskStatusArraySize = 16;
  unsigned long ulTotalRunTime;

  static uint32_t ulTaskSwitchCount = 0;
  static BaseType_t xTaskARan = pdFALSE;
  static BaseType_t xTaskBRan = pdFALSE;
  static BaseType_t xTaskCRan = pdFALSE;

  if ((xTestPassed == pdFALSE) && (xTestFailed == pdFALSE))
  {
    BaseType_t xTaskARunning = pdFALSE;

    uxNumTasksRunning = uxTaskGetSystemState((TaskStatus_t * const)&taskStatus, uxTaskStatusArraySize, &ulTotalRunTime);

    for(uxIdx = 0; uxIdx < uxNumTasksRunning; uxIdx++)
    {
      if ((strcmp(taskStatus[uxIdx].pcTaskName, "TaskA") == 0) && (taskStatus[uxIdx].eCurrentState == eRunning))
      {
        xTaskARunning = pdTRUE;
        xTaskARan = pdTRUE;
      }
      if ((strcmp(taskStatus[uxIdx].pcTaskName, "TaskB") == 0) && (taskStatus[uxIdx].eCurrentState == eRunning))
      {
        xTaskBRan = pdTRUE;
      }
      if ((strcmp(taskStatus[uxIdx].pcTaskName, "TaskC") == 0) && (taskStatus[uxIdx].eCurrentState == eRunning))
      {
        xTaskCRan = pdTRUE;
      }
    }

    if ((xTaskARunning == pdTRUE)&& (xTaskBState > 0) && (xTaskCRan == pdTRUE))
    {
      if (!((xTaskARunning == pdTRUE) &&(xTaskBRan == pdTRUE)))
      {
        xTestFailed = pdTRUE;
      }
      else
      {
        xTestPassed = pdTRUE;
      }
    }

    ulTaskSwitchCount++;
    if (ulTaskSwitchCount > 2048)
    {
      //sendReport("2k task swiches.\n\0", 0);
      xTestFailed = pdTRUE;
    }
  }
}

TaskHandle_t taskA;

void setup_test_fr6_001(void) {
  xTaskCreateAffinitySet(prvTaskA, "TaskA", configMINIMAL_STACK_SIZE, NULL,
              mainTASK_A_PRIORITY, 0x2, &taskA);

  xTaskCreate(prvTaskB, "TaskB", configMINIMAL_STACK_SIZE, NULL,
              mainTASK_B_PRIORITY, NULL);

  xTaskCreate(prvTaskC, "TaskC", configMINIMAL_STACK_SIZE, NULL,
              mainTASK_C_PRIORITY, NULL);
}

/* Is run before every test, put unit init calls here. */
void setUp(void)
{
}

/* Is run after every test, put unit clean-up calls here. */
void tearDown(void)
{
}

int main(void) {
  initTestEnvironment();

  setup_test_fr6_001();

  vTaskStartScheduler();

  /* should never reach here */
  panic_unsupported();

  return 0;
}

static void prvTaskA(void *pvParameters) {
  // wait with preemption disabled
  vTaskPreemptionDisable(taskA);
  xTaskAState++;
  busyWaitMicroseconds(2000000);
  vTaskPreemptionEnable(taskA);

  // idle the task
  for (;;) {
    vTaskDelay(pdMS_TO_TICKS(10));
  }
}

static void prvTaskB(void *pvParameters) {
  xTaskBState++;

  sendReport("TaskB Entering busyWait...\n\0", 0);
  busyWaitMicroseconds(2000000);

  // idle the task
  for (;;) {
    vTaskDelay(pdMS_TO_TICKS(10));
    busyWaitMicroseconds(100000);
  }
}

static void fr06_validate_vTaskPreemptionDisable(void) {
  int attempt;

  for(attempt=1; attempt < 25; attempt++)
  {
    if (xTestPassed || xTestFailed)
    {
      break;
    }

    vTaskDelay(pdMS_TO_TICKS(10));
  }

  TEST_ASSERT_TRUE(xTestPassed && !xTestFailed);
}

static void prvTaskC(void *pvParameters) {
  while (xTaskBState == 0) {
    busyWaitMicroseconds(1);
  }

  sendReport("TaskC Past Guard\n\0", 0);

  UNITY_BEGIN();

  RUN_TEST(fr06_validate_vTaskPreemptionDisable);

  UNITY_END();

  // idle the task
  for (;;) {
    vTaskDelay(pdMS_TO_TICKS(10));
    busyWaitMicroseconds(100000);
  }
}
