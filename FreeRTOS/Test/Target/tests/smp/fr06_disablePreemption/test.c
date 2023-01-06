/*
 * FreeRTOS Kernel <DEVELOPMENT BRANCH>
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 *
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

/**
 * @file test.c
 * @brief The scheduler shall not preempt a task for which preemption is
 * disabled.
 *
 * Procedure:
 *   - Create tasks A, B, & C, each with equal priority.
 *   - Disable preemption for task A. Task A will then decrease
 *     its own priority and busy loop for 2 seconds with it still
 *     disabled.
 *   - Task B will iterate between a busy loop and a yielding 10ms delay.
 *   - The traceTASK_SWITCHED_IN function is bound in order to track
 *     scheduler activity.
 *   - Task C will, between every 10ms yielding delay check the status
 *     as reported by the traceTASK_SWITCHED_IN function.
 * Expected:
 *   - That Task A will not be interrupted for the 2 seconds that it
 *     has preemption disabled.
 */

/* Kernel includes. */
#include "FreeRTOS.h" /* Must come first. */
#include "task.h"     /* RTOS task related API prototypes. */

#include <string.h>

#include "bsl.h"
#include "unity.h" /* unit testing support functions */
/*-----------------------------------------------------------*/

/* Priorities at which the tasks are created.  The max priority can be specified
 * as ( configMAX_PRIORITIES - 1 ). */
#define mainTASK_A_PRIORITY (tskIDLE_PRIORITY + 2)
#define mainTASK_B_PRIORITY (tskIDLE_PRIORITY + 2)
#define mainTASK_C_PRIORITY (tskIDLE_PRIORITY + 2)
/*-----------------------------------------------------------*/

static void vPrvTaskA(void *pvParameters);
static void vPrvTaskB(void *pvParameters);
static void vPrvTaskC(void *pvParameters);
static void fr06_validate_vTaskPreemptionDisable(void);
/*-----------------------------------------------------------*/

#if configNUMBER_OF_CORES != 2
#error Require two cores be configured for FreeRTOS
#endif /* if configNUMBER_OF_CORES != 2 */

#if configUSE_TASK_PREEMPTION_DISABLE != 1
#error configUSE_TASK_PREEMPTION_DISABLE shoud be 1 in this test case. Please check if testConfig.h is included.
#endif /* if configUSE_CORE_AFFINITY != 0 */

#if traceTASK_SWITCHED_IN != test_fr6TASK_SWITCHED_IN
#error Need to include testConfig.h in FreeRTOSConfig.h
#endif /* if traceTASK_SWITCHED_IN != test_fr6TASK_SWITCHED_IN */
/*-----------------------------------------------------------*/

static TaskHandle_t xTaskAHandler;
static TaskHandle_t xTaskBHandler;
static TaskHandle_t xTaskCHandler;
static BaseType_t xTestFailed = pdFALSE;
static BaseType_t xTestPassed = pdFALSE;
static BaseType_t xTaskAState = 0;
static BaseType_t xTaskBState = 0;
/*-----------------------------------------------------------*/

void test_fr6TASK_SWITCHED_IN(void) {
  UBaseType_t uxIdx, uxNumTasksRunning;
  TaskStatus_t taskStatus[16];
  UBaseType_t uxTaskStatusArraySize = 16;
  unsigned long ulTotalRunTime;

  static uint32_t ulTaskSwitchCount = 0;
  static BaseType_t xTaskARan = pdFALSE;
  static BaseType_t xTaskBRan = pdFALSE;
  static BaseType_t xTaskCRan = pdFALSE;

  if ((xTestPassed == pdFALSE) && (xTestFailed == pdFALSE)) {
    BaseType_t xTaskARunning = pdFALSE;

    uxNumTasksRunning =
        uxTaskGetSystemState((TaskStatus_t *const)&taskStatus,
                             uxTaskStatusArraySize, &ulTotalRunTime);

    for (uxIdx = 0; uxIdx < uxNumTasksRunning; uxIdx++) {
      if ((strcmp(taskStatus[uxIdx].pcTaskName, "TaskA") == 0) &&
          (taskStatus[uxIdx].eCurrentState == eRunning)) {
        xTaskARunning = pdTRUE;
        xTaskARan = pdTRUE;
      }

      if ((strcmp(taskStatus[uxIdx].pcTaskName, "TaskB") == 0) &&
          (taskStatus[uxIdx].eCurrentState == eRunning)) {
        xTaskBRan = pdTRUE;
      }

      if ((strcmp(taskStatus[uxIdx].pcTaskName, "TaskC") == 0) &&
          (taskStatus[uxIdx].eCurrentState == eRunning)) {
        xTaskCRan = pdTRUE;
      }
    }

    if ((xTaskARunning == pdTRUE) && (xTaskBState > 0) &&
        (xTaskCRan == pdTRUE)) {
      if (!((xTaskARunning == pdTRUE) && (xTaskBRan == pdTRUE))) {
        xTestFailed = pdTRUE;
      } else {
        xTestPassed = pdTRUE;
      }
    }

    ulTaskSwitchCount++;

    if (ulTaskSwitchCount > 2048) {
      /*sendReport("2k task swiches.\n\0", 0); */
      xTestFailed = pdTRUE;
    }
  }
}
/*-----------------------------------------------------------*/

static void fr06_validate_vTaskPreemptionDisable(void) {
  xTaskCreateAffinitySet(vPrvTaskA, "TaskA", configMINIMAL_STACK_SIZE, NULL,
                         mainTASK_A_PRIORITY, 0x2, &xTaskAHandler);

  xTaskCreate(vPrvTaskB, "TaskB", configMINIMAL_STACK_SIZE, NULL,
              mainTASK_B_PRIORITY, &xTaskBHandler);

  xTaskCreate(vPrvTaskC, "TaskC", configMINIMAL_STACK_SIZE, NULL,
              mainTASK_C_PRIORITY, &xTaskCHandler);

  while ((xTestPassed == pdFALSE) && (xTestFailed == pdFALSE)) {
    vTaskDelay(pdMS_TO_TICKS(100));
  }

  TEST_ASSERT_TRUE(xTestPassed == pdTRUE);
  TEST_ASSERT_TRUE(xTestFailed == pdFALSE);

  vTaskDelete(xTaskAHandler);
  vTaskDelete(xTaskBHandler);
  vTaskDelete(xTaskCHandler);
}
/*-----------------------------------------------------------*/

static void vPrvTaskA(void *pvParameters) {
  /* wait with preemption disabled */
  vTaskPreemptionDisable(NULL);
  vTaskPrioritySet(NULL, mainTASK_A_PRIORITY - 1);
  xTaskAState++;
  vPortBusyWaitMicroseconds((uint32_t)2000000);
  vTaskPreemptionEnable(NULL);
}
/*-----------------------------------------------------------*/

static void vPrvTaskB(void *pvParameters) {
  xTaskBState++;

  vPortSerialLog("TaskB Entering busyWait...\n\0");
  vPortBusyWaitMicroseconds((uint32_t)2000000);

  /* idle the task */
  for (;;) {
    vTaskDelay(pdMS_TO_TICKS(10));
    vPortBusyWaitMicroseconds((uint32_t)100000);
  }
}
/*-----------------------------------------------------------*/

static void vPrvTaskC(void *pvParameters) {
  int attempt;

  while (xTaskBState == 0) {
    vPortBusyWaitMicroseconds((uint32_t)1);
  }

  for (attempt = 1; attempt < 25; attempt++) {
    if (xTestPassed || xTestFailed) {
      break;
    }

    vTaskDelay(pdMS_TO_TICKS(10));
  }

  /* idle the task */
  for (;;) {
    vTaskDelay(pdMS_TO_TICKS(10));
    vPortBusyWaitMicroseconds((uint32_t)100000);
  }
}
/*-----------------------------------------------------------*/

/**
 * @brief A start entry for test runner to run FR06.
 */
void vTestRunner(void) {
  UNITY_BEGIN();

  RUN_TEST(fr06_validate_vTaskPreemptionDisable);

  UNITY_END();
}
/*-----------------------------------------------------------*/
