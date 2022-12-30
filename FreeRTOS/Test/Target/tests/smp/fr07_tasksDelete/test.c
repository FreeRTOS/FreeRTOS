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
 * @brief Implements FR7 test functions for SMP on target testing.
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
#define mainTASK_C_PRIORITY (tskIDLE_PRIORITY + 1)

#define mainSOFTWARE_TIMER_PERIOD_MS pdMS_TO_TICKS(10)

static void prvUnityStarter(void *pvParameters);
static void prvTaskA(void *pvParameters);
static void prvTaskB(void *pvParameters);

static void fr07_memoryFreedTaskRemoteDeleted();
static void fr07_memoryFreedTaskSelfDeleted();

#if configNUMBER_OF_CORES != 2
#error Require two cores be configured for FreeRTOS
#endif

TaskHandle_t taskA, taskB;

void setup_test_fr7_001(void) {
  xTaskCreate(prvUnityStarter, "unityStarter", configMINIMAL_STACK_SIZE, NULL,
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
  vPortInitTestEnvironment();

  setup_test_fr7_001();

  vTaskStartScheduler();
  // AMPLaunchOnCore(1, vTaskStartScheduler);

  /* should never reach here */
  panic_unsupported();

  return 0;
}

static volatile BaseType_t xTaskAState = 0;
static volatile BaseType_t xTaskBState = 0;

static uint32_t ulOriginalFreeHeapSize;

static void prvUnityStarter(void *pvParameters)
{
  UNITY_BEGIN();
  
  RUN_TEST( fr07_memoryFreedTaskSelfDeleted );
  RUN_TEST( fr07_memoryFreedTaskRemoteDeleted );

  UNITY_END();

  // idle the task
  for (;;) {
    vTaskDelay(mainSOFTWARE_TIMER_PERIOD_MS);
  }
}

static void createSelfDeleteTaskA()
{
  xTaskCreate(prvTaskA, "TaskA", configMINIMAL_STACK_SIZE, NULL,
              mainTASK_A_PRIORITY, &taskA);
}

static void createRemoteDeleteTaskB()
{
  xTaskCreate(prvTaskB, "TaskB", configMINIMAL_STACK_SIZE, NULL,
              mainTASK_B_PRIORITY, &taskB);
}

static void prvTaskA(void *pvParameters) {
  xTaskAState++;

  vTaskDelete( NULL );
}

static void prvTaskB(void *pvParameters) {
  xTaskBState++;

  // idle the task
  for (;;) {
    vTaskDelay(mainSOFTWARE_TIMER_PERIOD_MS);
  }
}

static void fr07_memoryFreedTaskSelfDeleted() {
  BaseType_t xAttempt;
  uint32_t ulFreeHeapSize = 0;

  ulOriginalFreeHeapSize = xPortGetFreeHeapSize();

  createSelfDeleteTaskA();

  while (xTaskAState <= 0) {
    vTaskDelay(mainSOFTWARE_TIMER_PERIOD_MS);
  }

  for(xAttempt=1; xAttempt<100; xAttempt++)
  {
    /* Reserve for idle task to delete the entire task. */
    vTaskDelay(mainSOFTWARE_TIMER_PERIOD_MS);
    ulFreeHeapSize = xPortGetFreeHeapSize();
    if (ulFreeHeapSize == ulOriginalFreeHeapSize) {
      break;
    }
  }
  
  TEST_ASSERT_TRUE(ulFreeHeapSize == ulOriginalFreeHeapSize);
}

static void fr07_memoryFreedTaskRemoteDeleted() {
  int xAttempt;
  uint32_t ulFreeHeapSize = 0;

  ulOriginalFreeHeapSize = xPortGetFreeHeapSize();

  createRemoteDeleteTaskB();

  while (xTaskBState <= 0) {
    vTaskDelay(mainSOFTWARE_TIMER_PERIOD_MS);
  }

  vTaskDelete(taskB);

  for(xAttempt=1; xAttempt<100; xAttempt++)
  {
    /* Reserve for idle task to delete the entire task. */
    vTaskDelay(mainSOFTWARE_TIMER_PERIOD_MS);
    ulFreeHeapSize = xPortGetFreeHeapSize();
    if (ulFreeHeapSize == ulOriginalFreeHeapSize) {
      break;
    }
  }
  
  TEST_ASSERT_TRUE(ulFreeHeapSize == ulOriginalFreeHeapSize);
}
