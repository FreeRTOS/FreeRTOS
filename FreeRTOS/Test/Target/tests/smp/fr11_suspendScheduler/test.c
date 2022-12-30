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
 * @brief Implements FR11 test functions for SMP on target testing.
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
#define mainTASK_B_PRIORITY (tskIDLE_PRIORITY + 1)

#define TASK_BLOCK_TIME_MS ( 3000 )
#define TASK_BUSYLOOP_TIME_MS ( 100 )

static void prvTaskA(void *pvParameters);
static void prvTaskB(void *pvParameters);

TaskHandle_t taskA, taskB;

#if configNUMBER_OF_CORES != 2
#error Require two cores be configured for FreeRTOS
#endif

void setup_test_fr11_001(void) {
  xTaskCreate(prvTaskA, "TaskA", configMINIMAL_STACK_SIZE * 2, NULL,
              mainTASK_A_PRIORITY, &taskA);

  xTaskCreate(prvTaskB, "TaskB", configMINIMAL_STACK_SIZE, NULL,
              mainTASK_B_PRIORITY, &taskB);
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

  setup_test_fr11_001();

  vTaskStartScheduler();

  /* should never reach here */
  panic_unsupported();

  return 0; 
}

static uint32_t ulTaskBState = 0;
static uint32_t ulTempTaskBState = 0;

static void fr11_validate_NoContextSwitchesOccurWhileSchedulerIsSuspended(void) {
  TEST_ASSERT_TRUE(ulTempTaskBState == 0);
}

static void prvTaskA(void *pvParameters) {
  uint32_t ulAttempTime = 0;

  vTaskSuspendAll();

  vTaskPrioritySet(taskB, mainTASK_A_PRIORITY+1);

  while( ulTaskBState == 0 )
  {
    ulAttempTime++;

    if( ulAttempTime > ( TASK_BLOCK_TIME_MS / TASK_BUSYLOOP_TIME_MS ) )
    {
      /* Break after polling 30 times. (total 3s) */
      break;
    }

    /* Wait 100ms. */
    vPortBusyWaitMicroseconds( (uint32_t) (TASK_BUSYLOOP_TIME_MS * 1000) );
  }

  /* Cache uTaskBState before resuming all tasks. */
  ulTempTaskBState = ulTaskBState;

  xTaskResumeAll();

  UNITY_BEGIN();

  RUN_TEST(fr11_validate_NoContextSwitchesOccurWhileSchedulerIsSuspended);

  UNITY_END();
 
  // idle the task
  for (;;) {
    vTaskDelay(pdMS_TO_TICKS(10));
  }
}

static void prvTaskB(void *pvParameters) {
  ulTaskBState++;

  // idle the task
  for (;;) {
    vTaskDelay(pdMS_TO_TICKS(10));
  }
}
