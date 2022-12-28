

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
#define mainTASK_C_PRIORITY (tskIDLE_PRIORITY + 3)

static void prvTaskA(void *pvParameters);
static void prvTaskB(void *pvParameters);
static void prvTaskC(void *pvParameters);

#if configNUMBER_OF_CORES != 2
#error Require two cores be configured for FreeRTOS
#endif

static BaseType_t xTestPassed = pdFALSE;
static BaseType_t xTestFailed = pdFALSE;

void test_fr2TASK_SWITCHED_IN(void) {
  UBaseType_t xIdx, xNumTasksRunning;
  TaskStatus_t taskStatus[16];
  UBaseType_t xTaskStatusArraySize = 16;
  unsigned long ulTotalRunTime;

  static uint32_t ulTaskSwitchCount = 0;
  static BaseType_t xTaskARan = pdFALSE;
  static BaseType_t xTaskBRan = pdFALSE;
  static BaseType_t xTaskCRan = pdFALSE;

  if (!(xTestPassed || xTestFailed))
  {
    xNumTasksRunning = uxTaskGetSystemState((TaskStatus_t * const)&taskStatus, xTaskStatusArraySize, &ulTotalRunTime);

    for(xIdx = 0; xIdx < xNumTasksRunning; xIdx++)
    {
      if ((strcmp(taskStatus[xIdx].pcTaskName, "TaskA") == 0) && (taskStatus[xIdx].eCurrentState == eRunning))
      {
        xTaskARan = pdTRUE;
      }
      if ((strcmp(taskStatus[xIdx].pcTaskName, "TaskB") == 0) && (taskStatus[xIdx].eCurrentState == eRunning))
      {
        xTaskBRan = pdTRUE;
      }
      if ((strcmp(taskStatus[xIdx].pcTaskName, "TaskC") == 0) && (taskStatus[xIdx].eCurrentState == eRunning))
      {
        xTaskCRan = pdTRUE;
      }
    }

    if (xTaskBRan == pdTRUE)
    {
      if (!((xTaskARan == pdTRUE) && (xTaskCRan == pdTRUE)))
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
      xTestFailed = pdTRUE;
    }
  }
}

void setup_test_fr2_001(void) {
  xTaskCreate(prvTaskA, "TaskA", configMINIMAL_STACK_SIZE, NULL,
              mainTASK_A_PRIORITY, NULL);

  xTaskCreate(prvTaskB, "TaskB", configMINIMAL_STACK_SIZE, NULL,
              mainTASK_B_PRIORITY, NULL);

  xTaskCreate(prvTaskC, "TaskC", configMINIMAL_STACK_SIZE, NULL,
              mainTASK_C_PRIORITY, NULL);
}

void setUp(void) {} /* Is run before every test, put unit init calls here. */
void tearDown(void) {
} /* Is run after every test, put unit clean-up calls here. */

int main(void) {
  initTestEnvironment();

  setup_test_fr2_001();

  vTaskStartScheduler();

  /* should never reach here */
  panic_unsupported();

  return 0;
}

static void prvTaskA(void *pvParameters) {
  // idle the task
  for (;;) {
    vTaskDelay(pdMS_TO_TICKS(10));
    busyWaitMicroseconds(100000);
  }
}

static void fr02_validateHigherPriorityTasksAlreadyRan(void)
{
  // xTestPassed and xTestFailed set by trace hook: test_fr2TASK_SWITCHED_IN

  TEST_ASSERT_FALSE(xTestFailed == pdTRUE);
  TEST_ASSERT_TRUE(xTestPassed == pdTRUE);
}

static void prvTaskB(void *pvParameters) {
  UNITY_BEGIN();

  RUN_TEST(fr02_validateHigherPriorityTasksAlreadyRan);

  UNITY_END();

  // idle the task
  for (;;) {
    vTaskDelay(pdMS_TO_TICKS(10));
    busyWaitMicroseconds(100000);
  }
}

static void prvTaskC(void *pvParameters) {
  // idle the task
  for (;;) {
    vTaskDelay(pdMS_TO_TICKS(10));
    busyWaitMicroseconds(100000);
  }
}
