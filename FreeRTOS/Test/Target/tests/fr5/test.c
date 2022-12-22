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
#define mainTASK_A_PRIORITY (tskIDLE_PRIORITY + 1)
#define mainTASK_B_PRIORITY (tskIDLE_PRIORITY + 2)

static void prvTaskA(void *pvParameters);
static void prvTaskB(void *pvParameters);

#if configNUMBER_OF_CORES != 2
#error Require two cores be configured for FreeRTOS
#endif

TaskHandle_t taskA, taskB;

void setup_test_fr5_001(void) {
  xTaskCreate(prvTaskA, "TaskA", configMINIMAL_STACK_SIZE, NULL,
              mainTASK_A_PRIORITY, &taskA);
  vTaskCoreAffinitySet(taskA, 0x1);

  xTaskCreate(prvTaskB, "TaskB", configMINIMAL_STACK_SIZE, NULL,
              mainTASK_B_PRIORITY, &taskB);
  vTaskCoreAffinitySet(taskB, 0x2);
}

void setUp(void) {} /* Is run before every test, put unit init calls here. */
void tearDown(void) {
} /* Is run after every test, put unit clean-up calls here. */

int main(void) {
  initTestEnvironment();

  setup_test_fr5_001();

  vTaskStartScheduler();

  /* should never reach here */
  panic_unsupported();

  return 0;
}

static bool taskADone = false;
static bool taskAOnCorrectCore = true;
static bool taskBOnCorrectCore = true;

static void prvTaskA(void *pvParameters) {
  BaseType_t core;

  int iter;

  for(iter=1;iter < 25;iter++)
  {
    vTaskDelay(pdMS_TO_TICKS(10));
    core = portGET_CORE_ID();
    if (core != 0)
    {
      taskAOnCorrectCore = false;
    }
  }

  taskADone = true;

  // idle the task
  for (;;) {
    vTaskDelay(pdMS_TO_TICKS(10));
    busyWaitMicroseconds(100000);
  }
}

static void fr05_validateTasksOnlyRunOnAssignedCores(void) {
  BaseType_t core;
  int iter;

  for(iter=1;iter < 25;iter++)
  {
    vTaskDelay(pdMS_TO_TICKS(10));
    core = portGET_CORE_ID();
    if (core != 1)
    {
      taskBOnCorrectCore = false;
    }
  }

  while(!taskADone)
  {
    vTaskDelay(pdMS_TO_TICKS(10));
    busyWaitMicroseconds(100000);
  }

  TEST_ASSERT_TRUE(taskAOnCorrectCore && taskBOnCorrectCore);

  if (taskAOnCorrectCore && taskBOnCorrectCore)
  {
    setPin(LED_PIN);
    sendReport(testPassedString, testPassedStringLen);
  }
  else
  {
    sendReport(testFailedString, testFailedStringLen);
  }
}

static void prvTaskB(void *pvParameters)
{
  UNITY_BEGIN();

  RUN_TEST(fr05_validateTasksOnlyRunOnAssignedCores);

  UNITY_END();
  // idle the task
  for (;;) {
    vTaskDelay(pdMS_TO_TICKS(10));
  }
}
