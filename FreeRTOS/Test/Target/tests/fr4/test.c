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

void setup_test_fr4_001(void) {
  xTaskCreate(prvTaskA, "TaskA", configMINIMAL_STACK_SIZE * 2, NULL,
              mainTASK_A_PRIORITY, NULL);

  xTaskCreate(prvTaskB, "TaskB", configMINIMAL_STACK_SIZE, NULL,
              mainTASK_B_PRIORITY, NULL);
}

void setUp(void) {} /* Is run before every test, put unit init calls here. */
void tearDown(void) {
} /* Is run after every test, put unit clean-up calls here. */

int main(void) {
  initTestEnvironment();

  setup_test_fr4_001();

  vTaskStartScheduler();

  /* should never reach here */
  panic_unsupported();

  return 0;
}

static bool taskBObservedRunning = false;

static void fr04_validateTasksDoNotRunAtSameTime(void) {
  int handlerNum = -1;
  TaskStatus_t taskStatus[16];
  UBaseType_t taskStatusArraySize = 16;
  unsigned long totalRunTime;
  int idx;
  int attempt = 1;
  int numTasksRunning;

  while(!taskBObservedRunning)
  {
    numTasksRunning = uxTaskGetSystemState((TaskStatus_t * const)&taskStatus, taskStatusArraySize, &totalRunTime);

    for(idx=0; idx < numTasksRunning; idx++)
    {
      if ((strcmp(taskStatus[idx].pcTaskName, "TaskB") == 0) && (taskStatus[idx].eCurrentState == eRunning))
      {
        taskBObservedRunning = true;
      }
    }

    vTaskDelay(pdMS_TO_TICKS(10));

    attempt++;

    if (attempt > 25) {
      break;
    }
  }

  TEST_ASSERT_TRUE(!taskBObservedRunning);

  if (taskBObservedRunning)
  {
    sendReport(pcTestFailedString, xTestFailedStringLen);
  }
  else
  {
    setPin(LED_PIN);
    sendReport(pcTestPassedString, xTestPassedStringLen);
  }
}

static void prvTaskA(void *pvParameters) {
  UNITY_BEGIN();

  RUN_TEST(fr04_validateTasksDoNotRunAtSameTime);

  UNITY_END();

// idle the task
  for (;;) {
    vTaskDelay(pdMS_TO_TICKS(10));
    busyWaitMicroseconds(100000);
  }
}

static void prvTaskB(void *pvParameters) {
  // idle the task
  for (;;) {
    vTaskDelay(pdMS_TO_TICKS(10));
    busyWaitMicroseconds(100000);
  }
}
