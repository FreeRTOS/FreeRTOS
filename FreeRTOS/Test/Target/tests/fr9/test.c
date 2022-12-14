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
#define mainTASK_C_PRIORITY (tskIDLE_PRIORITY + 1)

#define mainSOFTWARE_TIMER_PERIOD_MS pdMS_TO_TICKS(10)

static void prvTaskA(void *pvParameters);
static void prvTaskB(void *pvParameters);
static void prvTaskC(void *pvParameters);

#if configNUMBER_OF_CORES != 2
#error Require two cores be configured for FreeRTOS
#endif

static bool testFailed = false;
static bool testPassed = false;

void test_fr9TASK_SWITCHED_IN(void) {
  UBaseType_t idx, numTasksRunning;
  TaskStatus_t taskStatus[16];
  UBaseType_t taskStatusArraySize = 16;
  unsigned long totalRunTime;
  int coreIndex = 0;
  SchedTraceLogRow *logRow;
  int retcode = 0;

  static int taskSwitchCount = 0;
  static bool taskARan = false;
  static bool taskBRan = false;
  static bool taskCRan = false;

  if (!(testPassed || testFailed))
  {
    numTasksRunning = uxTaskGetSystemState((TaskStatus_t * const)&taskStatus, taskStatusArraySize, &totalRunTime);

    for(idx = 0; idx < numTasksRunning; idx++)
    {
      if ((strcmp(taskStatus[idx].pcTaskName, "TaskA") == 0) && (taskStatus[idx].eCurrentState == eRunning))
      {
        taskARan = true;
        sendReport("taskA\n\0", 0);
      }
      if ((strcmp(taskStatus[idx].pcTaskName, "TaskB") == 0) && (taskStatus[idx].eCurrentState == eRunning))
      {
        taskBRan = true;
        sendReport("taskB\n\0", 0);
      }
      if ((strcmp(taskStatus[idx].pcTaskName, "TaskC") == 0) && (taskStatus[idx].eCurrentState == eRunning))
      {
        taskCRan = true;
        sendReport("taskC\n\0", 0);
      }
    }

    if (taskCRan && taskBRan)
    {
      testPassed = true;
    }

    taskSwitchCount++;
    if (taskSwitchCount > 1500)
    {
      testFailed = true;
    }
  }
}

TaskHandle_t taskA;

void setup_test_fr9_001(void) {
  xTaskCreate(prvTaskA, "TaskA", configMINIMAL_STACK_SIZE, NULL,
              mainTASK_A_PRIORITY, &taskA);
  vTaskCoreAffinitySet(taskA, 0x2);

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

  UNITY_BEGIN();

  setup_test_fr9_001();

  vTaskStartScheduler();

  /* should never reach here */
  panic_unsupported();

  return 0; // UNITY_END is unreachable via this path. a state machine and
            // counter is used so that just one child task will call it
            // instead.
}

static void reportStatus(void) {
  TEST_ASSERT_TRUE(testPassed);

  if (testPassed)
  {
      setPin(LED_PIN);
      sendReport(testPassedString, testPassedStringLen);
  }
  else
  {
      sendReport(testFailedString, testFailedStringLen);
  }
}

static void checkTestStatus(void) {
  static bool statusReported = false;

  if (!statusReported)
  {
    if (testPassed || testFailed)
    {
      RUN_TEST(reportStatus);
      UNITY_END();
      statusReported = true;
    }
  }
}

static void prvTaskA(void *pvParameters) {
  taskENTER_CRITICAL();
  busyWaitMicroseconds(2000000);
  taskEXIT_CRITICAL();

  // idle the task
  for (;;) {
    vTaskDelay(mainSOFTWARE_TIMER_PERIOD_MS);
    checkTestStatus();
    busyWaitMicroseconds(100000);
  }
}

static void prvTaskB(void *pvParameters) {
  int iter = 1;
  int numIters = 10;
  char strbuf[] = "TRACE: task B enter critical section\n\0";
  size_t strbuf_len = sizeof(strbuf) / sizeof(char);

  vTaskDelay(pdMS_TO_TICKS(250));

  taskENTER_CRITICAL();
  busyWaitMicroseconds(2000000);
  taskEXIT_CRITICAL();

  // idle the task
  for (;;) {
    vTaskDelay(mainSOFTWARE_TIMER_PERIOD_MS);
    checkTestStatus();
    busyWaitMicroseconds(100000);
  }
}

static void prvTaskC(void *pvParameters) {
  // idle the task
  for (;;) {
    vTaskDelay(mainSOFTWARE_TIMER_PERIOD_MS);
    checkTestStatus();
    busyWaitMicroseconds(100000);
  }
}

