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

static void prvTaskA(void *pvParameters);
static void prvTaskB(void *pvParameters);
static void prvTaskC(void *pvParameters);

#if configNUMBER_OF_CORES != 2
#error Require two cores be configured for FreeRTOS
#endif

static bool testFailed = false;
static bool allTasksHaveRun = false;
static bool taskAHasEnteredCriticalSection = false;
static bool taskAHasExitedCriticalSection = false;
static bool taskBHasEnteredCriticalSection = false;

static int taskSwitchCount = 0;
static bool taskARan = false;
static bool taskBRan = false;
static bool taskCRan = false;

void test_fr9TASK_SWITCHED_IN(void) {
  UBaseType_t idx, numTasksRunning;
  TaskStatus_t taskStatus[16];
  UBaseType_t taskStatusArraySize = 16;
  unsigned long totalRunTime;
  int coreIndex = 0;
  SchedTraceLogRow *logRow;
  int retcode = 0;

  if (!(allTasksHaveRun || testFailed))
  {
    numTasksRunning = uxTaskGetSystemState((TaskStatus_t * const)&taskStatus, taskStatusArraySize, &totalRunTime);

    for(idx = 0; idx < numTasksRunning; idx++)
    {
      if ((strcmp(taskStatus[idx].pcTaskName, "TaskA") == 0) && (taskStatus[idx].eCurrentState == eRunning))
      {
        taskARan = true;
      }
      if ((strcmp(taskStatus[idx].pcTaskName, "TaskB") == 0) && (taskStatus[idx].eCurrentState == eRunning))
      {
        taskBRan = true;
      }
      if ((strcmp(taskStatus[idx].pcTaskName, "TaskC") == 0) && (taskStatus[idx].eCurrentState == eRunning))
      {
        taskCRan = true;
      }
    }

    if (taskARan && taskCRan && taskBRan)
    {
      allTasksHaveRun = true;
    }

    taskSwitchCount++;
    if (taskSwitchCount > 1500)
    {
      testFailed = true;
    }
  }
}

TaskHandle_t taskA, taskB;

void setup_test_fr9_001(void) {
  xTaskCreateAffinitySet(prvTaskA, "TaskA", configMINIMAL_STACK_SIZE, NULL,
              mainTASK_A_PRIORITY, 0x2, &taskA);

  xTaskCreate(prvTaskB, "TaskB", configMINIMAL_STACK_SIZE, NULL,
              mainTASK_B_PRIORITY, &taskB);

  xTaskCreate(prvTaskC, "TaskC", configMINIMAL_STACK_SIZE, NULL,
              mainTASK_C_PRIORITY, NULL);
}

void setUp(void) {} /* Is run before every test, put unit init calls here. */
void tearDown(void) {
} /* Is run after every test, put unit clean-up calls here. */

int main(void) {
  initTestEnvironment();

  setup_test_fr9_001();

  vTaskStartScheduler();

  /* should never reach here */
  panic_unsupported();

  return 0;
}

static void prvTaskA(void *pvParameters) {
  taskENTER_CRITICAL();
  taskAHasEnteredCriticalSection=true;
  busyWaitMicroseconds(250000);
  xTaskNotify(taskB, 0, eNoAction);
  busyWaitMicroseconds(10000000);
  taskEXIT_CRITICAL();
  taskAHasExitedCriticalSection = true;

  // idle the task
  for (;;) {
    vTaskDelay(pdMS_TO_TICKS(10));
    busyWaitMicroseconds(100000);
  }
}

static void prvTaskB(void *pvParameters) {
  vTaskDelay(pdMS_TO_TICKS(10));

  taskENTER_CRITICAL();
  taskBHasEnteredCriticalSection = true;
  busyWaitMicroseconds(8000000);
  taskEXIT_CRITICAL();

  // idle the task
  for (;;) {
    vTaskDelay(pdMS_TO_TICKS(10));
    busyWaitMicroseconds(100000);
  }
}

static void fr09_validateAllTasksHaveRun(void)
{
  char str[100];

  //TEST_ASSERT_TRUE(allTasksHaveRun && !taskBHasEnteredCriticalSection);

  sprintf(str, "TRACE: switchCount=%d, %s,%s,%s %s,%s,%s\n\0", taskSwitchCount,
    taskARan ? "T" : "F",
    taskBRan ? "T" : "F",
    taskCRan ? "T" : "F",
    taskAHasEnteredCriticalSection ? "T" : "F",
    taskAHasExitedCriticalSection ? "T" : "F",
    taskBHasEnteredCriticalSection ? "T" : "F");
  sendReport(str, 0);

  if (allTasksHaveRun)
  {
    sendReport("allTasksHaveRun\n\0", 0);
  }

  if (taskBHasEnteredCriticalSection)
  {
    sendReport("taskBHasEnteredCriticalSection\n\0", 0);
  }

  if (allTasksHaveRun && !taskBHasEnteredCriticalSection)
  {
      setPin(LED_PIN);
      sendReport(testPassedString, testPassedStringLen);
  }
  else
  {
      sendReport(testFailedString, testFailedStringLen);
  }
}

static void prvTaskC(void *pvParameters) {
  busyWaitMicroseconds(250000);

  UNITY_BEGIN();

  RUN_TEST(fr09_validateAllTasksHaveRun);
  
  UNITY_END();

  // idle the task
  for (;;) {
    vTaskDelay(pdMS_TO_TICKS(10));
    busyWaitMicroseconds(100000);
  }
}

