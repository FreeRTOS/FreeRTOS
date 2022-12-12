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

#define mainSOFTWARE_TIMER_PERIOD_MS pdMS_TO_TICKS(10)

static void prvTaskA(void *pvParameters);
static void prvTaskB(void *pvParameters);

TaskHandle_t taskA, taskB;

#if configNUMBER_OF_CORES != 2
#error Require two cores be configured for FreeRTOS
#endif

void setup_test_fr11_001(void) {
  xTaskCreate(prvTaskA, "TaskA", configMINIMAL_STACK_SIZE, NULL,
              mainTASK_A_PRIORITY, &taskA);

  xTaskCreate(prvTaskB, "TaskB", configMINIMAL_STACK_SIZE, NULL,
              mainTASK_B_PRIORITY, &taskB);
}

void setUp(void) {} /* Is run before every test, put unit init calls here. */
void tearDown(void) {
} /* Is run after every test, put unit clean-up calls here. */

int main(void) {
  initTestEnvironment();

  UNITY_BEGIN();

  RUN_TEST(setup_test_fr11_001);

  vTaskStartScheduler();
  // AMPLaunchOnCore(1, vTaskStartScheduler);

  /* should never reach here */
  panic_unsupported();

  return 0; // UNITY_END is unreachable via this path. a state machine and
            // counter is used so that just one child task will call it
            // instead.
}

static uint32_t taskBState = 0;

char strbuf_pass[] = "TEST PASSED\n";
size_t strbuf_pass_len = sizeof(strbuf_pass) / sizeof(char);
char strbuf_fail[] = "TEST FAILED\n";
size_t strbuf_fail_len = sizeof(strbuf_fail) / sizeof(char);

static void prvTaskA(void *pvParameters) {
  int handlerNum = -1;
  TaskStatus_t taskStatus[16];
  UBaseType_t taskStatusArraySize = 16;
  unsigned long totalRunTime;
  bool taskBObservedRunning = false;
  int idx;
  int numTasksRunning;
  int attempt = 0;

  vTaskDelay(pdMS_TO_TICKS(5000));

  vTaskSuspendAll();

  vTaskPrioritySet(taskB, mainTASK_A_PRIORITY+1);

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

    vTaskDelay(mainSOFTWARE_TIMER_PERIOD_MS);

    attempt++;

    if (attempt > 10) {
      break;
    }
  }

  xTaskResumeAll();

  if (taskBObservedRunning)
  {
    sendReport(strbuf_fail, strbuf_fail_len);
  }
  else
  {
    setPin(LED_PIN);
    sendReport(strbuf_pass, strbuf_pass_len);
  }


  // idle the task
  for (;;) {
    vTaskDelay(mainSOFTWARE_TIMER_PERIOD_MS);
  }
}

static void prvTaskB(void *pvParameters) {
  int iter = 1;
  int numIters = 10;
  char strbuf[] = "task B enter critical section";
  size_t strbuf_len = sizeof(strbuf) / sizeof(char);

  clearPin(LED_PIN);

  // idle the task
  for (;;) {
    taskBState++;
    vTaskDelay(mainSOFTWARE_TIMER_PERIOD_MS);
  }
}

void vApplicationStackOverflowHook(TaskHandle_t xTask, char *pcTaskName) {
  (void)pcTaskName;
  (void)xTask;

  /* Run time stack overflow checking is performed if
  configconfigCHECK_FOR_STACK_OVERFLOW is defined to 1 or 2.  This hook
  function is called if a stack overflow is detected.  pxCurrentTCB can be
  inspected in the debugger if the task name passed into this function is
  corrupt. */
  for (;;)
    ;
}

void vApplicationTickHook(void) {
  static uint32_t ulCount = 0;
  ulCount++;
}

void vApplicationMallocFailedHook(void) {
  char strbuf[] = "Malloc Failed";
  size_t strbuf_len = sizeof(strbuf) / sizeof(char);

  sendReport(strbuf, strbuf_len);
}
