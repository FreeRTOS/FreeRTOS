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

#define mainSOFTWARE_TIMER_PERIOD_MS pdMS_TO_TICKS(10)

char strbuf_good[] = "TEST PASSED\n\0";
size_t strbuf_good_len = sizeof(strbuf_good) / sizeof(char);

static void prvTaskA(void *pvParameters);
static void prvTaskB(void *pvParameters);

TaskHandle_t taskA, taskB;

#if configNUMBER_OF_CORES != 2
#error Require two cores be configured for FreeRTOS
#endif

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

  UNITY_BEGIN();

  RUN_TEST(setup_test_fr5_001);

  vTaskStartScheduler();
  // AMPLaunchOnCore(1, vTaskStartScheduler);

  /* should never reach here */
  panic_unsupported();

  return 0; // UNITY_END is unreachable via this path. a state machine and
            // counter is used so that just one child task will call it
            // instead.
}

static uint32_t taskBState = 0;

static void prvTaskA(void *pvParameters) {
  char strbuf_bad[] = "task A running on the wrong core\n\0";
  size_t strbuf_bad_len = sizeof(strbuf_bad) / sizeof(char);
  BaseType_t core;

  int iter;

  vTaskDelay(pdMS_TO_TICKS(5000));

  for(iter=1;iter < 10;iter++)
  {
    vTaskDelay(pdMS_TO_TICKS(100));
    core = portGET_CORE_ID();
    if (core != 0)
    {
      sendReport(strbuf_bad, strbuf_bad_len);
    }
    TEST_ASSERT_EQUAL_INT(core, 0);
  }

  sendReport(strbuf_good, strbuf_good_len);

  // idle the task
  for (;;) {
    vTaskDelay(mainSOFTWARE_TIMER_PERIOD_MS);
  }
}

static void prvTaskB(void *pvParameters) {
  char strbuf_bad[] = "task B running on the wrong core\n\0";
  size_t strbuf_bad_len = sizeof(strbuf_bad) / sizeof(char);
  BaseType_t core;

  int iter;

  vTaskDelay(pdMS_TO_TICKS(5000));

  for(iter=1;iter < 10;iter++)
  {
    vTaskDelay(pdMS_TO_TICKS(100));
    core = portGET_CORE_ID();
    if (core != 1)
    {
      sendReport(strbuf_bad, strbuf_bad_len);
    }
    TEST_ASSERT_EQUAL_INT(core, 1);
  }

  sendReport(strbuf_good, strbuf_good_len);

  // idle the task
  for (;;) {
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
  char strbuf[] = "Malloc Failed\n\0";
  size_t strbuf_len = sizeof(strbuf) / sizeof(char);

  sendReport(strbuf, strbuf_len);
}
