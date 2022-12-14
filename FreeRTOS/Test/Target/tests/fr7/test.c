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

static void prvTaskA(void *pvParameters);
static void prvTaskB(void *pvParameters);
static void prvTaskC(void *pvParameters);

#if configNUMBER_OF_CORES != 2
#error Require two cores be configured for FreeRTOS
#endif

TaskHandle_t taskA, taskB;

void setup_test_fr7_001(void) {
  xTaskCreate(prvTaskC, "TaskC", configMINIMAL_STACK_SIZE, NULL,
              mainTASK_C_PRIORITY, NULL);

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

  setup_test_fr7_001();

  vTaskStartScheduler();
  // AMPLaunchOnCore(1, vTaskStartScheduler);

  /* should never reach here */
  panic_unsupported();

  return 0; // UNITY_END is unreachable via this path. a state machine and
            // counter is used so that just one child task will call it
            // instead.
}

static uint32_t taskAState = 0;
static uint32_t taskBState = 0;
static uint32_t originalFreeHeap;
static uint32_t freeHeap;

static void prvTaskA(void *pvParameters) {
  while (taskBState < 0) {
    vTaskDelay(mainSOFTWARE_TIMER_PERIOD_MS);
  }

  taskAState++;

  originalFreeHeap = xPortGetFreeHeapSize();

  vTaskDelete(taskA);

  // idle the task
  for (;;) {
    vTaskDelay(mainSOFTWARE_TIMER_PERIOD_MS);
  }
}

static void prvTaskB(void *pvParameters) {

  taskBState++;

  // idle the task
  for (;;) {
    vTaskDelay(mainSOFTWARE_TIMER_PERIOD_MS);
  }
}

static void reportStatus(void) {
  TEST_ASSERT_TRUE(freeHeap == originalFreeHeap);
  if (freeHeap == originalFreeHeap)
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
  int attempt;

  while (taskAState < 0) {
    vTaskDelay(mainSOFTWARE_TIMER_PERIOD_MS);
  }

  vTaskDelete(taskB);

  for(attempt=1; attempt<100; attempt++)
  {
    vTaskDelay(mainSOFTWARE_TIMER_PERIOD_MS);
    freeHeap = xPortGetFreeHeapSize();
    if (freeHeap == originalFreeHeap) {
      break;
    }
  }

  RUN_TEST(reportStatus);

  UNITY_END();

  // idle the task
  for (;;) {
    vTaskDelay(mainSOFTWARE_TIMER_PERIOD_MS);
  }
}
