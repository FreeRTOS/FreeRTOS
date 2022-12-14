/* Kernel includes. */
#include "FreeRTOS.h" /* Must come first. */
#include "queue.h"    /* RTOS queue related API prototypes. */
#include "semphr.h"   /* Semaphore related API prototypes. */
#include "task.h"     /* RTOS task related API prototypes. */
#include "timers.h"   /* Software timer related API prototypes. */

#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>

#include "bsl.h"
#include "unity.h" /* unit testing support functions */

/* Priorities at which the tasks are created.  The max priority can be specified
as ( configMAX_PRIORITIES - 1 ). */
#define mainTASK_A_PRIORITY (tskIDLE_PRIORITY + 1)
#define mainTASK_B_PRIORITY (tskIDLE_PRIORITY + 2)

#define mainSOFTWARE_TIMER_PERIOD_MS pdMS_TO_TICKS(10)

static void prvTaskA(void *pvParameters);
static void prvTaskB(void *pvParameters);

#if configNUMBER_OF_CORES != 2
#error Require two cores be configured for FreeRTOS
#endif

void setup_test_fr8_001(void) {
  xTaskCreate(prvTaskA, "TaskA", configMINIMAL_STACK_SIZE, NULL,
              mainTASK_A_PRIORITY, NULL);

  xTaskCreate(prvTaskB, "TaskB", configMINIMAL_STACK_SIZE, NULL,
              mainTASK_B_PRIORITY, NULL);
}

void setUp(void) {} /* Is run before every test, put unit init calls here. */
void tearDown(void) {
} /* Is run after every test, put unit clean-up calls here. */

int main(void) {
  initTestEnvironment();

  UNITY_BEGIN();

  setup_test_fr8_001();

  vTaskStartScheduler();

  /* should never reach here */
  panic_unsupported();

  return 0; // UNITY_END is unreachable via this path. a state machine and
            // counter is used so that just one child task will call it
            // instead.
}

static uint32_t taskBState = 0;
static bool isrAssertionComplete = false;

static void softwareInterruptHandlerSimple(void) {
  int i;
  UBaseType_t uxSavedInterruptStatus;

  char strbuf_a[] = "TRACE: ISR enter\n\0";
  size_t strbuf_a_len = sizeof(strbuf_a) / sizeof(char);

  char strbuf_b[] = "TRCE: ISR exit\n\0";
  size_t strbuf_b_len = sizeof(strbuf_b) / sizeof(char);

  sendReport(strbuf_a, strbuf_a_len);
  uxSavedInterruptStatus = taskENTER_CRITICAL_FROM_ISR();

  clearPin(LED_PIN);

  taskEXIT_CRITICAL_FROM_ISR(uxSavedInterruptStatus);
  sendReport(strbuf_b, strbuf_b_len);

  isrAssertionComplete = true;
}

static void reportStatus(void) {
  TEST_ASSERT_TRUE(isrAssertionComplete);

  if (isrAssertionComplete)
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
    if (isrAssertionComplete)
    {
      RUN_TEST(reportStatus);
      UNITY_END();
      statusReported = true;
    }
  }
}

static void prvTaskA(void *pvParameters) {
  int handlerNum = -1;

  // wait for Task B to get to 6 itertions
  for (;;) {
    vTaskDelay(mainSOFTWARE_TIMER_PERIOD_MS);
    if (taskBState > 5) {
      break;
    }
  }

  setPin(LED_PIN);

  handlerNum = registerSoftwareInterruptHandler(softwareInterruptHandlerSimple);
  triggerSoftwareInterrupt(handlerNum);

  // idle the task
  for (;;) {
    vTaskDelay(mainSOFTWARE_TIMER_PERIOD_MS);
    checkTestStatus();
  }
}

static void prvTaskB(void *pvParameters) {
  int iter = 1;
  int numIters = 10;
  char strbuf[] = "TRACE: task B enter critical section\n\0";
  size_t strbuf_len = sizeof(strbuf) / sizeof(char);

  sendReport(strbuf, strbuf_len);

  for (iter = 1; iter < numIters; iter++) {
    vTaskDelay(mainSOFTWARE_TIMER_PERIOD_MS * 50);
    while (taskBState == 6 && !isrAssertionComplete) {
      vTaskDelay(mainSOFTWARE_TIMER_PERIOD_MS * 50);
    }
    taskENTER_CRITICAL();
    taskBState++;
    if ((iter % 2) == 0) {
      clearPin(LED_PIN);
    } else {
      setPin(LED_PIN);
    }
    taskEXIT_CRITICAL();
  }

  // idle the task
  for (;;) {
    vTaskDelay(mainSOFTWARE_TIMER_PERIOD_MS);
  }
}
