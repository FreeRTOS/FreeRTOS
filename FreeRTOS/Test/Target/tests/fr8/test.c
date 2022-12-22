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
static bool isrObservedTaskBInsideCriticalSection = false;
static bool insideTaskBCriticalSection = false;

static void softwareInterruptHandlerSimple(void) {
  int iter;
  UBaseType_t uxSavedInterruptStatus;

  for(iter = 1; iter < 10; iter++)
  {
    uxSavedInterruptStatus = taskENTER_CRITICAL_FROM_ISR();
    if (insideTaskBCriticalSection)
    {
      isrObservedTaskBInsideCriticalSection = true;
    }
    busyWaitMicroseconds(10000);
    taskEXIT_CRITICAL_FROM_ISR(uxSavedInterruptStatus);
  }

  isrAssertionComplete = true;
}

static void prvTaskA(void *pvParameters) {
  int handlerNum = -1;

  // wait for Task B to get to 6 itertions
  for (;;) {
    vTaskDelay(pdMS_TO_TICKS(10));
    if (taskBState > 5) {
      break;
    }
  }

  handlerNum = registerSoftwareInterruptHandler(softwareInterruptHandlerSimple);
  triggerSoftwareInterrupt(handlerNum);

  // idle the task
  for (;;) {
    vTaskDelay(pdMS_TO_TICKS(10));
  }
}

void fr08_validateOnlyOneCriticalSectionRanAtATime(void)
{
  TEST_ASSERT_TRUE(isrAssertionComplete && !isrObservedTaskBInsideCriticalSection);

  if (isrAssertionComplete && !isrObservedTaskBInsideCriticalSection)
  {
      setPin(LED_PIN);
      sendReport(testPassedString, testPassedStringLen);
  }
  else
  {
      sendReport(testFailedString, testFailedStringLen);
  }
}

static void prvTaskB(void *pvParameters) {
  int iter = 1;

  for (iter = 1; iter < 10; iter++) {
    vTaskDelay(pdMS_TO_TICKS(10));
    while (taskBState == 6 && !isrAssertionComplete) {
      vTaskDelay(pdMS_TO_TICKS(10));
    }
    taskENTER_CRITICAL();
    insideTaskBCriticalSection = true;
    busyWaitMicroseconds(10000);
    taskBState++;
    insideTaskBCriticalSection = false;
    taskEXIT_CRITICAL();
  }

  while (!isrAssertionComplete) {
      vTaskDelay(pdMS_TO_TICKS(10));
  }

  UNITY_BEGIN();

  RUN_TEST(fr08_validateOnlyOneCriticalSectionRanAtATime);

  UNITY_END();

  // idle the task
  for (;;) {
    vTaskDelay(pdMS_TO_TICKS(10));
  }
}
