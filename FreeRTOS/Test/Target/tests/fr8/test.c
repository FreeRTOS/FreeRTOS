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
#define mainTASK_B_PRIORITY (tskIDLE_PRIORITY + 1)

#define mainSOFTWARE_TIMER_PERIOD_MS pdMS_TO_TICKS(10)

static void prvTaskA(void *pvParameters);
static void prvTaskB(void *pvParameters);

#if configNUM_CORES != 2
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

  RUN_TEST(setup_test_fr8_001);

  vTaskStartScheduler();
  // AMPLaunchOnCore(1, vTaskStartScheduler);

  /* should never reach here */
  panic_unsupported();

  return 0; // UNITY_END is unreachable via this path. a state machine and
            // counter is used so that just one child task will call it
            // instead.
}

static uint32_t taskBState = 0;

static void softwareInterruptHandlerSimple(void) {
  int i;
  char strbuf_a[] = "ISR enter";
  size_t strbuf_a_len = sizeof(char) / sizeof(strbuf_a);

  char strbuf_b[] = "ISR exit";
  size_t strbuf_b_len = sizeof(char) / sizeof(strbuf_b);

  sendReport(strbuf_a, strbuf_a_len);
  taskENTER_CRITICAL();

  TEST_ASSERT_EQUAL_INT(taskBState, 6);

  taskEXIT_CRITICAL();
  sendReport(strbuf_b, strbuf_b_len);

  for (i = 0;; i++) {
    vTaskDelay(mainSOFTWARE_TIMER_PERIOD_MS * 100);
    if ((i % 2) == 0) {
      clearPin(LED_PIN);
    } else {
      setPin(LED_PIN);
    }
  }
}

static void prvTaskA(void *pvParameters) {
  int handlerNum = -1;

  // wait for Task B to exit the critical section
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
  }
}

static void prvTaskB(void *pvParameters) {
  int iter = 1;
  int numIters = 10;
  char strbuf[] = "task B enter critical section";
  size_t strbuf_len = sizeof(char) / sizeof(strbuf);

  vTaskDelay(pdMS_TO_TICKS(5000));

  sendReport(strbuf, strbuf_len);

  for (iter = 1; iter < numIters; iter++) {
    vTaskDelay(mainSOFTWARE_TIMER_PERIOD_MS * 100);
    taskENTER_CRITICAL();
    taskBState++;
    if ((iter % 2) == 0) {
      clearPin(LED_PIN);
    } else {
      setPin(LED_PIN);
    }
    taskEXIT_CRITICAL();
  }

  taskENTER_CRITICAL();
  taskBState++;
  taskEXIT_CRITICAL();

  // idle the task
  for (;;) {
    vTaskDelay(mainSOFTWARE_TIMER_PERIOD_MS);
  }
}

#if 0
static void prvTaskC(void *pvParameters) {
  BaseType_t xReturned;

  while (fr8_001_taskCompletions < 2) {
    vTaskDelay(pdMS_TO_TICKS(33));
  }

  xReturned = xTaskNotify( xTaskD, 0x00, eSetValueWithOverwrite );
  configASSERT( xReturned == pdPASS );
  ( void ) xReturned; /* In case configASSERT() is not defined. */

  xReturned = xTaskNotify( xTaskD, 0x01, eSetValueWithOverwrite );
  configASSERT( xReturned == pdPASS );
  ( void ) xReturned; /* In case configASSERT() is not defined. */
}

static void prvTaskD(void *pvParameters) {
  int aStateCopy;
  int iter=1;
  int numIters=5;

  while (fr8_001_taskCompletions < 2) {
    vTaskDelay(pdMS_TO_TICKS(33));
  }

  aStateCopy = taskAState;

  taskENTER_CRITICAL( );

  for (iter=1;iter< numIters;iter++) {
    vTaskDelay(mainSOFTWARE_TIMER_PERIOD_MS);
    TEST_ASSERT_EQUAL_INT(aStateCopy, taskAState);
    taskBState++;
  }

  taskEXIT_CRITICAL(  );
}
#endif

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
  size_t strbuf_len = sizeof(char) / sizeof(strbuf);

  sendReport(strbuf, strbuf_len);
}
