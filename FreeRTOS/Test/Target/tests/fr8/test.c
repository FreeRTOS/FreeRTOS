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

#define mainSOFTWARE_TIMER_PERIOD_MS pdMS_TO_TICKS(1000)

static void prvTaskA(void *pvParameters);
static void prvTaskB(void *pvParameters);

#if configNUM_CORES != 2
#error Require two cores be configured for FreeRTOS
#endif

void test_fr8(void) {
  xTaskCreate(prvTaskA, "TaskA", configMINIMAL_STACK_SIZE, NULL,
              mainTASK_A_PRIORITY, NULL);

  xTaskCreate(prvTaskB, "TaskB", configMINIMAL_STACK_SIZE, NULL,
              mainTASK_B_PRIORITY, NULL);

  vTaskStartScheduler();

  /* should never reach here */
  panic_unsupported();
}

void setUp(void) {} /* Is run before every test, put unit init calls here. */
void tearDown(void) {
} /* Is run after every test, put unit clean-up calls here. */

int main(void) {
  initTestEnvironment();

  UNITY_BEGIN();

  RUN_TEST(test_fr8);

  return 0; // UNITY_END is unreachable via this path. a state machine and
            // counter is used so that just one child task will call it
            // instead.
}

static uint32_t taskAState = 1;
static uint32_t taskBState = 1;

static void prvTaskA(void *pvParameters) {
  int bStateCopy;
  int iter=1;
  int numIters=5;

  bStateCopy = taskBState;

  taskENTER_CRITICAL( );

  for (iter=1;iter< numIters;iter++) {
    vTaskDelay(mainSOFTWARE_TIMER_PERIOD_MS);
    TEST_ASSERT_EQUAL_INT(bStateCopy, taskBState);
    taskAState++;
  }

  taskEXIT_CRITICAL( );
}

static void prvTaskB(void *pvParameters) {
  int aStateCopy;
  int iter=1;
  int numIters=5;

  aStateCopy = taskAState;

  taskENTER_CRITICAL( );

  for (iter=1;iter< numIters;iter++) {
    vTaskDelay(mainSOFTWARE_TIMER_PERIOD_MS);
    TEST_ASSERT_EQUAL_INT(aStateCopy, taskAState);
    taskBState++;
  }

  taskEXIT_CRITICAL(  );
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
  size_t strbuf_len = sizeof(char) / sizeof(strbuf);

  sendReport(strbuf, strbuf_len);
}
