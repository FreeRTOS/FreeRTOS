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

#define TASK_BLOCK_TIME_MS ( 3000 )
#define TASK_BUSYLOOP_TIME_MS ( 100 )

static void prvTaskA(void *pvParameters);
static void prvTaskB(void *pvParameters);

TaskHandle_t taskA, taskB;

#if configNUMBER_OF_CORES != 2
#error Require two cores be configured for FreeRTOS
#endif

void setup_test_fr11_001(void) {
  xTaskCreate(prvTaskA, "TaskA", configMINIMAL_STACK_SIZE * 2, NULL,
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

  setup_test_fr11_001();

  vTaskStartScheduler();

  /* should never reach here */
  panic_unsupported();

  return 0; // UNITY_END is unreachable via this path. a state machine and
            // counter is used so that just one child task will call it
            // instead.
}

static uint32_t uTaskBState = 0;
static uint32_t uTempTaskBState = 0;

static void reportStatus(void) {
  TEST_ASSERT_TRUE(uTempTaskBState == 0);

  if( uTempTaskBState == 0 )
  {
    setPin(LED_PIN);
    sendReport(testPassedString, testPassedStringLen);
  }
  else
  {
    sendReport(testFailedString, testFailedStringLen);
  }
}

static void prvTaskA(void *pvParameters) {
  uint32_t uAttempTime = 0;

  vTaskSuspendAll();

  vTaskPrioritySet(taskB, mainTASK_A_PRIORITY+1);

  while( uTaskBState == 0 )
  {
    uAttempTime++;

    if( uAttempTime > ( TASK_BLOCK_TIME_MS / TASK_BUSYLOOP_TIME_MS ) )
    {
      /* Break after polling 30 times. (total 3s) */
      break;
    }

    /* Wait 100ms. */
    busyWaitMicroseconds( TASK_BUSYLOOP_TIME_MS * 1000 );
  }

  /* Cache uTaskBState before resuming all tasks. */
  uTempTaskBState = uTaskBState;

  xTaskResumeAll();

  RUN_TEST(reportStatus);

  UNITY_END();
 
  // idle the task
  for (;;) {
    vTaskDelay(mainSOFTWARE_TIMER_PERIOD_MS);
  }
}

static void prvTaskB(void *pvParameters) {
  uTaskBState++;

  // idle the task
  for (;;) {
    vTaskDelay(mainSOFTWARE_TIMER_PERIOD_MS);
  }
}
