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

static void prvUnityStarter(void *pvParameters);
static void prvTaskA(void *pvParameters);
static void prvTaskB(void *pvParameters);

static void fr07_memoryFreedTaskRemoteDeleted();
static void fr07_memoryFreedTaskSelfDeleted();

#if configNUMBER_OF_CORES != 2
#error Require two cores be configured for FreeRTOS
#endif

TaskHandle_t taskA, taskB;

void setup_test_fr7_001(void) {
  xTaskCreate(prvUnityStarter, "unityStarter", configMINIMAL_STACK_SIZE, NULL,
              mainTASK_C_PRIORITY, NULL);
}

void setUp(void) {} /* Is run before every test, put unit init calls here. */
void tearDown(void) {
} /* Is run after every test, put unit clean-up calls here. */

int main(void) {
  initTestEnvironment();

  setup_test_fr7_001();

  vTaskStartScheduler();
  // AMPLaunchOnCore(1, vTaskStartScheduler);

  /* should never reach here */
  panic_unsupported();

  return 0;
}

static volatile uint32_t taskAState = 0;
static volatile uint32_t taskBState = 0;

static uint32_t ulOriginalFreeHeapSize;

static void prvUnityStarter(void *pvParameters)
{
  UNITY_BEGIN();
  
  RUN_TEST( fr07_memoryFreedTaskSelfDeleted );
  RUN_TEST( fr07_memoryFreedTaskRemoteDeleted );

  UNITY_END();

  // idle the task
  for (;;) {
    vTaskDelay(mainSOFTWARE_TIMER_PERIOD_MS);
  }
}

static void createSelfDeleteTaskA()
{
  xTaskCreate(prvTaskA, "TaskA", configMINIMAL_STACK_SIZE, NULL,
              mainTASK_A_PRIORITY, &taskA);
}

static void createRemoteDeleteTaskB()
{
  xTaskCreate(prvTaskB, "TaskB", configMINIMAL_STACK_SIZE, NULL,
              mainTASK_B_PRIORITY, &taskB);
}

static void prvTaskA(void *pvParameters) {
  taskAState++;

  vTaskDelete( NULL );
}

static void prvTaskB(void *pvParameters) {
  taskBState++;

  // idle the task
  for (;;) {
    vTaskDelay(mainSOFTWARE_TIMER_PERIOD_MS);
  }
}

static void fr07_memoryFreedTaskSelfDeleted() {
  int attempt;
  uint32_t ulFreeHeapSize = 0;

  ulOriginalFreeHeapSize = xPortGetFreeHeapSize();

  createSelfDeleteTaskA();

  while (taskAState <= 0) {
    vTaskDelay(mainSOFTWARE_TIMER_PERIOD_MS);
  }

  for(attempt=1; attempt<100; attempt++)
  {
    /* Reserve for idle task to delete the entire task. */
    vTaskDelay(mainSOFTWARE_TIMER_PERIOD_MS);
    ulFreeHeapSize = xPortGetFreeHeapSize();
    if (ulFreeHeapSize == ulOriginalFreeHeapSize) {
      break;
    }
  }
  
  TEST_ASSERT_TRUE(ulFreeHeapSize == ulOriginalFreeHeapSize);
}

static void fr07_memoryFreedTaskRemoteDeleted() {
  int attempt;
  uint32_t ulFreeHeapSize = 0;

  ulOriginalFreeHeapSize = xPortGetFreeHeapSize();

  createRemoteDeleteTaskB();

  while (taskBState <= 0) {
    vTaskDelay(mainSOFTWARE_TIMER_PERIOD_MS);
  }

  vTaskDelete(taskB);

  for(attempt=1; attempt<100; attempt++)
  {
    /* Reserve for idle task to delete the entire task. */
    vTaskDelay(mainSOFTWARE_TIMER_PERIOD_MS);
    ulFreeHeapSize = xPortGetFreeHeapSize();
    if (ulFreeHeapSize == ulOriginalFreeHeapSize) {
      break;
    }
  }
  
  TEST_ASSERT_TRUE(ulFreeHeapSize == ulOriginalFreeHeapSize);
}
