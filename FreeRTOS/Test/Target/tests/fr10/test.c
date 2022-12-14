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

#define COUNTER_MAX ( 3000 )

#define mainSOFTWARE_TIMER_PERIOD_MS pdMS_TO_TICKS(10)

static void prvUnityStarter(void *pvParameters);
static void fr10_onlyOneTaskEnterSuspendAll();
static void prvTaskA(void);
static void prvTaskB(void *pvParameters);

TaskHandle_t taskAHandle;
volatile BaseType_t xTaskACounter = 0;
volatile BaseType_t xIsTaskBFinished = pdFALSE;

#if configNUMBER_OF_CORES != 2
#error Require two cores be configured for FreeRTOS
#endif

void setup_test_task(void) {
  /* unityStarter run as Task A after setting Unity. */
  xTaskCreate(prvUnityStarter, "unityStarter", configMINIMAL_STACK_SIZE * 2, NULL,
              mainTASK_A_PRIORITY, &taskAHandle);

  /* Create task B to run on another core. */
  xTaskCreate(prvTaskB, "TaskB", configMINIMAL_STACK_SIZE * 2, NULL,
              mainTASK_B_PRIORITY, NULL);
}

void setUp(void) {} /* Is run before every test, put unit init calls here. */
void tearDown(void) {
} /* Is run after every test, put unit clean-up calls here. */

int main(void) {
  initTestEnvironment();

  setup_test_task();

  clearPin(LED_PIN);

  vTaskStartScheduler();
  // AMPLaunchOnCore(1, vTaskStartScheduler);

  /* should never reach here */
  panic_unsupported();

  return 0; // UNITY_END is unreachable via this path. a state machine and
            // counter is used so that just one child task will call it
            // instead.
}

static void prvUnityStarter(void *pvParameters)
{
  UNITY_BEGIN();
  
  RUN_TEST( fr10_onlyOneTaskEnterSuspendAll );

  UNITY_END();

  // idle the task
  for (;;) {
    vTaskDelay(mainSOFTWARE_TIMER_PERIOD_MS);
  }
}

static void fr10_onlyOneTaskEnterSuspendAll()
{
  /* Run as Task A. */
  prvTaskA();
}

static void prvTaskA(void)
{
  BaseType_t xLocalTaskCounter = 0;
  BaseType_t xTaskFailure = pdFALSE;

  vTaskSuspendAll();
  for( ;; )
  {
    xTaskACounter++;
    xLocalTaskCounter++;
    busyWaitMicroseconds( 1000 );

    if( xTaskACounter != xLocalTaskCounter )
    {
      xTaskFailure = pdTRUE;
      break;
    }
    else if( xTaskACounter >= COUNTER_MAX )
    {
      break;
    }
  }
  xTaskResumeAll();

  TEST_ASSERT_TRUE( xTaskFailure == pdFALSE );
  TEST_ASSERT_EQUAL_INT( xLocalTaskCounter, COUNTER_MAX );

  while( xIsTaskBFinished == pdFALSE )
  {
    busyWaitMicroseconds( 100000 );
  }
}

static void prvTaskB(void *pvParameters)
{
  while( xTaskACounter < 1 )
    asm("");
  
  vTaskSuspendAll();
  for( ;; )
  {
    xTaskACounter++;

    if( xTaskACounter >= COUNTER_MAX )
    {
      break;
    }
  }
  xTaskResumeAll();

  TEST_ASSERT_EQUAL_INT( xTaskACounter, COUNTER_MAX + 1 );
  xIsTaskBFinished = pdTRUE;

  // idle the task
  for (;;) {
    vTaskDelay(mainSOFTWARE_TIMER_PERIOD_MS);
  }
}
