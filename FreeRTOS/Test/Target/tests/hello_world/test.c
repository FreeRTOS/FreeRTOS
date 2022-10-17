/* Kernel includes. */
#include "FreeRTOS.h" /* Must come first. */
#include "bsl.h"      /* Board support library */
#include "queue.h"    /* RTOS queue related API */
#include "semphr.h"   /* Semaphore related API  */
#include "stdlib.h"
#include "task.h"   /* RTOS task related API */
#include "timers.h" /* Software timer related API */

#include "unity.h" /* unit testing support functions */

#include <stdint.h>

void setUp(void) {} /* Is run before every test, put unit init calls here. */
void tearDown(void) {
} /* Is run after every test, put unit clean-up calls here. */

void hello_world(void) {
  char strbuf[] = "Hello World\n";
  size_t strbuf_len = sizeof(char) / sizeof(strbuf);

  sendReport(strbuf, strbuf_len);

  UNITY_END();
}

int main(void) {
  initTestEnvironment();

  UNITY_BEGIN();

  RUN_TEST(hello_world);

  return 0; // UNITY_END is unreachable via this path. a state machine and
            // counter is used so that just one child task will call it
            // instead.
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
