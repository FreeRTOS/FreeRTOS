#include "bsl.h"

#include "pico/multicore.h"
#include "pico/mutex.h"
#include "pico/sem.h"
#include "pico/stdlib.h"

#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>

char pcTestPassedString[] = "TEST PASSED\n\0";
size_t xTestPassedStringLen = sizeof(pcTestPassedString) / sizeof(char);
char pcTestFailedString[] = "TEST FAILED\n\0";
size_t xTestFailedStringLen = sizeof(pcTestFailedString) / sizeof(char);

void vPortInitTestEnvironment(void) {
  /* Setup LED I/O */
  gpio_init(PICO_DEFAULT_LED_PIN);
  gpio_set_dir(PICO_DEFAULT_LED_PIN, GPIO_OUT);
  gpio_set_irq_enabled(PICO_DEFAULT_LED_PIN,
    GPIO_IRQ_LEVEL_LOW |
    GPIO_IRQ_LEVEL_HIGH |
    GPIO_IRQ_EDGE_FALL |
    GPIO_IRQ_EDGE_RISE,
    false);

  /* Want to be able to printf */
  stdio_init_all();
  while (!stdio_usb_connected())
  {
    gpio_put(PICO_DEFAULT_LED_PIN, 1);
    sleep_ms(250);
    gpio_put(PICO_DEFAULT_LED_PIN, 0);
    sleep_ms(250);
  }


}

void vPortSerialLog(char *pcBuffer) { printf("%s", pcBuffer); stdio_flush(); }

void vPortDelayMs(uint32_t ulMilliseconds) { sleep_ms(ulMilliseconds); }

void vPortBusyWaitMicroseconds(uint32_t ulMicroseconds) { busy_wait_us(ulMicroseconds); }

uint64_t uyPortGetCPUTime(void) {
  #ifdef NDEBUG
    return (uint64_t)get_absolute_time();
  #else
    return get_absolute_time()._private_us_since_boot;
  #endif
}

BaseType_t xPortAMPLaunchOnCore(BaseType_t xCoreNum, void (*function)(void)) {
  BaseType_t xRvb = -1;

  if (xCoreNum == 1) {
    multicore_launch_core1(*function);
    xRvb = 0;
  }

  return xRvb;
}

BaseType_t xPortRegisterSoftwareInterruptHandler(SoftwareInterruptHandler_t pvFunction) {
  irq_add_shared_handler(26, (irq_handler_t)pvFunction, 0);
  irq_set_enabled(26, true);
  return (BaseType_t)26;
}

void vPortDeleteSoftwareInterruptHandler(BaseType_t xNum, SoftwareInterruptHandler_t pvFunction) {
  irq_remove_handler((int)xNum, (irq_handler_t)pvFunction);
}

void vPortTriggerSoftwareInterrupt(BaseType_t xNum) {
  irq_set_pending((int)xNum);
}

#ifdef USE_BSL_DEFAULT_HOOKS
void vApplicationStackOverflowHook(TaskHandle_t xTask, char *pcTaskName) {
  (void)pcTaskName;
  (void)xTask;

  vPortSerialLog("ERROR: Stack Overflow\n\0");

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
  vPortSerialLog("ERROR: Malloc Failed\n\0");
}
#endif