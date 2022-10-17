#include "bsl.h"

#include "pico/multicore.h"
#include "pico/mutex.h"
#include "pico/sem.h"
#include "pico/stdlib.h"

#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>

void initTestEnvironment(void) {
  /* Want to be able to printf */
  stdio_init_all();

  /* And flash LED */
  gpio_init(PICO_DEFAULT_LED_PIN);
  gpio_set_dir(PICO_DEFAULT_LED_PIN, GPIO_OUT);
}

void sendReport(char *buffer, size_t len) { printf("%.*s", len, buffer); }

void setPin(int pinNum) { gpio_put(pinNum, 1); }

void clearPin(int pinNum) { gpio_put(pinNum, 0); }

void delayMs(uint32_t ms) { sleep_ms(ms); }

void busyWaitMicroseconds(uint32_t us) { busy_wait_us(us); }

uint64_t getCPUTime(void) { return (uint64_t)get_absolute_time(); }

int AMPLaunchOnCore(int coreNum, void (*function)(void)) {
  int rvb = -1;

  if (coreNum == 1) {
    multicore_launch_core1(*function);
    rvb = 0;
  }

  return rvb;
}
