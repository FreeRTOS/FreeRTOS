#include "bsl.h"

#include "pico/multicore.h"
#include "pico/mutex.h"
#include "pico/sem.h"
#include "pico/stdlib.h"

#include <stddef.h>

void BSL_Init(void) {
  /* Want to be able to printf */
  stdio_init_all();

  /* And flash LED */
  gpio_init(PICO_DEFAULT_LED_PIN);
  gpio_set_dir(PICO_DEFAULT_LED_PIN, GPIO_OUT);
}

int BSL_ToggleLED(void) { gpio_xor_mask(1u << PICO_DEFAULT_LED_PIN); }

int BSL_Write(char *buffer, size_t len) {}
