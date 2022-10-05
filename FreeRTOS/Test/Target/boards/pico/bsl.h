#ifndef _BOARD_SUPPORT_LIBRARY_H
#define _BOARD_SUPPORT_LIBRARY_H

#include "pico/stdlib.h"

#include <stddef.h>
#include <stdint.h>

extern void BSL_Init(void);
extern int BSL_ToggleLED(void);
extern int BSL_Write(char *buffer, size_t len);

// refactor anchor
// ^^ past
// ------------------------------------------------------------------------------
// vv future

#define CPUTIME_TO_MS_DIVISOR                                                  \
  (123456) // XXXADS must tune to platform if needed. some platforms will have a
           // time-sycned source but it will be relative to something

#define LED_PIN (PICO_DEFAULT_LED_PIN)

extern void initTestEnvironment(void);
extern void sendReport(char *buffer, size_t len);
extern void setPin(int pinNum);
extern void clearPin(int pinNum);
extern void delayMs(uint32_t ms);
extern void busyWaitMicroseconds(uint32_t us);
extern uint64_t getCPUTime(void);

extern int AMPLaunchOnCore(int coreNum, void (*function)(void));

#define CPUTIME_TO_MS(CPUTIME_INPUT)                                           \
  ((uin32_t)(CPUTIME_INPUT / CPUTIME_TO_MS_DIVISOR))
#define MS_TO_CPUTIME(MS_INPUT) ((uint64_t)(MS_INPUT * CPUTIME_TO_MS_DIVISOR))

#endif