#ifndef _PICO_BOARD_SUPPORT_LIBRARY_H
#define _PICO_BOARD_SUPPORT_LIBRARY_H

#include "FreeRTOSConfig.h"
#include "FreeRTOS.h"
#include "semphr.h"
#include "task.h"

#define PICO_STDIO_USB_CONNECT_WAIT_TIMEOUT_MS (5000)

#include "pico/stdlib.h"

#include <stddef.h>
#include <stdint.h>

#define CPUTIME_TO_MS_DIVISOR                                                  \
  (123456) // XXXADS must tune to platform if needed. some platforms will have a
           // time-sycned source but it will be relative to something


#define MAX_CORES (2)

extern char pcTestPassedString[];
extern size_t xTestPassedStringLen;
extern char pcTestFailedString[];
extern size_t xTestFailedStringLen;

typedef void (* SoftwareInterruptHandler_t)(void);

extern void vPortInitTestEnvironment(void);
extern void vPortDelayMs(uint32_t ulMilliseconds);
extern void vPortBusyWaitMicroseconds(uint32_t ulMicroseconds);
extern uint64_t uyPortGetCPUTime(void);

extern BaseType_t xPortAMPLaunchOnCore(BaseType_t xCoreNum, void (*pvFunction)(void));

extern BaseType_t xPortRegisterSoftwareInterruptHandler(SoftwareInterruptHandler_t pvFunction);
extern void vPortDeleteSoftwareInterruptHandler(BaseType_t xNum, SoftwareInterruptHandler_t pvFunction);
extern void vPortTriggerSoftwareInterrupt(BaseType_t xNum);

extern void vPortSerialLog(char *pcBuffer);

#define CPUTIME_TO_MS(CPUTIME_INPUT)                                           \
  ((uin32_t)(CPUTIME_INPUT / CPUTIME_TO_MS_DIVISOR))
#define MS_TO_CPUTIME(MS_INPUT) ((uint64_t)(MS_INPUT * CPUTIME_TO_MS_DIVISOR))

#ifdef USE_BSL_DEFAULT_HOOKS
extern void vApplicationStackOverflowHook(TaskHandle_t xTask, char *pcTaskName);
extern void vApplicationTickHook(void);
extern void vApplicationMallocFailedHook(void);
#endif

#endif