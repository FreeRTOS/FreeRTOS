#ifndef _BOARD_SUPPORT_LIBRARY_H
#define _BOARD_SUPPORT_LIBRARY_H

#include "pico/stdlib.h"

#include <stddef.h>
#include <stdint.h>
#include "FreeRTOSConfig.h"

#define CPUTIME_TO_MS_DIVISOR                                                  \
  (123456) // XXXADS must tune to platform if needed. some platforms will have a
           // time-sycned source but it will be relative to something

#define LED_PIN (PICO_DEFAULT_LED_PIN)

typedef void (* softwareInterruptHandler)(void);

typedef struct SchedTraceLogEntry {
  bool valid;
  uint64_t index;
  TaskStatus_t taskStatus;
} SchedTraceLogEntry;

typedef SchedTraceLogEntry[configNUM_CORES] SchedTraceLogRow;
#define MAX_SCHED_TRACE_LOG_ROWS (128)

typedef struct SchedTraceLog {
  UBaseType_t offset;
  SchedTraceLogRow rows[MAX_SCHED_TRACE_LOG_ROWS];
} SchedTraceLog;

extern void initTestEnvironment(void);
extern void sendReport(char *buffer, size_t len);
extern void setPin(int pinNum);
extern void clearPin(int pinNum);
extern void delayMs(uint32_t ms);
extern void busyWaitMicroseconds(uint32_t us);
extern uint64_t getCPUTime(void);

extern int AMPLaunchOnCore(int coreNum, void (*function)(void));

extern int registerSoftwareInterruptHandler(softwareInterruptHandler handler);
extern void deleteSoftwareInterruptHandler(int num, softwareInterruptHandler handler);
extern void triggerSoftwareInterrupt(int num);


#define CPUTIME_TO_MS(CPUTIME_INPUT)                                           \
  ((uin32_t)(CPUTIME_INPUT / CPUTIME_TO_MS_DIVISOR))
#define MS_TO_CPUTIME(MS_INPUT) ((uint64_t)(MS_INPUT * CPUTIME_TO_MS_DIVISOR))

#endif