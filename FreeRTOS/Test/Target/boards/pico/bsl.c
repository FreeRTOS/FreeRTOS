#include "bsl.h"

#include "pico/multicore.h"
#include "pico/mutex.h"
#include "pico/sem.h"
#include "pico/stdlib.h"

#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>

static SemaphoreHandle_t xSemLogSchedTrace = NULL;
uint64_t logSchedTraceNumber = 0;

int logSchedTrace(SchedTraceLog *traceLog) {
  UBaseType_t index, numTasksRunning;
  TaskStatus_t taskStatus[16];
  UBaseType_t taskStatusArraySize = 16;
  unsigned long totalRunTime;
  int coreIndex = 0;
  SchedTraceLogRow *logRow;
  int retcode = 0;
  
  numTasksRunning = uxTaskGetSystemState((TaskStatus_t * const)&taskStatus, taskStatusArraySize, &totalRunTime);

  for(index = 0; index < numTasksRunning; index++)
  {
      // ASSERT(coreIndex < MAX_CORES)
      if (taskStatus[index].eCurrentState == eRunning)
      {
        logRow = &(traceLog->rows[traceLog->offset]);
        logRow->valid = pdTRUE;
        logRow->number = logSchedTraceNumber++;
        memcpy(&logRow->taskStatus[coreIndex], &taskStatus[index], sizeof(struct xTASK_STATUS));

        coreIndex++;
      }
  }

  traceLog->offset++;
  if (traceLog->offset >= MAX_SCHED_TRACE_LOG_ROWS) {
    traceLog->offset = 0;
  }

  return retcode;
}

int reportSchedTraceLog(SchedTraceLog *traceLog)
{
  UBaseType_t idx, coreNum;
  SchedTraceLogRow *logRow;
  int retcode = 0;

  //if (xSemaphoreTake(xSemLogSchedTrace, portMAX_DELAY) == pdPASS)
  //{
    for(idx=0; idx < MAX_SCHED_TRACE_LOG_ROWS; idx++)
    {
      logRow = &traceLog->rows[idx];

      printf("SchedTraceLog: %lld\n", logRow->number);
      for(coreNum=0; coreNum < MAX_CORES; coreNum++) {
        printf("  CORE %d: %s\n", coreNum, logRow->taskStatus[coreNum].pcTaskName); // , logRow->taskStatus[coreNum].eCurrentState); eRunning, eReady, eBlocked, eSuspended, eDeleted
      }
    }

 //   if (xSemaphoreGive(xSemLogSchedTrace) == pdFAIL)
 //   {
 //     retcode = -1;
 //   }
 // }

  return retcode;
}

void initTestEnvironment(void) {
  //xSemLogSchedTrace = xSemaphoreCreateBinary();

  /* Want to be able to printf */
  stdio_init_all();

  /* And flash LED */
  gpio_init(PICO_DEFAULT_LED_PIN);
  gpio_set_dir(PICO_DEFAULT_LED_PIN, GPIO_OUT);
  gpio_set_irq_enabled(PICO_DEFAULT_LED_PIN,
    GPIO_IRQ_LEVEL_LOW |
    GPIO_IRQ_LEVEL_HIGH |
    GPIO_IRQ_EDGE_FALL |
    GPIO_IRQ_EDGE_RISE,
    false);
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

int registerSoftwareInterruptHandler(softwareInterruptHandler handler) {
  irq_add_shared_handler(26, (irq_handler_t)handler, 0);
  irq_set_enabled(26, true);
  return 26;
}

void deleteSoftwareInterruptHandler(int num, softwareInterruptHandler handler) {
  irq_remove_handler(num, (irq_handler_t)handler);
}

void triggerSoftwareInterrupt(int num) {
  irq_set_pending(num);
}