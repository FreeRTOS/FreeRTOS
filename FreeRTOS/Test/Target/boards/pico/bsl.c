#include "bsl.h"

#include "pico/multicore.h"
#include "pico/mutex.h"
#include "pico/sem.h"
#include "pico/stdlib.h"

#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>

char testPassedString[] = "TEST PASSED\n\0";
size_t testPassedStringLen = sizeof(testPassedString) / sizeof(char);
char testFailedString[] = "TEST FAILED\n\0";
size_t testFailedStringLen = sizeof(testFailedString) / sizeof(char);

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
        logRow->number = logSchedTraceNumber;
        memcpy(&logRow->taskStatus[coreIndex], &taskStatus[index], sizeof(struct xTASK_STATUS));

        coreIndex++;
      }
  }

  logSchedTraceNumber++;
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

  /* Setup LED I/O */
  gpio_init(PICO_DEFAULT_LED_PIN);
  gpio_set_dir(PICO_DEFAULT_LED_PIN, GPIO_OUT);
  gpio_set_irq_enabled(PICO_DEFAULT_LED_PIN,
    GPIO_IRQ_LEVEL_LOW |
    GPIO_IRQ_LEVEL_HIGH |
    GPIO_IRQ_EDGE_FALL |
    GPIO_IRQ_EDGE_RISE,
    false);

  /* Setup Output on GPIO0 */
  gpio_init(PICO_DEFAULT_UART_TX_PIN);
  gpio_set_function(PICO_DEFAULT_UART_TX_PIN, GPIO_FUNC_NULL);
  gpio_set_dir(PICO_DEFAULT_UART_TX_PIN, GPIO_OUT);
  gpio_set_slew_rate(PICO_DEFAULT_UART_TX_PIN, GPIO_SLEW_RATE_FAST);
  gpio_set_drive_strength(PICO_DEFAULT_UART_TX_PIN, GPIO_DRIVE_STRENGTH_8MA);
  gpio_set_irq_enabled(PICO_DEFAULT_UART_TX_PIN,
    GPIO_IRQ_LEVEL_LOW |
    GPIO_IRQ_LEVEL_HIGH |
    GPIO_IRQ_EDGE_FALL |
    GPIO_IRQ_EDGE_RISE,
    false);

  /* Want to be able to printf */
  stdio_init_all();
  while (!stdio_usb_connected())
  {
    setPin(LED_PIN);
    setPin(GPIO0_PIN);
    sleep_ms(250);
    clearPin(LED_PIN);
    clearPin(GPIO0_PIN);
    sleep_ms(250);
  }


}

void sendReport(char *buffer, size_t len) { printf("%s", buffer); stdio_flush(); }

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

#ifdef USE_BSL_DEFAULT_HOOKS
void vApplicationStackOverflowHook(TaskHandle_t xTask, char *pcTaskName) {
  (void)pcTaskName;
  (void)xTask;

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
  char strbuf[] = "Malloc Failed\n\0";
  size_t strbuf_len = sizeof(strbuf) / sizeof(char);

  sendReport(strbuf, strbuf_len);
}
#endif