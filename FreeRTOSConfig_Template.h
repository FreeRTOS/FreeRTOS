#ifndef FREERTOS_CONFIG_H
#define FREERTOS_CONFIG_H

#include <stdint.h>

/* Scheduler configuration */
#define configUSE_PREEMPTION                1
#define configUSE_IDLE_HOOK                 0
#define configUSE_TICK_HOOK                 0
#define configCPU_CLOCK_HZ                  (32000000UL)
#define configTICK_RATE_HZ                  ((TickType_t)1000)
#define configMAX_PRIORITIES                5
#define configMINIMAL_STACK_SIZE            ((uint16_t)128)
#define configTOTAL_HEAP_SIZE               ((size_t)10240)
#define configMAX_TASK_NAME_LEN             16
#define configUSE_16_BIT_TICKS              0
#define configIDLE_SHOULD_YIELD             1

/* Synchronization primitives */
#define configUSE_MUTEXES                   1
#define configUSE_COUNTING_SEMAPHORES       1
#define configUSE_QUEUE_SETS                 1
#define configUSE_TASK_NOTIFICATIONS         1

/* Stack overflow check */
#define configCHECK_FOR_STACK_OVERFLOW       2
#define configUSE_MALLOC_FAILED_HOOK         0

/* Optional functions */
#define INCLUDE_vTaskDelay                   1
#define INCLUDE_vTaskDelete                  1
#define INCLUDE_vTaskSuspend                 1
#define INCLUDE_xTaskGetSchedulerState       1
#define INCLUDE_xTaskGetCurrentTaskHandle   1

#endif /* FREERTOS_CONFIG_H */
