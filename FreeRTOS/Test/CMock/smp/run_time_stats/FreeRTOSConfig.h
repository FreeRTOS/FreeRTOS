/*
 * FreeRTOS V202212.00
 * Copyright (C) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */
#ifndef FREERTOS_CONFIG_H
#define FREERTOS_CONFIG_H

#include <stdint.h>
#include "fake_assert.h"

#define configUSE_PREEMPTION                       1
#define configUSE_PORT_OPTIMISED_TASK_SELECTION    0
#define configRUN_MULTIPLE_PRIORITIES              1
#define configUSE_CORE_AFFINITY                    ( configNUMBER_OF_CORES > 1 )
#define configUSE_TIME_SLICING                     0
#define configUSE_IDLE_HOOK                        0
#define configUSE_PASSIVE_IDLE_HOOK                0
#define configUSE_TICK_HOOK                        0
#define configTICK_RATE_HZ                         1000
#define configMINIMAL_STACK_SIZE                   128
#define configMAX_PRIORITIES                       3
#define configMAX_TASK_NAME_LEN                    12
#define configUSE_16_BIT_TICKS                     0
#define configUSE_TIMERS                           0
#define configSUPPORT_STATIC_ALLOCATION            1
#define configSUPPORT_DYNAMIC_ALLOCATION           0
#define configKERNEL_PROVIDED_STATIC_MEMORY        1
#define configCHECK_FOR_STACK_OVERFLOW             0
#define configUSE_TRACE_FACILITY                   0
#define configUSE_STATS_FORMATTING_FUNCTIONS       0
#define configGENERATE_RUN_TIME_STATS              1
#define portREMOVE_STATIC_QUALIFIER                1
#define portCRITICAL_NESTING_IN_TCB                1
#define portSTACK_GROWTH                           ( -1 )
#define INCLUDE_vTaskDelete                        0
#define INCLUDE_vTaskSuspend                       0
#define INCLUDE_vTaskDelay                         0
#define INCLUDE_xTaskDelayUntil                    0

extern configRUN_TIME_COUNTER_TYPE ulTestRunTimeCounter;
#define portCONFIGURE_TIMER_FOR_RUN_TIME_STATS()    do {} while( 0 )
#define portGET_RUN_TIME_COUNTER_VALUE()            ulTestRunTimeCounter
#define configASSERT( x )                           vFakeAssert( ( x ) != 0, __FILE__, __LINE__ )

#endif /* FREERTOS_CONFIG_H */
