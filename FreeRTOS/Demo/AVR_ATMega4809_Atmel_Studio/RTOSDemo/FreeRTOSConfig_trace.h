/*
 * FreeRTOS V202012.00
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. If you wish to use our Amazon
 * FreeRTOS name, please do so in a fair use way that does not cause confusion.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

#ifndef FREERTOS_CONFIG_TRACE_H
#define FREERTOS_CONFIG_TRACE_H		


#ifdef configMINIMAL_STACK_SIZE
#undef configMINIMAL_STACK_SIZE
#endif
#define configMINIMAL_STACK_SIZE 100

#ifdef configTOTAL_HEAP_SIZE
#undef configTOTAL_HEAP_SIZE
#endif
#define configTOTAL_HEAP_SIZE 0x1000

#ifdef configUSE_16_BIT_TICKS
#undef configUSE_16_BIT_TICKS
#endif
#define configUSE_16_BIT_TICKS 1

#ifdef configUSE_MUTEXES
#undef configUSE_MUTEXES
#endif
#define configUSE_MUTEXES 1

#ifdef configUSE_RECURSIVE_MUTEXES
#undef configUSE_RECURSIVE_MUTEXES
#endif
#define configUSE_RECURSIVE_MUTEXES 1

#ifdef configUSE_TRACE_FACILITY
#undef configUSE_TRACE_FACILITY
#endif
#define configUSE_TRACE_FACILITY 1

#ifdef configUSE_STATS_FORMATTING_FUNCTIONS
#undef configUSE_STATS_FORMATTING_FUNCTIONS
#endif
#define configUSE_STATS_FORMATTING_FUNCTIONS 1

#ifdef INCLUDE_vTaskDelayUntil
#undef INCLUDE_vTaskDelayUntil
#endif
#define INCLUDE_vTaskDelayUntil 1

#ifdef INCLUDE_vTaskDelay
#undef INCLUDE_vTaskDelay
#endif
#define INCLUDE_vTaskDelay 1

#ifdef INCLUDE_xTaskGetSchedulerState
#undef INCLUDE_xTaskGetSchedulerState
#endif
#define INCLUDE_xTaskGetSchedulerState 1

#ifdef INCLUDE_xTaskGetCurrentTaskHandle
#undef INCLUDE_xTaskGetCurrentTaskHandle
#endif
#define INCLUDE_xTaskGetCurrentTaskHandle 1

#ifdef INCLUDE_xTaskGetIdleTaskHandle
#undef INCLUDE_xTaskGetIdleTaskHandle
#endif
#define INCLUDE_xTaskGetIdleTaskHandle 1

#ifdef INCLUDE_eTaskGetState
#undef INCLUDE_eTaskGetState
#endif
#define INCLUDE_eTaskGetState 1


/* Integrates the Tracealyzer recorder with FreeRTOS */
#if ( configUSE_TRACE_FACILITY == 1 )

#define TRACE_ALLOC_CRITICAL_SECTION()
#define TRACE_ENTER_CRITICAL_SECTION() portENTER_CRITICAL()
#define TRACE_EXIT_CRITICAL_SECTION() portEXIT_CRITICAL()

/* Overwrite the definitions from trcRecorder.h - AVR port uses 16-bit pointers. */
#include "TraceRecorder/include/trcRecorder.h"

#undef  TRACE_GET_HIGH16
#define TRACE_GET_HIGH16(value) ((uint16_t)((value) & 0x0000FFFF))

#undef  TRACE_SET_HIGH16
#define TRACE_SET_HIGH16(current, value) (((current) & 0xFFFF0000) | (value))

#endif

#endif /* FREERTOS_CONFIG_TRACE_H */