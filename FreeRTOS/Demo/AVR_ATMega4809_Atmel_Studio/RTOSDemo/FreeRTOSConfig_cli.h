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

#ifndef FREERTOS_CONFIG_CLI_H
#define FREERTOS_CONFIG_CLI_H


#ifdef configMINIMAL_STACK_SIZE
#undef configMINIMAL_STACK_SIZE
#endif
#define configMINIMAL_STACK_SIZE 100

#ifdef configTOTAL_HEAP_SIZE
#undef configTOTAL_HEAP_SIZE
#endif
#define configTOTAL_HEAP_SIZE 0x800

#ifdef configCOMMAND_INT_MAX_OUTPUT_SIZE
#undef configCOMMAND_INT_MAX_OUTPUT_SIZE
#endif
#define configCOMMAND_INT_MAX_OUTPUT_SIZE 2048

#ifdef INCLUDE_vTaskDelayUntil
#undef INCLUDE_vTaskDelayUntil
#endif
#define INCLUDE_vTaskDelayUntil 1

#ifdef INCLUDE_vTaskDelay
#undef INCLUDE_vTaskDelay
#endif
#define INCLUDE_vTaskDelay 1

#ifdef configGENERATE_RUN_TIME_STATS
#undef configGENERATE_RUN_TIME_STATS
#endif
#define configGENERATE_RUN_TIME_STATS 1

#ifdef configUSE_TRACE_FACILITY
#undef configUSE_TRACE_FACILITY
#endif
#define configUSE_TRACE_FACILITY 1

#ifdef configUSE_STATS_FORMATTING_FUNCTIONS
#undef configUSE_STATS_FORMATTING_FUNCTIONS
#endif
#define configUSE_STATS_FORMATTING_FUNCTIONS 1

#define portCONFIGURE_TIMER_FOR_RUN_TIME_STATS() vMainConfigureTimerForRunTimeStats()
#define portGET_RUN_TIME_COUNTER_VALUE() ulMainGetRunTimeCounterValue()

#define TRC_USE_TRACEALYZER_RECORDER 0
#define TRACE_ALLOC_CRITICAL_SECTION()
#define TRACE_ENTER_CRITICAL_SECTION()
#define TRACE_EXIT_CRITICAL_SECTION()

#endif /* FREERTOS_CONFIG_CLI_H */