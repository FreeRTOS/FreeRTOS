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

#ifndef FREERTOS_CONFIG_FULL_H
#define FREERTOS_CONFIG_FULL_H


#ifdef configMINIMAL_STACK_SIZE
#undef configMINIMAL_STACK_SIZE
#endif
#define configMINIMAL_STACK_SIZE 110

/* Redefine heap memory allocation for Full demo. */
#ifdef configTOTAL_HEAP_SIZE
#undef configTOTAL_HEAP_SIZE
#endif
#define configTOTAL_HEAP_SIZE 0x1000

#ifdef INCLUDE_vTaskPrioritySet
#undef INCLUDE_vTaskPrioritySet
#endif
#define INCLUDE_vTaskPrioritySet 1

#ifdef INCLUDE_vTaskSuspend
#undef INCLUDE_vTaskSuspend
#endif
#define INCLUDE_vTaskSuspend 1

#ifdef INCLUDE_vTaskDelayUntil
#undef INCLUDE_vTaskDelayUntil
#endif
#define INCLUDE_vTaskDelayUntil 1

#ifdef INCLUDE_vTaskDelay
#undef INCLUDE_vTaskDelay
#endif
#define INCLUDE_vTaskDelay 1

#ifdef configUSE_TIMERS
#undef configUSE_TIMERS
#endif
#define configUSE_TIMERS 1

#ifdef configUSE_MUTEXES
#undef configUSE_MUTEXES
#endif
#define configUSE_MUTEXES 1

#ifdef configUSE_RECURSIVE_MUTEXES
#undef configUSE_RECURSIVE_MUTEXES
#endif
#define configUSE_RECURSIVE_MUTEXES 1

#ifdef configUSE_TICK_HOOK
#undef configUSE_TICK_HOOK
#endif
#define configUSE_TICK_HOOK 1

#endif /* FREERTOS_CONFIG_FULL_H */
