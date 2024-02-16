/*
 * FreeRTOS V202212.00
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#ifndef TEST_CONFIG_H
#define TEST_CONFIG_H

/* This file must be included at the end of the FreeRTOSConfig.h. It contains
 * any FreeRTOS specific configurations that the test requires. */

#ifdef configRUN_MULTIPLE_PRIORITIES
    #undef configRUN_MULTIPLE_PRIORITIES
#endif /* ifdef configRUN_MULTIPLE_PRIORITIES */

#ifdef configUSE_CORE_AFFINITY
    #undef configUSE_CORE_AFFINITY
#endif /* ifdef configUSE_CORE_AFFINITY */

#ifdef configUSE_TASK_PREEMPTION_DISABLE
    #undef configUSE_TASK_PREEMPTION_DISABLE
#endif /* ifdef configUSE_TASK_PREEMPTION_DISABLE */

#ifdef configUSE_TIME_SLICING
    #undef configUSE_TIME_SLICING
#endif /* ifdef configUSE_TIME_SLICING */

#ifdef configUSE_PREEMPTION
    #undef configUSE_PREEMPTION
#endif /* ifdef configUSE_PREEMPTION */

#define configRUN_MULTIPLE_PRIORITIES        1
#define configUSE_CORE_AFFINITY              0
#define configUSE_TASK_PREEMPTION_DISABLE    0
#define configUSE_TIME_SLICING               0
#define configUSE_PREEMPTION                 0

#endif /* ifndef TEST_CONFIG_H */
