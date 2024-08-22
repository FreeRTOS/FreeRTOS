/*
 * FreeRTOS V202212.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#include "FreeRTOS.h"
#include "task.h"
#include "tasksStubs.h"

#ifndef TASK_STUB_COUNTER
    #define TASK_STUB_COUNTER    0;
#endif

/* 5 is a magic number, but we need some number here as a default value.
 * This value is used to bound any loop depending on xTaskCheckForTimeOut
 * as a loop bound. It should be overwritten in the Makefile.json adapting
 * to the performance requirements of the harness. */
#ifndef TASK_STUB_COUNTER_LIMIT
    #define TASK_STUB_COUNTER_LIMIT    5;
#endif


static BaseType_t xCounter = TASK_STUB_COUNTER;
static BaseType_t xCounterLimit = TASK_STUB_COUNTER_LIMIT;

BaseType_t xTaskGetSchedulerState( void )
{
    return xState;
}

/* This function is another method apart from overwritting the defines to init the max
 * loop bound. */
void vInitTaskCheckForTimeOut( BaseType_t maxCounter,
                               BaseType_t maxCounter_limit )
{
    xCounter = maxCounter;
    xCounterLimit = maxCounter_limit;
}

/* This is mostly called in a loop. For CBMC, we have to bound the loop
 * to a max limits of calls. Therefore this Stub models a nondet timeout in
 * max TASK_STUB_COUNTER_LIMIT iterations.*/
BaseType_t xTaskCheckForTimeOut( TimeOut_t * const pxTimeOut,
                                 TickType_t * const pxTicksToWait )
{
    ++xCounter;

    if( xCounter == xCounterLimit )
    {
        return pdTRUE;
    }
    else
    {
        return nondet_basetype();
    }
}
