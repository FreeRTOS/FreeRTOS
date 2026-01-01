/* usertask
 *
 * Copyright (C) 2025 Advanced Micro Devices, Inc. or its affiliates. All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
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
 *
 */

#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "timers.h"
#include "usertask.h"
#include "stdio.h"

USERDATA QueueHandle_t xUserQueue = NULL;
USERDATA QueueHandle_t xUserResponseQueue = NULL;
#define STACK_SIZE            8192
USERDATA uint32_t user_stack_size=STACK_SIZE;
USERDATA uint8_t  userStack[STACK_SIZE]={0};

USERCODE void user_task(void *p) 
{
    TickType_t xNextWakeTime;
    for(;;) {
       uint64_t ulReceivedValue = 0;
       xQueueReceive( xUserQueue, &ulReceivedValue, portMAX_DELAY );
       uint64_t ulVal = *(uint64_t*)ulReceivedValue;
       xQueueSend( xUserResponseQueue, &ulVal, 0U );
    }
}
