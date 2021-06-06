/*
 * Copyright (C) 2017-2019 Alibaba Group Holding Limited. All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */



/******************************************************************************
 * @file     event_test.c
 * @brief    the main function for the event test
 * @version  V1.0
 * @date     02. June 2017
 ******************************************************************************/
#include "test_kernel.h"
#include <csi_kernel.h>
#include <stdint.h>

extern k_task_handle_t k_api_example_arr[];

#define EXAMPLE_K_EVENT_STK_SIZE 1024

static k_task_handle_t g_TestTask01;
static k_event_handle_t example_k_event_t;
static uint32_t get_flags;
static uint32_t uwEvent = 0;

#define event_wait         0x00001001
#define EVENT_TASK_PRIO    6

static void Example_Event()
{
    k_status_t ret;
    printf("Example_Event waits event 0x%x \n", event_wait);

    csi_kernel_event_wait(example_k_event_t, event_wait, KEVENT_OPT_SET_ALL, 0, &uwEvent, 100);
    ret = csi_kernel_event_get(example_k_event_t, &get_flags);

    if (ret != 0) {
        printf("Example_Event fail to get event\n");
    }

    if (uwEvent == get_flags) {
        printf("Example_Event,reads event :0x%x\n", uwEvent);
    } else {
        printf("Example_Event,reads event timeout\n");
    }

    csi_kernel_task_del(g_TestTask01);
}

void example_main(void)
{
    uint32_t uwRet;

    example_k_event_t = csi_kernel_event_new();

    if (example_k_event_t == NULL) {
        printf("fail to init event.\n");
        csi_kernel_task_del(csi_kernel_task_get_cur());
    }

    csi_kernel_task_new((k_task_entry_t)Example_Event, "EventTsk1", NULL, EVENT_TASK_PRIO, TASK_TIME_QUANTA, NULL, TEST_TASK_STACK_SIZE, &g_TestTask01);

    if (g_TestTask01 == NULL) {
        printf("fail to create task.\n");
        csi_kernel_event_del(example_k_event_t);
        csi_kernel_task_del(csi_kernel_task_get_cur());
    }

    printf("example_k_event writes event .\n");

    int ret = csi_kernel_event_set(example_k_event_t, event_wait, &uwRet);

    if (ret != 0) {
        printf("can not set\n");
        csi_kernel_event_del(example_k_event_t);
        csi_kernel_task_del(csi_kernel_task_get_cur());
    }

    if (get_flags != event_wait) {
        printf("fail to write.\n");
        csi_kernel_event_del(example_k_event_t);
        csi_kernel_task_del(csi_kernel_task_get_cur());
    }

    printf("test kernel event successfully!\n");
    csi_kernel_event_del(example_k_event_t);
    csi_kernel_task_del(csi_kernel_task_get_cur());
}
