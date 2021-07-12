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
 * @file     timer_test.c
 * @brief    the main function for the timer test
 * @version  V1.0
 * @date     02. June 2017
 ******************************************************************************/
#include "test_kernel.h"
#include <csi_kernel.h>
#include <stdint.h>

extern k_task_handle_t k_api_example_arr[];

static k_timer_cb_t Timer1_Callback(uint32_t arg);
static k_timer_cb_t Timer2_Callback(uint32_t arg);

uint32_t g_timercount1 = 0;
uint32_t g_timercount2 = 0;

static k_timer_cb_t Timer1_Callback(uint32_t arg)
{
    uint64_t tick_last1;
    tick_last1 = csi_kernel_get_ticks();
    g_timercount1 ++;
    printf("g_timercount1=%u\n", g_timercount1);
    printf("tick_last1 = %llu\n", tick_last1);
    return NULL;
}

static k_timer_cb_t Timer2_Callback(uint32_t arg)
{
    uint64_t tick_last2;
    g_timercount2 ++;
    tick_last2 = csi_kernel_get_ticks();
    printf("g_timercount2=%u\n", g_timercount2);
    printf("tick_last2 = %llu\n", tick_last2);
    return NULL;
}

void example_main(void)
{
    k_timer_handle_t timer01;
    k_timer_handle_t timer02;
    int32_t timer_state;
    k_status_t ret;

    timer01 = csi_kernel_timer_new((k_timer_cb_t)Timer1_Callback, KTIMER_TYPE_ONCE, NULL);
    timer02 = csi_kernel_timer_new((k_timer_cb_t)Timer2_Callback, KTIMER_TYPE_PERIODIC, NULL);

    if (timer01 == NULL || timer02 == NULL) {
        printf("create Timer failed\n");
    }

    ret  = csi_kernel_timer_start(timer01, 1000);

    if (ret != 0) {
        printf("start Timer1 failed\n");
    }

    csi_kernel_delay(200);

    timer_state = csi_kernel_timer_get_stat(timer01);
    printf("timer_state =%d\n", timer_state);

    ret = csi_kernel_timer_stop(timer01);

    if (ret != 0) {
        printf("stop Timer1 failed\n");
    }

    csi_kernel_timer_start(timer01, 1000);
    csi_kernel_delay(1000);

    ret = csi_kernel_timer_del(timer01);

    if (ret != 0) {
        printf("delete Timer1 failed\n");
    }

    csi_kernel_timer_start(timer02, 100);
    printf("start Timer2\n");
    csi_kernel_delay(1000);
    ret = csi_kernel_timer_stop(timer02);

    if (ret != 0) {
        printf("stop Timer2 failed\n");
    }

    ret = csi_kernel_timer_del(timer02);

    if (ret != 0) {
        printf("delete Timer2 failed\n");
    }

    printf("test kernel timer successfully !\n");
    csi_kernel_task_del(csi_kernel_task_get_cur());
}
