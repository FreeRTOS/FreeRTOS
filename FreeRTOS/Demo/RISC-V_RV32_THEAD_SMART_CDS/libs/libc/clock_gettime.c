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
 * @file     clock_gettime.c
 * @brief    clock_gettime()
 * @version  V1.0
 * @date     08. May 2019
 ******************************************************************************/

#include <stdio.h>
#include "sys_freq.h"
#include "drv_timer.h"
#include "soc.h"
#include <csi_config.h>
#include "time.h"
#include "pin.h"

#define MILLION 1000000

int clock_gettime(clockid_t clk_id, struct timespec *tp);
int clock_timer_stop(void);

/* APB frequence definition */
static uint32_t APB_FREQ;
static uint32_t TIMER_LOADCOUNT;

static timer_handle_t timer_handle;
static unsigned int Timer_LoopCount;    /* Count unit is 10 seconds */
static uint8_t timer_count_rise = 0;    /*1: timer cont increasing, 0: timer cont diminishing*/

static void timer_cb_fun(int32_t idx, timer_event_e event)
{
    if (TIMER_EVENT_TIMEOUT == event) {
        Timer_LoopCount++;
    }
}

static unsigned long long timer_current_value(void)
{
    unsigned int cv;

    int ret = csi_timer_get_current_value(timer_handle, &cv);

    if (ret != 0) {
        return 0;
    }

    if (timer_count_rise) {
        return (unsigned long long)(Timer_LoopCount) * (TIMER_LOADCOUNT + 1) + cv;
    }

    return (unsigned long long)(Timer_LoopCount + 1) * (TIMER_LOADCOUNT + 1) - cv - 1;
}

int clock_timer_init(void)
{
    if (CLOCK_GETTIME_USE_TIMER_ID > CONFIG_TIMER_NUM) {
        return EPERM;
    }

    uint32_t timer_loadtimer;
    timer_handle = csi_timer_initialize(CLOCK_GETTIME_USE_TIMER_ID, timer_cb_fun);

    if (timer_handle == NULL) {
        return -1;
    }

    APB_FREQ = drv_get_timer_freq(CLOCK_GETTIME_USE_TIMER_ID);
    timer_loadtimer = 10 * MILLION; /*10Mus=10s */
    TIMER_LOADCOUNT = timer_loadtimer * (APB_FREQ / MILLION);

    int ret = csi_timer_config(timer_handle, TIMER_MODE_RELOAD);

    if (ret != 0) {
        return -1;
    }

    ret = csi_timer_set_timeout(timer_handle, timer_loadtimer);

    if (ret != 0) {
        return -1;
    }

    unsigned int cv1, cv2;
    csi_timer_get_current_value(timer_handle, &cv1);
    csi_timer_get_current_value(timer_handle, &cv2);

    if (cv2 > cv1) {
        timer_count_rise = 1;
    }

    return 0;
}

int clock_timer_uninit(void)
{
    if (clock_timer_stop() != 0) {
        return -1;
    }

    if (csi_timer_uninitialize(timer_handle) != 0) {
        return -1;
    }

    timer_handle = NULL;

    return 0;
}

int clock_timer_start(void)
{
    int ret = -1;
    Timer_LoopCount = 0;

    ret = csi_timer_start(timer_handle);

    if (ret != 0) {
        return -1;
    }

#ifdef CONFIG_SYSLOG_LEVEL_DEBUG
    struct timespec ts_begin, ts_end;
    ret = clock_gettime(CLOCK_MONOTONIC, &ts_begin);

    if (ret != 0) {
        return -1;
    }

    ret = clock_gettime(CLOCK_MONOTONIC, &ts_end);

    if (ret != 0) {
        return -1;
    }

    unsigned long long error_margin_ns =
        (ts_end.tv_sec * 1000000000 + ts_end.tv_nsec) -
        (ts_begin.tv_sec * 1000000000 + ts_begin.tv_nsec);
    printf("clock_gettime() timing deviation is +%llu ns\n", error_margin_ns);
#endif

    return 0;
}

int clock_timer_stop(void)
{
    if (csi_timer_stop(timer_handle) != 0) {
        return -1;
    }

    return 0;
}

int clock_gettime(clockid_t clk_id, struct timespec *tp)
{
    if (clk_id != CLOCK_MONOTONIC) {
        return EINVAL;
    }

    if (timer_handle == 0) {
        return EPERM;
    }

    unsigned long long systimer_val = timer_current_value();
    tp->tv_sec = systimer_val / APB_FREQ;
    tp->tv_nsec = (systimer_val % APB_FREQ) * 1000 * MILLION / APB_FREQ;

    return  0;
}
