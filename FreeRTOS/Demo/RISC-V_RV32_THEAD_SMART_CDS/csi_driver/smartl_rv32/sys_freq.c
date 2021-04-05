/*
 * Copyright (C) 2017-2019 Alibaba Group Holding Limited
 */

/******************************************************************************
 * @file     sys_freq.c
 * @brief    source file for setting system frequency.
 * @version  V1.0
 * @date     18. July 2018
 ******************************************************************************/

#include <stdint.h>
#include <soc.h>
#include <sys_freq.h>

extern int g_system_clock;

int32_t drv_get_cpu_freq(int32_t idx)
{
    return g_system_clock;
}

int32_t drv_get_usi_freq(int32_t idx)
{
    return g_system_clock;
}

int32_t drv_get_usart_freq(int32_t idx)
{
    return g_system_clock;
}

int32_t drv_get_pwm_freq(int32_t idx)
{
    return g_system_clock;
}

int32_t drv_get_i2s_freq(int32_t idx)
{
    return g_system_clock;
}

int32_t drv_get_sys_freq(void)
{
    return g_system_clock;
}

int32_t drv_get_rtc_freq(int32_t idx)
{
    return g_system_clock;
}

int32_t drv_get_apb_freq(void)
{
    return g_system_clock;
}

int32_t drv_get_timer_freq(int32_t idx)
{
    return g_system_clock;
}
