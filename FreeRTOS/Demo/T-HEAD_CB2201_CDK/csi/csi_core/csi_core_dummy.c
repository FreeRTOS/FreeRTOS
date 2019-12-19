/*
 * Copyright (C) 2017 C-SKY Microsystems Co., Ltd. All rights reserved.
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
 * @file     csi_core_dummy.c
 * @brief    CSI Core Layer Source File
 * @version  V1.0
 * @date     02. June 2017
 ******************************************************************************/

#include "csi_core.h"

#define _WEAK_ __attribute__((weak))

/* ##################################    NVIC function  ############################################ */


_WEAK_ void drv_nvic_init(uint32_t prio_bits)
{
    return;
}
_WEAK_ void drv_nvic_enable_irq(int32_t irq_num)
{
    return;
}
_WEAK_ void drv_nvic_disable_irq(int32_t irq_num)
{
    return;
}

_WEAK_ uint32_t drv_nvic_get_pending_irq(int32_t irq_num)
{
    return 0;
}
_WEAK_ void drv_nvic_set_pending_irq(int32_t irq_num)
{
    return;
}
_WEAK_ void drv_nvic_clear_pending_irq(int32_t irq_num)
{
    return;
}
_WEAK_ uint32_t drv_nvic_get_active(int32_t irq_num)
{
    return 0;
}

_WEAK_ void drv_nvic_set_prio(int32_t irq_num, uint32_t priority)
{
    return;
}
_WEAK_ uint32_t drv_nvic_get_prio(int32_t irq_num)
{
    return 0;
}
/* ##########################  Cache functions  #################################### */

_WEAK_ void drv_icache_enable(void)
{
    return;
}
_WEAK_ void drv_icache_disable(void)
{
    return;
}
_WEAK_ void drv_icache_invalid(void)
{
    return;
}
_WEAK_ void drv_dcache_enable(void)
{
    return;
}
_WEAK_ void drv_dcache_disable(void)
{
    return;
}
_WEAK_ void drv_dcache_invalid(void)
{
    return;
}
_WEAK_ void drv_dcache_clean(void)
{
    return;
}
_WEAK_ void drv_dcache_clean_invalid(void)
{
    return;
}
_WEAK_ void drv_dcache_invalid_range(uint32_t *addr, int32_t dsize)
{
    return;
}
_WEAK_ void drv_dcache_clean_range(uint32_t *addr, int32_t dsize)
{
    return;
}
_WEAK_ void drv_dcache_clean_invalid_range(uint32_t *addr, int32_t dsize)
{
    return;
}
_WEAK_ void drv_cache_set_range(uint32_t index, uint32_t baseAddr, uint32_t size, uint32_t enable)
{
    return;
}
_WEAK_ void drv_cache_enable_profile(void)
{
    return;
}
_WEAK_ void drv_cache_disable_profile(void)
{
    return;
}
_WEAK_ void drv_cache_reset_profile(void)
{
    return;
}
_WEAK_ uint32_t drv_cache_get_access_time(void)
{
    return 0;
}
_WEAK_ uint32_t drv_cache_get_miss_time(void)
{
    return 0;
}
/* ##################################    SysTick function  ############################################ */

_WEAK_ uint32_t drv_coret_config(uint32_t ticks, int32_t irq_num)
{
    return 0;
}

