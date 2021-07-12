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
 * @file     sys_freq.h
 * @brief    header file for setting system frequency.
 * @version  V1.0
 * @date     18. July 2018
 ******************************************************************************/
#ifndef _SYS_FREQ_H_
#define _SYS_FREQ_H_

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

int32_t drv_get_i2s_freq(int32_t idx);
int32_t drv_get_pwm_freq(int32_t idx);
int32_t drv_get_usart_freq(int32_t idx);
int32_t drv_get_usi_freq(int32_t idx);
int32_t drv_get_sys_freq(void);
int32_t drv_get_apb_freq(void);
int32_t drv_get_rtc_freq(int32_t idx);
int32_t drv_get_timer_freq(int32_t idx);

int32_t drv_get_cpu_freq(int32_t idx);

#ifdef __cplusplus
}
#endif

#endif /* _SYS_FREQ_H_ */

