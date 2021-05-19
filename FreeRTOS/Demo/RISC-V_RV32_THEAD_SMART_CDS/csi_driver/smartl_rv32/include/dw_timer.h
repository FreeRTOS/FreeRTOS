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
 * @file     dw_timer.h
 * @brief    header file for timer driver
 * @version  V1.0
 * @date     02. June 2017
 ******************************************************************************/
#ifndef __DW_TIMER_H
#define __DW_TIMER_H

#include <stdio.h>
#include "soc.h"

#ifdef __cplusplus
extern "C" {
#endif

/*
 *  define the bits for TxControl
 */
#define DW_TIMER_TXCONTROL_ENABLE      (1UL << 0)
#define DW_TIMER_TXCONTROL_MODE        (1UL << 1)
#define DW_TIMER_TXCONTROL_INTMASK     (1UL << 2)
#define DW_TIMER_TXCONTROL_TRIGGER     (1UL << 4)

#define DW_TIMER_INIT_DEFAULT_VALUE     (0xffffffff / drv_get_timer_freq(0) * 1000000)

typedef struct {
    __IOM uint32_t TxLoadCount;              /* Offset: 0x000 (R/W)  Receive buffer register */
    __IM uint32_t TxCurrentValue;            /* Offset: 0x004 (R)  Transmission hold register */
    __IOM uint8_t TxControl: 5;              /* Offset: 0x008 (R/W)  Clock frequency division low section register */
    uint8_t  RESERVED0[3];
    __IM uint8_t TxEOI: 1;                   /* Offset: 0x00c (R)  Clock frequency division high section register */
    uint8_t  RESERVED1[3];
    __IM uint8_t TxIntStatus: 1;             /* Offset: 0x010 (R)  Interrupt enable register */
    uint8_t  RESERVED2[3];
} dw_timer_reg_t;

#ifdef __cplusplus
}
#endif

#endif /* __DW_TIMER_H */

