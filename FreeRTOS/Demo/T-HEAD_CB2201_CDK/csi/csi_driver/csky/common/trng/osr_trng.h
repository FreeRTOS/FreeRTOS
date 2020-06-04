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
 * @file     osr_trng.h
 * @brief    header file for trng driver
 * @version  V1.0
 * @date     02. June 2017
 ******************************************************************************/
#ifndef _OSR_TRNG_H_
#define _OSR_TRNG_H_

#include "drv_trng.h"
#include "soc.h"

/*
 *  define the bits for TCR
 */
#define TRNG_EN              (1UL << 0)
#define TRNG_DATA_READY      (0xff << 16)
#define TRNG_IRQ_BIT         (1UL << 24)

typedef struct {
    __IOM uint32_t  RBG_CR;                 /* Offset: 0x000 (W/R)  RBG control register */
    __IOM uint32_t  RBG_RTCR;               /* Offset: 0x004 (W/R)  RBG mode selection register */
    __IOM uint32_t  RBG_SR;                 /* Offset: 0x008 (W/R)  RBG status register */
    __IM  uint32_t  RBG_DR;                 /* Offset: 0x00c ( /R)  RBG data register */
          uint32_t  Reserved[4];
    __IOM uint32_t  RBG_FIFO_CR;            /* Offset: 0x020 (W/R)  FIFO control register */
    __IM  uint32_t  RBG_FIFO_SR;            /* Offset: 0x024 ( /R)  FIFO status register */
} osr_trng_reg_t;
#endif
