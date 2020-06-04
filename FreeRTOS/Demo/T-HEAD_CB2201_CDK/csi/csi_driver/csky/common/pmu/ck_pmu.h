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
 * @file     ck_pmu.h
 * @brief    head file for ck pmu
 * @version  V1.0
 * @date     02. June 2017
 ******************************************************************************/
#ifndef _CK_PMU_H_
#define _CK_PMU_H_

#include "drv_pmu.h"
#include "soc.h"

#define CONFIG_PMU_ENTER_WAIT_MODE  0x4
#define CONFIG_PMU_ENTER_DOZE_MODE  0x4
#define CONFIG_PMU_ENTER_STOP_MODE  0xc
#define CONFIG_PMU_ENTER_STANDBY_MODE   0x14

typedef struct {
    __IOM uint32_t LPCR;             /* Offset: 0x000 (R/W) low power control register */
    __IOM uint32_t MCLKSEL;          /* Offset: 0x004 (R/W) MCLK select register */
    __IOM uint32_t CRCR;             /* Offset: 0x008 (R/W) clock ratio control register */
    __IOM uint32_t CGCR;             /* Offset: 0x00c (R/W) clock gate control register */
    __IOM uint32_t CGSR;             /* Offset: 0x010 (R/W) clock gate status register */
    __IOM uint32_t CLKDSENR;         /* Offset: 0x014 (R/W) clock disable register */
    __IOM uint32_t CLKSTBR;          /* Offset: 0x018 (R/W) clock stable register */
    __IOM uint32_t CLKSTBST;         /* Offset: 0x01c (R/W) clock stable interrupt statue register */
    __IOM uint32_t CLKSTBMK;         /* Offset: 0x020 (R/W) clock stable interrupt mask register */
    __IOM uint32_t CSSCR;            /* Offset: 0x024 (R/W) clock source stable counter register */
    __IOM uint32_t DFCC;             /* Offset: 0x028 (R/W) dynamic frequence conversion control register */
    __IOM uint32_t PCR;              /* Offset: 0x02c (R/W) pll control register */
    __IOM uint32_t PLTR;             /* Offset: 0x030 (R/W) pll lock timer register */
    __IOM uint32_t SWHRC;            /* Offset: 0x034 (R/W) software HRST control register */
    __IOM uint32_t SWHRD;            /* Offset: 0x038 (R/W) software HRST duration register */
    __IOM uint32_t SWPRC;            /* Offset: 0x03c (R/W) software PRST control register */
    __IOM uint32_t SWPRD;            /* Offset: 0x040 (R/W) software PRST duration register */
    __IOM uint32_t SWRE;             /* Offset: 0x044 (R/W) software reset enable register */
    __IOM uint32_t BOOTSEL;          /* Offset: 0x048 (R/W) boot selection register */
    __IOM uint32_t SCGCR;            /* Offset: 0x04c (R/W) security clock gate control register */
    __IOM uint32_t SCGSR;            /* Offset: 0x050 (R/W) security clock gate status register */
} ck_pmu_reg_t;

#endif
