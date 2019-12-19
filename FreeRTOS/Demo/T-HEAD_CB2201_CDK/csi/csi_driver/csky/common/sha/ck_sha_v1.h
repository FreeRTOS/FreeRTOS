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
 * @file     ck_sha.h
 * @brief    header file for sha driver
 * @version  V1.0
 * @date     02. June 2017
 ******************************************************************************/
#ifndef _CK_SHA_H_
#define _CK_SHA_H_

#include <stdio.h>
#include "drv_sha.h"
#include "soc.h"

#define SHA_INIT_OFFSET         3
#define SHA_INT_ENABLE_OFFSET   4
#define SHA_ENDIAN_OFFSET       5
#define SHA_CAL_OFFSET          6
typedef struct {
    __IOM uint32_t SHA_CON;                     /* Offset: 0x000 (R/W)  Control register */
    __IOM uint32_t SHA_MODE;                    /* Offset: 0x004 (R/W)  Mode register */
    __IOM uint32_t SHA_INTSTATE;                /* Offset: 0x008 (R/W)  Instatus register */ 
    __IOM uint32_t SHA_BASEADDR;                /* Offset: 0x00c (R/W)  Baseaddr register */
    __IOM uint32_t SHA_DESTADDR;                /* Offset: 0x010 (R/W)  Dest addr register */
    __IOM uint32_t SHA_COUNTER0;                /* Offset: 0x014 (R/W)  count0 register */
    __IOM uint32_t SHA_COUNTER1;                /* Offset: 0x018 (R/W)  count1 register */
    __IOM uint32_t SHA_COUNTER2;                /* Offset: 0x01c (R/W)  count2 register */
    __IOM uint32_t SHA_COUNTER3;                /* Offset: 0x020 (R/W)  count3 register */
    __IOM uint32_t SHA_H0L;                     /* Offset: 0x024 (R/W)  H0L register */
    __IOM uint32_t SHA_H1L;                     /* Offset: 0x028 (R/W)  H1L register */
    __IOM uint32_t SHA_H2L;                     /* Offset: 0x02c (R/W)  H2L register */
    __IOM uint32_t SHA_H3L;                     /* Offset: 0x030 (R/W)  H3L register */
    __IOM uint32_t SHA_H4L;                     /* Offset: 0x034 (R/W)  H4L register */
    __IOM uint32_t SHA_H5L;                     /* Offset: 0x038 (R/W)  H5L register */
    __IOM uint32_t SHA_H6L;                     /* Offset: 0x03c (R/W)  H6L register */
    __IOM uint32_t SHA_H7L;                     /* Offset: 0x040 (R/W)  H7L register */
    __IOM uint32_t SHA_H0H;                     /* Offset: 0x044 (R/W)  H0H register */
    __IOM uint32_t SHA_H1H;                     /* Offset: 0x048 (R/W)  H1H register */
    __IOM uint32_t SHA_H2H;                     /* Offset: 0x04c (R/W)  H2H register */
    __IOM uint32_t SHA_H3H;                     /* Offset: 0x050 (R/W)  H3H register */
    __IOM uint32_t SHA_H4H;                     /* Offset: 0x054 (R/W)  H4H register */
    __IOM uint32_t SHA_H5H;                     /* Offset: 0x058 (R/W)  H5H register */
    __IOM uint32_t SHA_H6H;                     /* Offset: 0x05c (R/W)  H6H register */
    __IOM uint32_t SHA_H7H;                     /* Offset: 0x060 (R/W)  H7H register */
} ck_sha_reg_t;

#endif
