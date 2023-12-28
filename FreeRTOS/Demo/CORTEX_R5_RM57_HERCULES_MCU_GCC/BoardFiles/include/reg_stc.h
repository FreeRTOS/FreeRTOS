/** @file reg_stc.h
 *   @brief STC Register Layer Header File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - Definitions
 *   - Types
 *   .
 *   which are relevant for the STC driver.
 */

/*
 * Copyright (C) 2009-2018 Texas Instruments Incorporated - www.ti.com
 *
 *
 *  Redistribution and use in source and binary forms, with or without
 *  modification, are permitted provided that the following conditions
 *  are met:
 *
 *    Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 *    Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the
 *    distribution.
 *
 *    Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 *  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 *  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 *  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 *  A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 *  OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 *  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 *  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 *  DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 *  THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 *  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 *  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 */

#ifndef __REG_STC_H__
#define __REG_STC_H__

#include "sys_common.h"

/* USER CODE BEGIN (0) */
/* USER CODE END */

/* Stc Register Frame Definition */
/** @struct stcBase
 *   @brief STC Base Register Definition
 *
 *   This structure is used to access the STC module registers.
 */
/** @typedef stcBASE_t
 *   @brief STC Register Frame Type Definition
 *
 *   This type is used to access the STC Registers.
 */
typedef volatile struct stcBase
{
    uint32 STCGCR0;  /**< 0x0000: STC Control Register 0    */
    uint32 STCGCR1;  /**< 0x0004: STC Control Register 1 */
    uint32 STCTPR;   /**< 0x0008: STC Self-Test Run Timeout Counter Preload Register    */
    uint32 STCCADDR; /**< 0x000C: STC Self-Test Current ROM Address Register */
    uint32 STCCICR;  /**< 0x0010: STC Self-Test Current Interval Count Register */
    uint32 STCGSTAT; /**< 0x0014: STC Self-Test Global Status Register */
    uint32 STCFSTAT; /**< 0x0018: STC Self-Test Fail Status Register */
    uint32 CPU1_CURMISR3; /**< 0x001C: STC CPU1 Current MISR Register */
    uint32 CPU1_CURMISR2; /**< 0x0020: STC CPU1 Current MISR Register */
    uint32 CPU1_CURMISR1; /**< 0x0024: STC CPU1 Current MISR Register */
    uint32 CPU1_CURMISR0; /**< 0x0028: STC CPU1 Current MISR Register */
    uint32 CPU2_CURMISR3; /**< 0x002C: STC CPU1 Current MISR Register */
    uint32 CPU2_CURMISR2; /**< 0x0030: STC CPU1 Current MISR Register */
    uint32 CPU2_CURMISR1; /**< 0x0034: STC CPU1 Current MISR Register */
    uint32 CPU2_CURMISR0; /**< 0x0038: STC CPU1 Current MISR Register */
    uint32 STCSCSCR;      /**< 0x003C: STC Signature Compare Self-Check Register */
    uint32 STCCADDR1;     /**< 0x0040: STC Current ROM Address Register - CORE2 */
    uint32 STCCLKDIV;     /**< 0x0044: STC Clock Divider Register */
    uint32 STCSEGPLR;     /**< 0x0048: STC Segment First Preload Register */
} stcBASE_t;

#define stcREG1 ( ( stcBASE_t * ) 0xFFFFE600U )

#define stcREG2 ( ( stcBASE_t * ) 0xFFFF0800U )

/* USER CODE BEGIN (1) */
/* USER CODE END */

#endif
