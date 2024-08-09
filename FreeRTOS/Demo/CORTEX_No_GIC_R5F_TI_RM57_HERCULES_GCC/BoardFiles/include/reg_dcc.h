/** @file reg_dcc.h
 *   @brief DCC Register Layer Header File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - Definitions
 *   - Types
 *   - Interface Prototypes
 *   .
 *   which are relevant for the DCC driver.
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

#ifndef __REG_DCC_H__
#define __REG_DCC_H__

#include "sys_common.h"

/* USER CODE BEGIN (0) */
/* USER CODE END */

/* Dcc Register Frame Definition */
/** @struct dccBase
 *   @brief DCC Base Register Definition
 *
 *   This structure is used to access the DCC module registers.
 */
/** @typedef dccBASE_t
 *   @brief DCC Register Frame Type Definition
 *
 *   This type is used to access the DCC Registers.
 */
typedef volatile struct dccBase
{
    uint32 GCTRL;      /**< 0x0000: DCC Control Register		*/
    uint32 REV;        /**< 0x0004: DCC Revision Id Register    */
    uint32 CNT0SEED;   /**< 0x0008: DCC Counter0 Seed Register	*/
    uint32 VALID0SEED; /**< 0x000C: DCC Valid0 Seed Register    */
    uint32 CNT1SEED;   /**< 0x0010: DCC Counter1 Seed Register    */
    uint32 STAT;       /**< 0x0014: DCC Status Register    	*/
    uint32 CNT0;       /**< 0x0018: DCC Counter0 Value Register    */
    uint32 VALID0;     /**< 0x001C: DCC Valid0 Value Register    */
    uint32 CNT1;       /**< 0x0020: DCC Counter1 Value Register	*/
    uint32 CNT1CLKSRC; /**< 0x0024: DCC Counter1 Clock Source Selection Register    */
    uint32 CNT0CLKSRC; /**< 0x0028: DCC Counter0 Clock Source Selection Register    */
} dccBASE_t;

/** @def dccREG1
 *   @brief DCC1 Register Frame Pointer
 *
 *   This pointer is used by the DCC driver to access the dcc2 module registers.
 */
#define dccREG1 ( ( dccBASE_t * ) 0xFFFFEC00U )

/** @def dccREG2
 *   @brief DCC2 Register Frame Pointer
 *
 *   This pointer is used by the DCC driver to access the dcc2 module registers.
 */
#define dccREG2 ( ( dccBASE_t * ) 0xFFFFF400U )

/* USER CODE BEGIN (1) */
/* USER CODE END */

#endif
