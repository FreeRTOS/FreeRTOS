/** @file reg_epc.h
 *   @brief EPC Register Layer Header File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - Definitions
 *   - Types
 *   .
 *   which are relevant for the EPC driver.
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

#ifndef __REG_EPC_H__
#define __REG_EPC_H__

#include "sys_common.h"

#ifdef __cplusplus
extern "C" {
#endif

/* USER CODE BEGIN (0) */
/* USER CODE END */

/* EPC Register Frame Definition */
/** @struct epcBase
 *   @brief EPC Base Register Definition
 *
 *   This structure is used to access the EPC module registers.
 */
/** @typedef epcBASE_t
 *   @brief EPC Register Frame Type Definition
 *
 *   This type is used to access the EPC Registers.
 */
typedef volatile struct epcBase
{
    uint32 EPCREVID;      /**< 0x0000: EPC REVID Register */
    uint32 EPCCNTRL;      /**< 0x0004: EPC Control Register */
    uint32 UERRSTAT;      /**< 0x0008: Uncorrectable Error Status Register   */
    uint32 EPCERRSTAT;    /**< 0x000C: EPC Error Status Register */
    uint32 FIFOFULLSTAT;  /**< 0x0010: FIFO Full Status Register */
    uint32 OVRFLWSTAT;    /**< 0x0014: IP Interface FIFO Overflow Status Register */
    uint32 CAMAVAILSTAT;  /**< 0x0018: CAM Index Available Status Register */
    uint32 rsvd1;         /**< 0x001C: Reserved */
    uint32 UERRADDR[ 2 ]; /**< 0x0020 - 0x0024: Uncorrectable Error Address Registers */
    uint32 rsvd2[ 30 ];   /**< 0x0028 - 0x009C: Reserved */
    uint32 CAM_CONTENT[ 32 ]; /**< 0x00A0 - 0x011C: CAM Content Update Registers */
    uint32 rsvd3[ 56 ];       /**< 0x0120 - 0x01FC: Reserved */
    uint32 CAM_INDEX[ 8 ];    /**< 0x0200 - 0x021C: CAM Index Register 0 to 7 */
} epcBASE_t;

#define epcREG1 ( ( epcBASE_t * ) 0xFFFF0C00U )

/* USER CODE BEGIN (1) */
/* USER CODE END */

/**@}*/
#ifdef __cplusplus
}
#endif

#endif
