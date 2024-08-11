/** @file reg_sdcmmr.h
 *   @brief SDCMMR Register Layer Header File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - Definitions
 *   - Types
 *   .
 *   which are relevant for the SDCMMR driver.
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

#ifndef __REG_SDCMMR_H__
#define __REG_SDCMMR_H__

#include "sys_common.h"

#ifdef __cplusplus
extern "C" {
#endif

/* USER CODE BEGIN (0) */
/* USER CODE END */

/* SDCMMR Register Frame Definition */
/** @struct sdcmmrBase
 *   @brief SDCMMR Base Register Definition
 *
 *   This structure is used to access the SDCMMR module registers.
 */
/** @typedef sdcmmrBASE_t
 *   @brief SDCMMR Register Frame Type Definition
 *
 *   This type is used to access the SDCMMR Registers.
 */
typedef volatile struct sdcmmrBase
{
    uint32 SDC_STATUS;           /**< SDC Status Register */
    uint32 SDC_CONTROL;          /**< SDC Control Register */
    uint32 ERR_GENERIC_PARITY;   /**< Error Generic Parity Register */
    uint32 ERR_UNEXPECTED_TRANS; /**< Error Unexpected Transaction Register */
    uint32 ERR_TRANS_ID;         /**< Error Transaction ID Register */
    uint32 ERR_TRANS_SIGNATURE;  /**< Error Transaction Signature Register */
    uint32 ERR_TRANS_TYPE;       /**< Error Transaction Type Register */
    uint32 ERR_USER_PARITY;      /**< IError User Parity Register */
    uint32 SERR_UNEXPECTED_MID;  /**< Slave Error Unexpected Master ID register */
    uint32 SERR_ADDR_DECODE;     /**< Slave Error Address Decode Register */
    uint32 SERR_USER_PARITY;     /**< Slave Error User Parity Register */
} sdcmmrBASE_t;

#define sdcmmrREG1 ( ( sdcmmrBASE_t * ) 0xFA000000U )

/* USER CODE BEGIN (1) */
/* USER CODE END */

/**@}*/
#ifdef __cplusplus
}
#endif

#endif
