/** @file reg_scm.h
 *   @brief SCM Register Layer Header File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - Definitions
 *   - Types
 *   .
 *   which are relevant for the SCM driver.
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

#ifndef __REG_SCM_H__
#define __REG_SCM_H__

#include "sys_common.h"

#ifdef __cplusplus
extern "C" {
#endif

/* USER CODE BEGIN (0) */
/* USER CODE END */

/* SCM Register Frame Definition */
/** @struct scmBase
 *   @brief SCM Base Register Definition
 *
 *   This structure is used to access the SCM module registers.
 */
/** @typedef scmBASE_t
 *   @brief SCM Register Frame Type Definition
 *
 *   This type is used to access the SCM Registers.
 */
typedef volatile struct scmBase
{
    uint32 SCMREVID;      /**< 0x0000: SCM REVID Register */
    uint32 SCMCNTRL;      /**< 0x0004: SCM Control Register */
    uint32 SCMTHRESHOLD;  /**< 0x0008: SCM Compare Threshold Counter Register   */
    uint32 rsvd1;         /**< 0x000C: Reserved */
    uint32 SCMIAERR0STAT; /**< 0x0010: SCM Initiator Error0 Status Register */
    uint32 SCMIAERR1STAT; /**< 0x0014: SCM Initiator Error1 Status Register */
    uint32 SCMIASTAT;     /**< 0x0018: SCM Initiator Active Status Register */
    uint32 rsvd2;         /**< 0x001C: Reserved */
    uint32 SCMTASTAT;     /**< 0x0020: SCM Target Active Status Register */
} scmBASE_t;

#define scmREG1 ( ( scmBASE_t * ) 0xFFFF0A00U )

/* USER CODE BEGIN (1) */
/* USER CODE END */

/**@}*/
#ifdef __cplusplus
}
#endif

#endif
