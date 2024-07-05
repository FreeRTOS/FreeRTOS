/** @file nmpu.h
 *   @brief NMPU Driver Header File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - Definitions
 *   - Types
 *   - Interface Prototypes
 *   .
 *   which are relevant for the NMPU driver.
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

#ifndef NMPU_H_
#define NMPU_H_

#include "reg_nmpu.h"

#ifdef __cplusplus
extern "C" {
#endif

/* USER CODE BEGIN (0) */
/* USER CODE END */

typedef enum nmpuRegion
{
    NMPU_REGION0 = 0U,
    NMPU_REGION1 = 1U,
    NMPU_REGION2 = 2U,
    NMPU_REGION3 = 3U,
    NMPU_REGION4 = 4U,
    NMPU_REGION5 = 5U,
    NMPU_REGION6 = 6U,
    NMPU_REGION7 = 7U
} nmpuReg_t;

typedef enum nmpuAccessPermission
{
    NMPU_PRIV_NA_USER_NA = 0U,
    NMPU_PRIV_RW_USER_NA = 1U,
    NMPU_PRIV_RW_USER_RO = 2U,
    NMPU_PRIV_RW_USER_RW = 3U,
    NMPU_PRIV_RO_USER_NA = 5U,
    NMPU_PRIV_RO_USER_RO = 6U
} nmpuAP_t;

typedef enum nmpuRegionSize
{
    NMPU_SIZE_32_BYTES = 0x4U,
    NMPU_SIZE_64_BYTES = 0x5U,
    NMPU_SIZE_128_BYTES = 0x6U,
    NMPU_SIZE_256_BYTES = 0x7U,
    NMPU_SIZE_512_BYTES = 0x8U,
    NMPU_SIZE_1_KB = 0x9U,
    NMPU_SIZE_2_KB = 0xAU,
    NMPU_SIZE_4_KB = 0xBU,
    NMPU_SIZE_8_KB = 0xCU,
    NMPU_SIZE_16_KB = 0xDU,
    NMPU_SIZE_32_KB = 0xEU,
    NMPU_SIZE_64_KB = 0xFU,
    NMPU_SIZE_128_KB = 0x10U,
    NMPU_SIZE_256_KB = 0x11U,
    NMPU_SIZE_512_KB = 0x12U,
    NMPU_SIZE_1_MB = 0x13U,
    NMPU_SIZE_2_MB = 0x14U,
    NMPU_SIZE_4_MB = 0x15U,
    NMPU_SIZE_8_MB = 0x16U,
    NMPU_SIZE_16_MB = 0x17U,
    NMPU_SIZE_32_MB = 0x18U,
    NMPU_SIZE_64_MB = 0x19U,
    NMPU_SIZE_128_MB = 0x1AU,
    NMPU_SIZE_256_MB = 0x1BU,
    NMPU_SIZE_512_MB = 0x1CU,
    NMPU_SIZE_1_GB = 0x1DU,
    NMPU_SIZE_2_GB = 0x1EU,
    NMPU_SIZE_4_GB = 0x1FU
} nmpuRegionSize_t;

typedef enum nmpuError
{
    NMPU_ERROR_NONE,
    NMPU_ERROR_AP_READ,
    NMPU_ERROR_AP_WRITE,
    NMPU_ERROR_BG_READ,
    NMPU_ERROR_BG_WRITE
} nmpuErr_t;

typedef struct nmpuRegionAttributes
{
    uint32 baseaddr;
    nmpuReg_t regionsize;
    nmpuAP_t accesspermission;
} nmpuRegionAttributes_t;

/**
 * @defgroup NMPU NMPU
 * @brief System Memory Protection Unit
 *
 * Related files:
 * - reg_nmpu.h
 * - sys_nmpu.h
 * - sys_nmpu.c
 *
 * @addtogroup NMPU
 * @{
 */

void nmpuEnable( nmpuBASE_t * nmpu );
void nmpuDisable( nmpuBASE_t * nmpu );
void nmpuEnableErrorGen( nmpuBASE_t * nmpu );
void nmpuDisableErrorGen( nmpuBASE_t * nmpu );
boolean nmpuEnableRegion( nmpuBASE_t * nmpu,
                          nmpuReg_t region,
                          nmpuRegionAttributes_t config );
boolean nmpuDisableRegion( nmpuBASE_t * nmpu, nmpuReg_t region );
nmpuErr_t nmpuGetErrorStatus( nmpuBASE_t * nmpu );
nmpuReg_t nmpuGetErrorRegion( nmpuBASE_t * nmpu );
uint32 nmpuGetErrorAddress( nmpuBASE_t * nmpu );
void nmpuClearErrorStatus( nmpuBASE_t * nmpu );

/**@}*/

/* USER CODE BEGIN (1) */
/* USER CODE END */

#ifdef __cplusplus
}
#endif /*extern "C" */

#endif /* NMPU_H_ */
