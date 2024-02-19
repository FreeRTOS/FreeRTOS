/** @file sys_pmm.h
 *   @brief PMM Driver Header File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - Definitions
 *   - Types
 *   .
 *   which are relevant for the System driver.
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

#ifndef __SYS_PMM_H__
#define __SYS_PMM_H__

#include "reg_pmm.h"

#ifdef __cplusplus
extern "C" {
#endif

/* USER CODE BEGIN (0) */
/* USER CODE END */

/** @enum pmmLogicPDTag
 *   @brief PMM Logic Power Domain
 *
 *   Used to define PMM Logic Power Domain
 */
typedef enum pmmLogicPDTag
{
    PMM_LOGICPD1 = 5U, /*-- NOT USED*/
    PMM_LOGICPD2 = 0U,
    PMM_LOGICPD3 = 1U,
    PMM_LOGICPD4 = 2U,
    PMM_LOGICPD5 = 3U,
    PMM_LOGICPD6 = 4U
} pmm_LogicPD_t;

/** @enum pmmModeTag
 *   @brief PSCON operating mode
 *
 *   Used to define the operating mode of PSCON Compare Block
 */
typedef enum pmmModeTag
{
    LockStep = 0x0U,
    SelfTest = 0x6U,
    ErrorForcing = 0x9U,
    SelfTestErrorForcing = 0xFU
} pmm_Mode_t;

/**
 * @defgroup PMM PMM
 * @brief Power Management Module
 *
 * The PMM provides memory-mapped registers that control the states of the supported power
 * domains. The PMM includes interfaces to the Power Mode Controller (PMC) and the Power
 * State Controller (PSCON). The PMC and PSCON control the power up/down sequence of each
 * power domain.
 *
 * Related files:
 * - reg_pmm.h
 * - sys_pmm.h
 * - sys_pmm.c
 *
 * @addtogroup PMM
 * @{
 */

/* Pmm Interface Functions */
boolean pmmTurnONLogicPowerDomain( pmm_LogicPD_t logicPD );
boolean pmmTurnOFFLogicPowerDomain( pmm_LogicPD_t logicPD );
boolean pmmIsLogicPowerDomainActive( pmm_LogicPD_t logicPD );

/**@}*/

/* USER CODE BEGIN (1) */
/* USER CODE END */

#ifdef __cplusplus
}
#endif /*extern "C" */

#endif
