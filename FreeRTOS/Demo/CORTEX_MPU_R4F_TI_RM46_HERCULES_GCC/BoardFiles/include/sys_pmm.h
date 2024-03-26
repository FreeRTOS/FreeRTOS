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

/* Bit Masks */
#define PMM_LOGICPDPWRCTRL0_LOGICPDON0    0x0F000000U /*PD2*/
#define PMM_LOGICPDPWRCTRL0_LOGICPDON1    0x000F0000U /*PD3*/
#define PMM_LOGICPDPWRCTRL0_LOGICPDON2    0x00000F00U /*PD4*/
#define PMM_LOGICPDPWRCTRL0_LOGICPDON3    0x0000000FU /*PD5*/

#define PMM_MEMPDPWRCTRL0_MEMPDON0        0x0F000000U /*RAM_PD1*/
#define PMM_MEMPDPWRCTRL0_MEMPDON1        0x000F0000U /*RAM_PD2*/
#define PMM_MEMPDPWRCTRL0_MEMPDON2        0x00000F00U /*RAM_PD3*/

#define PMM_LOGICPDPWRSTAT_DOMAINON       0x00000100U
#define PMM_LOGICPDPWRSTAT_LOGICPDPWRSTAT 0x00000003U
#define PMM_MEMPDPWRSTAT_DOMAINON         0x00000100U
#define PMM_MEMPDPWRSTAT_MEMPDPWRSTAT     0x00000003U
#define PMM_GLOBALCTRL1_AUTOCLKWAKEENA    0x00000001U

/* Configuration registers initial value */
#define PMM_LOGICPDPWRCTRL0_CONFIGVALUE                                             \
    ( ( uint32 ) ( ( uint32 ) 0x5U << 24U ) | ( uint32 ) ( ( uint32 ) 0x5U << 16U ) \
      | ( uint32 ) ( ( uint32 ) 0xAU << 8U ) | ( uint32 ) ( ( uint32 ) 0x5U << 0U ) )
#define PMM_MEMPDPWRCTRL0_CONFIGVALUE \
    ( ( uint32 ) ( ( uint32 ) 0x5U << 24U ) | ( uint32 ) ( ( uint32 ) 0x5U << 16U ) )

#define PMM_PDCLKDISREG_CONFIGVALUE                 \
    ( ( uint32 ) ( ( uint32 ) ( 1U - 1U ) << 0U )   \
      | ( uint32 ) ( ( uint32 ) ( 1U - 1U ) << 1U ) \
      | ( uint32 ) ( ( uint32 ) ( 1U - 0U ) << 2U ) \
      | ( uint32 ) ( ( uint32 ) ( 1U - 1U ) << 3U ) )

#define PMM_GLOBALCTRL1_CONFIGVALUE \
    ( ( uint32 ) ( ( uint32 ) 0U << 8U ) | ( uint32 ) ( ( uint32 ) 0U << 0U ) )

/** @enum pmmLogicPDTag
 *   @brief PMM Logic Power Domain
 *
 *   Used to define PMM Logic Power Domain
 */
typedef enum pmmLogicPDTag
{
    PMM_LOGICPD1 = 4U, /*-- NOT USED*/
    PMM_LOGICPD2 = 0U,
    PMM_LOGICPD3 = 1U,
    PMM_LOGICPD4 = 2U,
    PMM_LOGICPD5 = 3U
} pmm_LogicPD_t;

/** @enum pmmMemPDTag
 *   @brief PMM Memory-Only Power Domain
 *
 *   Used to define PMM Memory-Only Power Domain
 */
typedef enum pmmMemPDTag
{
    PMM_MEMPD1 = 0U,
    PMM_MEMPD2 = 1U,
    PMM_MEMPD3 = 2U
} pmm_MemPD_t;

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

typedef struct pmm_config_reg
{
    uint32 CONFIG_LOGICPDPWRCTRL0;
    uint32 CONFIG_MEMPDPWRCTRL0;
    uint32 CONFIG_PDCLKDISREG;
    uint32 CONFIG_GLOBALCTRL1;
} pmm_config_reg_t;

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
void pmmInit( void );
void pmmTurnONLogicPowerDomain( pmm_LogicPD_t logicPD );
void pmmTurnONMemPowerDomain( pmm_MemPD_t memPD );
void pmmTurnOFFLogicPowerDomain( pmm_LogicPD_t logicPD );
void pmmTurnOFFMemPowerDomain( pmm_MemPD_t memPD );
boolean pmmIsLogicPowerDomainActive( pmm_LogicPD_t logicPD );
boolean pmmIsMemPowerDomainActive( pmm_MemPD_t memPD );
void pmmGetConfigValue( pmm_config_reg_t * config_reg, config_value_type_t type );
void pmmSetMode( pmm_Mode_t mode );
boolean pmmPerformSelfTest( void );

/**@}*/
/* USER CODE BEGIN (1) */
/* USER CODE END */

#ifdef __cplusplus
}
#endif /*extern "C" */

#endif /* ifndef __SYS_PMM_H__ */
