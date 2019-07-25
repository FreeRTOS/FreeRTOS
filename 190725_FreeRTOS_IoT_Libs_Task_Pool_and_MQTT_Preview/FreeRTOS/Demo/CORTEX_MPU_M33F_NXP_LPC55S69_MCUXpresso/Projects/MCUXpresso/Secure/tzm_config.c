/*
 * Copyright 2018 NXP
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include "fsl_common.h"
#include "tzm_config.h"

/*******************************************************************************
 * Definitions
 ******************************************************************************/
#define CODE_FLASH_START_NS         0x00010000  
#define CODE_FLASH_SIZE_NS          0x00072000
#define CODE_FLASH_START_NSC        0x1000FE00
#define CODE_FLASH_SIZE_NSC         0x200
#define DATA_RAM_START_NS           0x20008000
#define DATA_RAM_SIZE_NS            0x0002B000
#define PERIPH_START_NS             0x40000000
#define PERIPH_SIZE_NS              0x00100000

/*******************************************************************************
 * Variables
 ******************************************************************************/
#if defined(__MCUXPRESSO)
extern unsigned char _start_sg[];
#endif

/*!
 * @brief TrustZone initialization
 *
 * SAU Configuration
 * This function configures 3 regions:
 * 0x00010000 - 0x00081FFF - non-secure for code execution
 * 0x1000FE00 - 0x1000FFFF - secure, non-secure callable for veneer table
 * 0x20000000 - 0x20032FFF - non-secure for data
 *
 * AHB secure controller settings
 * After RESET all memories and peripherals are set to user:non-secure access
 * This function configures following memories and peripherals as secure:
 * 0x00000000 - 0x0000FFFF - for secure code execution (this is physical FLASH address)
 * 0x00008000 - 0x20032FFF - for secure data (this is physical RAM address)
 *
 * Secure peripherals: SYSCON, IOCON, FLEXCOMM0
 * NOTE: This example configures necessary peripherals for this example. 
 *       User should configure all peripherals, which shouldn't be accessible
 *       from normal world.
*/
void BOARD_InitTrustZone()
{
    /* Disable SAU */
    SAU->CTRL = 0U;
    
    /* Configure SAU region 0 - Non-secure RAM for CODE execution*/
    /* Set SAU region number */
    SAU->RNR = 0;
    /* Region base address */   
    SAU->RBAR = (CODE_FLASH_START_NS & SAU_RBAR_BADDR_Msk);
    /* Region end address */
    SAU->RLAR = ((CODE_FLASH_START_NS + CODE_FLASH_SIZE_NS-1) & SAU_RLAR_LADDR_Msk) | 
                 /* Region memory attribute index */
                 ((0U << SAU_RLAR_NSC_Pos) & SAU_RLAR_NSC_Msk) |
                 /* Enable region */
                 ((1U << SAU_RLAR_ENABLE_Pos) & SAU_RLAR_ENABLE_Msk); 
    
    /* Configure SAU region 1 - Non-secure RAM for DATA */
    /* Set SAU region number */
    SAU->RNR = 1;
    /* Region base address */   
    SAU->RBAR = (DATA_RAM_START_NS & SAU_RBAR_BADDR_Msk);
    /* Region end address */
    SAU->RLAR = ((DATA_RAM_START_NS + DATA_RAM_SIZE_NS-1) & SAU_RLAR_LADDR_Msk) | 
                 /* Region memory attribute index */
                 ((0U << SAU_RLAR_NSC_Pos) & SAU_RLAR_NSC_Msk) |
                 /* Enable region */
                 ((1U << SAU_RLAR_ENABLE_Pos) & SAU_RLAR_ENABLE_Msk); 
    
    /* Configure SAU region 2 - Non-secure callable FLASH for CODE veneer table*/
    /* Set SAU region number */
    SAU->RNR = 2;
    /* Region base address */   
#if defined(__MCUXPRESSO)
    SAU->RBAR = ((uint32_t)&_start_sg & SAU_RBAR_BADDR_Msk);
#else
    SAU->RBAR = (CODE_FLASH_START_NSC & SAU_RBAR_BADDR_Msk);
#endif
    /* Region end address */
#if defined(__MCUXPRESSO)
    SAU->RLAR = (((uint32_t)&_start_sg + CODE_FLASH_SIZE_NSC-1) & SAU_RLAR_LADDR_Msk) |
                 /* Region memory attribute index */
                 ((1U << SAU_RLAR_NSC_Pos) & SAU_RLAR_NSC_Msk) |
                 /* Enable region */
                 ((1U << SAU_RLAR_ENABLE_Pos) & SAU_RLAR_ENABLE_Msk);
#else
    SAU->RLAR = ((CODE_FLASH_START_NSC + CODE_FLASH_SIZE_NSC-1) & SAU_RLAR_LADDR_Msk) | 
                 /* Region memory attribute index */
                 ((1U << SAU_RLAR_NSC_Pos) & SAU_RLAR_NSC_Msk) |
                 /* Enable region */
                 ((1U << SAU_RLAR_ENABLE_Pos) & SAU_RLAR_ENABLE_Msk); 
#endif

    /* Configure SAU region 3 - Non-secure peripherals address space */
    /* Set SAU region number */
    SAU->RNR = 3;
    /* Region base address */
    SAU->RBAR = (PERIPH_START_NS & SAU_RBAR_BADDR_Msk);
    /* Region end address */
    SAU->RLAR = ((PERIPH_START_NS + PERIPH_SIZE_NS-1) & SAU_RLAR_LADDR_Msk) |
                 /* Region memory attribute index */
                 ((0U << SAU_RLAR_NSC_Pos) & SAU_RLAR_NSC_Msk) |
                 /* Enable region */
                 ((1U << SAU_RLAR_ENABLE_Pos) & SAU_RLAR_ENABLE_Msk);

    /* Force memory writes before continuing */
    __DSB();
    /* Flush and refill pipeline with updated permissions */
    __ISB();     
    /* Enable SAU */
    SAU->CTRL = 1U;  

    /*Configuration of AHB Secure Controller 
     * Possible values for every memory sector or peripheral rule: 
     *  0b00    Non-secure and Non-priviledge user access allowed.
     *  0b01    Non-secure and Privilege access allowed.
     *  0b10    Secure and Non-priviledge user access allowed.
     *  0b11    Secure and Priviledge user access allowed. */

    /* FLASH memory configuration from 0x00000000 to 0x0000FFFF, sector size is 32kB */
    AHB_SECURE_CTRL->SEC_CTRL_FLASH_ROM[0].SEC_CTRL_FLASH_MEM_RULE[0] = 0x00000033U;
    AHB_SECURE_CTRL->SEC_CTRL_FLASH_ROM[0].SEC_CTRL_FLASH_MEM_RULE[1] = 0x00000000U;
    AHB_SECURE_CTRL->SEC_CTRL_FLASH_ROM[0].SEC_CTRL_FLASH_MEM_RULE[2] = 0x00000000U;
    /* RAM memory configuration from 0x20000000 to 0x20007FFF, sector size is 4kB */
    /* Memory settings for user non-secure access (0x0U) is mentioned for completness only. It is default RESET value. */    
    AHB_SECURE_CTRL->SEC_CTRL_RAM0[0].MEM_RULE[0] = 0x33333333U;
    AHB_SECURE_CTRL->SEC_CTRL_RAM0[0].MEM_RULE[1] = 0x00000000U;
    AHB_SECURE_CTRL->SEC_CTRL_RAM1[0].MEM_RULE[0] = 0x00000000U;
    AHB_SECURE_CTRL->SEC_CTRL_RAM1[0].MEM_RULE[1] = 0x00000000U;
    AHB_SECURE_CTRL->SEC_CTRL_RAM2[0].MEM_RULE[0] = 0x00000000U;
    AHB_SECURE_CTRL->SEC_CTRL_RAM2[0].MEM_RULE[1] = 0x00000000U;
    AHB_SECURE_CTRL->SEC_CTRL_RAM3[0].MEM_RULE[0] = 0x00000000U;
    AHB_SECURE_CTRL->SEC_CTRL_RAM3[0].MEM_RULE[1] = 0x00000000U;
    AHB_SECURE_CTRL->SEC_CTRL_RAM4[0].MEM_RULE[0] = 0x00000000U;
    
    /* Set SYSCON and IOCON as secure */
    AHB_SECURE_CTRL->SEC_CTRL_APB_BRIDGE[0].SEC_CTRL_APB_BRIDGE0_MEM_CTRL0 = AHB_SECURE_CTRL_SEC_CTRL_APB_BRIDGE_SEC_CTRL_APB_BRIDGE0_MEM_CTRL0_SYSCON_RULE(0x3U) |
                                                                             AHB_SECURE_CTRL_SEC_CTRL_APB_BRIDGE_SEC_CTRL_APB_BRIDGE0_MEM_CTRL0_IOCON_RULE(0x3U);

    /* Set FLEXCOMM0 as secure */
    AHB_SECURE_CTRL->SEC_CTRL_AHB0_0_SLAVE_RULE = AHB_SECURE_CTRL_SEC_CTRL_AHB0_0_SLAVE_RULE_FLEXCOMM0_RULE(0x3U);

    /* Enable AHB secure controller check and lock all rule registers */
    AHB_SECURE_CTRL->MISC_CTRL_DP_REG = (AHB_SECURE_CTRL->MISC_CTRL_DP_REG & ~(AHB_SECURE_CTRL_MISC_CTRL_DP_REG_WRITE_LOCK_MASK | 
                                                                               AHB_SECURE_CTRL_MISC_CTRL_DP_REG_ENABLE_SECURE_CHECKING_MASK)) |
                                        AHB_SECURE_CTRL_MISC_CTRL_DP_REG_WRITE_LOCK(0x1U) |
                                        AHB_SECURE_CTRL_MISC_CTRL_DP_REG_ENABLE_SECURE_CHECKING(0x1U);
}
