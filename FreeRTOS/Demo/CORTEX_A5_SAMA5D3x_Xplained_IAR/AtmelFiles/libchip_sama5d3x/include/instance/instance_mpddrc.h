/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2012, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following condition is met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

#ifndef _SAMA5_MPDDRC_INSTANCE_
#define _SAMA5_MPDDRC_INSTANCE_

/* ========== Register definition for MPDDRC peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_MPDDRC_MR                      (0xFFFFEA00U) /**< \brief (MPDDRC) MPDDRC Mode Register */
#define REG_MPDDRC_RTR                     (0xFFFFEA04U) /**< \brief (MPDDRC) MPDDRC Refresh Timer Register */
#define REG_MPDDRC_CR                      (0xFFFFEA08U) /**< \brief (MPDDRC) MPDDRC Configuration Register */
#define REG_MPDDRC_TPR0                    (0xFFFFEA0CU) /**< \brief (MPDDRC) MPDDRC Timing Parameter 0 Register */
#define REG_MPDDRC_TPR1                    (0xFFFFEA10U) /**< \brief (MPDDRC) MPDDRC Timing Parameter 1 Register */
#define REG_MPDDRC_TPR2                    (0xFFFFEA14U) /**< \brief (MPDDRC) MPDDRC Timing Parameter 2 Register */
#define REG_MPDDRC_LPR                     (0xFFFFEA1CU) /**< \brief (MPDDRC) MPDDRC Low-power Register */
#define REG_MPDDRC_MD                      (0xFFFFEA20U) /**< \brief (MPDDRC) MPDDRC Memory Device Register */
#define REG_MPDDRC_LPDDR2_LPR              (0xFFFFEA28U) /**< \brief (MPDDRC) MPDDRC LPDDR2 Low-power Register */
#define REG_MPDDRC_LPDDR2_CAL_MR4          (0xFFFFEA2CU) /**< \brief (MPDDRC) MPDDRC LPDDR2 Calibration and MR4 Register */
#define REG_MPDDRC_LPDDR2_TIM_CAL          (0xFFFFEA30U) /**< \brief (MPDDRC) MPDDRC LPDDR2 Timing Calibration Register */
#define REG_MPDDRC_IO_CALIBR               (0xFFFFEA34U) /**< \brief (MPDDRC) MPDDRC IO Calibration */
#define REG_MPDDRC_OCMS                    (0xFFFFEA38U) /**< \brief (MPDDRC) MPDDRC OCMS Register */
#define REG_MPDDRC_OCMS_KEY1               (0xFFFFEA3CU) /**< \brief (MPDDRC) MPDDRC OCMS KEY1 Register */
#define REG_MPDDRC_OCMS_KEY2               (0xFFFFEA40U) /**< \brief (MPDDRC) MPDDRC OCMS KEY2 Register */
#define REG_MPDDRC_DLL_MOR                 (0xFFFFEA74U) /**< \brief (MPDDRC) MPDDRC DLL Master Offset Register */
#define REG_MPDDRC_DLL_SOR                 (0xFFFFEA78U) /**< \brief (MPDDRC) MPDDRC DLL Slave Offset Register */
#define REG_MPDDRC_DLL_MSR                 (0xFFFFEA7CU) /**< \brief (MPDDRC) MPDDRC DLL Master Status Register */
#define REG_MPDDRC_DLL_S0SR                (0xFFFFEA80U) /**< \brief (MPDDRC) MPDDRC DLL Slave 0 Status Register */
#define REG_MPDDRC_DLL_S1SR                (0xFFFFEA84U) /**< \brief (MPDDRC) MPDDRC DLL Slave 1 Status Register */
#define REG_MPDDRC_DLL_S2SR                (0xFFFFEA88U) /**< \brief (MPDDRC) MPDDRC DLL Slave 2 Status Register */
#define REG_MPDDRC_DLL_S3SR                (0xFFFFEA8CU) /**< \brief (MPDDRC) MPDDRC DLL Slave 3 Status Register */
#define REG_MPDDRC_WPCR                    (0xFFFFEAE4U) /**< \brief (MPDDRC) MPDDRC Write Protect Control Register */
#define REG_MPDDRC_WPSR                    (0xFFFFEAE8U) /**< \brief (MPDDRC) MPDDRC Write Protect Status Register */
#else
#define REG_MPDDRC_MR             (*(RwReg*)0xFFFFEA00U) /**< \brief (MPDDRC) MPDDRC Mode Register */
#define REG_MPDDRC_RTR            (*(RwReg*)0xFFFFEA04U) /**< \brief (MPDDRC) MPDDRC Refresh Timer Register */
#define REG_MPDDRC_CR             (*(RwReg*)0xFFFFEA08U) /**< \brief (MPDDRC) MPDDRC Configuration Register */
#define REG_MPDDRC_TPR0           (*(RwReg*)0xFFFFEA0CU) /**< \brief (MPDDRC) MPDDRC Timing Parameter 0 Register */
#define REG_MPDDRC_TPR1           (*(RwReg*)0xFFFFEA10U) /**< \brief (MPDDRC) MPDDRC Timing Parameter 1 Register */
#define REG_MPDDRC_TPR2           (*(RwReg*)0xFFFFEA14U) /**< \brief (MPDDRC) MPDDRC Timing Parameter 2 Register */
#define REG_MPDDRC_LPR            (*(RwReg*)0xFFFFEA1CU) /**< \brief (MPDDRC) MPDDRC Low-power Register */
#define REG_MPDDRC_MD             (*(RwReg*)0xFFFFEA20U) /**< \brief (MPDDRC) MPDDRC Memory Device Register */
#define REG_MPDDRC_LPDDR2_LPR     (*(RwReg*)0xFFFFEA28U) /**< \brief (MPDDRC) MPDDRC LPDDR2 Low-power Register */
#define REG_MPDDRC_LPDDR2_CAL_MR4 (*(RwReg*)0xFFFFEA2CU) /**< \brief (MPDDRC) MPDDRC LPDDR2 Calibration and MR4 Register */
#define REG_MPDDRC_LPDDR2_TIM_CAL (*(RwReg*)0xFFFFEA30U) /**< \brief (MPDDRC) MPDDRC LPDDR2 Timing Calibration Register */
#define REG_MPDDRC_IO_CALIBR      (*(RwReg*)0xFFFFEA34U) /**< \brief (MPDDRC) MPDDRC IO Calibration */
#define REG_MPDDRC_OCMS           (*(RwReg*)0xFFFFEA38U) /**< \brief (MPDDRC) MPDDRC OCMS Register */
#define REG_MPDDRC_OCMS_KEY1      (*(WoReg*)0xFFFFEA3CU) /**< \brief (MPDDRC) MPDDRC OCMS KEY1 Register */
#define REG_MPDDRC_OCMS_KEY2      (*(WoReg*)0xFFFFEA40U) /**< \brief (MPDDRC) MPDDRC OCMS KEY2 Register */
#define REG_MPDDRC_DLL_MOR        (*(RwReg*)0xFFFFEA74U) /**< \brief (MPDDRC) MPDDRC DLL Master Offset Register */
#define REG_MPDDRC_DLL_SOR        (*(RwReg*)0xFFFFEA78U) /**< \brief (MPDDRC) MPDDRC DLL Slave Offset Register */
#define REG_MPDDRC_DLL_MSR        (*(RoReg*)0xFFFFEA7CU) /**< \brief (MPDDRC) MPDDRC DLL Master Status Register */
#define REG_MPDDRC_DLL_S0SR       (*(RoReg*)0xFFFFEA80U) /**< \brief (MPDDRC) MPDDRC DLL Slave 0 Status Register */
#define REG_MPDDRC_DLL_S1SR       (*(RoReg*)0xFFFFEA84U) /**< \brief (MPDDRC) MPDDRC DLL Slave 1 Status Register */
#define REG_MPDDRC_DLL_S2SR       (*(RoReg*)0xFFFFEA88U) /**< \brief (MPDDRC) MPDDRC DLL Slave 2 Status Register */
#define REG_MPDDRC_DLL_S3SR       (*(RoReg*)0xFFFFEA8CU) /**< \brief (MPDDRC) MPDDRC DLL Slave 3 Status Register */
#define REG_MPDDRC_WPCR           (*(RwReg*)0xFFFFEAE4U) /**< \brief (MPDDRC) MPDDRC Write Protect Control Register */
#define REG_MPDDRC_WPSR           (*(RoReg*)0xFFFFEAE8U) /**< \brief (MPDDRC) MPDDRC Write Protect Status Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_MPDDRC_INSTANCE_ */
