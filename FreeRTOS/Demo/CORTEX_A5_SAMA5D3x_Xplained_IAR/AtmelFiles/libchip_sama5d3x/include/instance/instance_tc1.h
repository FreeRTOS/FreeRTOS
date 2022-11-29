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

#ifndef _SAMA5_TC1_INSTANCE_
#define _SAMA5_TC1_INSTANCE_

/* ========== Register definition for TC1 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_TC1_CCR0          (0xF8014000U) /**< \brief (TC1) Channel Control Register (channel = 0) */
#define REG_TC1_CMR0          (0xF8014004U) /**< \brief (TC1) Channel Mode Register (channel = 0) */
#define REG_TC1_RAB0          (0xF801400CU) /**< \brief (TC1) Register AB (channel = 0) */
#define REG_TC1_CV0           (0xF8014010U) /**< \brief (TC1) Counter Value (channel = 0) */
#define REG_TC1_RA0           (0xF8014014U) /**< \brief (TC1) Register A (channel = 0) */
#define REG_TC1_RB0           (0xF8014018U) /**< \brief (TC1) Register B (channel = 0) */
#define REG_TC1_RC0           (0xF801401CU) /**< \brief (TC1) Register C (channel = 0) */
#define REG_TC1_SR0           (0xF8014020U) /**< \brief (TC1) Status Register (channel = 0) */
#define REG_TC1_IER0          (0xF8014024U) /**< \brief (TC1) Interrupt Enable Register (channel = 0) */
#define REG_TC1_IDR0          (0xF8014028U) /**< \brief (TC1) Interrupt Disable Register (channel = 0) */
#define REG_TC1_IMR0          (0xF801402CU) /**< \brief (TC1) Interrupt Mask Register (channel = 0) */
#define REG_TC1_CCR1          (0xF8014040U) /**< \brief (TC1) Channel Control Register (channel = 1) */
#define REG_TC1_CMR1          (0xF8014044U) /**< \brief (TC1) Channel Mode Register (channel = 1) */
#define REG_TC1_RAB1          (0xF801404CU) /**< \brief (TC1) Register AB (channel = 1) */
#define REG_TC1_CV1           (0xF8014050U) /**< \brief (TC1) Counter Value (channel = 1) */
#define REG_TC1_RA1           (0xF8014054U) /**< \brief (TC1) Register A (channel = 1) */
#define REG_TC1_RB1           (0xF8014058U) /**< \brief (TC1) Register B (channel = 1) */
#define REG_TC1_RC1           (0xF801405CU) /**< \brief (TC1) Register C (channel = 1) */
#define REG_TC1_SR1           (0xF8014060U) /**< \brief (TC1) Status Register (channel = 1) */
#define REG_TC1_IER1          (0xF8014064U) /**< \brief (TC1) Interrupt Enable Register (channel = 1) */
#define REG_TC1_IDR1          (0xF8014068U) /**< \brief (TC1) Interrupt Disable Register (channel = 1) */
#define REG_TC1_IMR1          (0xF801406CU) /**< \brief (TC1) Interrupt Mask Register (channel = 1) */
#define REG_TC1_CCR2          (0xF8014080U) /**< \brief (TC1) Channel Control Register (channel = 2) */
#define REG_TC1_CMR2          (0xF8014084U) /**< \brief (TC1) Channel Mode Register (channel = 2) */
#define REG_TC1_RAB2          (0xF801408CU) /**< \brief (TC1) Register AB (channel = 2) */
#define REG_TC1_CV2           (0xF8014090U) /**< \brief (TC1) Counter Value (channel = 2) */
#define REG_TC1_RA2           (0xF8014094U) /**< \brief (TC1) Register A (channel = 2) */
#define REG_TC1_RB2           (0xF8014098U) /**< \brief (TC1) Register B (channel = 2) */
#define REG_TC1_RC2           (0xF801409CU) /**< \brief (TC1) Register C (channel = 2) */
#define REG_TC1_SR2           (0xF80140A0U) /**< \brief (TC1) Status Register (channel = 2) */
#define REG_TC1_IER2          (0xF80140A4U) /**< \brief (TC1) Interrupt Enable Register (channel = 2) */
#define REG_TC1_IDR2          (0xF80140A8U) /**< \brief (TC1) Interrupt Disable Register (channel = 2) */
#define REG_TC1_IMR2          (0xF80140ACU) /**< \brief (TC1) Interrupt Mask Register (channel = 2) */
#define REG_TC1_BCR           (0xF80140C0U) /**< \brief (TC1) Block Control Register */
#define REG_TC1_BMR           (0xF80140C4U) /**< \brief (TC1) Block Mode Register */
#else
#define REG_TC1_CCR0 (*(WoReg*)0xF8014000U) /**< \brief (TC1) Channel Control Register (channel = 0) */
#define REG_TC1_CMR0 (*(RwReg*)0xF8014004U) /**< \brief (TC1) Channel Mode Register (channel = 0) */
#define REG_TC1_RAB0 (*(RoReg*)0xF801400CU) /**< \brief (TC1) Register AB (channel = 0) */
#define REG_TC1_CV0  (*(RoReg*)0xF8014010U) /**< \brief (TC1) Counter Value (channel = 0) */
#define REG_TC1_RA0  (*(RwReg*)0xF8014014U) /**< \brief (TC1) Register A (channel = 0) */
#define REG_TC1_RB0  (*(RwReg*)0xF8014018U) /**< \brief (TC1) Register B (channel = 0) */
#define REG_TC1_RC0  (*(RwReg*)0xF801401CU) /**< \brief (TC1) Register C (channel = 0) */
#define REG_TC1_SR0  (*(RoReg*)0xF8014020U) /**< \brief (TC1) Status Register (channel = 0) */
#define REG_TC1_IER0 (*(WoReg*)0xF8014024U) /**< \brief (TC1) Interrupt Enable Register (channel = 0) */
#define REG_TC1_IDR0 (*(WoReg*)0xF8014028U) /**< \brief (TC1) Interrupt Disable Register (channel = 0) */
#define REG_TC1_IMR0 (*(RoReg*)0xF801402CU) /**< \brief (TC1) Interrupt Mask Register (channel = 0) */
#define REG_TC1_CCR1 (*(WoReg*)0xF8014040U) /**< \brief (TC1) Channel Control Register (channel = 1) */
#define REG_TC1_CMR1 (*(RwReg*)0xF8014044U) /**< \brief (TC1) Channel Mode Register (channel = 1) */
#define REG_TC1_RAB1 (*(RoReg*)0xF801404CU) /**< \brief (TC1) Register AB (channel = 1) */
#define REG_TC1_CV1  (*(RoReg*)0xF8014050U) /**< \brief (TC1) Counter Value (channel = 1) */
#define REG_TC1_RA1  (*(RwReg*)0xF8014054U) /**< \brief (TC1) Register A (channel = 1) */
#define REG_TC1_RB1  (*(RwReg*)0xF8014058U) /**< \brief (TC1) Register B (channel = 1) */
#define REG_TC1_RC1  (*(RwReg*)0xF801405CU) /**< \brief (TC1) Register C (channel = 1) */
#define REG_TC1_SR1  (*(RoReg*)0xF8014060U) /**< \brief (TC1) Status Register (channel = 1) */
#define REG_TC1_IER1 (*(WoReg*)0xF8014064U) /**< \brief (TC1) Interrupt Enable Register (channel = 1) */
#define REG_TC1_IDR1 (*(WoReg*)0xF8014068U) /**< \brief (TC1) Interrupt Disable Register (channel = 1) */
#define REG_TC1_IMR1 (*(RoReg*)0xF801406CU) /**< \brief (TC1) Interrupt Mask Register (channel = 1) */
#define REG_TC1_CCR2 (*(WoReg*)0xF8014080U) /**< \brief (TC1) Channel Control Register (channel = 2) */
#define REG_TC1_CMR2 (*(RwReg*)0xF8014084U) /**< \brief (TC1) Channel Mode Register (channel = 2) */
#define REG_TC1_RAB2 (*(RoReg*)0xF801408CU) /**< \brief (TC1) Register AB (channel = 2) */
#define REG_TC1_CV2  (*(RoReg*)0xF8014090U) /**< \brief (TC1) Counter Value (channel = 2) */
#define REG_TC1_RA2  (*(RwReg*)0xF8014094U) /**< \brief (TC1) Register A (channel = 2) */
#define REG_TC1_RB2  (*(RwReg*)0xF8014098U) /**< \brief (TC1) Register B (channel = 2) */
#define REG_TC1_RC2  (*(RwReg*)0xF801409CU) /**< \brief (TC1) Register C (channel = 2) */
#define REG_TC1_SR2  (*(RoReg*)0xF80140A0U) /**< \brief (TC1) Status Register (channel = 2) */
#define REG_TC1_IER2 (*(WoReg*)0xF80140A4U) /**< \brief (TC1) Interrupt Enable Register (channel = 2) */
#define REG_TC1_IDR2 (*(WoReg*)0xF80140A8U) /**< \brief (TC1) Interrupt Disable Register (channel = 2) */
#define REG_TC1_IMR2 (*(RoReg*)0xF80140ACU) /**< \brief (TC1) Interrupt Mask Register (channel = 2) */
#define REG_TC1_BCR  (*(WoReg*)0xF80140C0U) /**< \brief (TC1) Block Control Register */
#define REG_TC1_BMR  (*(RwReg*)0xF80140C4U) /**< \brief (TC1) Block Mode Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_TC1_INSTANCE_ */
