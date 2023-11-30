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

#ifndef _SAMA5_TC0_INSTANCE_
#define _SAMA5_TC0_INSTANCE_

/* ========== Register definition for TC0 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_TC0_CCR0          (0xF0010000U) /**< \brief (TC0) Channel Control Register (channel = 0) */
#define REG_TC0_CMR0          (0xF0010004U) /**< \brief (TC0) Channel Mode Register (channel = 0) */
#define REG_TC0_RAB0          (0xF001000CU) /**< \brief (TC0) Register AB (channel = 0) */
#define REG_TC0_CV0           (0xF0010010U) /**< \brief (TC0) Counter Value (channel = 0) */
#define REG_TC0_RA0           (0xF0010014U) /**< \brief (TC0) Register A (channel = 0) */
#define REG_TC0_RB0           (0xF0010018U) /**< \brief (TC0) Register B (channel = 0) */
#define REG_TC0_RC0           (0xF001001CU) /**< \brief (TC0) Register C (channel = 0) */
#define REG_TC0_SR0           (0xF0010020U) /**< \brief (TC0) Status Register (channel = 0) */
#define REG_TC0_IER0          (0xF0010024U) /**< \brief (TC0) Interrupt Enable Register (channel = 0) */
#define REG_TC0_IDR0          (0xF0010028U) /**< \brief (TC0) Interrupt Disable Register (channel = 0) */
#define REG_TC0_IMR0          (0xF001002CU) /**< \brief (TC0) Interrupt Mask Register (channel = 0) */
#define REG_TC0_CCR1          (0xF0010040U) /**< \brief (TC0) Channel Control Register (channel = 1) */
#define REG_TC0_CMR1          (0xF0010044U) /**< \brief (TC0) Channel Mode Register (channel = 1) */
#define REG_TC0_RAB1          (0xF001004CU) /**< \brief (TC0) Register AB (channel = 1) */
#define REG_TC0_CV1           (0xF0010050U) /**< \brief (TC0) Counter Value (channel = 1) */
#define REG_TC0_RA1           (0xF0010054U) /**< \brief (TC0) Register A (channel = 1) */
#define REG_TC0_RB1           (0xF0010058U) /**< \brief (TC0) Register B (channel = 1) */
#define REG_TC0_RC1           (0xF001005CU) /**< \brief (TC0) Register C (channel = 1) */
#define REG_TC0_SR1           (0xF0010060U) /**< \brief (TC0) Status Register (channel = 1) */
#define REG_TC0_IER1          (0xF0010064U) /**< \brief (TC0) Interrupt Enable Register (channel = 1) */
#define REG_TC0_IDR1          (0xF0010068U) /**< \brief (TC0) Interrupt Disable Register (channel = 1) */
#define REG_TC0_IMR1          (0xF001006CU) /**< \brief (TC0) Interrupt Mask Register (channel = 1) */
#define REG_TC0_CCR2          (0xF0010080U) /**< \brief (TC0) Channel Control Register (channel = 2) */
#define REG_TC0_CMR2          (0xF0010084U) /**< \brief (TC0) Channel Mode Register (channel = 2) */
#define REG_TC0_RAB2          (0xF001008CU) /**< \brief (TC0) Register AB (channel = 2) */
#define REG_TC0_CV2           (0xF0010090U) /**< \brief (TC0) Counter Value (channel = 2) */
#define REG_TC0_RA2           (0xF0010094U) /**< \brief (TC0) Register A (channel = 2) */
#define REG_TC0_RB2           (0xF0010098U) /**< \brief (TC0) Register B (channel = 2) */
#define REG_TC0_RC2           (0xF001009CU) /**< \brief (TC0) Register C (channel = 2) */
#define REG_TC0_SR2           (0xF00100A0U) /**< \brief (TC0) Status Register (channel = 2) */
#define REG_TC0_IER2          (0xF00100A4U) /**< \brief (TC0) Interrupt Enable Register (channel = 2) */
#define REG_TC0_IDR2          (0xF00100A8U) /**< \brief (TC0) Interrupt Disable Register (channel = 2) */
#define REG_TC0_IMR2          (0xF00100ACU) /**< \brief (TC0) Interrupt Mask Register (channel = 2) */
#define REG_TC0_BCR           (0xF00100C0U) /**< \brief (TC0) Block Control Register */
#define REG_TC0_BMR           (0xF00100C4U) /**< \brief (TC0) Block Mode Register */
#else
#define REG_TC0_CCR0 (*(WoReg*)0xF0010000U) /**< \brief (TC0) Channel Control Register (channel = 0) */
#define REG_TC0_CMR0 (*(RwReg*)0xF0010004U) /**< \brief (TC0) Channel Mode Register (channel = 0) */
#define REG_TC0_RAB0 (*(RoReg*)0xF001000CU) /**< \brief (TC0) Register AB (channel = 0) */
#define REG_TC0_CV0  (*(RoReg*)0xF0010010U) /**< \brief (TC0) Counter Value (channel = 0) */
#define REG_TC0_RA0  (*(RwReg*)0xF0010014U) /**< \brief (TC0) Register A (channel = 0) */
#define REG_TC0_RB0  (*(RwReg*)0xF0010018U) /**< \brief (TC0) Register B (channel = 0) */
#define REG_TC0_RC0  (*(RwReg*)0xF001001CU) /**< \brief (TC0) Register C (channel = 0) */
#define REG_TC0_SR0  (*(RoReg*)0xF0010020U) /**< \brief (TC0) Status Register (channel = 0) */
#define REG_TC0_IER0 (*(WoReg*)0xF0010024U) /**< \brief (TC0) Interrupt Enable Register (channel = 0) */
#define REG_TC0_IDR0 (*(WoReg*)0xF0010028U) /**< \brief (TC0) Interrupt Disable Register (channel = 0) */
#define REG_TC0_IMR0 (*(RoReg*)0xF001002CU) /**< \brief (TC0) Interrupt Mask Register (channel = 0) */
#define REG_TC0_CCR1 (*(WoReg*)0xF0010040U) /**< \brief (TC0) Channel Control Register (channel = 1) */
#define REG_TC0_CMR1 (*(RwReg*)0xF0010044U) /**< \brief (TC0) Channel Mode Register (channel = 1) */
#define REG_TC0_RAB1 (*(RoReg*)0xF001004CU) /**< \brief (TC0) Register AB (channel = 1) */
#define REG_TC0_CV1  (*(RoReg*)0xF0010050U) /**< \brief (TC0) Counter Value (channel = 1) */
#define REG_TC0_RA1  (*(RwReg*)0xF0010054U) /**< \brief (TC0) Register A (channel = 1) */
#define REG_TC0_RB1  (*(RwReg*)0xF0010058U) /**< \brief (TC0) Register B (channel = 1) */
#define REG_TC0_RC1  (*(RwReg*)0xF001005CU) /**< \brief (TC0) Register C (channel = 1) */
#define REG_TC0_SR1  (*(RoReg*)0xF0010060U) /**< \brief (TC0) Status Register (channel = 1) */
#define REG_TC0_IER1 (*(WoReg*)0xF0010064U) /**< \brief (TC0) Interrupt Enable Register (channel = 1) */
#define REG_TC0_IDR1 (*(WoReg*)0xF0010068U) /**< \brief (TC0) Interrupt Disable Register (channel = 1) */
#define REG_TC0_IMR1 (*(RoReg*)0xF001006CU) /**< \brief (TC0) Interrupt Mask Register (channel = 1) */
#define REG_TC0_CCR2 (*(WoReg*)0xF0010080U) /**< \brief (TC0) Channel Control Register (channel = 2) */
#define REG_TC0_CMR2 (*(RwReg*)0xF0010084U) /**< \brief (TC0) Channel Mode Register (channel = 2) */
#define REG_TC0_RAB2 (*(RoReg*)0xF001008CU) /**< \brief (TC0) Register AB (channel = 2) */
#define REG_TC0_CV2  (*(RoReg*)0xF0010090U) /**< \brief (TC0) Counter Value (channel = 2) */
#define REG_TC0_RA2  (*(RwReg*)0xF0010094U) /**< \brief (TC0) Register A (channel = 2) */
#define REG_TC0_RB2  (*(RwReg*)0xF0010098U) /**< \brief (TC0) Register B (channel = 2) */
#define REG_TC0_RC2  (*(RwReg*)0xF001009CU) /**< \brief (TC0) Register C (channel = 2) */
#define REG_TC0_SR2  (*(RoReg*)0xF00100A0U) /**< \brief (TC0) Status Register (channel = 2) */
#define REG_TC0_IER2 (*(WoReg*)0xF00100A4U) /**< \brief (TC0) Interrupt Enable Register (channel = 2) */
#define REG_TC0_IDR2 (*(WoReg*)0xF00100A8U) /**< \brief (TC0) Interrupt Disable Register (channel = 2) */
#define REG_TC0_IMR2 (*(RoReg*)0xF00100ACU) /**< \brief (TC0) Interrupt Mask Register (channel = 2) */
#define REG_TC0_BCR  (*(WoReg*)0xF00100C0U) /**< \brief (TC0) Block Control Register */
#define REG_TC0_BMR  (*(RwReg*)0xF00100C4U) /**< \brief (TC0) Block Mode Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_TC0_INSTANCE_ */
