/* ---------------------------------------------------------------------------- */
/*                  Atmel Microcontroller Software Support                      */
/*                       SAM Software Package License                           */
/* ---------------------------------------------------------------------------- */
/* Copyright (c) 2014, Atmel Corporation                                        */
/*                                                                              */
/* All rights reserved.                                                         */
/*                                                                              */
/* Redistribution and use in source and binary forms, with or without           */
/* modification, are permitted provided that the following condition is met:    */
/*                                                                              */
/* - Redistributions of source code must retain the above copyright notice,     */
/* this list of conditions and the disclaimer below.                            */
/*                                                                              */
/* Atmel's name may not be used to endorse or promote products derived from     */
/* this software without specific prior written permission.                     */
/*                                                                              */
/* DISCLAIMER:  THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR   */
/* IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF */
/* MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE   */
/* DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,      */
/* INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT */
/* LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,  */
/* OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF    */
/* LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING         */
/* NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, */
/* EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                           */
/* ---------------------------------------------------------------------------- */

#ifndef _SAMV71_TC0_INSTANCE_
#define _SAMV71_TC0_INSTANCE_

/* ========== Register definition for TC0 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
  #define REG_TC0_CCR0                   (0x4000C000U) /**< \brief (TC0) Channel Control Register (channel = 0) */
  #define REG_TC0_CMR0                   (0x4000C004U) /**< \brief (TC0) Channel Mode Register (channel = 0) */
  #define REG_TC0_SMMR0                  (0x4000C008U) /**< \brief (TC0) Stepper Motor Mode Register (channel = 0) */
  #define REG_TC0_RAB0                   (0x4000C00CU) /**< \brief (TC0) Register AB (channel = 0) */
  #define REG_TC0_CV0                    (0x4000C010U) /**< \brief (TC0) Counter Value (channel = 0) */
  #define REG_TC0_RA0                    (0x4000C014U) /**< \brief (TC0) Register A (channel = 0) */
  #define REG_TC0_RB0                    (0x4000C018U) /**< \brief (TC0) Register B (channel = 0) */
  #define REG_TC0_RC0                    (0x4000C01CU) /**< \brief (TC0) Register C (channel = 0) */
  #define REG_TC0_SR0                    (0x4000C020U) /**< \brief (TC0) Status Register (channel = 0) */
  #define REG_TC0_IER0                   (0x4000C024U) /**< \brief (TC0) Interrupt Enable Register (channel = 0) */
  #define REG_TC0_IDR0                   (0x4000C028U) /**< \brief (TC0) Interrupt Disable Register (channel = 0) */
  #define REG_TC0_IMR0                   (0x4000C02CU) /**< \brief (TC0) Interrupt Mask Register (channel = 0) */
  #define REG_TC0_EMR0                   (0x4000C030U) /**< \brief (TC0) Extended Mode Register (channel = 0) */
  #define REG_TC0_CCR1                   (0x4000C040U) /**< \brief (TC0) Channel Control Register (channel = 1) */
  #define REG_TC0_CMR1                   (0x4000C044U) /**< \brief (TC0) Channel Mode Register (channel = 1) */
  #define REG_TC0_SMMR1                  (0x4000C048U) /**< \brief (TC0) Stepper Motor Mode Register (channel = 1) */
  #define REG_TC0_RAB1                   (0x4000C04CU) /**< \brief (TC0) Register AB (channel = 1) */
  #define REG_TC0_CV1                    (0x4000C050U) /**< \brief (TC0) Counter Value (channel = 1) */
  #define REG_TC0_RA1                    (0x4000C054U) /**< \brief (TC0) Register A (channel = 1) */
  #define REG_TC0_RB1                    (0x4000C058U) /**< \brief (TC0) Register B (channel = 1) */
  #define REG_TC0_RC1                    (0x4000C05CU) /**< \brief (TC0) Register C (channel = 1) */
  #define REG_TC0_SR1                    (0x4000C060U) /**< \brief (TC0) Status Register (channel = 1) */
  #define REG_TC0_IER1                   (0x4000C064U) /**< \brief (TC0) Interrupt Enable Register (channel = 1) */
  #define REG_TC0_IDR1                   (0x4000C068U) /**< \brief (TC0) Interrupt Disable Register (channel = 1) */
  #define REG_TC0_IMR1                   (0x4000C06CU) /**< \brief (TC0) Interrupt Mask Register (channel = 1) */
  #define REG_TC0_EMR1                   (0x4000C070U) /**< \brief (TC0) Extended Mode Register (channel = 1) */
  #define REG_TC0_CCR2                   (0x4000C080U) /**< \brief (TC0) Channel Control Register (channel = 2) */
  #define REG_TC0_CMR2                   (0x4000C084U) /**< \brief (TC0) Channel Mode Register (channel = 2) */
  #define REG_TC0_SMMR2                  (0x4000C088U) /**< \brief (TC0) Stepper Motor Mode Register (channel = 2) */
  #define REG_TC0_RAB2                   (0x4000C08CU) /**< \brief (TC0) Register AB (channel = 2) */
  #define REG_TC0_CV2                    (0x4000C090U) /**< \brief (TC0) Counter Value (channel = 2) */
  #define REG_TC0_RA2                    (0x4000C094U) /**< \brief (TC0) Register A (channel = 2) */
  #define REG_TC0_RB2                    (0x4000C098U) /**< \brief (TC0) Register B (channel = 2) */
  #define REG_TC0_RC2                    (0x4000C09CU) /**< \brief (TC0) Register C (channel = 2) */
  #define REG_TC0_SR2                    (0x4000C0A0U) /**< \brief (TC0) Status Register (channel = 2) */
  #define REG_TC0_IER2                   (0x4000C0A4U) /**< \brief (TC0) Interrupt Enable Register (channel = 2) */
  #define REG_TC0_IDR2                   (0x4000C0A8U) /**< \brief (TC0) Interrupt Disable Register (channel = 2) */
  #define REG_TC0_IMR2                   (0x4000C0ACU) /**< \brief (TC0) Interrupt Mask Register (channel = 2) */
  #define REG_TC0_EMR2                   (0x4000C0B0U) /**< \brief (TC0) Extended Mode Register (channel = 2) */
  #define REG_TC0_BCR                    (0x4000C0C0U) /**< \brief (TC0) Block Control Register */
  #define REG_TC0_BMR                    (0x4000C0C4U) /**< \brief (TC0) Block Mode Register */
  #define REG_TC0_QIER                   (0x4000C0C8U) /**< \brief (TC0) QDEC Interrupt Enable Register */
  #define REG_TC0_QIDR                   (0x4000C0CCU) /**< \brief (TC0) QDEC Interrupt Disable Register */
  #define REG_TC0_QIMR                   (0x4000C0D0U) /**< \brief (TC0) QDEC Interrupt Mask Register */
  #define REG_TC0_QISR                   (0x4000C0D4U) /**< \brief (TC0) QDEC Interrupt Status Register */
  #define REG_TC0_FMR                    (0x4000C0D8U) /**< \brief (TC0) Fault Mode Register */
  #define REG_TC0_WPMR                   (0x4000C0E4U) /**< \brief (TC0) Write Protection Mode Register */
#else
  #define REG_TC0_CCR0  (*(__O  uint32_t*)0x4000C000U) /**< \brief (TC0) Channel Control Register (channel = 0) */
  #define REG_TC0_CMR0  (*(__IO uint32_t*)0x4000C004U) /**< \brief (TC0) Channel Mode Register (channel = 0) */
  #define REG_TC0_SMMR0 (*(__IO uint32_t*)0x4000C008U) /**< \brief (TC0) Stepper Motor Mode Register (channel = 0) */
  #define REG_TC0_RAB0  (*(__I  uint32_t*)0x4000C00CU) /**< \brief (TC0) Register AB (channel = 0) */
  #define REG_TC0_CV0   (*(__I  uint32_t*)0x4000C010U) /**< \brief (TC0) Counter Value (channel = 0) */
  #define REG_TC0_RA0   (*(__IO uint32_t*)0x4000C014U) /**< \brief (TC0) Register A (channel = 0) */
  #define REG_TC0_RB0   (*(__IO uint32_t*)0x4000C018U) /**< \brief (TC0) Register B (channel = 0) */
  #define REG_TC0_RC0   (*(__IO uint32_t*)0x4000C01CU) /**< \brief (TC0) Register C (channel = 0) */
  #define REG_TC0_SR0   (*(__I  uint32_t*)0x4000C020U) /**< \brief (TC0) Status Register (channel = 0) */
  #define REG_TC0_IER0  (*(__O  uint32_t*)0x4000C024U) /**< \brief (TC0) Interrupt Enable Register (channel = 0) */
  #define REG_TC0_IDR0  (*(__O  uint32_t*)0x4000C028U) /**< \brief (TC0) Interrupt Disable Register (channel = 0) */
  #define REG_TC0_IMR0  (*(__I  uint32_t*)0x4000C02CU) /**< \brief (TC0) Interrupt Mask Register (channel = 0) */
  #define REG_TC0_EMR0  (*(__IO uint32_t*)0x4000C030U) /**< \brief (TC0) Extended Mode Register (channel = 0) */
  #define REG_TC0_CCR1  (*(__O  uint32_t*)0x4000C040U) /**< \brief (TC0) Channel Control Register (channel = 1) */
  #define REG_TC0_CMR1  (*(__IO uint32_t*)0x4000C044U) /**< \brief (TC0) Channel Mode Register (channel = 1) */
  #define REG_TC0_SMMR1 (*(__IO uint32_t*)0x4000C048U) /**< \brief (TC0) Stepper Motor Mode Register (channel = 1) */
  #define REG_TC0_RAB1  (*(__I  uint32_t*)0x4000C04CU) /**< \brief (TC0) Register AB (channel = 1) */
  #define REG_TC0_CV1   (*(__I  uint32_t*)0x4000C050U) /**< \brief (TC0) Counter Value (channel = 1) */
  #define REG_TC0_RA1   (*(__IO uint32_t*)0x4000C054U) /**< \brief (TC0) Register A (channel = 1) */
  #define REG_TC0_RB1   (*(__IO uint32_t*)0x4000C058U) /**< \brief (TC0) Register B (channel = 1) */
  #define REG_TC0_RC1   (*(__IO uint32_t*)0x4000C05CU) /**< \brief (TC0) Register C (channel = 1) */
  #define REG_TC0_SR1   (*(__I  uint32_t*)0x4000C060U) /**< \brief (TC0) Status Register (channel = 1) */
  #define REG_TC0_IER1  (*(__O  uint32_t*)0x4000C064U) /**< \brief (TC0) Interrupt Enable Register (channel = 1) */
  #define REG_TC0_IDR1  (*(__O  uint32_t*)0x4000C068U) /**< \brief (TC0) Interrupt Disable Register (channel = 1) */
  #define REG_TC0_IMR1  (*(__I  uint32_t*)0x4000C06CU) /**< \brief (TC0) Interrupt Mask Register (channel = 1) */
  #define REG_TC0_EMR1  (*(__IO uint32_t*)0x4000C070U) /**< \brief (TC0) Extended Mode Register (channel = 1) */
  #define REG_TC0_CCR2  (*(__O  uint32_t*)0x4000C080U) /**< \brief (TC0) Channel Control Register (channel = 2) */
  #define REG_TC0_CMR2  (*(__IO uint32_t*)0x4000C084U) /**< \brief (TC0) Channel Mode Register (channel = 2) */
  #define REG_TC0_SMMR2 (*(__IO uint32_t*)0x4000C088U) /**< \brief (TC0) Stepper Motor Mode Register (channel = 2) */
  #define REG_TC0_RAB2  (*(__I  uint32_t*)0x4000C08CU) /**< \brief (TC0) Register AB (channel = 2) */
  #define REG_TC0_CV2   (*(__I  uint32_t*)0x4000C090U) /**< \brief (TC0) Counter Value (channel = 2) */
  #define REG_TC0_RA2   (*(__IO uint32_t*)0x4000C094U) /**< \brief (TC0) Register A (channel = 2) */
  #define REG_TC0_RB2   (*(__IO uint32_t*)0x4000C098U) /**< \brief (TC0) Register B (channel = 2) */
  #define REG_TC0_RC2   (*(__IO uint32_t*)0x4000C09CU) /**< \brief (TC0) Register C (channel = 2) */
  #define REG_TC0_SR2   (*(__I  uint32_t*)0x4000C0A0U) /**< \brief (TC0) Status Register (channel = 2) */
  #define REG_TC0_IER2  (*(__O  uint32_t*)0x4000C0A4U) /**< \brief (TC0) Interrupt Enable Register (channel = 2) */
  #define REG_TC0_IDR2  (*(__O  uint32_t*)0x4000C0A8U) /**< \brief (TC0) Interrupt Disable Register (channel = 2) */
  #define REG_TC0_IMR2  (*(__I  uint32_t*)0x4000C0ACU) /**< \brief (TC0) Interrupt Mask Register (channel = 2) */
  #define REG_TC0_EMR2  (*(__IO uint32_t*)0x4000C0B0U) /**< \brief (TC0) Extended Mode Register (channel = 2) */
  #define REG_TC0_BCR   (*(__O  uint32_t*)0x4000C0C0U) /**< \brief (TC0) Block Control Register */
  #define REG_TC0_BMR   (*(__IO uint32_t*)0x4000C0C4U) /**< \brief (TC0) Block Mode Register */
  #define REG_TC0_QIER  (*(__O  uint32_t*)0x4000C0C8U) /**< \brief (TC0) QDEC Interrupt Enable Register */
  #define REG_TC0_QIDR  (*(__O  uint32_t*)0x4000C0CCU) /**< \brief (TC0) QDEC Interrupt Disable Register */
  #define REG_TC0_QIMR  (*(__I  uint32_t*)0x4000C0D0U) /**< \brief (TC0) QDEC Interrupt Mask Register */
  #define REG_TC0_QISR  (*(__I  uint32_t*)0x4000C0D4U) /**< \brief (TC0) QDEC Interrupt Status Register */
  #define REG_TC0_FMR   (*(__IO uint32_t*)0x4000C0D8U) /**< \brief (TC0) Fault Mode Register */
  #define REG_TC0_WPMR  (*(__IO uint32_t*)0x4000C0E4U) /**< \brief (TC0) Write Protection Mode Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMV71_TC0_INSTANCE_ */
