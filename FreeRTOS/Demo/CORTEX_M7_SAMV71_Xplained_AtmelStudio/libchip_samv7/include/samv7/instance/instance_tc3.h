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

#ifndef _SAMV71_TC3_INSTANCE_
#define _SAMV71_TC3_INSTANCE_

/* ========== Register definition for TC3 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
  #define REG_TC3_CCR0                   (0x40054000U) /**< \brief (TC3) Channel Control Register (channel = 0) */
  #define REG_TC3_CMR0                   (0x40054004U) /**< \brief (TC3) Channel Mode Register (channel = 0) */
  #define REG_TC3_SMMR0                  (0x40054008U) /**< \brief (TC3) Stepper Motor Mode Register (channel = 0) */
  #define REG_TC3_RAB0                   (0x4005400CU) /**< \brief (TC3) Register AB (channel = 0) */
  #define REG_TC3_CV0                    (0x40054010U) /**< \brief (TC3) Counter Value (channel = 0) */
  #define REG_TC3_RA0                    (0x40054014U) /**< \brief (TC3) Register A (channel = 0) */
  #define REG_TC3_RB0                    (0x40054018U) /**< \brief (TC3) Register B (channel = 0) */
  #define REG_TC3_RC0                    (0x4005401CU) /**< \brief (TC3) Register C (channel = 0) */
  #define REG_TC3_SR0                    (0x40054020U) /**< \brief (TC3) Status Register (channel = 0) */
  #define REG_TC3_IER0                   (0x40054024U) /**< \brief (TC3) Interrupt Enable Register (channel = 0) */
  #define REG_TC3_IDR0                   (0x40054028U) /**< \brief (TC3) Interrupt Disable Register (channel = 0) */
  #define REG_TC3_IMR0                   (0x4005402CU) /**< \brief (TC3) Interrupt Mask Register (channel = 0) */
  #define REG_TC3_EMR0                   (0x40054030U) /**< \brief (TC3) Extended Mode Register (channel = 0) */
  #define REG_TC3_CCR1                   (0x40054040U) /**< \brief (TC3) Channel Control Register (channel = 1) */
  #define REG_TC3_CMR1                   (0x40054044U) /**< \brief (TC3) Channel Mode Register (channel = 1) */
  #define REG_TC3_SMMR1                  (0x40054048U) /**< \brief (TC3) Stepper Motor Mode Register (channel = 1) */
  #define REG_TC3_RAB1                   (0x4005404CU) /**< \brief (TC3) Register AB (channel = 1) */
  #define REG_TC3_CV1                    (0x40054050U) /**< \brief (TC3) Counter Value (channel = 1) */
  #define REG_TC3_RA1                    (0x40054054U) /**< \brief (TC3) Register A (channel = 1) */
  #define REG_TC3_RB1                    (0x40054058U) /**< \brief (TC3) Register B (channel = 1) */
  #define REG_TC3_RC1                    (0x4005405CU) /**< \brief (TC3) Register C (channel = 1) */
  #define REG_TC3_SR1                    (0x40054060U) /**< \brief (TC3) Status Register (channel = 1) */
  #define REG_TC3_IER1                   (0x40054064U) /**< \brief (TC3) Interrupt Enable Register (channel = 1) */
  #define REG_TC3_IDR1                   (0x40054068U) /**< \brief (TC3) Interrupt Disable Register (channel = 1) */
  #define REG_TC3_IMR1                   (0x4005406CU) /**< \brief (TC3) Interrupt Mask Register (channel = 1) */
  #define REG_TC3_EMR1                   (0x40054070U) /**< \brief (TC3) Extended Mode Register (channel = 1) */
  #define REG_TC3_CCR2                   (0x40054080U) /**< \brief (TC3) Channel Control Register (channel = 2) */
  #define REG_TC3_CMR2                   (0x40054084U) /**< \brief (TC3) Channel Mode Register (channel = 2) */
  #define REG_TC3_SMMR2                  (0x40054088U) /**< \brief (TC3) Stepper Motor Mode Register (channel = 2) */
  #define REG_TC3_RAB2                   (0x4005408CU) /**< \brief (TC3) Register AB (channel = 2) */
  #define REG_TC3_CV2                    (0x40054090U) /**< \brief (TC3) Counter Value (channel = 2) */
  #define REG_TC3_RA2                    (0x40054094U) /**< \brief (TC3) Register A (channel = 2) */
  #define REG_TC3_RB2                    (0x40054098U) /**< \brief (TC3) Register B (channel = 2) */
  #define REG_TC3_RC2                    (0x4005409CU) /**< \brief (TC3) Register C (channel = 2) */
  #define REG_TC3_SR2                    (0x400540A0U) /**< \brief (TC3) Status Register (channel = 2) */
  #define REG_TC3_IER2                   (0x400540A4U) /**< \brief (TC3) Interrupt Enable Register (channel = 2) */
  #define REG_TC3_IDR2                   (0x400540A8U) /**< \brief (TC3) Interrupt Disable Register (channel = 2) */
  #define REG_TC3_IMR2                   (0x400540ACU) /**< \brief (TC3) Interrupt Mask Register (channel = 2) */
  #define REG_TC3_EMR2                   (0x400540B0U) /**< \brief (TC3) Extended Mode Register (channel = 2) */
  #define REG_TC3_BCR                    (0x400540C0U) /**< \brief (TC3) Block Control Register */
  #define REG_TC3_BMR                    (0x400540C4U) /**< \brief (TC3) Block Mode Register */
  #define REG_TC3_QIER                   (0x400540C8U) /**< \brief (TC3) QDEC Interrupt Enable Register */
  #define REG_TC3_QIDR                   (0x400540CCU) /**< \brief (TC3) QDEC Interrupt Disable Register */
  #define REG_TC3_QIMR                   (0x400540D0U) /**< \brief (TC3) QDEC Interrupt Mask Register */
  #define REG_TC3_QISR                   (0x400540D4U) /**< \brief (TC3) QDEC Interrupt Status Register */
  #define REG_TC3_FMR                    (0x400540D8U) /**< \brief (TC3) Fault Mode Register */
  #define REG_TC3_WPMR                   (0x400540E4U) /**< \brief (TC3) Write Protection Mode Register */
#else
  #define REG_TC3_CCR0  (*(__O  uint32_t*)0x40054000U) /**< \brief (TC3) Channel Control Register (channel = 0) */
  #define REG_TC3_CMR0  (*(__IO uint32_t*)0x40054004U) /**< \brief (TC3) Channel Mode Register (channel = 0) */
  #define REG_TC3_SMMR0 (*(__IO uint32_t*)0x40054008U) /**< \brief (TC3) Stepper Motor Mode Register (channel = 0) */
  #define REG_TC3_RAB0  (*(__I  uint32_t*)0x4005400CU) /**< \brief (TC3) Register AB (channel = 0) */
  #define REG_TC3_CV0   (*(__I  uint32_t*)0x40054010U) /**< \brief (TC3) Counter Value (channel = 0) */
  #define REG_TC3_RA0   (*(__IO uint32_t*)0x40054014U) /**< \brief (TC3) Register A (channel = 0) */
  #define REG_TC3_RB0   (*(__IO uint32_t*)0x40054018U) /**< \brief (TC3) Register B (channel = 0) */
  #define REG_TC3_RC0   (*(__IO uint32_t*)0x4005401CU) /**< \brief (TC3) Register C (channel = 0) */
  #define REG_TC3_SR0   (*(__I  uint32_t*)0x40054020U) /**< \brief (TC3) Status Register (channel = 0) */
  #define REG_TC3_IER0  (*(__O  uint32_t*)0x40054024U) /**< \brief (TC3) Interrupt Enable Register (channel = 0) */
  #define REG_TC3_IDR0  (*(__O  uint32_t*)0x40054028U) /**< \brief (TC3) Interrupt Disable Register (channel = 0) */
  #define REG_TC3_IMR0  (*(__I  uint32_t*)0x4005402CU) /**< \brief (TC3) Interrupt Mask Register (channel = 0) */
  #define REG_TC3_EMR0  (*(__IO uint32_t*)0x40054030U) /**< \brief (TC3) Extended Mode Register (channel = 0) */
  #define REG_TC3_CCR1  (*(__O  uint32_t*)0x40054040U) /**< \brief (TC3) Channel Control Register (channel = 1) */
  #define REG_TC3_CMR1  (*(__IO uint32_t*)0x40054044U) /**< \brief (TC3) Channel Mode Register (channel = 1) */
  #define REG_TC3_SMMR1 (*(__IO uint32_t*)0x40054048U) /**< \brief (TC3) Stepper Motor Mode Register (channel = 1) */
  #define REG_TC3_RAB1  (*(__I  uint32_t*)0x4005404CU) /**< \brief (TC3) Register AB (channel = 1) */
  #define REG_TC3_CV1   (*(__I  uint32_t*)0x40054050U) /**< \brief (TC3) Counter Value (channel = 1) */
  #define REG_TC3_RA1   (*(__IO uint32_t*)0x40054054U) /**< \brief (TC3) Register A (channel = 1) */
  #define REG_TC3_RB1   (*(__IO uint32_t*)0x40054058U) /**< \brief (TC3) Register B (channel = 1) */
  #define REG_TC3_RC1   (*(__IO uint32_t*)0x4005405CU) /**< \brief (TC3) Register C (channel = 1) */
  #define REG_TC3_SR1   (*(__I  uint32_t*)0x40054060U) /**< \brief (TC3) Status Register (channel = 1) */
  #define REG_TC3_IER1  (*(__O  uint32_t*)0x40054064U) /**< \brief (TC3) Interrupt Enable Register (channel = 1) */
  #define REG_TC3_IDR1  (*(__O  uint32_t*)0x40054068U) /**< \brief (TC3) Interrupt Disable Register (channel = 1) */
  #define REG_TC3_IMR1  (*(__I  uint32_t*)0x4005406CU) /**< \brief (TC3) Interrupt Mask Register (channel = 1) */
  #define REG_TC3_EMR1  (*(__IO uint32_t*)0x40054070U) /**< \brief (TC3) Extended Mode Register (channel = 1) */
  #define REG_TC3_CCR2  (*(__O  uint32_t*)0x40054080U) /**< \brief (TC3) Channel Control Register (channel = 2) */
  #define REG_TC3_CMR2  (*(__IO uint32_t*)0x40054084U) /**< \brief (TC3) Channel Mode Register (channel = 2) */
  #define REG_TC3_SMMR2 (*(__IO uint32_t*)0x40054088U) /**< \brief (TC3) Stepper Motor Mode Register (channel = 2) */
  #define REG_TC3_RAB2  (*(__I  uint32_t*)0x4005408CU) /**< \brief (TC3) Register AB (channel = 2) */
  #define REG_TC3_CV2   (*(__I  uint32_t*)0x40054090U) /**< \brief (TC3) Counter Value (channel = 2) */
  #define REG_TC3_RA2   (*(__IO uint32_t*)0x40054094U) /**< \brief (TC3) Register A (channel = 2) */
  #define REG_TC3_RB2   (*(__IO uint32_t*)0x40054098U) /**< \brief (TC3) Register B (channel = 2) */
  #define REG_TC3_RC2   (*(__IO uint32_t*)0x4005409CU) /**< \brief (TC3) Register C (channel = 2) */
  #define REG_TC3_SR2   (*(__I  uint32_t*)0x400540A0U) /**< \brief (TC3) Status Register (channel = 2) */
  #define REG_TC3_IER2  (*(__O  uint32_t*)0x400540A4U) /**< \brief (TC3) Interrupt Enable Register (channel = 2) */
  #define REG_TC3_IDR2  (*(__O  uint32_t*)0x400540A8U) /**< \brief (TC3) Interrupt Disable Register (channel = 2) */
  #define REG_TC3_IMR2  (*(__I  uint32_t*)0x400540ACU) /**< \brief (TC3) Interrupt Mask Register (channel = 2) */
  #define REG_TC3_EMR2  (*(__IO uint32_t*)0x400540B0U) /**< \brief (TC3) Extended Mode Register (channel = 2) */
  #define REG_TC3_BCR   (*(__O  uint32_t*)0x400540C0U) /**< \brief (TC3) Block Control Register */
  #define REG_TC3_BMR   (*(__IO uint32_t*)0x400540C4U) /**< \brief (TC3) Block Mode Register */
  #define REG_TC3_QIER  (*(__O  uint32_t*)0x400540C8U) /**< \brief (TC3) QDEC Interrupt Enable Register */
  #define REG_TC3_QIDR  (*(__O  uint32_t*)0x400540CCU) /**< \brief (TC3) QDEC Interrupt Disable Register */
  #define REG_TC3_QIMR  (*(__I  uint32_t*)0x400540D0U) /**< \brief (TC3) QDEC Interrupt Mask Register */
  #define REG_TC3_QISR  (*(__I  uint32_t*)0x400540D4U) /**< \brief (TC3) QDEC Interrupt Status Register */
  #define REG_TC3_FMR   (*(__IO uint32_t*)0x400540D8U) /**< \brief (TC3) Fault Mode Register */
  #define REG_TC3_WPMR  (*(__IO uint32_t*)0x400540E4U) /**< \brief (TC3) Write Protection Mode Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMV71_TC3_INSTANCE_ */
