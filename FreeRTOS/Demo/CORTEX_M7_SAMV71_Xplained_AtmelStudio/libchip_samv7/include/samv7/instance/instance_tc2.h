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

#ifndef _SAMV71_TC2_INSTANCE_
#define _SAMV71_TC2_INSTANCE_

/* ========== Register definition for TC2 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
  #define REG_TC2_CCR0                   (0x40014000U) /**< \brief (TC2) Channel Control Register (channel = 0) */
  #define REG_TC2_CMR0                   (0x40014004U) /**< \brief (TC2) Channel Mode Register (channel = 0) */
  #define REG_TC2_SMMR0                  (0x40014008U) /**< \brief (TC2) Stepper Motor Mode Register (channel = 0) */
  #define REG_TC2_RAB0                   (0x4001400CU) /**< \brief (TC2) Register AB (channel = 0) */
  #define REG_TC2_CV0                    (0x40014010U) /**< \brief (TC2) Counter Value (channel = 0) */
  #define REG_TC2_RA0                    (0x40014014U) /**< \brief (TC2) Register A (channel = 0) */
  #define REG_TC2_RB0                    (0x40014018U) /**< \brief (TC2) Register B (channel = 0) */
  #define REG_TC2_RC0                    (0x4001401CU) /**< \brief (TC2) Register C (channel = 0) */
  #define REG_TC2_SR0                    (0x40014020U) /**< \brief (TC2) Status Register (channel = 0) */
  #define REG_TC2_IER0                   (0x40014024U) /**< \brief (TC2) Interrupt Enable Register (channel = 0) */
  #define REG_TC2_IDR0                   (0x40014028U) /**< \brief (TC2) Interrupt Disable Register (channel = 0) */
  #define REG_TC2_IMR0                   (0x4001402CU) /**< \brief (TC2) Interrupt Mask Register (channel = 0) */
  #define REG_TC2_EMR0                   (0x40014030U) /**< \brief (TC2) Extended Mode Register (channel = 0) */
  #define REG_TC2_CCR1                   (0x40014040U) /**< \brief (TC2) Channel Control Register (channel = 1) */
  #define REG_TC2_CMR1                   (0x40014044U) /**< \brief (TC2) Channel Mode Register (channel = 1) */
  #define REG_TC2_SMMR1                  (0x40014048U) /**< \brief (TC2) Stepper Motor Mode Register (channel = 1) */
  #define REG_TC2_RAB1                   (0x4001404CU) /**< \brief (TC2) Register AB (channel = 1) */
  #define REG_TC2_CV1                    (0x40014050U) /**< \brief (TC2) Counter Value (channel = 1) */
  #define REG_TC2_RA1                    (0x40014054U) /**< \brief (TC2) Register A (channel = 1) */
  #define REG_TC2_RB1                    (0x40014058U) /**< \brief (TC2) Register B (channel = 1) */
  #define REG_TC2_RC1                    (0x4001405CU) /**< \brief (TC2) Register C (channel = 1) */
  #define REG_TC2_SR1                    (0x40014060U) /**< \brief (TC2) Status Register (channel = 1) */
  #define REG_TC2_IER1                   (0x40014064U) /**< \brief (TC2) Interrupt Enable Register (channel = 1) */
  #define REG_TC2_IDR1                   (0x40014068U) /**< \brief (TC2) Interrupt Disable Register (channel = 1) */
  #define REG_TC2_IMR1                   (0x4001406CU) /**< \brief (TC2) Interrupt Mask Register (channel = 1) */
  #define REG_TC2_EMR1                   (0x40014070U) /**< \brief (TC2) Extended Mode Register (channel = 1) */
  #define REG_TC2_CCR2                   (0x40014080U) /**< \brief (TC2) Channel Control Register (channel = 2) */
  #define REG_TC2_CMR2                   (0x40014084U) /**< \brief (TC2) Channel Mode Register (channel = 2) */
  #define REG_TC2_SMMR2                  (0x40014088U) /**< \brief (TC2) Stepper Motor Mode Register (channel = 2) */
  #define REG_TC2_RAB2                   (0x4001408CU) /**< \brief (TC2) Register AB (channel = 2) */
  #define REG_TC2_CV2                    (0x40014090U) /**< \brief (TC2) Counter Value (channel = 2) */
  #define REG_TC2_RA2                    (0x40014094U) /**< \brief (TC2) Register A (channel = 2) */
  #define REG_TC2_RB2                    (0x40014098U) /**< \brief (TC2) Register B (channel = 2) */
  #define REG_TC2_RC2                    (0x4001409CU) /**< \brief (TC2) Register C (channel = 2) */
  #define REG_TC2_SR2                    (0x400140A0U) /**< \brief (TC2) Status Register (channel = 2) */
  #define REG_TC2_IER2                   (0x400140A4U) /**< \brief (TC2) Interrupt Enable Register (channel = 2) */
  #define REG_TC2_IDR2                   (0x400140A8U) /**< \brief (TC2) Interrupt Disable Register (channel = 2) */
  #define REG_TC2_IMR2                   (0x400140ACU) /**< \brief (TC2) Interrupt Mask Register (channel = 2) */
  #define REG_TC2_EMR2                   (0x400140B0U) /**< \brief (TC2) Extended Mode Register (channel = 2) */
  #define REG_TC2_BCR                    (0x400140C0U) /**< \brief (TC2) Block Control Register */
  #define REG_TC2_BMR                    (0x400140C4U) /**< \brief (TC2) Block Mode Register */
  #define REG_TC2_QIER                   (0x400140C8U) /**< \brief (TC2) QDEC Interrupt Enable Register */
  #define REG_TC2_QIDR                   (0x400140CCU) /**< \brief (TC2) QDEC Interrupt Disable Register */
  #define REG_TC2_QIMR                   (0x400140D0U) /**< \brief (TC2) QDEC Interrupt Mask Register */
  #define REG_TC2_QISR                   (0x400140D4U) /**< \brief (TC2) QDEC Interrupt Status Register */
  #define REG_TC2_FMR                    (0x400140D8U) /**< \brief (TC2) Fault Mode Register */
  #define REG_TC2_WPMR                   (0x400140E4U) /**< \brief (TC2) Write Protection Mode Register */
#else
  #define REG_TC2_CCR0  (*(__O  uint32_t*)0x40014000U) /**< \brief (TC2) Channel Control Register (channel = 0) */
  #define REG_TC2_CMR0  (*(__IO uint32_t*)0x40014004U) /**< \brief (TC2) Channel Mode Register (channel = 0) */
  #define REG_TC2_SMMR0 (*(__IO uint32_t*)0x40014008U) /**< \brief (TC2) Stepper Motor Mode Register (channel = 0) */
  #define REG_TC2_RAB0  (*(__I  uint32_t*)0x4001400CU) /**< \brief (TC2) Register AB (channel = 0) */
  #define REG_TC2_CV0   (*(__I  uint32_t*)0x40014010U) /**< \brief (TC2) Counter Value (channel = 0) */
  #define REG_TC2_RA0   (*(__IO uint32_t*)0x40014014U) /**< \brief (TC2) Register A (channel = 0) */
  #define REG_TC2_RB0   (*(__IO uint32_t*)0x40014018U) /**< \brief (TC2) Register B (channel = 0) */
  #define REG_TC2_RC0   (*(__IO uint32_t*)0x4001401CU) /**< \brief (TC2) Register C (channel = 0) */
  #define REG_TC2_SR0   (*(__I  uint32_t*)0x40014020U) /**< \brief (TC2) Status Register (channel = 0) */
  #define REG_TC2_IER0  (*(__O  uint32_t*)0x40014024U) /**< \brief (TC2) Interrupt Enable Register (channel = 0) */
  #define REG_TC2_IDR0  (*(__O  uint32_t*)0x40014028U) /**< \brief (TC2) Interrupt Disable Register (channel = 0) */
  #define REG_TC2_IMR0  (*(__I  uint32_t*)0x4001402CU) /**< \brief (TC2) Interrupt Mask Register (channel = 0) */
  #define REG_TC2_EMR0  (*(__IO uint32_t*)0x40014030U) /**< \brief (TC2) Extended Mode Register (channel = 0) */
  #define REG_TC2_CCR1  (*(__O  uint32_t*)0x40014040U) /**< \brief (TC2) Channel Control Register (channel = 1) */
  #define REG_TC2_CMR1  (*(__IO uint32_t*)0x40014044U) /**< \brief (TC2) Channel Mode Register (channel = 1) */
  #define REG_TC2_SMMR1 (*(__IO uint32_t*)0x40014048U) /**< \brief (TC2) Stepper Motor Mode Register (channel = 1) */
  #define REG_TC2_RAB1  (*(__I  uint32_t*)0x4001404CU) /**< \brief (TC2) Register AB (channel = 1) */
  #define REG_TC2_CV1   (*(__I  uint32_t*)0x40014050U) /**< \brief (TC2) Counter Value (channel = 1) */
  #define REG_TC2_RA1   (*(__IO uint32_t*)0x40014054U) /**< \brief (TC2) Register A (channel = 1) */
  #define REG_TC2_RB1   (*(__IO uint32_t*)0x40014058U) /**< \brief (TC2) Register B (channel = 1) */
  #define REG_TC2_RC1   (*(__IO uint32_t*)0x4001405CU) /**< \brief (TC2) Register C (channel = 1) */
  #define REG_TC2_SR1   (*(__I  uint32_t*)0x40014060U) /**< \brief (TC2) Status Register (channel = 1) */
  #define REG_TC2_IER1  (*(__O  uint32_t*)0x40014064U) /**< \brief (TC2) Interrupt Enable Register (channel = 1) */
  #define REG_TC2_IDR1  (*(__O  uint32_t*)0x40014068U) /**< \brief (TC2) Interrupt Disable Register (channel = 1) */
  #define REG_TC2_IMR1  (*(__I  uint32_t*)0x4001406CU) /**< \brief (TC2) Interrupt Mask Register (channel = 1) */
  #define REG_TC2_EMR1  (*(__IO uint32_t*)0x40014070U) /**< \brief (TC2) Extended Mode Register (channel = 1) */
  #define REG_TC2_CCR2  (*(__O  uint32_t*)0x40014080U) /**< \brief (TC2) Channel Control Register (channel = 2) */
  #define REG_TC2_CMR2  (*(__IO uint32_t*)0x40014084U) /**< \brief (TC2) Channel Mode Register (channel = 2) */
  #define REG_TC2_SMMR2 (*(__IO uint32_t*)0x40014088U) /**< \brief (TC2) Stepper Motor Mode Register (channel = 2) */
  #define REG_TC2_RAB2  (*(__I  uint32_t*)0x4001408CU) /**< \brief (TC2) Register AB (channel = 2) */
  #define REG_TC2_CV2   (*(__I  uint32_t*)0x40014090U) /**< \brief (TC2) Counter Value (channel = 2) */
  #define REG_TC2_RA2   (*(__IO uint32_t*)0x40014094U) /**< \brief (TC2) Register A (channel = 2) */
  #define REG_TC2_RB2   (*(__IO uint32_t*)0x40014098U) /**< \brief (TC2) Register B (channel = 2) */
  #define REG_TC2_RC2   (*(__IO uint32_t*)0x4001409CU) /**< \brief (TC2) Register C (channel = 2) */
  #define REG_TC2_SR2   (*(__I  uint32_t*)0x400140A0U) /**< \brief (TC2) Status Register (channel = 2) */
  #define REG_TC2_IER2  (*(__O  uint32_t*)0x400140A4U) /**< \brief (TC2) Interrupt Enable Register (channel = 2) */
  #define REG_TC2_IDR2  (*(__O  uint32_t*)0x400140A8U) /**< \brief (TC2) Interrupt Disable Register (channel = 2) */
  #define REG_TC2_IMR2  (*(__I  uint32_t*)0x400140ACU) /**< \brief (TC2) Interrupt Mask Register (channel = 2) */
  #define REG_TC2_EMR2  (*(__IO uint32_t*)0x400140B0U) /**< \brief (TC2) Extended Mode Register (channel = 2) */
  #define REG_TC2_BCR   (*(__O  uint32_t*)0x400140C0U) /**< \brief (TC2) Block Control Register */
  #define REG_TC2_BMR   (*(__IO uint32_t*)0x400140C4U) /**< \brief (TC2) Block Mode Register */
  #define REG_TC2_QIER  (*(__O  uint32_t*)0x400140C8U) /**< \brief (TC2) QDEC Interrupt Enable Register */
  #define REG_TC2_QIDR  (*(__O  uint32_t*)0x400140CCU) /**< \brief (TC2) QDEC Interrupt Disable Register */
  #define REG_TC2_QIMR  (*(__I  uint32_t*)0x400140D0U) /**< \brief (TC2) QDEC Interrupt Mask Register */
  #define REG_TC2_QISR  (*(__I  uint32_t*)0x400140D4U) /**< \brief (TC2) QDEC Interrupt Status Register */
  #define REG_TC2_FMR   (*(__IO uint32_t*)0x400140D8U) /**< \brief (TC2) Fault Mode Register */
  #define REG_TC2_WPMR  (*(__IO uint32_t*)0x400140E4U) /**< \brief (TC2) Write Protection Mode Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMV71_TC2_INSTANCE_ */
