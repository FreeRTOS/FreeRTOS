/**
 * \file
 *
 * Copyright (c) 2015 Atmel Corporation. All rights reserved.
 *
 * \asf_license_start
 *
 * \page License
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 *
 * 3. The name of Atmel may not be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * 4. This software may only be redistributed and used in connection with an
 *    Atmel microcontroller product.
 *
 * THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * EXPRESSLY AND SPECIFICALLY DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
 * ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *
 * \asf_license_stop
 *
 */
/*
 * Support and FAQ: visit <a href="http://www.atmel.com/design-support/">Atmel Support</a>
 */

#ifndef _SAME70_PMC_INSTANCE_
#define _SAME70_PMC_INSTANCE_

/* ========== Register definition for PMC peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
  #define REG_PMC_SCER                        (0x400E0600U) /**< \brief (PMC) System Clock Enable Register */
  #define REG_PMC_SCDR                        (0x400E0604U) /**< \brief (PMC) System Clock Disable Register */
  #define REG_PMC_SCSR                        (0x400E0608U) /**< \brief (PMC) System Clock Status Register */
  #define REG_PMC_PCER0                       (0x400E0610U) /**< \brief (PMC) Peripheral Clock Enable Register 0 */
  #define REG_PMC_PCDR0                       (0x400E0614U) /**< \brief (PMC) Peripheral Clock Disable Register 0 */
  #define REG_PMC_PCSR0                       (0x400E0618U) /**< \brief (PMC) Peripheral Clock Status Register 0 */
  #define REG_CKGR_UCKR                       (0x400E061CU) /**< \brief (PMC) UTMI Clock Register */
  #define REG_CKGR_MOR                        (0x400E0620U) /**< \brief (PMC) Main Oscillator Register */
  #define REG_CKGR_MCFR                       (0x400E0624U) /**< \brief (PMC) Main Clock Frequency Register */
  #define REG_CKGR_PLLAR                      (0x400E0628U) /**< \brief (PMC) PLLA Register */
  #define REG_PMC_MCKR                        (0x400E0630U) /**< \brief (PMC) Master Clock Register */
  #define REG_PMC_USB                         (0x400E0638U) /**< \brief (PMC) USB Clock Register */
  #define REG_PMC_PCK                         (0x400E0640U) /**< \brief (PMC) Programmable Clock 0 Register */
  #define REG_PMC_IER                         (0x400E0660U) /**< \brief (PMC) Interrupt Enable Register */
  #define REG_PMC_IDR                         (0x400E0664U) /**< \brief (PMC) Interrupt Disable Register */
  #define REG_PMC_SR                          (0x400E0668U) /**< \brief (PMC) Status Register */
  #define REG_PMC_IMR                         (0x400E066CU) /**< \brief (PMC) Interrupt Mask Register */
  #define REG_PMC_FSMR                        (0x400E0670U) /**< \brief (PMC) Fast Startup Mode Register */
  #define REG_PMC_FSPR                        (0x400E0674U) /**< \brief (PMC) Fast Startup Polarity Register */
  #define REG_PMC_FOCR                        (0x400E0678U) /**< \brief (PMC) Fault Output Clear Register */
  #define REG_PMC_WPMR                        (0x400E06E4U) /**< \brief (PMC) Write Protection Mode Register */
  #define REG_PMC_WPSR                        (0x400E06E8U) /**< \brief (PMC) Write Protection Status Register */
  #define REG_PMC_PCER1                       (0x400E0700U) /**< \brief (PMC) Peripheral Clock Enable Register 1 */
  #define REG_PMC_PCDR1                       (0x400E0704U) /**< \brief (PMC) Peripheral Clock Disable Register 1 */
  #define REG_PMC_PCSR1                       (0x400E0708U) /**< \brief (PMC) Peripheral Clock Status Register 1 */
  #define REG_PMC_PCR                         (0x400E070CU) /**< \brief (PMC) Peripheral Control Register */
  #define REG_PMC_OCR                         (0x400E0710U) /**< \brief (PMC) Oscillator Calibration Register */
  #define REG_PMC_SLPWK_ER0                   (0x400E0714U) /**< \brief (PMC) SleepWalking Enable Register 0 */
  #define REG_PMC_SLPWK_DR0                   (0x400E0718U) /**< \brief (PMC) SleepWalking Disable Register 0 */
  #define REG_PMC_SLPWK_SR0                   (0x400E071CU) /**< \brief (PMC) SleepWalking Status Register 0 */
  #define REG_PMC_SLPWK_ASR0                  (0x400E0720U) /**< \brief (PMC) SleepWalking Activity Status Register 0 */
  #define REG_PMC_SLPWK_ER1                   (0x400E0734U) /**< \brief (PMC) SleepWalking Enable Register 1 */
  #define REG_PMC_SLPWK_DR1                   (0x400E0738U) /**< \brief (PMC) SleepWalking Disable Register 1 */
  #define REG_PMC_SLPWK_SR1                   (0x400E073CU) /**< \brief (PMC) SleepWalking Status Register 1 */
  #define REG_PMC_SLPWK_ASR1                  (0x400E0740U) /**< \brief (PMC) SleepWalking Activity Status Register 1 */
  #define REG_PMC_SLPWK_AIPR                  (0x400E0744U) /**< \brief (PMC) SleepWalking Activity In Progress Register */
#else
  #define REG_PMC_SCER       (*(__O  uint32_t*)0x400E0600U) /**< \brief (PMC) System Clock Enable Register */
  #define REG_PMC_SCDR       (*(__O  uint32_t*)0x400E0604U) /**< \brief (PMC) System Clock Disable Register */
  #define REG_PMC_SCSR       (*(__I  uint32_t*)0x400E0608U) /**< \brief (PMC) System Clock Status Register */
  #define REG_PMC_PCER0      (*(__O  uint32_t*)0x400E0610U) /**< \brief (PMC) Peripheral Clock Enable Register 0 */
  #define REG_PMC_PCDR0      (*(__O  uint32_t*)0x400E0614U) /**< \brief (PMC) Peripheral Clock Disable Register 0 */
  #define REG_PMC_PCSR0      (*(__I  uint32_t*)0x400E0618U) /**< \brief (PMC) Peripheral Clock Status Register 0 */
  #define REG_CKGR_UCKR      (*(__IO uint32_t*)0x400E061CU) /**< \brief (PMC) UTMI Clock Register */
  #define REG_CKGR_MOR       (*(__IO uint32_t*)0x400E0620U) /**< \brief (PMC) Main Oscillator Register */
  #define REG_CKGR_MCFR      (*(__IO uint32_t*)0x400E0624U) /**< \brief (PMC) Main Clock Frequency Register */
  #define REG_CKGR_PLLAR     (*(__IO uint32_t*)0x400E0628U) /**< \brief (PMC) PLLA Register */
  #define REG_PMC_MCKR       (*(__IO uint32_t*)0x400E0630U) /**< \brief (PMC) Master Clock Register */
  #define REG_PMC_USB        (*(__IO uint32_t*)0x400E0638U) /**< \brief (PMC) USB Clock Register */
  #define REG_PMC_PCK        (*(__IO uint32_t*)0x400E0640U) /**< \brief (PMC) Programmable Clock 0 Register */
  #define REG_PMC_IER        (*(__O  uint32_t*)0x400E0660U) /**< \brief (PMC) Interrupt Enable Register */
  #define REG_PMC_IDR        (*(__O  uint32_t*)0x400E0664U) /**< \brief (PMC) Interrupt Disable Register */
  #define REG_PMC_SR         (*(__I  uint32_t*)0x400E0668U) /**< \brief (PMC) Status Register */
  #define REG_PMC_IMR        (*(__I  uint32_t*)0x400E066CU) /**< \brief (PMC) Interrupt Mask Register */
  #define REG_PMC_FSMR       (*(__IO uint32_t*)0x400E0670U) /**< \brief (PMC) Fast Startup Mode Register */
  #define REG_PMC_FSPR       (*(__IO uint32_t*)0x400E0674U) /**< \brief (PMC) Fast Startup Polarity Register */
  #define REG_PMC_FOCR       (*(__O  uint32_t*)0x400E0678U) /**< \brief (PMC) Fault Output Clear Register */
  #define REG_PMC_WPMR       (*(__IO uint32_t*)0x400E06E4U) /**< \brief (PMC) Write Protection Mode Register */
  #define REG_PMC_WPSR       (*(__I  uint32_t*)0x400E06E8U) /**< \brief (PMC) Write Protection Status Register */
  #define REG_PMC_PCER1      (*(__O  uint32_t*)0x400E0700U) /**< \brief (PMC) Peripheral Clock Enable Register 1 */
  #define REG_PMC_PCDR1      (*(__O  uint32_t*)0x400E0704U) /**< \brief (PMC) Peripheral Clock Disable Register 1 */
  #define REG_PMC_PCSR1      (*(__I  uint32_t*)0x400E0708U) /**< \brief (PMC) Peripheral Clock Status Register 1 */
  #define REG_PMC_PCR        (*(__IO uint32_t*)0x400E070CU) /**< \brief (PMC) Peripheral Control Register */
  #define REG_PMC_OCR        (*(__IO uint32_t*)0x400E0710U) /**< \brief (PMC) Oscillator Calibration Register */
  #define REG_PMC_SLPWK_ER0  (*(__O  uint32_t*)0x400E0714U) /**< \brief (PMC) SleepWalking Enable Register 0 */
  #define REG_PMC_SLPWK_DR0  (*(__O  uint32_t*)0x400E0718U) /**< \brief (PMC) SleepWalking Disable Register 0 */
  #define REG_PMC_SLPWK_SR0  (*(__I  uint32_t*)0x400E071CU) /**< \brief (PMC) SleepWalking Status Register 0 */
  #define REG_PMC_SLPWK_ASR0 (*(__I  uint32_t*)0x400E0720U) /**< \brief (PMC) SleepWalking Activity Status Register 0 */
  #define REG_PMC_SLPWK_ER1  (*(__O  uint32_t*)0x400E0734U) /**< \brief (PMC) SleepWalking Enable Register 1 */
  #define REG_PMC_SLPWK_DR1  (*(__O  uint32_t*)0x400E0738U) /**< \brief (PMC) SleepWalking Disable Register 1 */
  #define REG_PMC_SLPWK_SR1  (*(__I  uint32_t*)0x400E073CU) /**< \brief (PMC) SleepWalking Status Register 1 */
  #define REG_PMC_SLPWK_ASR1 (*(__I  uint32_t*)0x400E0740U) /**< \brief (PMC) SleepWalking Activity Status Register 1 */
  #define REG_PMC_SLPWK_AIPR (*(__I  uint32_t*)0x400E0744U) /**< \brief (PMC) SleepWalking Activity In Progress Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAME70_PMC_INSTANCE_ */
