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

#ifndef _SAME70_TWIHS0_INSTANCE_
#define _SAME70_TWIHS0_INSTANCE_

/* ========== Register definition for TWIHS0 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
  #define REG_TWIHS0_CR                     (0x40018000U) /**< \brief (TWIHS0) Control Register */
  #define REG_TWIHS0_MMR                    (0x40018004U) /**< \brief (TWIHS0) Master Mode Register */
  #define REG_TWIHS0_SMR                    (0x40018008U) /**< \brief (TWIHS0) Slave Mode Register */
  #define REG_TWIHS0_IADR                   (0x4001800CU) /**< \brief (TWIHS0) Internal Address Register */
  #define REG_TWIHS0_CWGR                   (0x40018010U) /**< \brief (TWIHS0) Clock Waveform Generator Register */
  #define REG_TWIHS0_SR                     (0x40018020U) /**< \brief (TWIHS0) Status Register */
  #define REG_TWIHS0_IER                    (0x40018024U) /**< \brief (TWIHS0) Interrupt Enable Register */
  #define REG_TWIHS0_IDR                    (0x40018028U) /**< \brief (TWIHS0) Interrupt Disable Register */
  #define REG_TWIHS0_IMR                    (0x4001802CU) /**< \brief (TWIHS0) Interrupt Mask Register */
  #define REG_TWIHS0_RHR                    (0x40018030U) /**< \brief (TWIHS0) Receive Holding Register */
  #define REG_TWIHS0_THR                    (0x40018034U) /**< \brief (TWIHS0) Transmit Holding Register */
  #define REG_TWIHS0_SMBTR                  (0x40018038U) /**< \brief (TWIHS0) SMBus Timing Register */
  #define REG_TWIHS0_FILTR                  (0x40018044U) /**< \brief (TWIHS0) Filter Register */
  #define REG_TWIHS0_SWMR                   (0x4001804CU) /**< \brief (TWIHS0) SleepWalking Matching Register */
  #define REG_TWIHS0_WPMR                   (0x400180E4U) /**< \brief (TWIHS0) Write Protection Mode Register */
  #define REG_TWIHS0_WPSR                   (0x400180E8U) /**< \brief (TWIHS0) Write Protection Status Register */
#else
  #define REG_TWIHS0_CR    (*(__O  uint32_t*)0x40018000U) /**< \brief (TWIHS0) Control Register */
  #define REG_TWIHS0_MMR   (*(__IO uint32_t*)0x40018004U) /**< \brief (TWIHS0) Master Mode Register */
  #define REG_TWIHS0_SMR   (*(__IO uint32_t*)0x40018008U) /**< \brief (TWIHS0) Slave Mode Register */
  #define REG_TWIHS0_IADR  (*(__IO uint32_t*)0x4001800CU) /**< \brief (TWIHS0) Internal Address Register */
  #define REG_TWIHS0_CWGR  (*(__IO uint32_t*)0x40018010U) /**< \brief (TWIHS0) Clock Waveform Generator Register */
  #define REG_TWIHS0_SR    (*(__I  uint32_t*)0x40018020U) /**< \brief (TWIHS0) Status Register */
  #define REG_TWIHS0_IER   (*(__O  uint32_t*)0x40018024U) /**< \brief (TWIHS0) Interrupt Enable Register */
  #define REG_TWIHS0_IDR   (*(__O  uint32_t*)0x40018028U) /**< \brief (TWIHS0) Interrupt Disable Register */
  #define REG_TWIHS0_IMR   (*(__I  uint32_t*)0x4001802CU) /**< \brief (TWIHS0) Interrupt Mask Register */
  #define REG_TWIHS0_RHR   (*(__I  uint32_t*)0x40018030U) /**< \brief (TWIHS0) Receive Holding Register */
  #define REG_TWIHS0_THR   (*(__O  uint32_t*)0x40018034U) /**< \brief (TWIHS0) Transmit Holding Register */
  #define REG_TWIHS0_SMBTR (*(__IO uint32_t*)0x40018038U) /**< \brief (TWIHS0) SMBus Timing Register */
  #define REG_TWIHS0_FILTR (*(__IO uint32_t*)0x40018044U) /**< \brief (TWIHS0) Filter Register */
  #define REG_TWIHS0_SWMR  (*(__IO uint32_t*)0x4001804CU) /**< \brief (TWIHS0) SleepWalking Matching Register */
  #define REG_TWIHS0_WPMR  (*(__IO uint32_t*)0x400180E4U) /**< \brief (TWIHS0) Write Protection Mode Register */
  #define REG_TWIHS0_WPSR  (*(__I  uint32_t*)0x400180E8U) /**< \brief (TWIHS0) Write Protection Status Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAME70_TWIHS0_INSTANCE_ */
