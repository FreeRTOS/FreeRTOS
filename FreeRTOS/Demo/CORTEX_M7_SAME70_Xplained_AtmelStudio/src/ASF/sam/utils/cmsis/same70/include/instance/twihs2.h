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

#ifndef _SAME70_TWIHS2_INSTANCE_
#define _SAME70_TWIHS2_INSTANCE_

/* ========== Register definition for TWIHS2 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
  #define REG_TWIHS2_CR                     (0x40060000U) /**< \brief (TWIHS2) Control Register */
  #define REG_TWIHS2_MMR                    (0x40060004U) /**< \brief (TWIHS2) Master Mode Register */
  #define REG_TWIHS2_SMR                    (0x40060008U) /**< \brief (TWIHS2) Slave Mode Register */
  #define REG_TWIHS2_IADR                   (0x4006000CU) /**< \brief (TWIHS2) Internal Address Register */
  #define REG_TWIHS2_CWGR                   (0x40060010U) /**< \brief (TWIHS2) Clock Waveform Generator Register */
  #define REG_TWIHS2_SR                     (0x40060020U) /**< \brief (TWIHS2) Status Register */
  #define REG_TWIHS2_IER                    (0x40060024U) /**< \brief (TWIHS2) Interrupt Enable Register */
  #define REG_TWIHS2_IDR                    (0x40060028U) /**< \brief (TWIHS2) Interrupt Disable Register */
  #define REG_TWIHS2_IMR                    (0x4006002CU) /**< \brief (TWIHS2) Interrupt Mask Register */
  #define REG_TWIHS2_RHR                    (0x40060030U) /**< \brief (TWIHS2) Receive Holding Register */
  #define REG_TWIHS2_THR                    (0x40060034U) /**< \brief (TWIHS2) Transmit Holding Register */
  #define REG_TWIHS2_SMBTR                  (0x40060038U) /**< \brief (TWIHS2) SMBus Timing Register */
  #define REG_TWIHS2_FILTR                  (0x40060044U) /**< \brief (TWIHS2) Filter Register */
  #define REG_TWIHS2_SWMR                   (0x4006004CU) /**< \brief (TWIHS2) SleepWalking Matching Register */
  #define REG_TWIHS2_WPMR                   (0x400600E4U) /**< \brief (TWIHS2) Write Protection Mode Register */
  #define REG_TWIHS2_WPSR                   (0x400600E8U) /**< \brief (TWIHS2) Write Protection Status Register */
#else
  #define REG_TWIHS2_CR    (*(__O  uint32_t*)0x40060000U) /**< \brief (TWIHS2) Control Register */
  #define REG_TWIHS2_MMR   (*(__IO uint32_t*)0x40060004U) /**< \brief (TWIHS2) Master Mode Register */
  #define REG_TWIHS2_SMR   (*(__IO uint32_t*)0x40060008U) /**< \brief (TWIHS2) Slave Mode Register */
  #define REG_TWIHS2_IADR  (*(__IO uint32_t*)0x4006000CU) /**< \brief (TWIHS2) Internal Address Register */
  #define REG_TWIHS2_CWGR  (*(__IO uint32_t*)0x40060010U) /**< \brief (TWIHS2) Clock Waveform Generator Register */
  #define REG_TWIHS2_SR    (*(__I  uint32_t*)0x40060020U) /**< \brief (TWIHS2) Status Register */
  #define REG_TWIHS2_IER   (*(__O  uint32_t*)0x40060024U) /**< \brief (TWIHS2) Interrupt Enable Register */
  #define REG_TWIHS2_IDR   (*(__O  uint32_t*)0x40060028U) /**< \brief (TWIHS2) Interrupt Disable Register */
  #define REG_TWIHS2_IMR   (*(__I  uint32_t*)0x4006002CU) /**< \brief (TWIHS2) Interrupt Mask Register */
  #define REG_TWIHS2_RHR   (*(__I  uint32_t*)0x40060030U) /**< \brief (TWIHS2) Receive Holding Register */
  #define REG_TWIHS2_THR   (*(__O  uint32_t*)0x40060034U) /**< \brief (TWIHS2) Transmit Holding Register */
  #define REG_TWIHS2_SMBTR (*(__IO uint32_t*)0x40060038U) /**< \brief (TWIHS2) SMBus Timing Register */
  #define REG_TWIHS2_FILTR (*(__IO uint32_t*)0x40060044U) /**< \brief (TWIHS2) Filter Register */
  #define REG_TWIHS2_SWMR  (*(__IO uint32_t*)0x4006004CU) /**< \brief (TWIHS2) SleepWalking Matching Register */
  #define REG_TWIHS2_WPMR  (*(__IO uint32_t*)0x400600E4U) /**< \brief (TWIHS2) Write Protection Mode Register */
  #define REG_TWIHS2_WPSR  (*(__I  uint32_t*)0x400600E8U) /**< \brief (TWIHS2) Write Protection Status Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAME70_TWIHS2_INSTANCE_ */
