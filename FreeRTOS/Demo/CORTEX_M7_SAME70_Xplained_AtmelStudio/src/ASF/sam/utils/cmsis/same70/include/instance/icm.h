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

#ifndef _SAME70_ICM_INSTANCE_
#define _SAME70_ICM_INSTANCE_

/* ========== Register definition for ICM peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
  #define REG_ICM_CFG                     (0x40048000U) /**< \brief (ICM) Configuration Register */
  #define REG_ICM_CTRL                    (0x40048004U) /**< \brief (ICM) Control Register */
  #define REG_ICM_SR                      (0x40048008U) /**< \brief (ICM) Status Register */
  #define REG_ICM_IER                     (0x40048010U) /**< \brief (ICM) Interrupt Enable Register */
  #define REG_ICM_IDR                     (0x40048014U) /**< \brief (ICM) Interrupt Disable Register */
  #define REG_ICM_IMR                     (0x40048018U) /**< \brief (ICM) Interrupt Mask Register */
  #define REG_ICM_ISR                     (0x4004801CU) /**< \brief (ICM) Interrupt Status Register */
  #define REG_ICM_UASR                    (0x40048020U) /**< \brief (ICM) Undefined Access Status Register */
  #define REG_ICM_DSCR                    (0x40048030U) /**< \brief (ICM) Region Descriptor Area Start Address Register */
  #define REG_ICM_HASH                    (0x40048034U) /**< \brief (ICM) Region Hash Area Start Address Register */
  #define REG_ICM_UIHVAL                  (0x40048038U) /**< \brief (ICM) User Initial Hash Value 0 Register */
#else
  #define REG_ICM_CFG    (*(__IO uint32_t*)0x40048000U) /**< \brief (ICM) Configuration Register */
  #define REG_ICM_CTRL   (*(__O  uint32_t*)0x40048004U) /**< \brief (ICM) Control Register */
  #define REG_ICM_SR     (*(__O  uint32_t*)0x40048008U) /**< \brief (ICM) Status Register */
  #define REG_ICM_IER    (*(__O  uint32_t*)0x40048010U) /**< \brief (ICM) Interrupt Enable Register */
  #define REG_ICM_IDR    (*(__O  uint32_t*)0x40048014U) /**< \brief (ICM) Interrupt Disable Register */
  #define REG_ICM_IMR    (*(__I  uint32_t*)0x40048018U) /**< \brief (ICM) Interrupt Mask Register */
  #define REG_ICM_ISR    (*(__I  uint32_t*)0x4004801CU) /**< \brief (ICM) Interrupt Status Register */
  #define REG_ICM_UASR   (*(__I  uint32_t*)0x40048020U) /**< \brief (ICM) Undefined Access Status Register */
  #define REG_ICM_DSCR   (*(__IO uint32_t*)0x40048030U) /**< \brief (ICM) Region Descriptor Area Start Address Register */
  #define REG_ICM_HASH   (*(__IO uint32_t*)0x40048034U) /**< \brief (ICM) Region Hash Area Start Address Register */
  #define REG_ICM_UIHVAL (*(__O  uint32_t*)0x40048038U) /**< \brief (ICM) User Initial Hash Value 0 Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAME70_ICM_INSTANCE_ */
