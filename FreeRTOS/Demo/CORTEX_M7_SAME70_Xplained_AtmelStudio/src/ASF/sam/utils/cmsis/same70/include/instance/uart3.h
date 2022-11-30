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
#ifndef _SAME70_UART3_INSTANCE_
#define _SAME70_UART3_INSTANCE_

/* ========== Register definition for UART3 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
  #define REG_UART3_CR                    (0x400E1C00U) /**< \brief (UART3) Control Register */
  #define REG_UART3_MR                    (0x400E1C04U) /**< \brief (UART3) Mode Register */
  #define REG_UART3_IER                   (0x400E1C08U) /**< \brief (UART3) Interrupt Enable Register */
  #define REG_UART3_IDR                   (0x400E1C0CU) /**< \brief (UART3) Interrupt Disable Register */
  #define REG_UART3_IMR                   (0x400E1C10U) /**< \brief (UART3) Interrupt Mask Register */
  #define REG_UART3_SR                    (0x400E1C14U) /**< \brief (UART3) Status Register */
  #define REG_UART3_RHR                   (0x400E1C18U) /**< \brief (UART3) Receive Holding Register */
  #define REG_UART3_THR                   (0x400E1C1CU) /**< \brief (UART3) Transmit Holding Register */
  #define REG_UART3_BRGR                  (0x400E1C20U) /**< \brief (UART3) Baud Rate Generator Register */
  #define REG_UART3_CMPR                  (0x400E1C24U) /**< \brief (UART3) Comparison Register */
  #define REG_UART3_WPMR                  (0x400E1CE4U) /**< \brief (UART3) Write Protection Mode Register */
#else
  #define REG_UART3_CR   (*(__O  uint32_t*)0x400E1C00U) /**< \brief (UART3) Control Register */
  #define REG_UART3_MR   (*(__IO uint32_t*)0x400E1C04U) /**< \brief (UART3) Mode Register */
  #define REG_UART3_IER  (*(__O  uint32_t*)0x400E1C08U) /**< \brief (UART3) Interrupt Enable Register */
  #define REG_UART3_IDR  (*(__O  uint32_t*)0x400E1C0CU) /**< \brief (UART3) Interrupt Disable Register */
  #define REG_UART3_IMR  (*(__I  uint32_t*)0x400E1C10U) /**< \brief (UART3) Interrupt Mask Register */
  #define REG_UART3_SR   (*(__I  uint32_t*)0x400E1C14U) /**< \brief (UART3) Status Register */
  #define REG_UART3_RHR  (*(__I  uint32_t*)0x400E1C18U) /**< \brief (UART3) Receive Holding Register */
  #define REG_UART3_THR  (*(__O  uint32_t*)0x400E1C1CU) /**< \brief (UART3) Transmit Holding Register */
  #define REG_UART3_BRGR (*(__IO uint32_t*)0x400E1C20U) /**< \brief (UART3) Baud Rate Generator Register */
  #define REG_UART3_CMPR (*(__IO uint32_t*)0x400E1C24U) /**< \brief (UART3) Comparison Register */
  #define REG_UART3_WPMR (*(__IO uint32_t*)0x400E1CE4U) /**< \brief (UART3) Write Protection Mode Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAME70_UART3_INSTANCE_ */
