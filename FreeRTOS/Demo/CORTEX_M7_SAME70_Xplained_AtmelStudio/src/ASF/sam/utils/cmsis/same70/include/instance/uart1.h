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

#ifndef _SAME70_UART1_INSTANCE_
#define _SAME70_UART1_INSTANCE_

/* ========== Register definition for UART1 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
  #define REG_UART1_CR                    (0x400E0A00U) /**< \brief (UART1) Control Register */
  #define REG_UART1_MR                    (0x400E0A04U) /**< \brief (UART1) Mode Register */
  #define REG_UART1_IER                   (0x400E0A08U) /**< \brief (UART1) Interrupt Enable Register */
  #define REG_UART1_IDR                   (0x400E0A0CU) /**< \brief (UART1) Interrupt Disable Register */
  #define REG_UART1_IMR                   (0x400E0A10U) /**< \brief (UART1) Interrupt Mask Register */
  #define REG_UART1_SR                    (0x400E0A14U) /**< \brief (UART1) Status Register */
  #define REG_UART1_RHR                   (0x400E0A18U) /**< \brief (UART1) Receive Holding Register */
  #define REG_UART1_THR                   (0x400E0A1CU) /**< \brief (UART1) Transmit Holding Register */
  #define REG_UART1_BRGR                  (0x400E0A20U) /**< \brief (UART1) Baud Rate Generator Register */
  #define REG_UART1_CMPR                  (0x400E0A24U) /**< \brief (UART1) Comparison Register */
  #define REG_UART1_WPMR                  (0x400E0AE4U) /**< \brief (UART1) Write Protection Mode Register */
#else
  #define REG_UART1_CR   (*(__O  uint32_t*)0x400E0A00U) /**< \brief (UART1) Control Register */
  #define REG_UART1_MR   (*(__IO uint32_t*)0x400E0A04U) /**< \brief (UART1) Mode Register */
  #define REG_UART1_IER  (*(__O  uint32_t*)0x400E0A08U) /**< \brief (UART1) Interrupt Enable Register */
  #define REG_UART1_IDR  (*(__O  uint32_t*)0x400E0A0CU) /**< \brief (UART1) Interrupt Disable Register */
  #define REG_UART1_IMR  (*(__I  uint32_t*)0x400E0A10U) /**< \brief (UART1) Interrupt Mask Register */
  #define REG_UART1_SR   (*(__I  uint32_t*)0x400E0A14U) /**< \brief (UART1) Status Register */
  #define REG_UART1_RHR  (*(__I  uint32_t*)0x400E0A18U) /**< \brief (UART1) Receive Holding Register */
  #define REG_UART1_THR  (*(__O  uint32_t*)0x400E0A1CU) /**< \brief (UART1) Transmit Holding Register */
  #define REG_UART1_BRGR (*(__IO uint32_t*)0x400E0A20U) /**< \brief (UART1) Baud Rate Generator Register */
  #define REG_UART1_CMPR (*(__IO uint32_t*)0x400E0A24U) /**< \brief (UART1) Comparison Register */
  #define REG_UART1_WPMR (*(__IO uint32_t*)0x400E0AE4U) /**< \brief (UART1) Write Protection Mode Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAME70_UART1_INSTANCE_ */
