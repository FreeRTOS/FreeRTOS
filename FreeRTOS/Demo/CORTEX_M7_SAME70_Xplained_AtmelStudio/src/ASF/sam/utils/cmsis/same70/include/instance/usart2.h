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

#ifndef _SAME70_USART2_INSTANCE_
#define _SAME70_USART2_INSTANCE_

/* ========== Register definition for USART2 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
  #define REG_USART2_CR                        (0x4002C000U) /**< \brief (USART2) Control Register */
  #define REG_USART2_MR                        (0x4002C004U) /**< \brief (USART2) Mode Register */
  #define REG_USART2_IER                       (0x4002C008U) /**< \brief (USART2) Interrupt Enable Register */
  #define REG_USART2_IDR                       (0x4002C00CU) /**< \brief (USART2) Interrupt Disable Register */
  #define REG_USART2_IMR                       (0x4002C010U) /**< \brief (USART2) Interrupt Mask Register */
  #define REG_USART2_CSR                       (0x4002C014U) /**< \brief (USART2) Channel Status Register */
  #define REG_USART2_RHR                       (0x4002C018U) /**< \brief (USART2) Receive Holding Register */
  #define REG_USART2_THR                       (0x4002C01CU) /**< \brief (USART2) Transmit Holding Register */
  #define REG_USART2_BRGR                      (0x4002C020U) /**< \brief (USART2) Baud Rate Generator Register */
  #define REG_USART2_RTOR                      (0x4002C024U) /**< \brief (USART2) Receiver Time-out Register */
  #define REG_USART2_TTGR                      (0x4002C028U) /**< \brief (USART2) Transmitter Timeguard Register */
  #define REG_USART2_MAN                       (0x4002C050U) /**< \brief (USART2) Manchester Configuration Register */
  #define REG_USART2_LINMR                     (0x4002C054U) /**< \brief (USART2) LIN Mode Register */
  #define REG_USART2_LINIR                     (0x4002C058U) /**< \brief (USART2) LIN Identifier Register */
  #define REG_USART2_LINBRR                    (0x4002C05CU) /**< \brief (USART2) LIN Baud Rate Register */
  #define REG_USART2_LONMR                     (0x4002C060U) /**< \brief (USART2) LON Mode Register */
  #define REG_USART2_LONPR                     (0x4002C064U) /**< \brief (USART2) LON Preamble Register */
  #define REG_USART2_LONDL                     (0x4002C068U) /**< \brief (USART2) LON Data Length Register */
  #define REG_USART2_LONL2HDR                  (0x4002C06CU) /**< \brief (USART2) LON L2HDR Register */
  #define REG_USART2_LONBL                     (0x4002C070U) /**< \brief (USART2) LON Backlog Register */
  #define REG_USART2_LONB1TX                   (0x4002C074U) /**< \brief (USART2) LON Beta1 Tx Register */
  #define REG_USART2_LONB1RX                   (0x4002C078U) /**< \brief (USART2) LON Beta1 Rx Register */
  #define REG_USART2_LONPRIO                   (0x4002C07CU) /**< \brief (USART2) LON Priority Register */
  #define REG_USART2_IDTTX                     (0x4002C080U) /**< \brief (USART2) LON IDT Tx Register */
  #define REG_USART2_IDTRX                     (0x4002C084U) /**< \brief (USART2) LON IDT Rx Register */
  #define REG_USART2_ICDIFF                    (0x4002C088U) /**< \brief (USART2) IC DIFF Register */
  #define REG_USART2_WPMR                      (0x4002C0E4U) /**< \brief (USART2) Write Protection Mode Register */
  #define REG_USART2_WPSR                      (0x4002C0E8U) /**< \brief (USART2) Write Protection Status Register */
#else
  #define REG_USART2_CR       (*(__O  uint32_t*)0x4002C000U) /**< \brief (USART2) Control Register */
  #define REG_USART2_MR       (*(__IO uint32_t*)0x4002C004U) /**< \brief (USART2) Mode Register */
  #define REG_USART2_IER      (*(__O  uint32_t*)0x4002C008U) /**< \brief (USART2) Interrupt Enable Register */
  #define REG_USART2_IDR      (*(__O  uint32_t*)0x4002C00CU) /**< \brief (USART2) Interrupt Disable Register */
  #define REG_USART2_IMR      (*(__I  uint32_t*)0x4002C010U) /**< \brief (USART2) Interrupt Mask Register */
  #define REG_USART2_CSR      (*(__I  uint32_t*)0x4002C014U) /**< \brief (USART2) Channel Status Register */
  #define REG_USART2_RHR      (*(__I  uint32_t*)0x4002C018U) /**< \brief (USART2) Receive Holding Register */
  #define REG_USART2_THR      (*(__O  uint32_t*)0x4002C01CU) /**< \brief (USART2) Transmit Holding Register */
  #define REG_USART2_BRGR     (*(__IO uint32_t*)0x4002C020U) /**< \brief (USART2) Baud Rate Generator Register */
  #define REG_USART2_RTOR     (*(__IO uint32_t*)0x4002C024U) /**< \brief (USART2) Receiver Time-out Register */
  #define REG_USART2_TTGR     (*(__IO uint32_t*)0x4002C028U) /**< \brief (USART2) Transmitter Timeguard Register */
  #define REG_USART2_MAN      (*(__IO uint32_t*)0x4002C050U) /**< \brief (USART2) Manchester Configuration Register */
  #define REG_USART2_LINMR    (*(__IO uint32_t*)0x4002C054U) /**< \brief (USART2) LIN Mode Register */
  #define REG_USART2_LINIR    (*(__IO uint32_t*)0x4002C058U) /**< \brief (USART2) LIN Identifier Register */
  #define REG_USART2_LINBRR   (*(__I  uint32_t*)0x4002C05CU) /**< \brief (USART2) LIN Baud Rate Register */
  #define REG_USART2_LONMR    (*(__IO uint32_t*)0x4002C060U) /**< \brief (USART2) LON Mode Register */
  #define REG_USART2_LONPR    (*(__IO uint32_t*)0x4002C064U) /**< \brief (USART2) LON Preamble Register */
  #define REG_USART2_LONDL    (*(__IO uint32_t*)0x4002C068U) /**< \brief (USART2) LON Data Length Register */
  #define REG_USART2_LONL2HDR (*(__IO uint32_t*)0x4002C06CU) /**< \brief (USART2) LON L2HDR Register */
  #define REG_USART2_LONBL    (*(__I  uint32_t*)0x4002C070U) /**< \brief (USART2) LON Backlog Register */
  #define REG_USART2_LONB1TX  (*(__IO uint32_t*)0x4002C074U) /**< \brief (USART2) LON Beta1 Tx Register */
  #define REG_USART2_LONB1RX  (*(__IO uint32_t*)0x4002C078U) /**< \brief (USART2) LON Beta1 Rx Register */
  #define REG_USART2_LONPRIO  (*(__IO uint32_t*)0x4002C07CU) /**< \brief (USART2) LON Priority Register */
  #define REG_USART2_IDTTX    (*(__IO uint32_t*)0x4002C080U) /**< \brief (USART2) LON IDT Tx Register */
  #define REG_USART2_IDTRX    (*(__IO uint32_t*)0x4002C084U) /**< \brief (USART2) LON IDT Rx Register */
  #define REG_USART2_ICDIFF   (*(__IO uint32_t*)0x4002C088U) /**< \brief (USART2) IC DIFF Register */
  #define REG_USART2_WPMR     (*(__IO uint32_t*)0x4002C0E4U) /**< \brief (USART2) Write Protection Mode Register */
  #define REG_USART2_WPSR     (*(__I  uint32_t*)0x4002C0E8U) /**< \brief (USART2) Write Protection Status Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAME70_USART2_INSTANCE_ */
