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

#ifndef _SAMV71_USART0_INSTANCE_
#define _SAMV71_USART0_INSTANCE_

/* ========== Register definition for USART0 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
  #define REG_USART0_CR                        (0x40024000U) /**< \brief (USART0) Control Register */
  #define REG_USART0_MR                        (0x40024004U) /**< \brief (USART0) Mode Register */
  #define REG_USART0_IER                       (0x40024008U) /**< \brief (USART0) Interrupt Enable Register */
  #define REG_USART0_IDR                       (0x4002400CU) /**< \brief (USART0) Interrupt Disable Register */
  #define REG_USART0_IMR                       (0x40024010U) /**< \brief (USART0) Interrupt Mask Register */
  #define REG_USART0_CSR                       (0x40024014U) /**< \brief (USART0) Channel Status Register */
  #define REG_USART0_RHR                       (0x40024018U) /**< \brief (USART0) Receive Holding Register */
  #define REG_USART0_THR                       (0x4002401CU) /**< \brief (USART0) Transmit Holding Register */
  #define REG_USART0_BRGR                      (0x40024020U) /**< \brief (USART0) Baud Rate Generator Register */
  #define REG_USART0_RTOR                      (0x40024024U) /**< \brief (USART0) Receiver Time-out Register */
  #define REG_USART0_TTGR                      (0x40024028U) /**< \brief (USART0) Transmitter Timeguard Register */
  #define REG_USART0_MAN                       (0x40024050U) /**< \brief (USART0) Manchester Configuration Register */
  #define REG_USART0_LINMR                     (0x40024054U) /**< \brief (USART0) LIN Mode Register */
  #define REG_USART0_LINIR                     (0x40024058U) /**< \brief (USART0) LIN Identifier Register */
  #define REG_USART0_LINBRR                    (0x4002405CU) /**< \brief (USART0) LIN Baud Rate Register */
  #define REG_USART0_LONMR                     (0x40024060U) /**< \brief (USART0) LON Mode Register */
  #define REG_USART0_LONPR                     (0x40024064U) /**< \brief (USART0) LON Preamble Register */
  #define REG_USART0_LONDL                     (0x40024068U) /**< \brief (USART0) LON Data Length Register */
  #define REG_USART0_LONL2HDR                  (0x4002406CU) /**< \brief (USART0) LON L2HDR Register */
  #define REG_USART0_LONBL                     (0x40024070U) /**< \brief (USART0) LON Backlog Register */
  #define REG_USART0_LONB1TX                   (0x40024074U) /**< \brief (USART0) LON Beta1 Tx Register */
  #define REG_USART0_LONB1RX                   (0x40024078U) /**< \brief (USART0) LON Beta1 Rx Register */
  #define REG_USART0_LONPRIO                   (0x4002407CU) /**< \brief (USART0) LON Priority Register */
  #define REG_USART0_IDTTX                     (0x40024080U) /**< \brief (USART0) LON IDT Tx Register */
  #define REG_USART0_IDTRX                     (0x40024084U) /**< \brief (USART0) LON IDT Rx Register */
  #define REG_USART0_ICDIFF                    (0x40024088U) /**< \brief (USART0) IC DIFF Register */
  #define REG_USART0_WPMR                      (0x400240E4U) /**< \brief (USART0) Write Protection Mode Register */
  #define REG_USART0_WPSR                      (0x400240E8U) /**< \brief (USART0) Write Protection Status Register */
#else
  #define REG_USART0_CR       (*(__O  uint32_t*)0x40024000U) /**< \brief (USART0) Control Register */
  #define REG_USART0_MR       (*(__IO uint32_t*)0x40024004U) /**< \brief (USART0) Mode Register */
  #define REG_USART0_IER      (*(__O  uint32_t*)0x40024008U) /**< \brief (USART0) Interrupt Enable Register */
  #define REG_USART0_IDR      (*(__O  uint32_t*)0x4002400CU) /**< \brief (USART0) Interrupt Disable Register */
  #define REG_USART0_IMR      (*(__I  uint32_t*)0x40024010U) /**< \brief (USART0) Interrupt Mask Register */
  #define REG_USART0_CSR      (*(__I  uint32_t*)0x40024014U) /**< \brief (USART0) Channel Status Register */
  #define REG_USART0_RHR      (*(__I  uint32_t*)0x40024018U) /**< \brief (USART0) Receive Holding Register */
  #define REG_USART0_THR      (*(__O  uint32_t*)0x4002401CU) /**< \brief (USART0) Transmit Holding Register */
  #define REG_USART0_BRGR     (*(__IO uint32_t*)0x40024020U) /**< \brief (USART0) Baud Rate Generator Register */
  #define REG_USART0_RTOR     (*(__IO uint32_t*)0x40024024U) /**< \brief (USART0) Receiver Time-out Register */
  #define REG_USART0_TTGR     (*(__IO uint32_t*)0x40024028U) /**< \brief (USART0) Transmitter Timeguard Register */
  #define REG_USART0_MAN      (*(__IO uint32_t*)0x40024050U) /**< \brief (USART0) Manchester Configuration Register */
  #define REG_USART0_LINMR    (*(__IO uint32_t*)0x40024054U) /**< \brief (USART0) LIN Mode Register */
  #define REG_USART0_LINIR    (*(__IO uint32_t*)0x40024058U) /**< \brief (USART0) LIN Identifier Register */
  #define REG_USART0_LINBRR   (*(__I  uint32_t*)0x4002405CU) /**< \brief (USART0) LIN Baud Rate Register */
  #define REG_USART0_LONMR    (*(__IO uint32_t*)0x40024060U) /**< \brief (USART0) LON Mode Register */
  #define REG_USART0_LONPR    (*(__IO uint32_t*)0x40024064U) /**< \brief (USART0) LON Preamble Register */
  #define REG_USART0_LONDL    (*(__IO uint32_t*)0x40024068U) /**< \brief (USART0) LON Data Length Register */
  #define REG_USART0_LONL2HDR (*(__IO uint32_t*)0x4002406CU) /**< \brief (USART0) LON L2HDR Register */
  #define REG_USART0_LONBL    (*(__I  uint32_t*)0x40024070U) /**< \brief (USART0) LON Backlog Register */
  #define REG_USART0_LONB1TX  (*(__IO uint32_t*)0x40024074U) /**< \brief (USART0) LON Beta1 Tx Register */
  #define REG_USART0_LONB1RX  (*(__IO uint32_t*)0x40024078U) /**< \brief (USART0) LON Beta1 Rx Register */
  #define REG_USART0_LONPRIO  (*(__IO uint32_t*)0x4002407CU) /**< \brief (USART0) LON Priority Register */
  #define REG_USART0_IDTTX    (*(__IO uint32_t*)0x40024080U) /**< \brief (USART0) LON IDT Tx Register */
  #define REG_USART0_IDTRX    (*(__IO uint32_t*)0x40024084U) /**< \brief (USART0) LON IDT Rx Register */
  #define REG_USART0_ICDIFF   (*(__IO uint32_t*)0x40024088U) /**< \brief (USART0) IC DIFF Register */
  #define REG_USART0_WPMR     (*(__IO uint32_t*)0x400240E4U) /**< \brief (USART0) Write Protection Mode Register */
  #define REG_USART0_WPSR     (*(__I  uint32_t*)0x400240E8U) /**< \brief (USART0) Write Protection Status Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMV71_USART0_INSTANCE_ */
