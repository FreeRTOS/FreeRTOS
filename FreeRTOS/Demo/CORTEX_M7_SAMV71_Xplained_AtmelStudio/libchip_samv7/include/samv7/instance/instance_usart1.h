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

#ifndef _SAMV71_USART1_INSTANCE_
#define _SAMV71_USART1_INSTANCE_

/* ========== Register definition for USART1 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
  #define REG_USART1_CR                        (0x40028000U) /**< \brief (USART1) Control Register */
  #define REG_USART1_MR                        (0x40028004U) /**< \brief (USART1) Mode Register */
  #define REG_USART1_IER                       (0x40028008U) /**< \brief (USART1) Interrupt Enable Register */
  #define REG_USART1_IDR                       (0x4002800CU) /**< \brief (USART1) Interrupt Disable Register */
  #define REG_USART1_IMR                       (0x40028010U) /**< \brief (USART1) Interrupt Mask Register */
  #define REG_USART1_CSR                       (0x40028014U) /**< \brief (USART1) Channel Status Register */
  #define REG_USART1_RHR                       (0x40028018U) /**< \brief (USART1) Receive Holding Register */
  #define REG_USART1_THR                       (0x4002801CU) /**< \brief (USART1) Transmit Holding Register */
  #define REG_USART1_BRGR                      (0x40028020U) /**< \brief (USART1) Baud Rate Generator Register */
  #define REG_USART1_RTOR                      (0x40028024U) /**< \brief (USART1) Receiver Time-out Register */
  #define REG_USART1_TTGR                      (0x40028028U) /**< \brief (USART1) Transmitter Timeguard Register */
  #define REG_USART1_MAN                       (0x40028050U) /**< \brief (USART1) Manchester Configuration Register */
  #define REG_USART1_LINMR                     (0x40028054U) /**< \brief (USART1) LIN Mode Register */
  #define REG_USART1_LINIR                     (0x40028058U) /**< \brief (USART1) LIN Identifier Register */
  #define REG_USART1_LINBRR                    (0x4002805CU) /**< \brief (USART1) LIN Baud Rate Register */
  #define REG_USART1_LONMR                     (0x40028060U) /**< \brief (USART1) LON Mode Register */
  #define REG_USART1_LONPR                     (0x40028064U) /**< \brief (USART1) LON Preamble Register */
  #define REG_USART1_LONDL                     (0x40028068U) /**< \brief (USART1) LON Data Length Register */
  #define REG_USART1_LONL2HDR                  (0x4002806CU) /**< \brief (USART1) LON L2HDR Register */
  #define REG_USART1_LONBL                     (0x40028070U) /**< \brief (USART1) LON Backlog Register */
  #define REG_USART1_LONB1TX                   (0x40028074U) /**< \brief (USART1) LON Beta1 Tx Register */
  #define REG_USART1_LONB1RX                   (0x40028078U) /**< \brief (USART1) LON Beta1 Rx Register */
  #define REG_USART1_LONPRIO                   (0x4002807CU) /**< \brief (USART1) LON Priority Register */
  #define REG_USART1_IDTTX                     (0x40028080U) /**< \brief (USART1) LON IDT Tx Register */
  #define REG_USART1_IDTRX                     (0x40028084U) /**< \brief (USART1) LON IDT Rx Register */
  #define REG_USART1_ICDIFF                    (0x40028088U) /**< \brief (USART1) IC DIFF Register */
  #define REG_USART1_WPMR                      (0x400280E4U) /**< \brief (USART1) Write Protection Mode Register */
  #define REG_USART1_WPSR                      (0x400280E8U) /**< \brief (USART1) Write Protection Status Register */
#else
  #define REG_USART1_CR       (*(__O  uint32_t*)0x40028000U) /**< \brief (USART1) Control Register */
  #define REG_USART1_MR       (*(__IO uint32_t*)0x40028004U) /**< \brief (USART1) Mode Register */
  #define REG_USART1_IER      (*(__O  uint32_t*)0x40028008U) /**< \brief (USART1) Interrupt Enable Register */
  #define REG_USART1_IDR      (*(__O  uint32_t*)0x4002800CU) /**< \brief (USART1) Interrupt Disable Register */
  #define REG_USART1_IMR      (*(__I  uint32_t*)0x40028010U) /**< \brief (USART1) Interrupt Mask Register */
  #define REG_USART1_CSR      (*(__I  uint32_t*)0x40028014U) /**< \brief (USART1) Channel Status Register */
  #define REG_USART1_RHR      (*(__I  uint32_t*)0x40028018U) /**< \brief (USART1) Receive Holding Register */
  #define REG_USART1_THR      (*(__O  uint32_t*)0x4002801CU) /**< \brief (USART1) Transmit Holding Register */
  #define REG_USART1_BRGR     (*(__IO uint32_t*)0x40028020U) /**< \brief (USART1) Baud Rate Generator Register */
  #define REG_USART1_RTOR     (*(__IO uint32_t*)0x40028024U) /**< \brief (USART1) Receiver Time-out Register */
  #define REG_USART1_TTGR     (*(__IO uint32_t*)0x40028028U) /**< \brief (USART1) Transmitter Timeguard Register */
  #define REG_USART1_MAN      (*(__IO uint32_t*)0x40028050U) /**< \brief (USART1) Manchester Configuration Register */
  #define REG_USART1_LINMR    (*(__IO uint32_t*)0x40028054U) /**< \brief (USART1) LIN Mode Register */
  #define REG_USART1_LINIR    (*(__IO uint32_t*)0x40028058U) /**< \brief (USART1) LIN Identifier Register */
  #define REG_USART1_LINBRR   (*(__I  uint32_t*)0x4002805CU) /**< \brief (USART1) LIN Baud Rate Register */
  #define REG_USART1_LONMR    (*(__IO uint32_t*)0x40028060U) /**< \brief (USART1) LON Mode Register */
  #define REG_USART1_LONPR    (*(__IO uint32_t*)0x40028064U) /**< \brief (USART1) LON Preamble Register */
  #define REG_USART1_LONDL    (*(__IO uint32_t*)0x40028068U) /**< \brief (USART1) LON Data Length Register */
  #define REG_USART1_LONL2HDR (*(__IO uint32_t*)0x4002806CU) /**< \brief (USART1) LON L2HDR Register */
  #define REG_USART1_LONBL    (*(__I  uint32_t*)0x40028070U) /**< \brief (USART1) LON Backlog Register */
  #define REG_USART1_LONB1TX  (*(__IO uint32_t*)0x40028074U) /**< \brief (USART1) LON Beta1 Tx Register */
  #define REG_USART1_LONB1RX  (*(__IO uint32_t*)0x40028078U) /**< \brief (USART1) LON Beta1 Rx Register */
  #define REG_USART1_LONPRIO  (*(__IO uint32_t*)0x4002807CU) /**< \brief (USART1) LON Priority Register */
  #define REG_USART1_IDTTX    (*(__IO uint32_t*)0x40028080U) /**< \brief (USART1) LON IDT Tx Register */
  #define REG_USART1_IDTRX    (*(__IO uint32_t*)0x40028084U) /**< \brief (USART1) LON IDT Rx Register */
  #define REG_USART1_ICDIFF   (*(__IO uint32_t*)0x40028088U) /**< \brief (USART1) IC DIFF Register */
  #define REG_USART1_WPMR     (*(__IO uint32_t*)0x400280E4U) /**< \brief (USART1) Write Protection Mode Register */
  #define REG_USART1_WPSR     (*(__I  uint32_t*)0x400280E8U) /**< \brief (USART1) Write Protection Status Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMV71_USART1_INSTANCE_ */
