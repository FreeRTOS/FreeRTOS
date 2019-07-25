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

#ifndef _SAMV71_UART1_INSTANCE_
#define _SAMV71_UART1_INSTANCE_

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

#endif /* _SAMV71_UART1_INSTANCE_ */
