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

#ifndef _SAM_UART2_INSTANCE_
#define _SAM_UART2_INSTANCE_

/* ========== Register definition for UART2 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
  #define REG_UART2_CR                    (0x400E1A00U) /**< \brief (UART2) Control Register */
  #define REG_UART2_MR                    (0x400E1A04U) /**< \brief (UART2) Mode Register */
  #define REG_UART2_IER                   (0x400E1A08U) /**< \brief (UART2) Interrupt Enable Register */
  #define REG_UART2_IDR                   (0x400E1A0CU) /**< \brief (UART2) Interrupt Disable Register */
  #define REG_UART2_IMR                   (0x400E1A10U) /**< \brief (UART2) Interrupt Mask Register */
  #define REG_UART2_SR                    (0x400E1A14U) /**< \brief (UART2) Status Register */
  #define REG_UART2_RHR                   (0x400E1A18U) /**< \brief (UART2) Receive Holding Register */
  #define REG_UART2_THR                   (0x400E1A1CU) /**< \brief (UART2) Transmit Holding Register */
  #define REG_UART2_BRGR                  (0x400E1A20U) /**< \brief (UART2) Baud Rate Generator Register */
  #define REG_UART2_CMPR                  (0x400E1A24U) /**< \brief (UART2) Comparison Register */
  #define REG_UART2_WPMR                  (0x400E1AE4U) /**< \brief (UART2) Write Protection Mode Register */
#else
  #define REG_UART2_CR   (*(__O  uint32_t*)0x400E1A00U) /**< \brief (UART2) Control Register */
  #define REG_UART2_MR   (*(__IO uint32_t*)0x400E1A04U) /**< \brief (UART2) Mode Register */
  #define REG_UART2_IER  (*(__O  uint32_t*)0x400E1A08U) /**< \brief (UART2) Interrupt Enable Register */
  #define REG_UART2_IDR  (*(__O  uint32_t*)0x400E1A0CU) /**< \brief (UART2) Interrupt Disable Register */
  #define REG_UART2_IMR  (*(__I  uint32_t*)0x400E1A10U) /**< \brief (UART2) Interrupt Mask Register */
  #define REG_UART2_SR   (*(__I  uint32_t*)0x400E1A14U) /**< \brief (UART2) Status Register */
  #define REG_UART2_RHR  (*(__I  uint32_t*)0x400E1A18U) /**< \brief (UART2) Receive Holding Register */
  #define REG_UART2_THR  (*(__O  uint32_t*)0x400E1A1CU) /**< \brief (UART2) Transmit Holding Register */
  #define REG_UART2_BRGR (*(__IO uint32_t*)0x400E1A20U) /**< \brief (UART2) Baud Rate Generator Register */
  #define REG_UART2_CMPR (*(__IO uint32_t*)0x400E1A24U) /**< \brief (UART2) Comparison Register */
  #define REG_UART2_WPMR (*(__IO uint32_t*)0x400E1AE4U) /**< \brief (UART2) Write Protection Mode Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAM_UART2_INSTANCE_ */
