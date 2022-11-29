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

#ifndef _SAMV71_SPI1_INSTANCE_
#define _SAMV71_SPI1_INSTANCE_

/* ========== Register definition for SPI1 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
  #define REG_SPI1_CR                    (0x40058000U) /**< \brief (SPI1) Control Register */
  #define REG_SPI1_MR                    (0x40058004U) /**< \brief (SPI1) Mode Register */
  #define REG_SPI1_RDR                   (0x40058008U) /**< \brief (SPI1) Receive Data Register */
  #define REG_SPI1_TDR                   (0x4005800CU) /**< \brief (SPI1) Transmit Data Register */
  #define REG_SPI1_SR                    (0x40058010U) /**< \brief (SPI1) Status Register */
  #define REG_SPI1_IER                   (0x40058014U) /**< \brief (SPI1) Interrupt Enable Register */
  #define REG_SPI1_IDR                   (0x40058018U) /**< \brief (SPI1) Interrupt Disable Register */
  #define REG_SPI1_IMR                   (0x4005801CU) /**< \brief (SPI1) Interrupt Mask Register */
  #define REG_SPI1_CSR                   (0x40058030U) /**< \brief (SPI1) Chip Select Register */
  #define REG_SPI1_WPMR                  (0x400580E4U) /**< \brief (SPI1) Write Protection Mode Register */
  #define REG_SPI1_WPSR                  (0x400580E8U) /**< \brief (SPI1) Write Protection Status Register */
#else
  #define REG_SPI1_CR   (*(__O  uint32_t*)0x40058000U) /**< \brief (SPI1) Control Register */
  #define REG_SPI1_MR   (*(__IO uint32_t*)0x40058004U) /**< \brief (SPI1) Mode Register */
  #define REG_SPI1_RDR  (*(__I  uint32_t*)0x40058008U) /**< \brief (SPI1) Receive Data Register */
  #define REG_SPI1_TDR  (*(__O  uint32_t*)0x4005800CU) /**< \brief (SPI1) Transmit Data Register */
  #define REG_SPI1_SR   (*(__I  uint32_t*)0x40058010U) /**< \brief (SPI1) Status Register */
  #define REG_SPI1_IER  (*(__O  uint32_t*)0x40058014U) /**< \brief (SPI1) Interrupt Enable Register */
  #define REG_SPI1_IDR  (*(__O  uint32_t*)0x40058018U) /**< \brief (SPI1) Interrupt Disable Register */
  #define REG_SPI1_IMR  (*(__I  uint32_t*)0x4005801CU) /**< \brief (SPI1) Interrupt Mask Register */
  #define REG_SPI1_CSR  (*(__IO uint32_t*)0x40058030U) /**< \brief (SPI1) Chip Select Register */
  #define REG_SPI1_WPMR (*(__IO uint32_t*)0x400580E4U) /**< \brief (SPI1) Write Protection Mode Register */
  #define REG_SPI1_WPSR (*(__I  uint32_t*)0x400580E8U) /**< \brief (SPI1) Write Protection Status Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMV71_SPI1_INSTANCE_ */
