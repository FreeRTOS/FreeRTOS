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

#ifndef _SAM_TWI2_INSTANCE_
#define _SAM_TWI2_INSTANCE_

/* ========== Register definition for TWI2 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
  #define REG_TWI2_CR                    (0x40060000U) /**< \brief (TWI2) Control Register */
  #define REG_TWI2_MMR                   (0x40060004U) /**< \brief (TWI2) Master Mode Register */
  #define REG_TWI2_SMR                   (0x40060008U) /**< \brief (TWI2) Slave Mode Register */
  #define REG_TWI2_IADR                  (0x4006000CU) /**< \brief (TWI2) Internal Address Register */
  #define REG_TWI2_CWGR                  (0x40060010U) /**< \brief (TWI2) Clock Waveform Generator Register */
  #define REG_TWI2_SR                    (0x40060020U) /**< \brief (TWI2) Status Register */
  #define REG_TWI2_IER                   (0x40060024U) /**< \brief (TWI2) Interrupt Enable Register */
  #define REG_TWI2_IDR                   (0x40060028U) /**< \brief (TWI2) Interrupt Disable Register */
  #define REG_TWI2_IMR                   (0x4006002CU) /**< \brief (TWI2) Interrupt Mask Register */
  #define REG_TWI2_RHR                   (0x40060030U) /**< \brief (TWI2) Receive Holding Register */
  #define REG_TWI2_THR                   (0x40060034U) /**< \brief (TWI2) Transmit Holding Register */
  #define REG_TWI2_WPMR                  (0x400600E4U) /**< \brief (TWI2) Write Protection Mode Register */
  #define REG_TWI2_WPSR                  (0x400600E8U) /**< \brief (TWI2) Write Protection Status Register */
#else
  #define REG_TWI2_CR   (*(__O  uint32_t*)0x40060000U) /**< \brief (TWI2) Control Register */
  #define REG_TWI2_MMR  (*(__IO uint32_t*)0x40060004U) /**< \brief (TWI2) Master Mode Register */
  #define REG_TWI2_SMR  (*(__IO uint32_t*)0x40060008U) /**< \brief (TWI2) Slave Mode Register */
  #define REG_TWI2_IADR (*(__IO uint32_t*)0x4006000CU) /**< \brief (TWI2) Internal Address Register */
  #define REG_TWI2_CWGR (*(__IO uint32_t*)0x40060010U) /**< \brief (TWI2) Clock Waveform Generator Register */
  #define REG_TWI2_SR   (*(__I  uint32_t*)0x40060020U) /**< \brief (TWI2) Status Register */
  #define REG_TWI2_IER  (*(__O  uint32_t*)0x40060024U) /**< \brief (TWI2) Interrupt Enable Register */
  #define REG_TWI2_IDR  (*(__O  uint32_t*)0x40060028U) /**< \brief (TWI2) Interrupt Disable Register */
  #define REG_TWI2_IMR  (*(__I  uint32_t*)0x4006002CU) /**< \brief (TWI2) Interrupt Mask Register */
  #define REG_TWI2_RHR  (*(__I  uint32_t*)0x40060030U) /**< \brief (TWI2) Receive Holding Register */
  #define REG_TWI2_THR  (*(__O  uint32_t*)0x40060034U) /**< \brief (TWI2) Transmit Holding Register */
  #define REG_TWI2_WPMR (*(__IO uint32_t*)0x400600E4U) /**< \brief (TWI2) Write Protection Mode Register */
  #define REG_TWI2_WPSR (*(__I  uint32_t*)0x400600E8U) /**< \brief (TWI2) Write Protection Status Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAM_TWI2_INSTANCE_ */
