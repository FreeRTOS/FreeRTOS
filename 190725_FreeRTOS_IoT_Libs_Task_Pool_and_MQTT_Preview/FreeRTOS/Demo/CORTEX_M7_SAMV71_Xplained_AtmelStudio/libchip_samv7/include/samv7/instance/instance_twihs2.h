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

#ifndef _SAMV71_TWIHS2_INSTANCE_
#define _SAMV71_TWIHS2_INSTANCE_

/* ========== Register definition for TWIHS2 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
  #define REG_TWIHS2_CR                     (0x40060000U) /**< \brief (TWIHS2) Control Register */
  #define REG_TWIHS2_MMR                    (0x40060004U) /**< \brief (TWIHS2) Master Mode Register */
  #define REG_TWIHS2_SMR                    (0x40060008U) /**< \brief (TWIHS2) Slave Mode Register */
  #define REG_TWIHS2_IADR                   (0x4006000CU) /**< \brief (TWIHS2) Internal Address Register */
  #define REG_TWIHS2_CWGR                   (0x40060010U) /**< \brief (TWIHS2) Clock Waveform Generator Register */
  #define REG_TWIHS2_SR                     (0x40060020U) /**< \brief (TWIHS2) Status Register */
  #define REG_TWIHS2_IER                    (0x40060024U) /**< \brief (TWIHS2) Interrupt Enable Register */
  #define REG_TWIHS2_IDR                    (0x40060028U) /**< \brief (TWIHS2) Interrupt Disable Register */
  #define REG_TWIHS2_IMR                    (0x4006002CU) /**< \brief (TWIHS2) Interrupt Mask Register */
  #define REG_TWIHS2_RHR                    (0x40060030U) /**< \brief (TWIHS2) Receive Holding Register */
  #define REG_TWIHS2_THR                    (0x40060034U) /**< \brief (TWIHS2) Transmit Holding Register */
  #define REG_TWIHS2_SMBTR                  (0x40060038U) /**< \brief (TWIHS2) SMBus Timing Register */
  #define REG_TWIHS2_FILTR                  (0x40060044U) /**< \brief (TWIHS2) Filter Register */
  #define REG_TWIHS2_SWMR                   (0x4006004CU) /**< \brief (TWIHS2) SleepWalking Matching Register */
  #define REG_TWIHS2_WPMR                   (0x400600E4U) /**< \brief (TWIHS2) Write Protection Mode Register */
  #define REG_TWIHS2_WPSR                   (0x400600E8U) /**< \brief (TWIHS2) Write Protection Status Register */
#else
  #define REG_TWIHS2_CR    (*(__O  uint32_t*)0x40060000U) /**< \brief (TWIHS2) Control Register */
  #define REG_TWIHS2_MMR   (*(__IO uint32_t*)0x40060004U) /**< \brief (TWIHS2) Master Mode Register */
  #define REG_TWIHS2_SMR   (*(__IO uint32_t*)0x40060008U) /**< \brief (TWIHS2) Slave Mode Register */
  #define REG_TWIHS2_IADR  (*(__IO uint32_t*)0x4006000CU) /**< \brief (TWIHS2) Internal Address Register */
  #define REG_TWIHS2_CWGR  (*(__IO uint32_t*)0x40060010U) /**< \brief (TWIHS2) Clock Waveform Generator Register */
  #define REG_TWIHS2_SR    (*(__I  uint32_t*)0x40060020U) /**< \brief (TWIHS2) Status Register */
  #define REG_TWIHS2_IER   (*(__O  uint32_t*)0x40060024U) /**< \brief (TWIHS2) Interrupt Enable Register */
  #define REG_TWIHS2_IDR   (*(__O  uint32_t*)0x40060028U) /**< \brief (TWIHS2) Interrupt Disable Register */
  #define REG_TWIHS2_IMR   (*(__I  uint32_t*)0x4006002CU) /**< \brief (TWIHS2) Interrupt Mask Register */
  #define REG_TWIHS2_RHR   (*(__I  uint32_t*)0x40060030U) /**< \brief (TWIHS2) Receive Holding Register */
  #define REG_TWIHS2_THR   (*(__O  uint32_t*)0x40060034U) /**< \brief (TWIHS2) Transmit Holding Register */
  #define REG_TWIHS2_SMBTR (*(__IO uint32_t*)0x40060038U) /**< \brief (TWIHS2) SMBus Timing Register */
  #define REG_TWIHS2_FILTR (*(__IO uint32_t*)0x40060044U) /**< \brief (TWIHS2) Filter Register */
  #define REG_TWIHS2_SWMR  (*(__IO uint32_t*)0x4006004CU) /**< \brief (TWIHS2) SleepWalking Matching Register */
  #define REG_TWIHS2_WPMR  (*(__IO uint32_t*)0x400600E4U) /**< \brief (TWIHS2) Write Protection Mode Register */
  #define REG_TWIHS2_WPSR  (*(__I  uint32_t*)0x400600E8U) /**< \brief (TWIHS2) Write Protection Status Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMV71_TWIHS2_INSTANCE_ */
