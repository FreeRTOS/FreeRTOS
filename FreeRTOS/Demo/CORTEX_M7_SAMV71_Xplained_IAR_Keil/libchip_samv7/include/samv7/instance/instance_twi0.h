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

#ifndef _SAM_TWI0_INSTANCE_
#define _SAM_TWI0_INSTANCE_

/* ========== Register definition for TWI0 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
  #define REG_TWI0_CR                     (0x40018000U) /**< \brief (TWI0) Control Register */
  #define REG_TWI0_MMR                    (0x40018004U) /**< \brief (TWI0) Master Mode Register */
  #define REG_TWI0_SMR                    (0x40018008U) /**< \brief (TWI0) Slave Mode Register */
  #define REG_TWI0_IADR                   (0x4001800CU) /**< \brief (TWI0) Internal Address Register */
  #define REG_TWI0_CWGR                   (0x40018010U) /**< \brief (TWI0) Clock Waveform Generator Register */
  #define REG_TWI0_SR                     (0x40018020U) /**< \brief (TWI0) Status Register */
  #define REG_TWI0_IER                    (0x40018024U) /**< \brief (TWI0) Interrupt Enable Register */
  #define REG_TWI0_IDR                    (0x40018028U) /**< \brief (TWI0) Interrupt Disable Register */
  #define REG_TWI0_IMR                    (0x4001802CU) /**< \brief (TWI0) Interrupt Mask Register */
  #define REG_TWI0_RHR                    (0x40018030U) /**< \brief (TWI0) Receive Holding Register */
  #define REG_TWI0_THR                    (0x40018034U) /**< \brief (TWI0) Transmit Holding Register */
  #define REG_TWI0_SMBTR                  (0x40018038U) /**< \brief (TWI0) SMBus Timing Register */
  #define REG_TWI0_ACR                    (0x40018040U) /**< \brief (TWI0) Alternative Command Register */
  #define REG_TWI0_FILTR                  (0x40018044U) /**< \brief (TWI0) Filter Register */
  #define REG_TWI0_SWMR                   (0x4001804CU) /**< \brief (TWI0) SleepWalking Matching Register */
  #define REG_TWI0_DR                     (0x400180D0U) /**< \brief (TWI0) Debug Register */
  #define REG_TWI0_WPMR                   (0x400180E4U) /**< \brief (TWI0) Protection Mode Register */
  #define REG_TWI0_WPSR                   (0x400180E8U) /**< \brief (TWI0) Protection Status Register */
  #define REG_TWI0_VER                    (0x400180FCU) /**< \brief (TWI0) Version Register */
#else
  #define REG_TWI0_CR    (*(__O  uint32_t*)0x40018000U) /**< \brief (TWI0) Control Register */
  #define REG_TWI0_MMR   (*(__IO uint32_t*)0x40018004U) /**< \brief (TWI0) Master Mode Register */
  #define REG_TWI0_SMR   (*(__IO uint32_t*)0x40018008U) /**< \brief (TWI0) Slave Mode Register */
  #define REG_TWI0_IADR  (*(__IO uint32_t*)0x4001800CU) /**< \brief (TWI0) Internal Address Register */
  #define REG_TWI0_CWGR  (*(__IO uint32_t*)0x40018010U) /**< \brief (TWI0) Clock Waveform Generator Register */
  #define REG_TWI0_SR    (*(__I  uint32_t*)0x40018020U) /**< \brief (TWI0) Status Register */
  #define REG_TWI0_IER   (*(__O  uint32_t*)0x40018024U) /**< \brief (TWI0) Interrupt Enable Register */
  #define REG_TWI0_IDR   (*(__O  uint32_t*)0x40018028U) /**< \brief (TWI0) Interrupt Disable Register */
  #define REG_TWI0_IMR   (*(__I  uint32_t*)0x4001802CU) /**< \brief (TWI0) Interrupt Mask Register */
  #define REG_TWI0_RHR   (*(__I  uint32_t*)0x40018030U) /**< \brief (TWI0) Receive Holding Register */
  #define REG_TWI0_THR   (*(__O  uint32_t*)0x40018034U) /**< \brief (TWI0) Transmit Holding Register */
  #define REG_TWI0_SMBTR (*(__IO uint32_t*)0x40018038U) /**< \brief (TWI0) SMBus Timing Register */
  #define REG_TWI0_ACR   (*(__IO uint32_t*)0x40018040U) /**< \brief (TWI0) Alternative Command Register */
  #define REG_TWI0_FILTR (*(__IO uint32_t*)0x40018044U) /**< \brief (TWI0) Filter Register */
  #define REG_TWI0_SWMR  (*(__IO uint32_t*)0x4001804CU) /**< \brief (TWI0) SleepWalking Matching Register */
  #define REG_TWI0_DR    (*(__I  uint32_t*)0x400180D0U) /**< \brief (TWI0) Debug Register */
  #define REG_TWI0_WPMR  (*(__IO uint32_t*)0x400180E4U) /**< \brief (TWI0) Protection Mode Register */
  #define REG_TWI0_WPSR  (*(__I  uint32_t*)0x400180E8U) /**< \brief (TWI0) Protection Status Register */
  #define REG_TWI0_VER   (*(__I  uint32_t*)0x400180FCU) /**< \brief (TWI0) Version Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAM_TWI0_INSTANCE_ */
