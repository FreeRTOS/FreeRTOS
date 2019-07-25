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

#ifndef _SAMV71_MLB_INSTANCE_
#define _SAMV71_MLB_INSTANCE_

/* ========== Register definition for MLB peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
  #define REG_MLB_MLBC0                  (0x40068000U) /**< \brief (MLB) MediaLB Control 0 Register */
  #define REG_MLB_MS0                    (0x4006800CU) /**< \brief (MLB) MediaLB Channel Status 0 Register */
  #define REG_MLB_MS1                    (0x40068014U) /**< \brief (MLB) MediaLB Channel Status1 Register */
  #define REG_MLB_MSS                    (0x40068020U) /**< \brief (MLB) MediaLB System Status Register */
  #define REG_MLB_MSD                    (0x40068024U) /**< \brief (MLB) MediaLB System Data Register */
  #define REG_MLB_MIEN                   (0x4006802CU) /**< \brief (MLB) MediaLB Interrupt Enable Register */
  #define REG_MLB_MLBC1                  (0x4006803CU) /**< \brief (MLB) MediaLB Control 1 Register */
  #define REG_MLB_HCTL                   (0x40068080U) /**< \brief (MLB) HBI Control Register */
  #define REG_MLB_HCMR                   (0x40068088U) /**< \brief (MLB) HBI Channel Mask 0 Register */
  #define REG_MLB_HCER                   (0x40068090U) /**< \brief (MLB) HBI Channel Error 0 Register */
  #define REG_MLB_HCBR                   (0x40068098U) /**< \brief (MLB) HBI Channel Busy 0 Register */
  #define REG_MLB_MDAT                   (0x400680C0U) /**< \brief (MLB) MIF Data 0 Register */
  #define REG_MLB_MDWE                   (0x400680D0U) /**< \brief (MLB) MIF Data Write Enable 0 Register */
  #define REG_MLB_MCTL                   (0x400680E0U) /**< \brief (MLB) MIF Control Register */
  #define REG_MLB_MADR                   (0x400680E4U) /**< \brief (MLB) MIF Address Register */
  #define REG_MLB_ACTL                   (0x400683C0U) /**< \brief (MLB) AHB Control Register */
  #define REG_MLB_ACSR                   (0x400683D0U) /**< \brief (MLB) AHB Channel Status 0 Register */
  #define REG_MLB_ACMR                   (0x400683D8U) /**< \brief (MLB) AHB Channel Mask 0 Register */
#else
  #define REG_MLB_MLBC0 (*(__IO uint32_t*)0x40068000U) /**< \brief (MLB) MediaLB Control 0 Register */
  #define REG_MLB_MS0   (*(__IO uint32_t*)0x4006800CU) /**< \brief (MLB) MediaLB Channel Status 0 Register */
  #define REG_MLB_MS1   (*(__IO uint32_t*)0x40068014U) /**< \brief (MLB) MediaLB Channel Status1 Register */
  #define REG_MLB_MSS   (*(__IO uint32_t*)0x40068020U) /**< \brief (MLB) MediaLB System Status Register */
  #define REG_MLB_MSD   (*(__I  uint32_t*)0x40068024U) /**< \brief (MLB) MediaLB System Data Register */
  #define REG_MLB_MIEN  (*(__IO uint32_t*)0x4006802CU) /**< \brief (MLB) MediaLB Interrupt Enable Register */
  #define REG_MLB_MLBC1 (*(__IO uint32_t*)0x4006803CU) /**< \brief (MLB) MediaLB Control 1 Register */
  #define REG_MLB_HCTL  (*(__IO uint32_t*)0x40068080U) /**< \brief (MLB) HBI Control Register */
  #define REG_MLB_HCMR  (*(__IO uint32_t*)0x40068088U) /**< \brief (MLB) HBI Channel Mask 0 Register */
  #define REG_MLB_HCER  (*(__I  uint32_t*)0x40068090U) /**< \brief (MLB) HBI Channel Error 0 Register */
  #define REG_MLB_HCBR  (*(__I  uint32_t*)0x40068098U) /**< \brief (MLB) HBI Channel Busy 0 Register */
  #define REG_MLB_MDAT  (*(__IO uint32_t*)0x400680C0U) /**< \brief (MLB) MIF Data 0 Register */
  #define REG_MLB_MDWE  (*(__IO uint32_t*)0x400680D0U) /**< \brief (MLB) MIF Data Write Enable 0 Register */
  #define REG_MLB_MCTL  (*(__IO uint32_t*)0x400680E0U) /**< \brief (MLB) MIF Control Register */
  #define REG_MLB_MADR  (*(__IO uint32_t*)0x400680E4U) /**< \brief (MLB) MIF Address Register */
  #define REG_MLB_ACTL  (*(__IO uint32_t*)0x400683C0U) /**< \brief (MLB) AHB Control Register */
  #define REG_MLB_ACSR  (*(__IO uint32_t*)0x400683D0U) /**< \brief (MLB) AHB Channel Status 0 Register */
  #define REG_MLB_ACMR  (*(__IO uint32_t*)0x400683D8U) /**< \brief (MLB) AHB Channel Mask 0 Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMV71_MLB_INSTANCE_ */
