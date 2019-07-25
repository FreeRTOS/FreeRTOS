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

#ifndef _SAMV71_MATRIX_INSTANCE_
#define _SAMV71_MATRIX_INSTANCE_

/* ========== Register definition for MATRIX peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
  #define REG_MATRIX_MCFG                   (0x40088000U) /**< \brief (MATRIX) Master Configuration Register */
  #define REG_MATRIX_SCFG                   (0x40088040U) /**< \brief (MATRIX) Slave Configuration Register */
  #define REG_MATRIX_PRAS0                  (0x40088080U) /**< \brief (MATRIX) Priority Register A for Slave 0 */
  #define REG_MATRIX_PRBS0                  (0x40088084U) /**< \brief (MATRIX) Priority Register B for Slave 0 */
  #define REG_MATRIX_PRAS1                  (0x40088088U) /**< \brief (MATRIX) Priority Register A for Slave 1 */
  #define REG_MATRIX_PRBS1                  (0x4008808CU) /**< \brief (MATRIX) Priority Register B for Slave 1 */
  #define REG_MATRIX_PRAS2                  (0x40088090U) /**< \brief (MATRIX) Priority Register A for Slave 2 */
  #define REG_MATRIX_PRBS2                  (0x40088094U) /**< \brief (MATRIX) Priority Register B for Slave 2 */
  #define REG_MATRIX_PRAS3                  (0x40088098U) /**< \brief (MATRIX) Priority Register A for Slave 3 */
  #define REG_MATRIX_PRBS3                  (0x4008809CU) /**< \brief (MATRIX) Priority Register B for Slave 3 */
  #define REG_MATRIX_PRAS4                  (0x400880A0U) /**< \brief (MATRIX) Priority Register A for Slave 4 */
  #define REG_MATRIX_PRBS4                  (0x400880A4U) /**< \brief (MATRIX) Priority Register B for Slave 4 */
  #define REG_MATRIX_PRAS5                  (0x400880A8U) /**< \brief (MATRIX) Priority Register A for Slave 5 */
  #define REG_MATRIX_PRBS5                  (0x400880ACU) /**< \brief (MATRIX) Priority Register B for Slave 5 */
  #define REG_MATRIX_PRAS6                  (0x400880B0U) /**< \brief (MATRIX) Priority Register A for Slave 6 */
  #define REG_MATRIX_PRBS6                  (0x400880B4U) /**< \brief (MATRIX) Priority Register B for Slave 6 */
  #define REG_MATRIX_PRAS7                  (0x400880B8U) /**< \brief (MATRIX) Priority Register A for Slave 7 */
  #define REG_MATRIX_PRBS7                  (0x400880BCU) /**< \brief (MATRIX) Priority Register B for Slave 7 */
  #define REG_MATRIX_PRAS8                  (0x400880C0U) /**< \brief (MATRIX) Priority Register A for Slave 8 */
  #define REG_MATRIX_PRBS8                  (0x400880C4U) /**< \brief (MATRIX) Priority Register B for Slave 8 */
  #define REG_MATRIX_MRCR                   (0x40088100U) /**< \brief (MATRIX) Master Remap Control Register */
  #define REG_CCFG_CAN0                     (0x40088110U) /**< \brief (MATRIX) CAN0 Configuration Register */
  #define REG_CCFG_SYSIO                    (0x40088114U) /**< \brief (MATRIX) System I/O and CAN1 Configuration Register */
  #define REG_CCFG_SMCNFCS                  (0x40088124U) /**< \brief (MATRIX) SMC NAND Flash Chip Select Configuration Register */
  #define REG_MATRIX_WPMR                   (0x400881E4U) /**< \brief (MATRIX) Write Protection Mode Register */
  #define REG_MATRIX_WPSR                   (0x400881E8U) /**< \brief (MATRIX) Write Protection Status Register */
#else
  #define REG_MATRIX_MCFG  (*(__IO uint32_t*)0x40088000U) /**< \brief (MATRIX) Master Configuration Register */
  #define REG_MATRIX_SCFG  (*(__IO uint32_t*)0x40088040U) /**< \brief (MATRIX) Slave Configuration Register */
  #define REG_MATRIX_PRAS0 (*(__IO uint32_t*)0x40088080U) /**< \brief (MATRIX) Priority Register A for Slave 0 */
  #define REG_MATRIX_PRBS0 (*(__IO uint32_t*)0x40088084U) /**< \brief (MATRIX) Priority Register B for Slave 0 */
  #define REG_MATRIX_PRAS1 (*(__IO uint32_t*)0x40088088U) /**< \brief (MATRIX) Priority Register A for Slave 1 */
  #define REG_MATRIX_PRBS1 (*(__IO uint32_t*)0x4008808CU) /**< \brief (MATRIX) Priority Register B for Slave 1 */
  #define REG_MATRIX_PRAS2 (*(__IO uint32_t*)0x40088090U) /**< \brief (MATRIX) Priority Register A for Slave 2 */
  #define REG_MATRIX_PRBS2 (*(__IO uint32_t*)0x40088094U) /**< \brief (MATRIX) Priority Register B for Slave 2 */
  #define REG_MATRIX_PRAS3 (*(__IO uint32_t*)0x40088098U) /**< \brief (MATRIX) Priority Register A for Slave 3 */
  #define REG_MATRIX_PRBS3 (*(__IO uint32_t*)0x4008809CU) /**< \brief (MATRIX) Priority Register B for Slave 3 */
  #define REG_MATRIX_PRAS4 (*(__IO uint32_t*)0x400880A0U) /**< \brief (MATRIX) Priority Register A for Slave 4 */
  #define REG_MATRIX_PRBS4 (*(__IO uint32_t*)0x400880A4U) /**< \brief (MATRIX) Priority Register B for Slave 4 */
  #define REG_MATRIX_PRAS5 (*(__IO uint32_t*)0x400880A8U) /**< \brief (MATRIX) Priority Register A for Slave 5 */
  #define REG_MATRIX_PRBS5 (*(__IO uint32_t*)0x400880ACU) /**< \brief (MATRIX) Priority Register B for Slave 5 */
  #define REG_MATRIX_PRAS6 (*(__IO uint32_t*)0x400880B0U) /**< \brief (MATRIX) Priority Register A for Slave 6 */
  #define REG_MATRIX_PRBS6 (*(__IO uint32_t*)0x400880B4U) /**< \brief (MATRIX) Priority Register B for Slave 6 */
  #define REG_MATRIX_PRAS7 (*(__IO uint32_t*)0x400880B8U) /**< \brief (MATRIX) Priority Register A for Slave 7 */
  #define REG_MATRIX_PRBS7 (*(__IO uint32_t*)0x400880BCU) /**< \brief (MATRIX) Priority Register B for Slave 7 */
  #define REG_MATRIX_PRAS8 (*(__IO uint32_t*)0x400880C0U) /**< \brief (MATRIX) Priority Register A for Slave 8 */
  #define REG_MATRIX_PRBS8 (*(__IO uint32_t*)0x400880C4U) /**< \brief (MATRIX) Priority Register B for Slave 8 */
  #define REG_MATRIX_MRCR  (*(__IO uint32_t*)0x40088100U) /**< \brief (MATRIX) Master Remap Control Register */
  #define REG_CCFG_CAN0    (*(__IO uint32_t*)0x40088110U) /**< \brief (MATRIX) CAN0 Configuration Register */
  #define REG_CCFG_SYSIO   (*(__IO uint32_t*)0x40088114U) /**< \brief (MATRIX) System I/O and CAN1 Configuration Register */
  #define REG_CCFG_SMCNFCS (*(__IO uint32_t*)0x40088124U) /**< \brief (MATRIX) SMC NAND Flash Chip Select Configuration Register */
  #define REG_MATRIX_WPMR  (*(__IO uint32_t*)0x400881E4U) /**< \brief (MATRIX) Write Protection Mode Register */
  #define REG_MATRIX_WPSR  (*(__I  uint32_t*)0x400881E8U) /**< \brief (MATRIX) Write Protection Status Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMV71_MATRIX_INSTANCE_ */
