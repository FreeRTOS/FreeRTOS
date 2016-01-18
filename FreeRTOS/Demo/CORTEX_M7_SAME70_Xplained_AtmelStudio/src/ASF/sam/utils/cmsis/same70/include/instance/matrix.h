/**
 * \file
 *
 * Copyright (c) 2015 Atmel Corporation. All rights reserved.
 *
 * \asf_license_start
 *
 * \page License
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 *
 * 3. The name of Atmel may not be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * 4. This software may only be redistributed and used in connection with an
 *    Atmel microcontroller product.
 *
 * THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * EXPRESSLY AND SPECIFICALLY DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
 * ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *
 * \asf_license_stop
 *
 */
/*
 * Support and FAQ: visit <a href="http://www.atmel.com/design-support/">Atmel Support</a>
 */

#ifndef _SAME70_MATRIX_INSTANCE_
#define _SAME70_MATRIX_INSTANCE_

/* ========== Register definition for MATRIX peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
  #define REG_MATRIX_MCFG0                   (0x40088000U) /**< \brief (MATRIX) Master Configuration Register 0 */
  #define REG_MATRIX_MCFG1                   (0x40088004U) /**< \brief (MATRIX) Master Configuration Register 1 */
  #define REG_MATRIX_MCFG2                   (0x40088008U) /**< \brief (MATRIX) Master Configuration Register 2 */
  #define REG_MATRIX_MCFG3                   (0x4008800CU) /**< \brief (MATRIX) Master Configuration Register 3 */
  #define REG_MATRIX_MCFG4                   (0x40088010U) /**< \brief (MATRIX) Master Configuration Register 4 */
  #define REG_MATRIX_MCFG5                   (0x40088014U) /**< \brief (MATRIX) Master Configuration Register 5 */
  #define REG_MATRIX_MCFG6                   (0x40088018U) /**< \brief (MATRIX) Master Configuration Register 6 */
  #define REG_MATRIX_MCFG8                   (0x40088020U) /**< \brief (MATRIX) Master Configuration Register 8 */
  #define REG_MATRIX_MCFG9                   (0x40088024U) /**< \brief (MATRIX) Master Configuration Register 9 */
  #define REG_MATRIX_MCFG10                  (0x40088028U) /**< \brief (MATRIX) Master Configuration Register 10 */
  #define REG_MATRIX_MCFG11                  (0x4008802CU) /**< \brief (MATRIX) Master Configuration Register 11 */
  #define REG_MATRIX_SCFG                    (0x40088040U) /**< \brief (MATRIX) Slave Configuration Register */
  #define REG_MATRIX_PRAS0                   (0x40088080U) /**< \brief (MATRIX) Priority Register A for Slave 0 */
  #define REG_MATRIX_PRBS0                   (0x40088084U) /**< \brief (MATRIX) Priority Register B for Slave 0 */
  #define REG_MATRIX_PRAS1                   (0x40088088U) /**< \brief (MATRIX) Priority Register A for Slave 1 */
  #define REG_MATRIX_PRBS1                   (0x4008808CU) /**< \brief (MATRIX) Priority Register B for Slave 1 */
  #define REG_MATRIX_PRAS2                   (0x40088090U) /**< \brief (MATRIX) Priority Register A for Slave 2 */
  #define REG_MATRIX_PRBS2                   (0x40088094U) /**< \brief (MATRIX) Priority Register B for Slave 2 */
  #define REG_MATRIX_PRAS3                   (0x40088098U) /**< \brief (MATRIX) Priority Register A for Slave 3 */
  #define REG_MATRIX_PRBS3                   (0x4008809CU) /**< \brief (MATRIX) Priority Register B for Slave 3 */
  #define REG_MATRIX_PRAS4                   (0x400880A0U) /**< \brief (MATRIX) Priority Register A for Slave 4 */
  #define REG_MATRIX_PRBS4                   (0x400880A4U) /**< \brief (MATRIX) Priority Register B for Slave 4 */
  #define REG_MATRIX_PRAS5                   (0x400880A8U) /**< \brief (MATRIX) Priority Register A for Slave 5 */
  #define REG_MATRIX_PRBS5                   (0x400880ACU) /**< \brief (MATRIX) Priority Register B for Slave 5 */
  #define REG_MATRIX_PRAS6                   (0x400880B0U) /**< \brief (MATRIX) Priority Register A for Slave 6 */
  #define REG_MATRIX_PRBS6                   (0x400880B4U) /**< \brief (MATRIX) Priority Register B for Slave 6 */
  #define REG_MATRIX_PRAS7                   (0x400880B8U) /**< \brief (MATRIX) Priority Register A for Slave 7 */
  #define REG_MATRIX_PRBS7                   (0x400880BCU) /**< \brief (MATRIX) Priority Register B for Slave 7 */
  #define REG_MATRIX_PRAS8                   (0x400880C0U) /**< \brief (MATRIX) Priority Register A for Slave 8 */
  #define REG_MATRIX_PRBS8                   (0x400880C4U) /**< \brief (MATRIX) Priority Register B for Slave 8 */
  #define REG_MATRIX_MRCR                    (0x40088100U) /**< \brief (MATRIX) Master Remap Control Register */
  #define REG_CCFG_CAN0                      (0x40088110U) /**< \brief (MATRIX) CAN0 Configuration Register */
  #define REG_CCFG_SYSIO                     (0x40088114U) /**< \brief (MATRIX) System I/O and CAN1 Configuration Register */
  #define REG_CCFG_SMCNFCS                   (0x40088124U) /**< \brief (MATRIX) SMC NAND Flash Chip Select Configuration Register */
  #define REG_MATRIX_WPMR                    (0x400881E4U) /**< \brief (MATRIX) Write Protection Mode Register */
  #define REG_MATRIX_WPSR                    (0x400881E8U) /**< \brief (MATRIX) Write Protection Status Register */
#else
  #define REG_MATRIX_MCFG0  (*(__IO uint32_t*)0x40088000U) /**< \brief (MATRIX) Master Configuration Register 0 */
  #define REG_MATRIX_MCFG1  (*(__IO uint32_t*)0x40088004U) /**< \brief (MATRIX) Master Configuration Register 1 */
  #define REG_MATRIX_MCFG2  (*(__IO uint32_t*)0x40088008U) /**< \brief (MATRIX) Master Configuration Register 2 */
  #define REG_MATRIX_MCFG3  (*(__IO uint32_t*)0x4008800CU) /**< \brief (MATRIX) Master Configuration Register 3 */
  #define REG_MATRIX_MCFG4  (*(__IO uint32_t*)0x40088010U) /**< \brief (MATRIX) Master Configuration Register 4 */
  #define REG_MATRIX_MCFG5  (*(__IO uint32_t*)0x40088014U) /**< \brief (MATRIX) Master Configuration Register 5 */
  #define REG_MATRIX_MCFG6  (*(__IO uint32_t*)0x40088018U) /**< \brief (MATRIX) Master Configuration Register 6 */
  #define REG_MATRIX_MCFG8  (*(__IO uint32_t*)0x40088020U) /**< \brief (MATRIX) Master Configuration Register 8 */
  #define REG_MATRIX_MCFG9  (*(__IO uint32_t*)0x40088024U) /**< \brief (MATRIX) Master Configuration Register 9 */
  #define REG_MATRIX_MCFG10 (*(__IO uint32_t*)0x40088028U) /**< \brief (MATRIX) Master Configuration Register 10 */
  #define REG_MATRIX_MCFG11 (*(__IO uint32_t*)0x4008802CU) /**< \brief (MATRIX) Master Configuration Register 11 */
  #define REG_MATRIX_SCFG   (*(__IO uint32_t*)0x40088040U) /**< \brief (MATRIX) Slave Configuration Register */
  #define REG_MATRIX_PRAS0  (*(__IO uint32_t*)0x40088080U) /**< \brief (MATRIX) Priority Register A for Slave 0 */
  #define REG_MATRIX_PRBS0  (*(__IO uint32_t*)0x40088084U) /**< \brief (MATRIX) Priority Register B for Slave 0 */
  #define REG_MATRIX_PRAS1  (*(__IO uint32_t*)0x40088088U) /**< \brief (MATRIX) Priority Register A for Slave 1 */
  #define REG_MATRIX_PRBS1  (*(__IO uint32_t*)0x4008808CU) /**< \brief (MATRIX) Priority Register B for Slave 1 */
  #define REG_MATRIX_PRAS2  (*(__IO uint32_t*)0x40088090U) /**< \brief (MATRIX) Priority Register A for Slave 2 */
  #define REG_MATRIX_PRBS2  (*(__IO uint32_t*)0x40088094U) /**< \brief (MATRIX) Priority Register B for Slave 2 */
  #define REG_MATRIX_PRAS3  (*(__IO uint32_t*)0x40088098U) /**< \brief (MATRIX) Priority Register A for Slave 3 */
  #define REG_MATRIX_PRBS3  (*(__IO uint32_t*)0x4008809CU) /**< \brief (MATRIX) Priority Register B for Slave 3 */
  #define REG_MATRIX_PRAS4  (*(__IO uint32_t*)0x400880A0U) /**< \brief (MATRIX) Priority Register A for Slave 4 */
  #define REG_MATRIX_PRBS4  (*(__IO uint32_t*)0x400880A4U) /**< \brief (MATRIX) Priority Register B for Slave 4 */
  #define REG_MATRIX_PRAS5  (*(__IO uint32_t*)0x400880A8U) /**< \brief (MATRIX) Priority Register A for Slave 5 */
  #define REG_MATRIX_PRBS5  (*(__IO uint32_t*)0x400880ACU) /**< \brief (MATRIX) Priority Register B for Slave 5 */
  #define REG_MATRIX_PRAS6  (*(__IO uint32_t*)0x400880B0U) /**< \brief (MATRIX) Priority Register A for Slave 6 */
  #define REG_MATRIX_PRBS6  (*(__IO uint32_t*)0x400880B4U) /**< \brief (MATRIX) Priority Register B for Slave 6 */
  #define REG_MATRIX_PRAS7  (*(__IO uint32_t*)0x400880B8U) /**< \brief (MATRIX) Priority Register A for Slave 7 */
  #define REG_MATRIX_PRBS7  (*(__IO uint32_t*)0x400880BCU) /**< \brief (MATRIX) Priority Register B for Slave 7 */
  #define REG_MATRIX_PRAS8  (*(__IO uint32_t*)0x400880C0U) /**< \brief (MATRIX) Priority Register A for Slave 8 */
  #define REG_MATRIX_PRBS8  (*(__IO uint32_t*)0x400880C4U) /**< \brief (MATRIX) Priority Register B for Slave 8 */
  #define REG_MATRIX_MRCR   (*(__IO uint32_t*)0x40088100U) /**< \brief (MATRIX) Master Remap Control Register */
  #define REG_CCFG_CAN0     (*(__IO uint32_t*)0x40088110U) /**< \brief (MATRIX) CAN0 Configuration Register */
  #define REG_CCFG_SYSIO    (*(__IO uint32_t*)0x40088114U) /**< \brief (MATRIX) System I/O and CAN1 Configuration Register */
  #define REG_CCFG_SMCNFCS  (*(__IO uint32_t*)0x40088124U) /**< \brief (MATRIX) SMC NAND Flash Chip Select Configuration Register */
  #define REG_MATRIX_WPMR   (*(__IO uint32_t*)0x400881E4U) /**< \brief (MATRIX) Write Protection Mode Register */
  #define REG_MATRIX_WPSR   (*(__I  uint32_t*)0x400881E8U) /**< \brief (MATRIX) Write Protection Status Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAME70_MATRIX_INSTANCE_ */
