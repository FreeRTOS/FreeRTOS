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

#ifndef _SAM_MATRIX_INSTANCE_
#define _SAM_MATRIX_INSTANCE_

/* ========== Register definition for MATRIX peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
  #define REG_MATRIX_MCFG                     (0x40088000U) /**< \brief (MATRIX) Master Configuration Register */
  #define REG_MATRIX_SCFG                     (0x40088040U) /**< \brief (MATRIX) Slave Configuration Register */
  #define REG_MATRIX_PRAS0                    (0x40088080U) /**< \brief (MATRIX) Priority Register A for Slave 0 */
  #define REG_MATRIX_PRBS0                    (0x40088084U) /**< \brief (MATRIX) Priority Register B for Slave 0 */
  #define REG_MATRIX_PRAS1                    (0x40088088U) /**< \brief (MATRIX) Priority Register A for Slave 1 */
  #define REG_MATRIX_PRBS1                    (0x4008808CU) /**< \brief (MATRIX) Priority Register B for Slave 1 */
  #define REG_MATRIX_PRAS2                    (0x40088090U) /**< \brief (MATRIX) Priority Register A for Slave 2 */
  #define REG_MATRIX_PRBS2                    (0x40088094U) /**< \brief (MATRIX) Priority Register B for Slave 2 */
  #define REG_MATRIX_PRAS3                    (0x40088098U) /**< \brief (MATRIX) Priority Register A for Slave 3 */
  #define REG_MATRIX_PRBS3                    (0x4008809CU) /**< \brief (MATRIX) Priority Register B for Slave 3 */
  #define REG_MATRIX_PRAS4                    (0x400880A0U) /**< \brief (MATRIX) Priority Register A for Slave 4 */
  #define REG_MATRIX_PRBS4                    (0x400880A4U) /**< \brief (MATRIX) Priority Register B for Slave 4 */
  #define REG_MATRIX_PRAS5                    (0x400880A8U) /**< \brief (MATRIX) Priority Register A for Slave 5 */
  #define REG_MATRIX_PRBS5                    (0x400880ACU) /**< \brief (MATRIX) Priority Register B for Slave 5 */
  #define REG_MATRIX_PRAS6                    (0x400880B0U) /**< \brief (MATRIX) Priority Register A for Slave 6 */
  #define REG_MATRIX_PRBS6                    (0x400880B4U) /**< \brief (MATRIX) Priority Register B for Slave 6 */
  #define REG_MATRIX_PRAS7                    (0x400880B8U) /**< \brief (MATRIX) Priority Register A for Slave 7 */
  #define REG_MATRIX_PRBS7                    (0x400880BCU) /**< \brief (MATRIX) Priority Register B for Slave 7 */
  #define REG_MATRIX_PRAS8                    (0x400880C0U) /**< \brief (MATRIX) Priority Register A for Slave 8 */
  #define REG_MATRIX_PRBS8                    (0x400880C4U) /**< \brief (MATRIX) Priority Register B for Slave 8 */
  #define REG_MATRIX_PRAS9                    (0x400880C8U) /**< \brief (MATRIX) Priority Register A for Slave 9 */
  #define REG_MATRIX_PRBS9                    (0x400880CCU) /**< \brief (MATRIX) Priority Register B for Slave 9 */
  #define REG_MATRIX_PRAS10                   (0x400880D0U) /**< \brief (MATRIX) Priority Register A for Slave 10 */
  #define REG_MATRIX_PRBS10                   (0x400880D4U) /**< \brief (MATRIX) Priority Register B for Slave 10 */
  #define REG_MATRIX_PRAS11                   (0x400880D8U) /**< \brief (MATRIX) Priority Register A for Slave 11 */
  #define REG_MATRIX_PRBS11                   (0x400880DCU) /**< \brief (MATRIX) Priority Register B for Slave 11 */
  #define REG_MATRIX_PRAS12                   (0x400880E0U) /**< \brief (MATRIX) Priority Register A for Slave 12 */
  #define REG_MATRIX_PRBS12                   (0x400880E4U) /**< \brief (MATRIX) Priority Register B for Slave 12 */
  #define REG_MATRIX_PRAS13                   (0x400880E8U) /**< \brief (MATRIX) Priority Register A for Slave 13 */
  #define REG_MATRIX_PRBS13                   (0x400880ECU) /**< \brief (MATRIX) Priority Register B for Slave 13 */
  #define REG_MATRIX_PRAS14                   (0x400880F0U) /**< \brief (MATRIX) Priority Register A for Slave 14 */
  #define REG_MATRIX_PRBS14                   (0x400880F4U) /**< \brief (MATRIX) Priority Register B for Slave 14 */
  #define REG_MATRIX_PRAS15                   (0x400880F8U) /**< \brief (MATRIX) Priority Register A for Slave 15 */
  #define REG_MATRIX_PRBS15                   (0x400880FCU) /**< \brief (MATRIX) Priority Register B for Slave 15 */
  #define REG_MATRIX_MRCR                     (0x40088100U) /**< \brief (MATRIX) Master Remap Control Register */
  #define REG_MATRIX_SFR                      (0x40088110U) /**< \brief (MATRIX) Special Function Register */
  #define REG_MATRIX_MEIER                    (0x40088150U) /**< \brief (MATRIX) Master Error Interrupt Enable Register */
  #define REG_MATRIX_MEIDR                    (0x40088154U) /**< \brief (MATRIX) Master Error Interrupt Disable Register */
  #define REG_MATRIX_MEIMR                    (0x40088158U) /**< \brief (MATRIX) Master Error Interrupt Mask Register */
  #define REG_MATRIX_MESR                     (0x4008815CU) /**< \brief (MATRIX) Master Error Status Register */
  #define REG_MATRIX_MEAR                     (0x40088160U) /**< \brief (MATRIX) Master 0 Error Address Register */
  #define REG_MATRIX_WPMR                     (0x400881E4U) /**< \brief (MATRIX) Write Protect Mode Register */
  #define REG_MATRIX_WPSR                     (0x400881E8U) /**< \brief (MATRIX) Write Protect Status Register */
  #define REG_MATRIX_VERSION                  (0x400881FCU) /**< \brief (MATRIX) Version Register */
  #define REG_MATRIX_SSR                      (0x40088200U) /**< \brief (MATRIX) Security Slave 0 Register */
  #define REG_MATRIX_SASSR                    (0x40088240U) /**< \brief (MATRIX) Security Areas Split Slave 0 Register */
  #define REG_MATRIX_SRTSR                    (0x40088280U) /**< \brief (MATRIX) Security Region Top Slave 0 Register */
  #define REG_MATRIX_SPSELR                   (0x400882C0U) /**< \brief (MATRIX) Security Peripheral Select 1 Register */
#else
  #define REG_MATRIX_MCFG    (*(__IO uint32_t*)0x40088000U) /**< \brief (MATRIX) Master Configuration Register */
  #define REG_MATRIX_SCFG    (*(__IO uint32_t*)0x40088040U) /**< \brief (MATRIX) Slave Configuration Register */
  #define REG_MATRIX_PRAS0   (*(__IO uint32_t*)0x40088080U) /**< \brief (MATRIX) Priority Register A for Slave 0 */
  #define REG_MATRIX_PRBS0   (*(__IO uint32_t*)0x40088084U) /**< \brief (MATRIX) Priority Register B for Slave 0 */
  #define REG_MATRIX_PRAS1   (*(__IO uint32_t*)0x40088088U) /**< \brief (MATRIX) Priority Register A for Slave 1 */
  #define REG_MATRIX_PRBS1   (*(__IO uint32_t*)0x4008808CU) /**< \brief (MATRIX) Priority Register B for Slave 1 */
  #define REG_MATRIX_PRAS2   (*(__IO uint32_t*)0x40088090U) /**< \brief (MATRIX) Priority Register A for Slave 2 */
  #define REG_MATRIX_PRBS2   (*(__IO uint32_t*)0x40088094U) /**< \brief (MATRIX) Priority Register B for Slave 2 */
  #define REG_MATRIX_PRAS3   (*(__IO uint32_t*)0x40088098U) /**< \brief (MATRIX) Priority Register A for Slave 3 */
  #define REG_MATRIX_PRBS3   (*(__IO uint32_t*)0x4008809CU) /**< \brief (MATRIX) Priority Register B for Slave 3 */
  #define REG_MATRIX_PRAS4   (*(__IO uint32_t*)0x400880A0U) /**< \brief (MATRIX) Priority Register A for Slave 4 */
  #define REG_MATRIX_PRBS4   (*(__IO uint32_t*)0x400880A4U) /**< \brief (MATRIX) Priority Register B for Slave 4 */
  #define REG_MATRIX_PRAS5   (*(__IO uint32_t*)0x400880A8U) /**< \brief (MATRIX) Priority Register A for Slave 5 */
  #define REG_MATRIX_PRBS5   (*(__IO uint32_t*)0x400880ACU) /**< \brief (MATRIX) Priority Register B for Slave 5 */
  #define REG_MATRIX_PRAS6   (*(__IO uint32_t*)0x400880B0U) /**< \brief (MATRIX) Priority Register A for Slave 6 */
  #define REG_MATRIX_PRBS6   (*(__IO uint32_t*)0x400880B4U) /**< \brief (MATRIX) Priority Register B for Slave 6 */
  #define REG_MATRIX_PRAS7   (*(__IO uint32_t*)0x400880B8U) /**< \brief (MATRIX) Priority Register A for Slave 7 */
  #define REG_MATRIX_PRBS7   (*(__IO uint32_t*)0x400880BCU) /**< \brief (MATRIX) Priority Register B for Slave 7 */
  #define REG_MATRIX_PRAS8   (*(__IO uint32_t*)0x400880C0U) /**< \brief (MATRIX) Priority Register A for Slave 8 */
  #define REG_MATRIX_PRBS8   (*(__IO uint32_t*)0x400880C4U) /**< \brief (MATRIX) Priority Register B for Slave 8 */
  #define REG_MATRIX_PRAS9   (*(__IO uint32_t*)0x400880C8U) /**< \brief (MATRIX) Priority Register A for Slave 9 */
  #define REG_MATRIX_PRBS9   (*(__IO uint32_t*)0x400880CCU) /**< \brief (MATRIX) Priority Register B for Slave 9 */
  #define REG_MATRIX_PRAS10  (*(__IO uint32_t*)0x400880D0U) /**< \brief (MATRIX) Priority Register A for Slave 10 */
  #define REG_MATRIX_PRBS10  (*(__IO uint32_t*)0x400880D4U) /**< \brief (MATRIX) Priority Register B for Slave 10 */
  #define REG_MATRIX_PRAS11  (*(__IO uint32_t*)0x400880D8U) /**< \brief (MATRIX) Priority Register A for Slave 11 */
  #define REG_MATRIX_PRBS11  (*(__IO uint32_t*)0x400880DCU) /**< \brief (MATRIX) Priority Register B for Slave 11 */
  #define REG_MATRIX_PRAS12  (*(__IO uint32_t*)0x400880E0U) /**< \brief (MATRIX) Priority Register A for Slave 12 */
  #define REG_MATRIX_PRBS12  (*(__IO uint32_t*)0x400880E4U) /**< \brief (MATRIX) Priority Register B for Slave 12 */
  #define REG_MATRIX_PRAS13  (*(__IO uint32_t*)0x400880E8U) /**< \brief (MATRIX) Priority Register A for Slave 13 */
  #define REG_MATRIX_PRBS13  (*(__IO uint32_t*)0x400880ECU) /**< \brief (MATRIX) Priority Register B for Slave 13 */
  #define REG_MATRIX_PRAS14  (*(__IO uint32_t*)0x400880F0U) /**< \brief (MATRIX) Priority Register A for Slave 14 */
  #define REG_MATRIX_PRBS14  (*(__IO uint32_t*)0x400880F4U) /**< \brief (MATRIX) Priority Register B for Slave 14 */
  #define REG_MATRIX_PRAS15  (*(__IO uint32_t*)0x400880F8U) /**< \brief (MATRIX) Priority Register A for Slave 15 */
  #define REG_MATRIX_PRBS15  (*(__IO uint32_t*)0x400880FCU) /**< \brief (MATRIX) Priority Register B for Slave 15 */
  #define REG_MATRIX_MRCR    (*(__IO uint32_t*)0x40088100U) /**< \brief (MATRIX) Master Remap Control Register */
  #define REG_MATRIX_SFR     (*(__IO uint32_t*)0x40088110U) /**< \brief (MATRIX) Special Function Register */
  #define REG_MATRIX_MEIER   (*(__O  uint32_t*)0x40088150U) /**< \brief (MATRIX) Master Error Interrupt Enable Register */
  #define REG_MATRIX_MEIDR   (*(__O  uint32_t*)0x40088154U) /**< \brief (MATRIX) Master Error Interrupt Disable Register */
  #define REG_MATRIX_MEIMR   (*(__I  uint32_t*)0x40088158U) /**< \brief (MATRIX) Master Error Interrupt Mask Register */
  #define REG_MATRIX_MESR    (*(__I  uint32_t*)0x4008815CU) /**< \brief (MATRIX) Master Error Status Register */
  #define REG_MATRIX_MEAR    (*(__I  uint32_t*)0x40088160U) /**< \brief (MATRIX) Master 0 Error Address Register */
  #define REG_MATRIX_WPMR    (*(__IO uint32_t*)0x400881E4U) /**< \brief (MATRIX) Write Protect Mode Register */
  #define REG_MATRIX_WPSR    (*(__I  uint32_t*)0x400881E8U) /**< \brief (MATRIX) Write Protect Status Register */
  #define REG_MATRIX_VERSION (*(__I  uint32_t*)0x400881FCU) /**< \brief (MATRIX) Version Register */
  #define REG_MATRIX_SSR     (*(__IO uint32_t*)0x40088200U) /**< \brief (MATRIX) Security Slave 0 Register */
  #define REG_MATRIX_SASSR   (*(__IO uint32_t*)0x40088240U) /**< \brief (MATRIX) Security Areas Split Slave 0 Register */
  #define REG_MATRIX_SRTSR   (*(__IO uint32_t*)0x40088280U) /**< \brief (MATRIX) Security Region Top Slave 0 Register */
  #define REG_MATRIX_SPSELR  (*(__IO uint32_t*)0x400882C0U) /**< \brief (MATRIX) Security Peripheral Select 1 Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAM_MATRIX_INSTANCE_ */
