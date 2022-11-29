/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2012, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following condition is met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

#ifndef _SAMA5_MATRIX_INSTANCE_
#define _SAMA5_MATRIX_INSTANCE_

/* ========== Register definition for MATRIX peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_MATRIX_MCFG              (0xFFFFEC00U) /**< \brief (MATRIX) Master Configuration Register */
#define REG_MATRIX_SCFG              (0xFFFFEC40U) /**< \brief (MATRIX) Slave Configuration Register */
#define REG_MATRIX_PRAS0             (0xFFFFEC80U) /**< \brief (MATRIX) Priority Register A for Slave 0 */
#define REG_MATRIX_PRBS0             (0xFFFFEC84U) /**< \brief (MATRIX) Priority Register B for Slave 0 */
#define REG_MATRIX_PRAS1             (0xFFFFEC88U) /**< \brief (MATRIX) Priority Register A for Slave 1 */
#define REG_MATRIX_PRBS1             (0xFFFFEC8CU) /**< \brief (MATRIX) Priority Register B for Slave 1 */
#define REG_MATRIX_PRAS2             (0xFFFFEC90U) /**< \brief (MATRIX) Priority Register A for Slave 2 */
#define REG_MATRIX_PRBS2             (0xFFFFEC94U) /**< \brief (MATRIX) Priority Register B for Slave 2 */
#define REG_MATRIX_PRAS3             (0xFFFFEC98U) /**< \brief (MATRIX) Priority Register A for Slave 3 */
#define REG_MATRIX_PRBS3             (0xFFFFEC9CU) /**< \brief (MATRIX) Priority Register B for Slave 3 */
#define REG_MATRIX_PRAS4             (0xFFFFECA0U) /**< \brief (MATRIX) Priority Register A for Slave 4 */
#define REG_MATRIX_PRBS4             (0xFFFFECA4U) /**< \brief (MATRIX) Priority Register B for Slave 4 */
#define REG_MATRIX_PRAS5             (0xFFFFECA8U) /**< \brief (MATRIX) Priority Register A for Slave 5 */
#define REG_MATRIX_PRBS5             (0xFFFFECACU) /**< \brief (MATRIX) Priority Register B for Slave 5 */
#define REG_MATRIX_PRAS6             (0xFFFFECB0U) /**< \brief (MATRIX) Priority Register A for Slave 6 */
#define REG_MATRIX_PRBS6             (0xFFFFECB4U) /**< \brief (MATRIX) Priority Register B for Slave 6 */
#define REG_MATRIX_PRAS7             (0xFFFFECB8U) /**< \brief (MATRIX) Priority Register A for Slave 7 */
#define REG_MATRIX_PRBS7             (0xFFFFECBCU) /**< \brief (MATRIX) Priority Register B for Slave 7 */
#define REG_MATRIX_PRAS8             (0xFFFFECC0U) /**< \brief (MATRIX) Priority Register A for Slave 8 */
#define REG_MATRIX_PRBS8             (0xFFFFECC4U) /**< \brief (MATRIX) Priority Register B for Slave 8 */
#define REG_MATRIX_PRAS9             (0xFFFFECC8U) /**< \brief (MATRIX) Priority Register A for Slave 9 */
#define REG_MATRIX_PRBS9             (0xFFFFECCCU) /**< \brief (MATRIX) Priority Register B for Slave 9 */
#define REG_MATRIX_PRAS10            (0xFFFFECD0U) /**< \brief (MATRIX) Priority Register A for Slave 10 */
#define REG_MATRIX_PRBS10            (0xFFFFECD4U) /**< \brief (MATRIX) Priority Register B for Slave 10 */
#define REG_MATRIX_PRAS11            (0xFFFFECD8U) /**< \brief (MATRIX) Priority Register A for Slave 11 */
#define REG_MATRIX_PRBS11            (0xFFFFECDCU) /**< \brief (MATRIX) Priority Register B for Slave 11 */
#define REG_MATRIX_PRAS12            (0xFFFFECE0U) /**< \brief (MATRIX) Priority Register A for Slave 12 */
#define REG_MATRIX_PRBS12            (0xFFFFECE4U) /**< \brief (MATRIX) Priority Register B for Slave 12 */
#define REG_MATRIX_PRAS13            (0xFFFFECE8U) /**< \brief (MATRIX) Priority Register A for Slave 13 */
#define REG_MATRIX_PRBS13            (0xFFFFECECU) /**< \brief (MATRIX) Priority Register B for Slave 13 */
#define REG_MATRIX_PRAS14            (0xFFFFECF0U) /**< \brief (MATRIX) Priority Register A for Slave 14 */
#define REG_MATRIX_PRBS14            (0xFFFFECF4U) /**< \brief (MATRIX) Priority Register B for Slave 14 */
#define REG_MATRIX_PRAS15            (0xFFFFECF8U) /**< \brief (MATRIX) Priority Register A for Slave 15 */
#define REG_MATRIX_PRBS15            (0xFFFFECFCU) /**< \brief (MATRIX) Priority Register B for Slave 15 */
#define REG_MATRIX_MRCR              (0xFFFFED00U) /**< \brief (MATRIX) Master Remap Control Register */
#define REG_MATRIX_SFR               (0xFFFFED10U) /**< \brief (MATRIX) Special Function Register */
#define REG_MATRIX_WPMR              (0xFFFFEDE4U) /**< \brief (MATRIX) Write Protect Mode Register */
#define REG_MATRIX_WPSR              (0xFFFFEDE8U) /**< \brief (MATRIX) Write Protect Status Register */
#else
#define REG_MATRIX_MCFG     (*(RwReg*)0xFFFFEC00U) /**< \brief (MATRIX) Master Configuration Register */
#define REG_MATRIX_SCFG     (*(RwReg*)0xFFFFEC40U) /**< \brief (MATRIX) Slave Configuration Register */
#define REG_MATRIX_PRAS0    (*(RwReg*)0xFFFFEC80U) /**< \brief (MATRIX) Priority Register A for Slave 0 */
#define REG_MATRIX_PRBS0    (*(RwReg*)0xFFFFEC84U) /**< \brief (MATRIX) Priority Register B for Slave 0 */
#define REG_MATRIX_PRAS1    (*(RwReg*)0xFFFFEC88U) /**< \brief (MATRIX) Priority Register A for Slave 1 */
#define REG_MATRIX_PRBS1    (*(RwReg*)0xFFFFEC8CU) /**< \brief (MATRIX) Priority Register B for Slave 1 */
#define REG_MATRIX_PRAS2    (*(RwReg*)0xFFFFEC90U) /**< \brief (MATRIX) Priority Register A for Slave 2 */
#define REG_MATRIX_PRBS2    (*(RwReg*)0xFFFFEC94U) /**< \brief (MATRIX) Priority Register B for Slave 2 */
#define REG_MATRIX_PRAS3    (*(RwReg*)0xFFFFEC98U) /**< \brief (MATRIX) Priority Register A for Slave 3 */
#define REG_MATRIX_PRBS3    (*(RwReg*)0xFFFFEC9CU) /**< \brief (MATRIX) Priority Register B for Slave 3 */
#define REG_MATRIX_PRAS4    (*(RwReg*)0xFFFFECA0U) /**< \brief (MATRIX) Priority Register A for Slave 4 */
#define REG_MATRIX_PRBS4    (*(RwReg*)0xFFFFECA4U) /**< \brief (MATRIX) Priority Register B for Slave 4 */
#define REG_MATRIX_PRAS5    (*(RwReg*)0xFFFFECA8U) /**< \brief (MATRIX) Priority Register A for Slave 5 */
#define REG_MATRIX_PRBS5    (*(RwReg*)0xFFFFECACU) /**< \brief (MATRIX) Priority Register B for Slave 5 */
#define REG_MATRIX_PRAS6    (*(RwReg*)0xFFFFECB0U) /**< \brief (MATRIX) Priority Register A for Slave 6 */
#define REG_MATRIX_PRBS6    (*(RwReg*)0xFFFFECB4U) /**< \brief (MATRIX) Priority Register B for Slave 6 */
#define REG_MATRIX_PRAS7    (*(RwReg*)0xFFFFECB8U) /**< \brief (MATRIX) Priority Register A for Slave 7 */
#define REG_MATRIX_PRBS7    (*(RwReg*)0xFFFFECBCU) /**< \brief (MATRIX) Priority Register B for Slave 7 */
#define REG_MATRIX_PRAS8    (*(RwReg*)0xFFFFECC0U) /**< \brief (MATRIX) Priority Register A for Slave 8 */
#define REG_MATRIX_PRBS8    (*(RwReg*)0xFFFFECC4U) /**< \brief (MATRIX) Priority Register B for Slave 8 */
#define REG_MATRIX_PRAS9    (*(RwReg*)0xFFFFECC8U) /**< \brief (MATRIX) Priority Register A for Slave 9 */
#define REG_MATRIX_PRBS9    (*(RwReg*)0xFFFFECCCU) /**< \brief (MATRIX) Priority Register B for Slave 9 */
#define REG_MATRIX_PRAS10   (*(RwReg*)0xFFFFECD0U) /**< \brief (MATRIX) Priority Register A for Slave 10 */
#define REG_MATRIX_PRBS10   (*(RwReg*)0xFFFFECD4U) /**< \brief (MATRIX) Priority Register B for Slave 10 */
#define REG_MATRIX_PRAS11   (*(RwReg*)0xFFFFECD8U) /**< \brief (MATRIX) Priority Register A for Slave 11 */
#define REG_MATRIX_PRBS11   (*(RwReg*)0xFFFFECDCU) /**< \brief (MATRIX) Priority Register B for Slave 11 */
#define REG_MATRIX_PRAS12   (*(RwReg*)0xFFFFECE0U) /**< \brief (MATRIX) Priority Register A for Slave 12 */
#define REG_MATRIX_PRBS12   (*(RwReg*)0xFFFFECE4U) /**< \brief (MATRIX) Priority Register B for Slave 12 */
#define REG_MATRIX_PRAS13   (*(RwReg*)0xFFFFECE8U) /**< \brief (MATRIX) Priority Register A for Slave 13 */
#define REG_MATRIX_PRBS13   (*(RwReg*)0xFFFFECECU) /**< \brief (MATRIX) Priority Register B for Slave 13 */
#define REG_MATRIX_PRAS14   (*(RwReg*)0xFFFFECF0U) /**< \brief (MATRIX) Priority Register A for Slave 14 */
#define REG_MATRIX_PRBS14   (*(RwReg*)0xFFFFECF4U) /**< \brief (MATRIX) Priority Register B for Slave 14 */
#define REG_MATRIX_PRAS15   (*(RwReg*)0xFFFFECF8U) /**< \brief (MATRIX) Priority Register A for Slave 15 */
#define REG_MATRIX_PRBS15   (*(RwReg*)0xFFFFECFCU) /**< \brief (MATRIX) Priority Register B for Slave 15 */
#define REG_MATRIX_MRCR     (*(RwReg*)0xFFFFED00U) /**< \brief (MATRIX) Master Remap Control Register */
#define REG_MATRIX_SFR      (*(RwReg*)0xFFFFED10U) /**< \brief (MATRIX) Special Function Register */
#define REG_MATRIX_WPMR     (*(RwReg*)0xFFFFEDE4U) /**< \brief (MATRIX) Write Protect Mode Register */
#define REG_MATRIX_WPSR     (*(RoReg*)0xFFFFEDE8U) /**< \brief (MATRIX) Write Protect Status Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_MATRIX_INSTANCE_ */
