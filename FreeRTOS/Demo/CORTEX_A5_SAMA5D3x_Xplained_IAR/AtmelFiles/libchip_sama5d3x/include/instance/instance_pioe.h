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

#ifndef _SAMA5_PIOE_INSTANCE_
#define _SAMA5_PIOE_INSTANCE_

/* ========== Register definition for PIOE peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_PIOE_PER                (0xFFFFFA00U) /**< \brief (PIOE) PIO Enable Register */
#define REG_PIOE_PDR                (0xFFFFFA04U) /**< \brief (PIOE) PIO Disable Register */
#define REG_PIOE_PSR                (0xFFFFFA08U) /**< \brief (PIOE) PIO Status Register */
#define REG_PIOE_OER                (0xFFFFFA10U) /**< \brief (PIOE) Output Enable Register */
#define REG_PIOE_ODR                (0xFFFFFA14U) /**< \brief (PIOE) Output Disable Register */
#define REG_PIOE_OSR                (0xFFFFFA18U) /**< \brief (PIOE) Output Status Register */
#define REG_PIOE_IFER               (0xFFFFFA20U) /**< \brief (PIOE) Glitch Input Filter Enable Register */
#define REG_PIOE_IFDR               (0xFFFFFA24U) /**< \brief (PIOE) Glitch Input Filter Disable Register */
#define REG_PIOE_IFSR               (0xFFFFFA28U) /**< \brief (PIOE) Glitch Input Filter Status Register */
#define REG_PIOE_SODR               (0xFFFFFA30U) /**< \brief (PIOE) Set Output Data Register */
#define REG_PIOE_CODR               (0xFFFFFA34U) /**< \brief (PIOE) Clear Output Data Register */
#define REG_PIOE_ODSR               (0xFFFFFA38U) /**< \brief (PIOE) Output Data Status Register */
#define REG_PIOE_PDSR               (0xFFFFFA3CU) /**< \brief (PIOE) Pin Data Status Register */
#define REG_PIOE_IER                (0xFFFFFA40U) /**< \brief (PIOE) Interrupt Enable Register */
#define REG_PIOE_IDR                (0xFFFFFA44U) /**< \brief (PIOE) Interrupt Disable Register */
#define REG_PIOE_IMR                (0xFFFFFA48U) /**< \brief (PIOE) Interrupt Mask Register */
#define REG_PIOE_ISR                (0xFFFFFA4CU) /**< \brief (PIOE) Interrupt Status Register */
#define REG_PIOE_MDER               (0xFFFFFA50U) /**< \brief (PIOE) Multi-driver Enable Register */
#define REG_PIOE_MDDR               (0xFFFFFA54U) /**< \brief (PIOE) Multi-driver Disable Register */
#define REG_PIOE_MDSR               (0xFFFFFA58U) /**< \brief (PIOE) Multi-driver Status Register */
#define REG_PIOE_PUDR               (0xFFFFFA60U) /**< \brief (PIOE) Pull-up Disable Register */
#define REG_PIOE_PUER               (0xFFFFFA64U) /**< \brief (PIOE) Pull-up Enable Register */
#define REG_PIOE_PUSR               (0xFFFFFA68U) /**< \brief (PIOE) Pad Pull-up Status Register */
#define REG_PIOE_ABCDSR             (0xFFFFFA70U) /**< \brief (PIOE) Peripheral Select Register */
#define REG_PIOE_IFSCDR             (0xFFFFFA80U) /**< \brief (PIOE) Input Filter Slow Clock Disable Register */
#define REG_PIOE_IFSCER             (0xFFFFFA84U) /**< \brief (PIOE) Input Filter Slow Clock Enable Register */
#define REG_PIOE_IFSCSR             (0xFFFFFA88U) /**< \brief (PIOE) Input Filter Slow Clock Status Register */
#define REG_PIOE_SCDR               (0xFFFFFA8CU) /**< \brief (PIOE) Slow Clock Divider Debouncing Register */
#define REG_PIOE_PPDDR              (0xFFFFFA90U) /**< \brief (PIOE) Pad Pull-down Disable Register */
#define REG_PIOE_PPDER              (0xFFFFFA94U) /**< \brief (PIOE) Pad Pull-down Enable Register */
#define REG_PIOE_PPDSR              (0xFFFFFA98U) /**< \brief (PIOE) Pad Pull-down Status Register */
#define REG_PIOE_OWER               (0xFFFFFAA0U) /**< \brief (PIOE) Output Write Enable */
#define REG_PIOE_OWDR               (0xFFFFFAA4U) /**< \brief (PIOE) Output Write Disable */
#define REG_PIOE_OWSR               (0xFFFFFAA8U) /**< \brief (PIOE) Output Write Status Register */
#define REG_PIOE_AIMER              (0xFFFFFAB0U) /**< \brief (PIOE) Additional Interrupt Modes Enable Register */
#define REG_PIOE_AIMDR              (0xFFFFFAB4U) /**< \brief (PIOE) Additional Interrupt Modes Disables Register */
#define REG_PIOE_AIMMR              (0xFFFFFAB8U) /**< \brief (PIOE) Additional Interrupt Modes Mask Register */
#define REG_PIOE_ESR                (0xFFFFFAC0U) /**< \brief (PIOE) Edge Select Register */
#define REG_PIOE_LSR                (0xFFFFFAC4U) /**< \brief (PIOE) Level Select Register */
#define REG_PIOE_ELSR               (0xFFFFFAC8U) /**< \brief (PIOE) Edge/Level Status Register */
#define REG_PIOE_FELLSR             (0xFFFFFAD0U) /**< \brief (PIOE) Falling Edge/Low Level Select Register */
#define REG_PIOE_REHLSR             (0xFFFFFAD4U) /**< \brief (PIOE) Rising Edge/ High Level Select Register */
#define REG_PIOE_FRLHSR             (0xFFFFFAD8U) /**< \brief (PIOE) Fall/Rise - Low/High Status Register */
#define REG_PIOE_LOCKSR             (0xFFFFFAE0U) /**< \brief (PIOE) Lock Status */
#define REG_PIOE_WPMR               (0xFFFFFAE4U) /**< \brief (PIOE) Write Protect Mode Register */
#define REG_PIOE_WPSR               (0xFFFFFAE8U) /**< \brief (PIOE) Write Protect Status Register */
#define REG_PIOE_SCHMITT            (0xFFFFFB00U) /**< \brief (PIOE) Schmitt Trigger Register */
#define REG_PIOE_DRIVER1            (0xFFFFFB18U) /**< \brief (PIOE) I/O Drive Register 1 */
#define REG_PIOE_DRIVER2            (0xFFFFFB1CU) /**< \brief (PIOE) I/O Drive Register 2 */
#else
#define REG_PIOE_PER       (*(WoReg*)0xFFFFFA00U) /**< \brief (PIOE) PIO Enable Register */
#define REG_PIOE_PDR       (*(WoReg*)0xFFFFFA04U) /**< \brief (PIOE) PIO Disable Register */
#define REG_PIOE_PSR       (*(RoReg*)0xFFFFFA08U) /**< \brief (PIOE) PIO Status Register */
#define REG_PIOE_OER       (*(WoReg*)0xFFFFFA10U) /**< \brief (PIOE) Output Enable Register */
#define REG_PIOE_ODR       (*(WoReg*)0xFFFFFA14U) /**< \brief (PIOE) Output Disable Register */
#define REG_PIOE_OSR       (*(RoReg*)0xFFFFFA18U) /**< \brief (PIOE) Output Status Register */
#define REG_PIOE_IFER      (*(WoReg*)0xFFFFFA20U) /**< \brief (PIOE) Glitch Input Filter Enable Register */
#define REG_PIOE_IFDR      (*(WoReg*)0xFFFFFA24U) /**< \brief (PIOE) Glitch Input Filter Disable Register */
#define REG_PIOE_IFSR      (*(RoReg*)0xFFFFFA28U) /**< \brief (PIOE) Glitch Input Filter Status Register */
#define REG_PIOE_SODR      (*(WoReg*)0xFFFFFA30U) /**< \brief (PIOE) Set Output Data Register */
#define REG_PIOE_CODR      (*(WoReg*)0xFFFFFA34U) /**< \brief (PIOE) Clear Output Data Register */
#define REG_PIOE_ODSR      (*(RwReg*)0xFFFFFA38U) /**< \brief (PIOE) Output Data Status Register */
#define REG_PIOE_PDSR      (*(RoReg*)0xFFFFFA3CU) /**< \brief (PIOE) Pin Data Status Register */
#define REG_PIOE_IER       (*(WoReg*)0xFFFFFA40U) /**< \brief (PIOE) Interrupt Enable Register */
#define REG_PIOE_IDR       (*(WoReg*)0xFFFFFA44U) /**< \brief (PIOE) Interrupt Disable Register */
#define REG_PIOE_IMR       (*(RoReg*)0xFFFFFA48U) /**< \brief (PIOE) Interrupt Mask Register */
#define REG_PIOE_ISR       (*(RoReg*)0xFFFFFA4CU) /**< \brief (PIOE) Interrupt Status Register */
#define REG_PIOE_MDER      (*(WoReg*)0xFFFFFA50U) /**< \brief (PIOE) Multi-driver Enable Register */
#define REG_PIOE_MDDR      (*(WoReg*)0xFFFFFA54U) /**< \brief (PIOE) Multi-driver Disable Register */
#define REG_PIOE_MDSR      (*(RoReg*)0xFFFFFA58U) /**< \brief (PIOE) Multi-driver Status Register */
#define REG_PIOE_PUDR      (*(WoReg*)0xFFFFFA60U) /**< \brief (PIOE) Pull-up Disable Register */
#define REG_PIOE_PUER      (*(WoReg*)0xFFFFFA64U) /**< \brief (PIOE) Pull-up Enable Register */
#define REG_PIOE_PUSR      (*(RoReg*)0xFFFFFA68U) /**< \brief (PIOE) Pad Pull-up Status Register */
#define REG_PIOE_ABCDSR    (*(RwReg*)0xFFFFFA70U) /**< \brief (PIOE) Peripheral Select Register */
#define REG_PIOE_IFSCDR    (*(WoReg*)0xFFFFFA80U) /**< \brief (PIOE) Input Filter Slow Clock Disable Register */
#define REG_PIOE_IFSCER    (*(WoReg*)0xFFFFFA84U) /**< \brief (PIOE) Input Filter Slow Clock Enable Register */
#define REG_PIOE_IFSCSR    (*(RoReg*)0xFFFFFA88U) /**< \brief (PIOE) Input Filter Slow Clock Status Register */
#define REG_PIOE_SCDR      (*(RwReg*)0xFFFFFA8CU) /**< \brief (PIOE) Slow Clock Divider Debouncing Register */
#define REG_PIOE_PPDDR     (*(WoReg*)0xFFFFFA90U) /**< \brief (PIOE) Pad Pull-down Disable Register */
#define REG_PIOE_PPDER     (*(WoReg*)0xFFFFFA94U) /**< \brief (PIOE) Pad Pull-down Enable Register */
#define REG_PIOE_PPDSR     (*(RoReg*)0xFFFFFA98U) /**< \brief (PIOE) Pad Pull-down Status Register */
#define REG_PIOE_OWER      (*(WoReg*)0xFFFFFAA0U) /**< \brief (PIOE) Output Write Enable */
#define REG_PIOE_OWDR      (*(WoReg*)0xFFFFFAA4U) /**< \brief (PIOE) Output Write Disable */
#define REG_PIOE_OWSR      (*(RoReg*)0xFFFFFAA8U) /**< \brief (PIOE) Output Write Status Register */
#define REG_PIOE_AIMER     (*(WoReg*)0xFFFFFAB0U) /**< \brief (PIOE) Additional Interrupt Modes Enable Register */
#define REG_PIOE_AIMDR     (*(WoReg*)0xFFFFFAB4U) /**< \brief (PIOE) Additional Interrupt Modes Disables Register */
#define REG_PIOE_AIMMR     (*(RoReg*)0xFFFFFAB8U) /**< \brief (PIOE) Additional Interrupt Modes Mask Register */
#define REG_PIOE_ESR       (*(WoReg*)0xFFFFFAC0U) /**< \brief (PIOE) Edge Select Register */
#define REG_PIOE_LSR       (*(WoReg*)0xFFFFFAC4U) /**< \brief (PIOE) Level Select Register */
#define REG_PIOE_ELSR      (*(RoReg*)0xFFFFFAC8U) /**< \brief (PIOE) Edge/Level Status Register */
#define REG_PIOE_FELLSR    (*(WoReg*)0xFFFFFAD0U) /**< \brief (PIOE) Falling Edge/Low Level Select Register */
#define REG_PIOE_REHLSR    (*(WoReg*)0xFFFFFAD4U) /**< \brief (PIOE) Rising Edge/ High Level Select Register */
#define REG_PIOE_FRLHSR    (*(RoReg*)0xFFFFFAD8U) /**< \brief (PIOE) Fall/Rise - Low/High Status Register */
#define REG_PIOE_LOCKSR    (*(RoReg*)0xFFFFFAE0U) /**< \brief (PIOE) Lock Status */
#define REG_PIOE_WPMR      (*(RwReg*)0xFFFFFAE4U) /**< \brief (PIOE) Write Protect Mode Register */
#define REG_PIOE_WPSR      (*(RoReg*)0xFFFFFAE8U) /**< \brief (PIOE) Write Protect Status Register */
#define REG_PIOE_SCHMITT   (*(RwReg*)0xFFFFFB00U) /**< \brief (PIOE) Schmitt Trigger Register */
#define REG_PIOE_DRIVER1   (*(RwReg*)0xFFFFFB18U) /**< \brief (PIOE) I/O Drive Register 1 */
#define REG_PIOE_DRIVER2   (*(RwReg*)0xFFFFFB1CU) /**< \brief (PIOE) I/O Drive Register 2 */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_PIOE_INSTANCE_ */
