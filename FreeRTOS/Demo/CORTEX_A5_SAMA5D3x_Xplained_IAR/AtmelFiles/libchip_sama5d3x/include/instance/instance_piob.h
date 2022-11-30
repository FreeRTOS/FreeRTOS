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

#ifndef _SAMA5_PIOB_INSTANCE_
#define _SAMA5_PIOB_INSTANCE_

/* ========== Register definition for PIOB peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_PIOB_PER                (0xFFFFF400U) /**< \brief (PIOB) PIO Enable Register */
#define REG_PIOB_PDR                (0xFFFFF404U) /**< \brief (PIOB) PIO Disable Register */
#define REG_PIOB_PSR                (0xFFFFF408U) /**< \brief (PIOB) PIO Status Register */
#define REG_PIOB_OER                (0xFFFFF410U) /**< \brief (PIOB) Output Enable Register */
#define REG_PIOB_ODR                (0xFFFFF414U) /**< \brief (PIOB) Output Disable Register */
#define REG_PIOB_OSR                (0xFFFFF418U) /**< \brief (PIOB) Output Status Register */
#define REG_PIOB_IFER               (0xFFFFF420U) /**< \brief (PIOB) Glitch Input Filter Enable Register */
#define REG_PIOB_IFDR               (0xFFFFF424U) /**< \brief (PIOB) Glitch Input Filter Disable Register */
#define REG_PIOB_IFSR               (0xFFFFF428U) /**< \brief (PIOB) Glitch Input Filter Status Register */
#define REG_PIOB_SODR               (0xFFFFF430U) /**< \brief (PIOB) Set Output Data Register */
#define REG_PIOB_CODR               (0xFFFFF434U) /**< \brief (PIOB) Clear Output Data Register */
#define REG_PIOB_ODSR               (0xFFFFF438U) /**< \brief (PIOB) Output Data Status Register */
#define REG_PIOB_PDSR               (0xFFFFF43CU) /**< \brief (PIOB) Pin Data Status Register */
#define REG_PIOB_IER                (0xFFFFF440U) /**< \brief (PIOB) Interrupt Enable Register */
#define REG_PIOB_IDR                (0xFFFFF444U) /**< \brief (PIOB) Interrupt Disable Register */
#define REG_PIOB_IMR                (0xFFFFF448U) /**< \brief (PIOB) Interrupt Mask Register */
#define REG_PIOB_ISR                (0xFFFFF44CU) /**< \brief (PIOB) Interrupt Status Register */
#define REG_PIOB_MDER               (0xFFFFF450U) /**< \brief (PIOB) Multi-driver Enable Register */
#define REG_PIOB_MDDR               (0xFFFFF454U) /**< \brief (PIOB) Multi-driver Disable Register */
#define REG_PIOB_MDSR               (0xFFFFF458U) /**< \brief (PIOB) Multi-driver Status Register */
#define REG_PIOB_PUDR               (0xFFFFF460U) /**< \brief (PIOB) Pull-up Disable Register */
#define REG_PIOB_PUER               (0xFFFFF464U) /**< \brief (PIOB) Pull-up Enable Register */
#define REG_PIOB_PUSR               (0xFFFFF468U) /**< \brief (PIOB) Pad Pull-up Status Register */
#define REG_PIOB_ABCDSR             (0xFFFFF470U) /**< \brief (PIOB) Peripheral Select Register */
#define REG_PIOB_IFSCDR             (0xFFFFF480U) /**< \brief (PIOB) Input Filter Slow Clock Disable Register */
#define REG_PIOB_IFSCER             (0xFFFFF484U) /**< \brief (PIOB) Input Filter Slow Clock Enable Register */
#define REG_PIOB_IFSCSR             (0xFFFFF488U) /**< \brief (PIOB) Input Filter Slow Clock Status Register */
#define REG_PIOB_SCDR               (0xFFFFF48CU) /**< \brief (PIOB) Slow Clock Divider Debouncing Register */
#define REG_PIOB_PPDDR              (0xFFFFF490U) /**< \brief (PIOB) Pad Pull-down Disable Register */
#define REG_PIOB_PPDER              (0xFFFFF494U) /**< \brief (PIOB) Pad Pull-down Enable Register */
#define REG_PIOB_PPDSR              (0xFFFFF498U) /**< \brief (PIOB) Pad Pull-down Status Register */
#define REG_PIOB_OWER               (0xFFFFF4A0U) /**< \brief (PIOB) Output Write Enable */
#define REG_PIOB_OWDR               (0xFFFFF4A4U) /**< \brief (PIOB) Output Write Disable */
#define REG_PIOB_OWSR               (0xFFFFF4A8U) /**< \brief (PIOB) Output Write Status Register */
#define REG_PIOB_AIMER              (0xFFFFF4B0U) /**< \brief (PIOB) Additional Interrupt Modes Enable Register */
#define REG_PIOB_AIMDR              (0xFFFFF4B4U) /**< \brief (PIOB) Additional Interrupt Modes Disables Register */
#define REG_PIOB_AIMMR              (0xFFFFF4B8U) /**< \brief (PIOB) Additional Interrupt Modes Mask Register */
#define REG_PIOB_ESR                (0xFFFFF4C0U) /**< \brief (PIOB) Edge Select Register */
#define REG_PIOB_LSR                (0xFFFFF4C4U) /**< \brief (PIOB) Level Select Register */
#define REG_PIOB_ELSR               (0xFFFFF4C8U) /**< \brief (PIOB) Edge/Level Status Register */
#define REG_PIOB_FELLSR             (0xFFFFF4D0U) /**< \brief (PIOB) Falling Edge/Low Level Select Register */
#define REG_PIOB_REHLSR             (0xFFFFF4D4U) /**< \brief (PIOB) Rising Edge/ High Level Select Register */
#define REG_PIOB_FRLHSR             (0xFFFFF4D8U) /**< \brief (PIOB) Fall/Rise - Low/High Status Register */
#define REG_PIOB_LOCKSR             (0xFFFFF4E0U) /**< \brief (PIOB) Lock Status */
#define REG_PIOB_WPMR               (0xFFFFF4E4U) /**< \brief (PIOB) Write Protect Mode Register */
#define REG_PIOB_WPSR               (0xFFFFF4E8U) /**< \brief (PIOB) Write Protect Status Register */
#define REG_PIOB_SCHMITT            (0xFFFFF500U) /**< \brief (PIOB) Schmitt Trigger Register */
#define REG_PIOB_DRIVER1            (0xFFFFF518U) /**< \brief (PIOB) I/O Drive Register 1 */
#define REG_PIOB_DRIVER2            (0xFFFFF51CU) /**< \brief (PIOB) I/O Drive Register 2 */
#else
#define REG_PIOB_PER       (*(WoReg*)0xFFFFF400U) /**< \brief (PIOB) PIO Enable Register */
#define REG_PIOB_PDR       (*(WoReg*)0xFFFFF404U) /**< \brief (PIOB) PIO Disable Register */
#define REG_PIOB_PSR       (*(RoReg*)0xFFFFF408U) /**< \brief (PIOB) PIO Status Register */
#define REG_PIOB_OER       (*(WoReg*)0xFFFFF410U) /**< \brief (PIOB) Output Enable Register */
#define REG_PIOB_ODR       (*(WoReg*)0xFFFFF414U) /**< \brief (PIOB) Output Disable Register */
#define REG_PIOB_OSR       (*(RoReg*)0xFFFFF418U) /**< \brief (PIOB) Output Status Register */
#define REG_PIOB_IFER      (*(WoReg*)0xFFFFF420U) /**< \brief (PIOB) Glitch Input Filter Enable Register */
#define REG_PIOB_IFDR      (*(WoReg*)0xFFFFF424U) /**< \brief (PIOB) Glitch Input Filter Disable Register */
#define REG_PIOB_IFSR      (*(RoReg*)0xFFFFF428U) /**< \brief (PIOB) Glitch Input Filter Status Register */
#define REG_PIOB_SODR      (*(WoReg*)0xFFFFF430U) /**< \brief (PIOB) Set Output Data Register */
#define REG_PIOB_CODR      (*(WoReg*)0xFFFFF434U) /**< \brief (PIOB) Clear Output Data Register */
#define REG_PIOB_ODSR      (*(RwReg*)0xFFFFF438U) /**< \brief (PIOB) Output Data Status Register */
#define REG_PIOB_PDSR      (*(RoReg*)0xFFFFF43CU) /**< \brief (PIOB) Pin Data Status Register */
#define REG_PIOB_IER       (*(WoReg*)0xFFFFF440U) /**< \brief (PIOB) Interrupt Enable Register */
#define REG_PIOB_IDR       (*(WoReg*)0xFFFFF444U) /**< \brief (PIOB) Interrupt Disable Register */
#define REG_PIOB_IMR       (*(RoReg*)0xFFFFF448U) /**< \brief (PIOB) Interrupt Mask Register */
#define REG_PIOB_ISR       (*(RoReg*)0xFFFFF44CU) /**< \brief (PIOB) Interrupt Status Register */
#define REG_PIOB_MDER      (*(WoReg*)0xFFFFF450U) /**< \brief (PIOB) Multi-driver Enable Register */
#define REG_PIOB_MDDR      (*(WoReg*)0xFFFFF454U) /**< \brief (PIOB) Multi-driver Disable Register */
#define REG_PIOB_MDSR      (*(RoReg*)0xFFFFF458U) /**< \brief (PIOB) Multi-driver Status Register */
#define REG_PIOB_PUDR      (*(WoReg*)0xFFFFF460U) /**< \brief (PIOB) Pull-up Disable Register */
#define REG_PIOB_PUER      (*(WoReg*)0xFFFFF464U) /**< \brief (PIOB) Pull-up Enable Register */
#define REG_PIOB_PUSR      (*(RoReg*)0xFFFFF468U) /**< \brief (PIOB) Pad Pull-up Status Register */
#define REG_PIOB_ABCDSR    (*(RwReg*)0xFFFFF470U) /**< \brief (PIOB) Peripheral Select Register */
#define REG_PIOB_IFSCDR    (*(WoReg*)0xFFFFF480U) /**< \brief (PIOB) Input Filter Slow Clock Disable Register */
#define REG_PIOB_IFSCER    (*(WoReg*)0xFFFFF484U) /**< \brief (PIOB) Input Filter Slow Clock Enable Register */
#define REG_PIOB_IFSCSR    (*(RoReg*)0xFFFFF488U) /**< \brief (PIOB) Input Filter Slow Clock Status Register */
#define REG_PIOB_SCDR      (*(RwReg*)0xFFFFF48CU) /**< \brief (PIOB) Slow Clock Divider Debouncing Register */
#define REG_PIOB_PPDDR     (*(WoReg*)0xFFFFF490U) /**< \brief (PIOB) Pad Pull-down Disable Register */
#define REG_PIOB_PPDER     (*(WoReg*)0xFFFFF494U) /**< \brief (PIOB) Pad Pull-down Enable Register */
#define REG_PIOB_PPDSR     (*(RoReg*)0xFFFFF498U) /**< \brief (PIOB) Pad Pull-down Status Register */
#define REG_PIOB_OWER      (*(WoReg*)0xFFFFF4A0U) /**< \brief (PIOB) Output Write Enable */
#define REG_PIOB_OWDR      (*(WoReg*)0xFFFFF4A4U) /**< \brief (PIOB) Output Write Disable */
#define REG_PIOB_OWSR      (*(RoReg*)0xFFFFF4A8U) /**< \brief (PIOB) Output Write Status Register */
#define REG_PIOB_AIMER     (*(WoReg*)0xFFFFF4B0U) /**< \brief (PIOB) Additional Interrupt Modes Enable Register */
#define REG_PIOB_AIMDR     (*(WoReg*)0xFFFFF4B4U) /**< \brief (PIOB) Additional Interrupt Modes Disables Register */
#define REG_PIOB_AIMMR     (*(RoReg*)0xFFFFF4B8U) /**< \brief (PIOB) Additional Interrupt Modes Mask Register */
#define REG_PIOB_ESR       (*(WoReg*)0xFFFFF4C0U) /**< \brief (PIOB) Edge Select Register */
#define REG_PIOB_LSR       (*(WoReg*)0xFFFFF4C4U) /**< \brief (PIOB) Level Select Register */
#define REG_PIOB_ELSR      (*(RoReg*)0xFFFFF4C8U) /**< \brief (PIOB) Edge/Level Status Register */
#define REG_PIOB_FELLSR    (*(WoReg*)0xFFFFF4D0U) /**< \brief (PIOB) Falling Edge/Low Level Select Register */
#define REG_PIOB_REHLSR    (*(WoReg*)0xFFFFF4D4U) /**< \brief (PIOB) Rising Edge/ High Level Select Register */
#define REG_PIOB_FRLHSR    (*(RoReg*)0xFFFFF4D8U) /**< \brief (PIOB) Fall/Rise - Low/High Status Register */
#define REG_PIOB_LOCKSR    (*(RoReg*)0xFFFFF4E0U) /**< \brief (PIOB) Lock Status */
#define REG_PIOB_WPMR      (*(RwReg*)0xFFFFF4E4U) /**< \brief (PIOB) Write Protect Mode Register */
#define REG_PIOB_WPSR      (*(RoReg*)0xFFFFF4E8U) /**< \brief (PIOB) Write Protect Status Register */
#define REG_PIOB_SCHMITT   (*(RwReg*)0xFFFFF500U) /**< \brief (PIOB) Schmitt Trigger Register */
#define REG_PIOB_DRIVER1   (*(RwReg*)0xFFFFF518U) /**< \brief (PIOB) I/O Drive Register 1 */
#define REG_PIOB_DRIVER2   (*(RwReg*)0xFFFFF51CU) /**< \brief (PIOB) I/O Drive Register 2 */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_PIOB_INSTANCE_ */
