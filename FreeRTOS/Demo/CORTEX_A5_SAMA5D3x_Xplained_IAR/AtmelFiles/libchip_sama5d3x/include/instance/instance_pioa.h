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

#ifndef _SAMA5_PIOA_INSTANCE_
#define _SAMA5_PIOA_INSTANCE_

/* ========== Register definition for PIOA peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_PIOA_PER                (0xFFFFF200U) /**< \brief (PIOA) PIO Enable Register */
#define REG_PIOA_PDR                (0xFFFFF204U) /**< \brief (PIOA) PIO Disable Register */
#define REG_PIOA_PSR                (0xFFFFF208U) /**< \brief (PIOA) PIO Status Register */
#define REG_PIOA_OER                (0xFFFFF210U) /**< \brief (PIOA) Output Enable Register */
#define REG_PIOA_ODR                (0xFFFFF214U) /**< \brief (PIOA) Output Disable Register */
#define REG_PIOA_OSR                (0xFFFFF218U) /**< \brief (PIOA) Output Status Register */
#define REG_PIOA_IFER               (0xFFFFF220U) /**< \brief (PIOA) Glitch Input Filter Enable Register */
#define REG_PIOA_IFDR               (0xFFFFF224U) /**< \brief (PIOA) Glitch Input Filter Disable Register */
#define REG_PIOA_IFSR               (0xFFFFF228U) /**< \brief (PIOA) Glitch Input Filter Status Register */
#define REG_PIOA_SODR               (0xFFFFF230U) /**< \brief (PIOA) Set Output Data Register */
#define REG_PIOA_CODR               (0xFFFFF234U) /**< \brief (PIOA) Clear Output Data Register */
#define REG_PIOA_ODSR               (0xFFFFF238U) /**< \brief (PIOA) Output Data Status Register */
#define REG_PIOA_PDSR               (0xFFFFF23CU) /**< \brief (PIOA) Pin Data Status Register */
#define REG_PIOA_IER                (0xFFFFF240U) /**< \brief (PIOA) Interrupt Enable Register */
#define REG_PIOA_IDR                (0xFFFFF244U) /**< \brief (PIOA) Interrupt Disable Register */
#define REG_PIOA_IMR                (0xFFFFF248U) /**< \brief (PIOA) Interrupt Mask Register */
#define REG_PIOA_ISR                (0xFFFFF24CU) /**< \brief (PIOA) Interrupt Status Register */
#define REG_PIOA_MDER               (0xFFFFF250U) /**< \brief (PIOA) Multi-driver Enable Register */
#define REG_PIOA_MDDR               (0xFFFFF254U) /**< \brief (PIOA) Multi-driver Disable Register */
#define REG_PIOA_MDSR               (0xFFFFF258U) /**< \brief (PIOA) Multi-driver Status Register */
#define REG_PIOA_PUDR               (0xFFFFF260U) /**< \brief (PIOA) Pull-up Disable Register */
#define REG_PIOA_PUER               (0xFFFFF264U) /**< \brief (PIOA) Pull-up Enable Register */
#define REG_PIOA_PUSR               (0xFFFFF268U) /**< \brief (PIOA) Pad Pull-up Status Register */
#define REG_PIOA_ABCDSR             (0xFFFFF270U) /**< \brief (PIOA) Peripheral Select Register */
#define REG_PIOA_IFSCDR             (0xFFFFF280U) /**< \brief (PIOA) Input Filter Slow Clock Disable Register */
#define REG_PIOA_IFSCER             (0xFFFFF284U) /**< \brief (PIOA) Input Filter Slow Clock Enable Register */
#define REG_PIOA_IFSCSR             (0xFFFFF288U) /**< \brief (PIOA) Input Filter Slow Clock Status Register */
#define REG_PIOA_SCDR               (0xFFFFF28CU) /**< \brief (PIOA) Slow Clock Divider Debouncing Register */
#define REG_PIOA_PPDDR              (0xFFFFF290U) /**< \brief (PIOA) Pad Pull-down Disable Register */
#define REG_PIOA_PPDER              (0xFFFFF294U) /**< \brief (PIOA) Pad Pull-down Enable Register */
#define REG_PIOA_PPDSR              (0xFFFFF298U) /**< \brief (PIOA) Pad Pull-down Status Register */
#define REG_PIOA_OWER               (0xFFFFF2A0U) /**< \brief (PIOA) Output Write Enable */
#define REG_PIOA_OWDR               (0xFFFFF2A4U) /**< \brief (PIOA) Output Write Disable */
#define REG_PIOA_OWSR               (0xFFFFF2A8U) /**< \brief (PIOA) Output Write Status Register */
#define REG_PIOA_AIMER              (0xFFFFF2B0U) /**< \brief (PIOA) Additional Interrupt Modes Enable Register */
#define REG_PIOA_AIMDR              (0xFFFFF2B4U) /**< \brief (PIOA) Additional Interrupt Modes Disables Register */
#define REG_PIOA_AIMMR              (0xFFFFF2B8U) /**< \brief (PIOA) Additional Interrupt Modes Mask Register */
#define REG_PIOA_ESR                (0xFFFFF2C0U) /**< \brief (PIOA) Edge Select Register */
#define REG_PIOA_LSR                (0xFFFFF2C4U) /**< \brief (PIOA) Level Select Register */
#define REG_PIOA_ELSR               (0xFFFFF2C8U) /**< \brief (PIOA) Edge/Level Status Register */
#define REG_PIOA_FELLSR             (0xFFFFF2D0U) /**< \brief (PIOA) Falling Edge/Low Level Select Register */
#define REG_PIOA_REHLSR             (0xFFFFF2D4U) /**< \brief (PIOA) Rising Edge/ High Level Select Register */
#define REG_PIOA_FRLHSR             (0xFFFFF2D8U) /**< \brief (PIOA) Fall/Rise - Low/High Status Register */
#define REG_PIOA_LOCKSR             (0xFFFFF2E0U) /**< \brief (PIOA) Lock Status */
#define REG_PIOA_WPMR               (0xFFFFF2E4U) /**< \brief (PIOA) Write Protect Mode Register */
#define REG_PIOA_WPSR               (0xFFFFF2E8U) /**< \brief (PIOA) Write Protect Status Register */
#define REG_PIOA_SCHMITT            (0xFFFFF300U) /**< \brief (PIOA) Schmitt Trigger Register */
#define REG_PIOA_DRIVER1            (0xFFFFF318U) /**< \brief (PIOA) I/O Drive Register 1 */
#define REG_PIOA_DRIVER2            (0xFFFFF31CU) /**< \brief (PIOA) I/O Drive Register 2 */
#else
#define REG_PIOA_PER       (*(WoReg*)0xFFFFF200U) /**< \brief (PIOA) PIO Enable Register */
#define REG_PIOA_PDR       (*(WoReg*)0xFFFFF204U) /**< \brief (PIOA) PIO Disable Register */
#define REG_PIOA_PSR       (*(RoReg*)0xFFFFF208U) /**< \brief (PIOA) PIO Status Register */
#define REG_PIOA_OER       (*(WoReg*)0xFFFFF210U) /**< \brief (PIOA) Output Enable Register */
#define REG_PIOA_ODR       (*(WoReg*)0xFFFFF214U) /**< \brief (PIOA) Output Disable Register */
#define REG_PIOA_OSR       (*(RoReg*)0xFFFFF218U) /**< \brief (PIOA) Output Status Register */
#define REG_PIOA_IFER      (*(WoReg*)0xFFFFF220U) /**< \brief (PIOA) Glitch Input Filter Enable Register */
#define REG_PIOA_IFDR      (*(WoReg*)0xFFFFF224U) /**< \brief (PIOA) Glitch Input Filter Disable Register */
#define REG_PIOA_IFSR      (*(RoReg*)0xFFFFF228U) /**< \brief (PIOA) Glitch Input Filter Status Register */
#define REG_PIOA_SODR      (*(WoReg*)0xFFFFF230U) /**< \brief (PIOA) Set Output Data Register */
#define REG_PIOA_CODR      (*(WoReg*)0xFFFFF234U) /**< \brief (PIOA) Clear Output Data Register */
#define REG_PIOA_ODSR      (*(RwReg*)0xFFFFF238U) /**< \brief (PIOA) Output Data Status Register */
#define REG_PIOA_PDSR      (*(RoReg*)0xFFFFF23CU) /**< \brief (PIOA) Pin Data Status Register */
#define REG_PIOA_IER       (*(WoReg*)0xFFFFF240U) /**< \brief (PIOA) Interrupt Enable Register */
#define REG_PIOA_IDR       (*(WoReg*)0xFFFFF244U) /**< \brief (PIOA) Interrupt Disable Register */
#define REG_PIOA_IMR       (*(RoReg*)0xFFFFF248U) /**< \brief (PIOA) Interrupt Mask Register */
#define REG_PIOA_ISR       (*(RoReg*)0xFFFFF24CU) /**< \brief (PIOA) Interrupt Status Register */
#define REG_PIOA_MDER      (*(WoReg*)0xFFFFF250U) /**< \brief (PIOA) Multi-driver Enable Register */
#define REG_PIOA_MDDR      (*(WoReg*)0xFFFFF254U) /**< \brief (PIOA) Multi-driver Disable Register */
#define REG_PIOA_MDSR      (*(RoReg*)0xFFFFF258U) /**< \brief (PIOA) Multi-driver Status Register */
#define REG_PIOA_PUDR      (*(WoReg*)0xFFFFF260U) /**< \brief (PIOA) Pull-up Disable Register */
#define REG_PIOA_PUER      (*(WoReg*)0xFFFFF264U) /**< \brief (PIOA) Pull-up Enable Register */
#define REG_PIOA_PUSR      (*(RoReg*)0xFFFFF268U) /**< \brief (PIOA) Pad Pull-up Status Register */
#define REG_PIOA_ABCDSR    (*(RwReg*)0xFFFFF270U) /**< \brief (PIOA) Peripheral Select Register */
#define REG_PIOA_IFSCDR    (*(WoReg*)0xFFFFF280U) /**< \brief (PIOA) Input Filter Slow Clock Disable Register */
#define REG_PIOA_IFSCER    (*(WoReg*)0xFFFFF284U) /**< \brief (PIOA) Input Filter Slow Clock Enable Register */
#define REG_PIOA_IFSCSR    (*(RoReg*)0xFFFFF288U) /**< \brief (PIOA) Input Filter Slow Clock Status Register */
#define REG_PIOA_SCDR      (*(RwReg*)0xFFFFF28CU) /**< \brief (PIOA) Slow Clock Divider Debouncing Register */
#define REG_PIOA_PPDDR     (*(WoReg*)0xFFFFF290U) /**< \brief (PIOA) Pad Pull-down Disable Register */
#define REG_PIOA_PPDER     (*(WoReg*)0xFFFFF294U) /**< \brief (PIOA) Pad Pull-down Enable Register */
#define REG_PIOA_PPDSR     (*(RoReg*)0xFFFFF298U) /**< \brief (PIOA) Pad Pull-down Status Register */
#define REG_PIOA_OWER      (*(WoReg*)0xFFFFF2A0U) /**< \brief (PIOA) Output Write Enable */
#define REG_PIOA_OWDR      (*(WoReg*)0xFFFFF2A4U) /**< \brief (PIOA) Output Write Disable */
#define REG_PIOA_OWSR      (*(RoReg*)0xFFFFF2A8U) /**< \brief (PIOA) Output Write Status Register */
#define REG_PIOA_AIMER     (*(WoReg*)0xFFFFF2B0U) /**< \brief (PIOA) Additional Interrupt Modes Enable Register */
#define REG_PIOA_AIMDR     (*(WoReg*)0xFFFFF2B4U) /**< \brief (PIOA) Additional Interrupt Modes Disables Register */
#define REG_PIOA_AIMMR     (*(RoReg*)0xFFFFF2B8U) /**< \brief (PIOA) Additional Interrupt Modes Mask Register */
#define REG_PIOA_ESR       (*(WoReg*)0xFFFFF2C0U) /**< \brief (PIOA) Edge Select Register */
#define REG_PIOA_LSR       (*(WoReg*)0xFFFFF2C4U) /**< \brief (PIOA) Level Select Register */
#define REG_PIOA_ELSR      (*(RoReg*)0xFFFFF2C8U) /**< \brief (PIOA) Edge/Level Status Register */
#define REG_PIOA_FELLSR    (*(WoReg*)0xFFFFF2D0U) /**< \brief (PIOA) Falling Edge/Low Level Select Register */
#define REG_PIOA_REHLSR    (*(WoReg*)0xFFFFF2D4U) /**< \brief (PIOA) Rising Edge/ High Level Select Register */
#define REG_PIOA_FRLHSR    (*(RoReg*)0xFFFFF2D8U) /**< \brief (PIOA) Fall/Rise - Low/High Status Register */
#define REG_PIOA_LOCKSR    (*(RoReg*)0xFFFFF2E0U) /**< \brief (PIOA) Lock Status */
#define REG_PIOA_WPMR      (*(RwReg*)0xFFFFF2E4U) /**< \brief (PIOA) Write Protect Mode Register */
#define REG_PIOA_WPSR      (*(RoReg*)0xFFFFF2E8U) /**< \brief (PIOA) Write Protect Status Register */
#define REG_PIOA_SCHMITT   (*(RwReg*)0xFFFFF300U) /**< \brief (PIOA) Schmitt Trigger Register */
#define REG_PIOA_DRIVER1   (*(RwReg*)0xFFFFF318U) /**< \brief (PIOA) I/O Drive Register 1 */
#define REG_PIOA_DRIVER2   (*(RwReg*)0xFFFFF31CU) /**< \brief (PIOA) I/O Drive Register 2 */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_PIOA_INSTANCE_ */
