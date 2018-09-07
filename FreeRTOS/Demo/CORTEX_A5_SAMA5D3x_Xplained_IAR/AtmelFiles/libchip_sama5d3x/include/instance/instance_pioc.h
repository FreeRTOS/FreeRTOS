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

#ifndef _SAMA5_PIOC_INSTANCE_
#define _SAMA5_PIOC_INSTANCE_

/* ========== Register definition for PIOC peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_PIOC_PER                (0xFFFFF600U) /**< \brief (PIOC) PIO Enable Register */
#define REG_PIOC_PDR                (0xFFFFF604U) /**< \brief (PIOC) PIO Disable Register */
#define REG_PIOC_PSR                (0xFFFFF608U) /**< \brief (PIOC) PIO Status Register */
#define REG_PIOC_OER                (0xFFFFF610U) /**< \brief (PIOC) Output Enable Register */
#define REG_PIOC_ODR                (0xFFFFF614U) /**< \brief (PIOC) Output Disable Register */
#define REG_PIOC_OSR                (0xFFFFF618U) /**< \brief (PIOC) Output Status Register */
#define REG_PIOC_IFER               (0xFFFFF620U) /**< \brief (PIOC) Glitch Input Filter Enable Register */
#define REG_PIOC_IFDR               (0xFFFFF624U) /**< \brief (PIOC) Glitch Input Filter Disable Register */
#define REG_PIOC_IFSR               (0xFFFFF628U) /**< \brief (PIOC) Glitch Input Filter Status Register */
#define REG_PIOC_SODR               (0xFFFFF630U) /**< \brief (PIOC) Set Output Data Register */
#define REG_PIOC_CODR               (0xFFFFF634U) /**< \brief (PIOC) Clear Output Data Register */
#define REG_PIOC_ODSR               (0xFFFFF638U) /**< \brief (PIOC) Output Data Status Register */
#define REG_PIOC_PDSR               (0xFFFFF63CU) /**< \brief (PIOC) Pin Data Status Register */
#define REG_PIOC_IER                (0xFFFFF640U) /**< \brief (PIOC) Interrupt Enable Register */
#define REG_PIOC_IDR                (0xFFFFF644U) /**< \brief (PIOC) Interrupt Disable Register */
#define REG_PIOC_IMR                (0xFFFFF648U) /**< \brief (PIOC) Interrupt Mask Register */
#define REG_PIOC_ISR                (0xFFFFF64CU) /**< \brief (PIOC) Interrupt Status Register */
#define REG_PIOC_MDER               (0xFFFFF650U) /**< \brief (PIOC) Multi-driver Enable Register */
#define REG_PIOC_MDDR               (0xFFFFF654U) /**< \brief (PIOC) Multi-driver Disable Register */
#define REG_PIOC_MDSR               (0xFFFFF658U) /**< \brief (PIOC) Multi-driver Status Register */
#define REG_PIOC_PUDR               (0xFFFFF660U) /**< \brief (PIOC) Pull-up Disable Register */
#define REG_PIOC_PUER               (0xFFFFF664U) /**< \brief (PIOC) Pull-up Enable Register */
#define REG_PIOC_PUSR               (0xFFFFF668U) /**< \brief (PIOC) Pad Pull-up Status Register */
#define REG_PIOC_ABCDSR             (0xFFFFF670U) /**< \brief (PIOC) Peripheral Select Register */
#define REG_PIOC_IFSCDR             (0xFFFFF680U) /**< \brief (PIOC) Input Filter Slow Clock Disable Register */
#define REG_PIOC_IFSCER             (0xFFFFF684U) /**< \brief (PIOC) Input Filter Slow Clock Enable Register */
#define REG_PIOC_IFSCSR             (0xFFFFF688U) /**< \brief (PIOC) Input Filter Slow Clock Status Register */
#define REG_PIOC_SCDR               (0xFFFFF68CU) /**< \brief (PIOC) Slow Clock Divider Debouncing Register */
#define REG_PIOC_PPDDR              (0xFFFFF690U) /**< \brief (PIOC) Pad Pull-down Disable Register */
#define REG_PIOC_PPDER              (0xFFFFF694U) /**< \brief (PIOC) Pad Pull-down Enable Register */
#define REG_PIOC_PPDSR              (0xFFFFF698U) /**< \brief (PIOC) Pad Pull-down Status Register */
#define REG_PIOC_OWER               (0xFFFFF6A0U) /**< \brief (PIOC) Output Write Enable */
#define REG_PIOC_OWDR               (0xFFFFF6A4U) /**< \brief (PIOC) Output Write Disable */
#define REG_PIOC_OWSR               (0xFFFFF6A8U) /**< \brief (PIOC) Output Write Status Register */
#define REG_PIOC_AIMER              (0xFFFFF6B0U) /**< \brief (PIOC) Additional Interrupt Modes Enable Register */
#define REG_PIOC_AIMDR              (0xFFFFF6B4U) /**< \brief (PIOC) Additional Interrupt Modes Disables Register */
#define REG_PIOC_AIMMR              (0xFFFFF6B8U) /**< \brief (PIOC) Additional Interrupt Modes Mask Register */
#define REG_PIOC_ESR                (0xFFFFF6C0U) /**< \brief (PIOC) Edge Select Register */
#define REG_PIOC_LSR                (0xFFFFF6C4U) /**< \brief (PIOC) Level Select Register */
#define REG_PIOC_ELSR               (0xFFFFF6C8U) /**< \brief (PIOC) Edge/Level Status Register */
#define REG_PIOC_FELLSR             (0xFFFFF6D0U) /**< \brief (PIOC) Falling Edge/Low Level Select Register */
#define REG_PIOC_REHLSR             (0xFFFFF6D4U) /**< \brief (PIOC) Rising Edge/ High Level Select Register */
#define REG_PIOC_FRLHSR             (0xFFFFF6D8U) /**< \brief (PIOC) Fall/Rise - Low/High Status Register */
#define REG_PIOC_LOCKSR             (0xFFFFF6E0U) /**< \brief (PIOC) Lock Status */
#define REG_PIOC_WPMR               (0xFFFFF6E4U) /**< \brief (PIOC) Write Protect Mode Register */
#define REG_PIOC_WPSR               (0xFFFFF6E8U) /**< \brief (PIOC) Write Protect Status Register */
#define REG_PIOC_SCHMITT            (0xFFFFF700U) /**< \brief (PIOC) Schmitt Trigger Register */
#define REG_PIOC_DRIVER1            (0xFFFFF718U) /**< \brief (PIOC) I/O Drive Register 1 */
#define REG_PIOC_DRIVER2            (0xFFFFF71CU) /**< \brief (PIOC) I/O Drive Register 2 */
#else
#define REG_PIOC_PER       (*(WoReg*)0xFFFFF600U) /**< \brief (PIOC) PIO Enable Register */
#define REG_PIOC_PDR       (*(WoReg*)0xFFFFF604U) /**< \brief (PIOC) PIO Disable Register */
#define REG_PIOC_PSR       (*(RoReg*)0xFFFFF608U) /**< \brief (PIOC) PIO Status Register */
#define REG_PIOC_OER       (*(WoReg*)0xFFFFF610U) /**< \brief (PIOC) Output Enable Register */
#define REG_PIOC_ODR       (*(WoReg*)0xFFFFF614U) /**< \brief (PIOC) Output Disable Register */
#define REG_PIOC_OSR       (*(RoReg*)0xFFFFF618U) /**< \brief (PIOC) Output Status Register */
#define REG_PIOC_IFER      (*(WoReg*)0xFFFFF620U) /**< \brief (PIOC) Glitch Input Filter Enable Register */
#define REG_PIOC_IFDR      (*(WoReg*)0xFFFFF624U) /**< \brief (PIOC) Glitch Input Filter Disable Register */
#define REG_PIOC_IFSR      (*(RoReg*)0xFFFFF628U) /**< \brief (PIOC) Glitch Input Filter Status Register */
#define REG_PIOC_SODR      (*(WoReg*)0xFFFFF630U) /**< \brief (PIOC) Set Output Data Register */
#define REG_PIOC_CODR      (*(WoReg*)0xFFFFF634U) /**< \brief (PIOC) Clear Output Data Register */
#define REG_PIOC_ODSR      (*(RwReg*)0xFFFFF638U) /**< \brief (PIOC) Output Data Status Register */
#define REG_PIOC_PDSR      (*(RoReg*)0xFFFFF63CU) /**< \brief (PIOC) Pin Data Status Register */
#define REG_PIOC_IER       (*(WoReg*)0xFFFFF640U) /**< \brief (PIOC) Interrupt Enable Register */
#define REG_PIOC_IDR       (*(WoReg*)0xFFFFF644U) /**< \brief (PIOC) Interrupt Disable Register */
#define REG_PIOC_IMR       (*(RoReg*)0xFFFFF648U) /**< \brief (PIOC) Interrupt Mask Register */
#define REG_PIOC_ISR       (*(RoReg*)0xFFFFF64CU) /**< \brief (PIOC) Interrupt Status Register */
#define REG_PIOC_MDER      (*(WoReg*)0xFFFFF650U) /**< \brief (PIOC) Multi-driver Enable Register */
#define REG_PIOC_MDDR      (*(WoReg*)0xFFFFF654U) /**< \brief (PIOC) Multi-driver Disable Register */
#define REG_PIOC_MDSR      (*(RoReg*)0xFFFFF658U) /**< \brief (PIOC) Multi-driver Status Register */
#define REG_PIOC_PUDR      (*(WoReg*)0xFFFFF660U) /**< \brief (PIOC) Pull-up Disable Register */
#define REG_PIOC_PUER      (*(WoReg*)0xFFFFF664U) /**< \brief (PIOC) Pull-up Enable Register */
#define REG_PIOC_PUSR      (*(RoReg*)0xFFFFF668U) /**< \brief (PIOC) Pad Pull-up Status Register */
#define REG_PIOC_ABCDSR    (*(RwReg*)0xFFFFF670U) /**< \brief (PIOC) Peripheral Select Register */
#define REG_PIOC_IFSCDR    (*(WoReg*)0xFFFFF680U) /**< \brief (PIOC) Input Filter Slow Clock Disable Register */
#define REG_PIOC_IFSCER    (*(WoReg*)0xFFFFF684U) /**< \brief (PIOC) Input Filter Slow Clock Enable Register */
#define REG_PIOC_IFSCSR    (*(RoReg*)0xFFFFF688U) /**< \brief (PIOC) Input Filter Slow Clock Status Register */
#define REG_PIOC_SCDR      (*(RwReg*)0xFFFFF68CU) /**< \brief (PIOC) Slow Clock Divider Debouncing Register */
#define REG_PIOC_PPDDR     (*(WoReg*)0xFFFFF690U) /**< \brief (PIOC) Pad Pull-down Disable Register */
#define REG_PIOC_PPDER     (*(WoReg*)0xFFFFF694U) /**< \brief (PIOC) Pad Pull-down Enable Register */
#define REG_PIOC_PPDSR     (*(RoReg*)0xFFFFF698U) /**< \brief (PIOC) Pad Pull-down Status Register */
#define REG_PIOC_OWER      (*(WoReg*)0xFFFFF6A0U) /**< \brief (PIOC) Output Write Enable */
#define REG_PIOC_OWDR      (*(WoReg*)0xFFFFF6A4U) /**< \brief (PIOC) Output Write Disable */
#define REG_PIOC_OWSR      (*(RoReg*)0xFFFFF6A8U) /**< \brief (PIOC) Output Write Status Register */
#define REG_PIOC_AIMER     (*(WoReg*)0xFFFFF6B0U) /**< \brief (PIOC) Additional Interrupt Modes Enable Register */
#define REG_PIOC_AIMDR     (*(WoReg*)0xFFFFF6B4U) /**< \brief (PIOC) Additional Interrupt Modes Disables Register */
#define REG_PIOC_AIMMR     (*(RoReg*)0xFFFFF6B8U) /**< \brief (PIOC) Additional Interrupt Modes Mask Register */
#define REG_PIOC_ESR       (*(WoReg*)0xFFFFF6C0U) /**< \brief (PIOC) Edge Select Register */
#define REG_PIOC_LSR       (*(WoReg*)0xFFFFF6C4U) /**< \brief (PIOC) Level Select Register */
#define REG_PIOC_ELSR      (*(RoReg*)0xFFFFF6C8U) /**< \brief (PIOC) Edge/Level Status Register */
#define REG_PIOC_FELLSR    (*(WoReg*)0xFFFFF6D0U) /**< \brief (PIOC) Falling Edge/Low Level Select Register */
#define REG_PIOC_REHLSR    (*(WoReg*)0xFFFFF6D4U) /**< \brief (PIOC) Rising Edge/ High Level Select Register */
#define REG_PIOC_FRLHSR    (*(RoReg*)0xFFFFF6D8U) /**< \brief (PIOC) Fall/Rise - Low/High Status Register */
#define REG_PIOC_LOCKSR    (*(RoReg*)0xFFFFF6E0U) /**< \brief (PIOC) Lock Status */
#define REG_PIOC_WPMR      (*(RwReg*)0xFFFFF6E4U) /**< \brief (PIOC) Write Protect Mode Register */
#define REG_PIOC_WPSR      (*(RoReg*)0xFFFFF6E8U) /**< \brief (PIOC) Write Protect Status Register */
#define REG_PIOC_SCHMITT   (*(RwReg*)0xFFFFF700U) /**< \brief (PIOC) Schmitt Trigger Register */
#define REG_PIOC_DRIVER1   (*(RwReg*)0xFFFFF718U) /**< \brief (PIOC) I/O Drive Register 1 */
#define REG_PIOC_DRIVER2   (*(RwReg*)0xFFFFF71CU) /**< \brief (PIOC) I/O Drive Register 2 */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_PIOC_INSTANCE_ */
