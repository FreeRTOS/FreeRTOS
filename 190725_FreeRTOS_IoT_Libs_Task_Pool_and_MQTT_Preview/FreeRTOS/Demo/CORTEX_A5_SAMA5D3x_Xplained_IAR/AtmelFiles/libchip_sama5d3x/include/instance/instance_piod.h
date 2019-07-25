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

#ifndef _SAMA5_PIOD_INSTANCE_
#define _SAMA5_PIOD_INSTANCE_

/* ========== Register definition for PIOD peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_PIOD_PER                (0xFFFFF800U) /**< \brief (PIOD) PIO Enable Register */
#define REG_PIOD_PDR                (0xFFFFF804U) /**< \brief (PIOD) PIO Disable Register */
#define REG_PIOD_PSR                (0xFFFFF808U) /**< \brief (PIOD) PIO Status Register */
#define REG_PIOD_OER                (0xFFFFF810U) /**< \brief (PIOD) Output Enable Register */
#define REG_PIOD_ODR                (0xFFFFF814U) /**< \brief (PIOD) Output Disable Register */
#define REG_PIOD_OSR                (0xFFFFF818U) /**< \brief (PIOD) Output Status Register */
#define REG_PIOD_IFER               (0xFFFFF820U) /**< \brief (PIOD) Glitch Input Filter Enable Register */
#define REG_PIOD_IFDR               (0xFFFFF824U) /**< \brief (PIOD) Glitch Input Filter Disable Register */
#define REG_PIOD_IFSR               (0xFFFFF828U) /**< \brief (PIOD) Glitch Input Filter Status Register */
#define REG_PIOD_SODR               (0xFFFFF830U) /**< \brief (PIOD) Set Output Data Register */
#define REG_PIOD_CODR               (0xFFFFF834U) /**< \brief (PIOD) Clear Output Data Register */
#define REG_PIOD_ODSR               (0xFFFFF838U) /**< \brief (PIOD) Output Data Status Register */
#define REG_PIOD_PDSR               (0xFFFFF83CU) /**< \brief (PIOD) Pin Data Status Register */
#define REG_PIOD_IER                (0xFFFFF840U) /**< \brief (PIOD) Interrupt Enable Register */
#define REG_PIOD_IDR                (0xFFFFF844U) /**< \brief (PIOD) Interrupt Disable Register */
#define REG_PIOD_IMR                (0xFFFFF848U) /**< \brief (PIOD) Interrupt Mask Register */
#define REG_PIOD_ISR                (0xFFFFF84CU) /**< \brief (PIOD) Interrupt Status Register */
#define REG_PIOD_MDER               (0xFFFFF850U) /**< \brief (PIOD) Multi-driver Enable Register */
#define REG_PIOD_MDDR               (0xFFFFF854U) /**< \brief (PIOD) Multi-driver Disable Register */
#define REG_PIOD_MDSR               (0xFFFFF858U) /**< \brief (PIOD) Multi-driver Status Register */
#define REG_PIOD_PUDR               (0xFFFFF860U) /**< \brief (PIOD) Pull-up Disable Register */
#define REG_PIOD_PUER               (0xFFFFF864U) /**< \brief (PIOD) Pull-up Enable Register */
#define REG_PIOD_PUSR               (0xFFFFF868U) /**< \brief (PIOD) Pad Pull-up Status Register */
#define REG_PIOD_ABCDSR             (0xFFFFF870U) /**< \brief (PIOD) Peripheral Select Register */
#define REG_PIOD_IFSCDR             (0xFFFFF880U) /**< \brief (PIOD) Input Filter Slow Clock Disable Register */
#define REG_PIOD_IFSCER             (0xFFFFF884U) /**< \brief (PIOD) Input Filter Slow Clock Enable Register */
#define REG_PIOD_IFSCSR             (0xFFFFF888U) /**< \brief (PIOD) Input Filter Slow Clock Status Register */
#define REG_PIOD_SCDR               (0xFFFFF88CU) /**< \brief (PIOD) Slow Clock Divider Debouncing Register */
#define REG_PIOD_PPDDR              (0xFFFFF890U) /**< \brief (PIOD) Pad Pull-down Disable Register */
#define REG_PIOD_PPDER              (0xFFFFF894U) /**< \brief (PIOD) Pad Pull-down Enable Register */
#define REG_PIOD_PPDSR              (0xFFFFF898U) /**< \brief (PIOD) Pad Pull-down Status Register */
#define REG_PIOD_OWER               (0xFFFFF8A0U) /**< \brief (PIOD) Output Write Enable */
#define REG_PIOD_OWDR               (0xFFFFF8A4U) /**< \brief (PIOD) Output Write Disable */
#define REG_PIOD_OWSR               (0xFFFFF8A8U) /**< \brief (PIOD) Output Write Status Register */
#define REG_PIOD_AIMER              (0xFFFFF8B0U) /**< \brief (PIOD) Additional Interrupt Modes Enable Register */
#define REG_PIOD_AIMDR              (0xFFFFF8B4U) /**< \brief (PIOD) Additional Interrupt Modes Disables Register */
#define REG_PIOD_AIMMR              (0xFFFFF8B8U) /**< \brief (PIOD) Additional Interrupt Modes Mask Register */
#define REG_PIOD_ESR                (0xFFFFF8C0U) /**< \brief (PIOD) Edge Select Register */
#define REG_PIOD_LSR                (0xFFFFF8C4U) /**< \brief (PIOD) Level Select Register */
#define REG_PIOD_ELSR               (0xFFFFF8C8U) /**< \brief (PIOD) Edge/Level Status Register */
#define REG_PIOD_FELLSR             (0xFFFFF8D0U) /**< \brief (PIOD) Falling Edge/Low Level Select Register */
#define REG_PIOD_REHLSR             (0xFFFFF8D4U) /**< \brief (PIOD) Rising Edge/ High Level Select Register */
#define REG_PIOD_FRLHSR             (0xFFFFF8D8U) /**< \brief (PIOD) Fall/Rise - Low/High Status Register */
#define REG_PIOD_LOCKSR             (0xFFFFF8E0U) /**< \brief (PIOD) Lock Status */
#define REG_PIOD_WPMR               (0xFFFFF8E4U) /**< \brief (PIOD) Write Protect Mode Register */
#define REG_PIOD_WPSR               (0xFFFFF8E8U) /**< \brief (PIOD) Write Protect Status Register */
#define REG_PIOD_SCHMITT            (0xFFFFF900U) /**< \brief (PIOD) Schmitt Trigger Register */
#define REG_PIOD_DRIVER1            (0xFFFFF918U) /**< \brief (PIOD) I/O Drive Register 1 */
#define REG_PIOD_DRIVER2            (0xFFFFF91CU) /**< \brief (PIOD) I/O Drive Register 2 */
#else
#define REG_PIOD_PER       (*(WoReg*)0xFFFFF800U) /**< \brief (PIOD) PIO Enable Register */
#define REG_PIOD_PDR       (*(WoReg*)0xFFFFF804U) /**< \brief (PIOD) PIO Disable Register */
#define REG_PIOD_PSR       (*(RoReg*)0xFFFFF808U) /**< \brief (PIOD) PIO Status Register */
#define REG_PIOD_OER       (*(WoReg*)0xFFFFF810U) /**< \brief (PIOD) Output Enable Register */
#define REG_PIOD_ODR       (*(WoReg*)0xFFFFF814U) /**< \brief (PIOD) Output Disable Register */
#define REG_PIOD_OSR       (*(RoReg*)0xFFFFF818U) /**< \brief (PIOD) Output Status Register */
#define REG_PIOD_IFER      (*(WoReg*)0xFFFFF820U) /**< \brief (PIOD) Glitch Input Filter Enable Register */
#define REG_PIOD_IFDR      (*(WoReg*)0xFFFFF824U) /**< \brief (PIOD) Glitch Input Filter Disable Register */
#define REG_PIOD_IFSR      (*(RoReg*)0xFFFFF828U) /**< \brief (PIOD) Glitch Input Filter Status Register */
#define REG_PIOD_SODR      (*(WoReg*)0xFFFFF830U) /**< \brief (PIOD) Set Output Data Register */
#define REG_PIOD_CODR      (*(WoReg*)0xFFFFF834U) /**< \brief (PIOD) Clear Output Data Register */
#define REG_PIOD_ODSR      (*(RwReg*)0xFFFFF838U) /**< \brief (PIOD) Output Data Status Register */
#define REG_PIOD_PDSR      (*(RoReg*)0xFFFFF83CU) /**< \brief (PIOD) Pin Data Status Register */
#define REG_PIOD_IER       (*(WoReg*)0xFFFFF840U) /**< \brief (PIOD) Interrupt Enable Register */
#define REG_PIOD_IDR       (*(WoReg*)0xFFFFF844U) /**< \brief (PIOD) Interrupt Disable Register */
#define REG_PIOD_IMR       (*(RoReg*)0xFFFFF848U) /**< \brief (PIOD) Interrupt Mask Register */
#define REG_PIOD_ISR       (*(RoReg*)0xFFFFF84CU) /**< \brief (PIOD) Interrupt Status Register */
#define REG_PIOD_MDER      (*(WoReg*)0xFFFFF850U) /**< \brief (PIOD) Multi-driver Enable Register */
#define REG_PIOD_MDDR      (*(WoReg*)0xFFFFF854U) /**< \brief (PIOD) Multi-driver Disable Register */
#define REG_PIOD_MDSR      (*(RoReg*)0xFFFFF858U) /**< \brief (PIOD) Multi-driver Status Register */
#define REG_PIOD_PUDR      (*(WoReg*)0xFFFFF860U) /**< \brief (PIOD) Pull-up Disable Register */
#define REG_PIOD_PUER      (*(WoReg*)0xFFFFF864U) /**< \brief (PIOD) Pull-up Enable Register */
#define REG_PIOD_PUSR      (*(RoReg*)0xFFFFF868U) /**< \brief (PIOD) Pad Pull-up Status Register */
#define REG_PIOD_ABCDSR    (*(RwReg*)0xFFFFF870U) /**< \brief (PIOD) Peripheral Select Register */
#define REG_PIOD_IFSCDR    (*(WoReg*)0xFFFFF880U) /**< \brief (PIOD) Input Filter Slow Clock Disable Register */
#define REG_PIOD_IFSCER    (*(WoReg*)0xFFFFF884U) /**< \brief (PIOD) Input Filter Slow Clock Enable Register */
#define REG_PIOD_IFSCSR    (*(RoReg*)0xFFFFF888U) /**< \brief (PIOD) Input Filter Slow Clock Status Register */
#define REG_PIOD_SCDR      (*(RwReg*)0xFFFFF88CU) /**< \brief (PIOD) Slow Clock Divider Debouncing Register */
#define REG_PIOD_PPDDR     (*(WoReg*)0xFFFFF890U) /**< \brief (PIOD) Pad Pull-down Disable Register */
#define REG_PIOD_PPDER     (*(WoReg*)0xFFFFF894U) /**< \brief (PIOD) Pad Pull-down Enable Register */
#define REG_PIOD_PPDSR     (*(RoReg*)0xFFFFF898U) /**< \brief (PIOD) Pad Pull-down Status Register */
#define REG_PIOD_OWER      (*(WoReg*)0xFFFFF8A0U) /**< \brief (PIOD) Output Write Enable */
#define REG_PIOD_OWDR      (*(WoReg*)0xFFFFF8A4U) /**< \brief (PIOD) Output Write Disable */
#define REG_PIOD_OWSR      (*(RoReg*)0xFFFFF8A8U) /**< \brief (PIOD) Output Write Status Register */
#define REG_PIOD_AIMER     (*(WoReg*)0xFFFFF8B0U) /**< \brief (PIOD) Additional Interrupt Modes Enable Register */
#define REG_PIOD_AIMDR     (*(WoReg*)0xFFFFF8B4U) /**< \brief (PIOD) Additional Interrupt Modes Disables Register */
#define REG_PIOD_AIMMR     (*(RoReg*)0xFFFFF8B8U) /**< \brief (PIOD) Additional Interrupt Modes Mask Register */
#define REG_PIOD_ESR       (*(WoReg*)0xFFFFF8C0U) /**< \brief (PIOD) Edge Select Register */
#define REG_PIOD_LSR       (*(WoReg*)0xFFFFF8C4U) /**< \brief (PIOD) Level Select Register */
#define REG_PIOD_ELSR      (*(RoReg*)0xFFFFF8C8U) /**< \brief (PIOD) Edge/Level Status Register */
#define REG_PIOD_FELLSR    (*(WoReg*)0xFFFFF8D0U) /**< \brief (PIOD) Falling Edge/Low Level Select Register */
#define REG_PIOD_REHLSR    (*(WoReg*)0xFFFFF8D4U) /**< \brief (PIOD) Rising Edge/ High Level Select Register */
#define REG_PIOD_FRLHSR    (*(RoReg*)0xFFFFF8D8U) /**< \brief (PIOD) Fall/Rise - Low/High Status Register */
#define REG_PIOD_LOCKSR    (*(RoReg*)0xFFFFF8E0U) /**< \brief (PIOD) Lock Status */
#define REG_PIOD_WPMR      (*(RwReg*)0xFFFFF8E4U) /**< \brief (PIOD) Write Protect Mode Register */
#define REG_PIOD_WPSR      (*(RoReg*)0xFFFFF8E8U) /**< \brief (PIOD) Write Protect Status Register */
#define REG_PIOD_SCHMITT   (*(RwReg*)0xFFFFF900U) /**< \brief (PIOD) Schmitt Trigger Register */
#define REG_PIOD_DRIVER1   (*(RwReg*)0xFFFFF918U) /**< \brief (PIOD) I/O Drive Register 1 */
#define REG_PIOD_DRIVER2   (*(RwReg*)0xFFFFF91CU) /**< \brief (PIOD) I/O Drive Register 2 */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_PIOD_INSTANCE_ */
