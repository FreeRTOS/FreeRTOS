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

#ifndef _SAMA5_PMC_INSTANCE_
#define _SAMA5_PMC_INSTANCE_

/* ========== Register definition for PMC peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_PMC_SCER             (0xFFFFFC00U) /**< \brief (PMC) System Clock Enable Register */
#define REG_PMC_SCDR             (0xFFFFFC04U) /**< \brief (PMC) System Clock Disable Register */
#define REG_PMC_SCSR             (0xFFFFFC08U) /**< \brief (PMC) System Clock Status Register */
#define REG_PMC_PCER0            (0xFFFFFC10U) /**< \brief (PMC) Peripheral Clock Enable Register 0 */
#define REG_PMC_PCDR0            (0xFFFFFC14U) /**< \brief (PMC) Peripheral Clock Disable Register 0 */
#define REG_PMC_PCSR0            (0xFFFFFC18U) /**< \brief (PMC) Peripheral Clock Status Register 0 */
#define REG_CKGR_UCKR            (0xFFFFFC1CU) /**< \brief (PMC) UTMI Clock Register */
#define REG_CKGR_MOR             (0xFFFFFC20U) /**< \brief (PMC) Main Oscillator Register */
#define REG_CKGR_MCFR            (0xFFFFFC24U) /**< \brief (PMC) Main Clock Frequency Register */
#define REG_CKGR_PLLAR           (0xFFFFFC28U) /**< \brief (PMC) PLLA Register */
#define REG_PMC_MCKR             (0xFFFFFC30U) /**< \brief (PMC) Master Clock Register */
#define REG_PMC_USB              (0xFFFFFC38U) /**< \brief (PMC) USB Clock Register */
#define REG_PMC_SMD              (0xFFFFFC3CU) /**< \brief (PMC) Soft Modem Clock Register */
#define REG_PMC_PCK              (0xFFFFFC40U) /**< \brief (PMC) Programmable Clock 0 Register */
#define REG_PMC_IER              (0xFFFFFC60U) /**< \brief (PMC) Interrupt Enable Register */
#define REG_PMC_IDR              (0xFFFFFC64U) /**< \brief (PMC) Interrupt Disable Register */
#define REG_PMC_SR               (0xFFFFFC68U) /**< \brief (PMC) Status Register */
#define REG_PMC_IMR              (0xFFFFFC6CU) /**< \brief (PMC) Interrupt Mask Register */
#define REG_PMC_PLLICPR          (0xFFFFFC80U) /**< \brief (PMC) PLL Charge Pump Current Register */
#define REG_PMC_WPMR             (0xFFFFFCE4U) /**< \brief (PMC) Write Protect Mode Register */
#define REG_PMC_WPSR             (0xFFFFFCE8U) /**< \brief (PMC) Write Protect Status Register */
#define REG_PMC_PCER1            (0xFFFFFD00U) /**< \brief (PMC) Peripheral Clock Enable Register 1 */
#define REG_PMC_PCDR1            (0xFFFFFD04U) /**< \brief (PMC) Peripheral Clock Disable Register 1 */
#define REG_PMC_PCSR1            (0xFFFFFD08U) /**< \brief (PMC) Peripheral Clock Status Register 1 */
#define REG_PMC_PCR              (0xFFFFFD0CU) /**< \brief (PMC) Peripheral Control Register */
#else
#define REG_PMC_SCER    (*(WoReg*)0xFFFFFC00U) /**< \brief (PMC) System Clock Enable Register */
#define REG_PMC_SCDR    (*(WoReg*)0xFFFFFC04U) /**< \brief (PMC) System Clock Disable Register */
#define REG_PMC_SCSR    (*(RoReg*)0xFFFFFC08U) /**< \brief (PMC) System Clock Status Register */
#define REG_PMC_PCER0   (*(WoReg*)0xFFFFFC10U) /**< \brief (PMC) Peripheral Clock Enable Register 0 */
#define REG_PMC_PCDR0   (*(WoReg*)0xFFFFFC14U) /**< \brief (PMC) Peripheral Clock Disable Register 0 */
#define REG_PMC_PCSR0   (*(RoReg*)0xFFFFFC18U) /**< \brief (PMC) Peripheral Clock Status Register 0 */
#define REG_CKGR_UCKR   (*(RwReg*)0xFFFFFC1CU) /**< \brief (PMC) UTMI Clock Register */
#define REG_CKGR_MOR    (*(RwReg*)0xFFFFFC20U) /**< \brief (PMC) Main Oscillator Register */
#define REG_CKGR_MCFR   (*(RoReg*)0xFFFFFC24U) /**< \brief (PMC) Main Clock Frequency Register */
#define REG_CKGR_PLLAR  (*(RwReg*)0xFFFFFC28U) /**< \brief (PMC) PLLA Register */
#define REG_PMC_MCKR    (*(RwReg*)0xFFFFFC30U) /**< \brief (PMC) Master Clock Register */
#define REG_PMC_USB     (*(RwReg*)0xFFFFFC38U) /**< \brief (PMC) USB Clock Register */
#define REG_PMC_SMD     (*(RwReg*)0xFFFFFC3CU) /**< \brief (PMC) Soft Modem Clock Register */
#define REG_PMC_PCK     (*(RwReg*)0xFFFFFC40U) /**< \brief (PMC) Programmable Clock 0 Register */
#define REG_PMC_IER     (*(WoReg*)0xFFFFFC60U) /**< \brief (PMC) Interrupt Enable Register */
#define REG_PMC_IDR     (*(WoReg*)0xFFFFFC64U) /**< \brief (PMC) Interrupt Disable Register */
#define REG_PMC_SR      (*(RoReg*)0xFFFFFC68U) /**< \brief (PMC) Status Register */
#define REG_PMC_IMR     (*(RoReg*)0xFFFFFC6CU) /**< \brief (PMC) Interrupt Mask Register */
#define REG_PMC_PLLICPR (*(WoReg*)0xFFFFFC80U) /**< \brief (PMC) PLL Charge Pump Current Register */
#define REG_PMC_WPMR    (*(RwReg*)0xFFFFFCE4U) /**< \brief (PMC) Write Protect Mode Register */
#define REG_PMC_WPSR    (*(RoReg*)0xFFFFFCE8U) /**< \brief (PMC) Write Protect Status Register */
#define REG_PMC_PCER1   (*(WoReg*)0xFFFFFD00U) /**< \brief (PMC) Peripheral Clock Enable Register 1 */
#define REG_PMC_PCDR1   (*(WoReg*)0xFFFFFD04U) /**< \brief (PMC) Peripheral Clock Disable Register 1 */
#define REG_PMC_PCSR1   (*(RoReg*)0xFFFFFD08U) /**< \brief (PMC) Peripheral Clock Status Register 1 */
#define REG_PMC_PCR     (*(RwReg*)0xFFFFFD0CU) /**< \brief (PMC) Peripheral Control Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_PMC_INSTANCE_ */
