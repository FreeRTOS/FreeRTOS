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

#ifndef _SAMA5_ADC_INSTANCE_
#define _SAMA5_ADC_INSTANCE_

/* ========== Register definition for ADC peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_ADC_CR               (0xF8018000U) /**< \brief (ADC) Control Register */
#define REG_ADC_MR               (0xF8018004U) /**< \brief (ADC) Mode Register */
#define REG_ADC_SEQR1            (0xF8018008U) /**< \brief (ADC) Channel Sequence Register 1 */
#define REG_ADC_SEQR2            (0xF801800CU) /**< \brief (ADC) Channel Sequence Register 2 */
#define REG_ADC_CHER             (0xF8018010U) /**< \brief (ADC) Channel Enable Register */
#define REG_ADC_CHDR             (0xF8018014U) /**< \brief (ADC) Channel Disable Register */
#define REG_ADC_CHSR             (0xF8018018U) /**< \brief (ADC) Channel Status Register */
#define REG_ADC_LCDR             (0xF8018020U) /**< \brief (ADC) Last Converted Data Register */
#define REG_ADC_IER              (0xF8018024U) /**< \brief (ADC) Interrupt Enable Register */
#define REG_ADC_IDR              (0xF8018028U) /**< \brief (ADC) Interrupt Disable Register */
#define REG_ADC_IMR              (0xF801802CU) /**< \brief (ADC) Interrupt Mask Register */
#define REG_ADC_ISR              (0xF8018030U) /**< \brief (ADC) Interrupt Status Register */
#define REG_ADC_OVER             (0xF801803CU) /**< \brief (ADC) Overrun Status Register */
#define REG_ADC_EMR              (0xF8018040U) /**< \brief (ADC) Extended Mode Register */
#define REG_ADC_CWR              (0xF8018044U) /**< \brief (ADC) Compare Window Register */
#define REG_ADC_CGR              (0xF8018048U) /**< \brief (ADC) Channel Gain Register */
#define REG_ADC_COR              (0xF801804CU) /**< \brief (ADC) Channel Offset Register */
#define REG_ADC_CDR              (0xF8018050U) /**< \brief (ADC) Channel Data Register */
#define REG_ADC_ACR              (0xF8018094U) /**< \brief (ADC) Analog Control Register */
#define REG_ADC_TSMR             (0xF80180B0U) /**< \brief (ADC) Touchscreen Mode Register */
#define REG_ADC_XPOSR            (0xF80180B4U) /**< \brief (ADC) Touchscreen X Position Register */
#define REG_ADC_YPOSR            (0xF80180B8U) /**< \brief (ADC) Touchscreen Y Position Register */
#define REG_ADC_PRESSR           (0xF80180BCU) /**< \brief (ADC) Touchscreen Pressure Register */
#define REG_ADC_TRGR             (0xF80180C0U) /**< \brief (ADC) Trigger Register */
#define REG_ADC_WPMR             (0xF80180E4U) /**< \brief (ADC) Write Protect Mode Register */
#define REG_ADC_WPSR             (0xF80180E8U) /**< \brief (ADC) Write Protect Status Register */
#else
#define REG_ADC_CR      (*(WoReg*)0xF8018000U) /**< \brief (ADC) Control Register */
#define REG_ADC_MR      (*(RwReg*)0xF8018004U) /**< \brief (ADC) Mode Register */
#define REG_ADC_SEQR1   (*(RwReg*)0xF8018008U) /**< \brief (ADC) Channel Sequence Register 1 */
#define REG_ADC_SEQR2   (*(RwReg*)0xF801800CU) /**< \brief (ADC) Channel Sequence Register 2 */
#define REG_ADC_CHER    (*(WoReg*)0xF8018010U) /**< \brief (ADC) Channel Enable Register */
#define REG_ADC_CHDR    (*(WoReg*)0xF8018014U) /**< \brief (ADC) Channel Disable Register */
#define REG_ADC_CHSR    (*(RoReg*)0xF8018018U) /**< \brief (ADC) Channel Status Register */
#define REG_ADC_LCDR    (*(RoReg*)0xF8018020U) /**< \brief (ADC) Last Converted Data Register */
#define REG_ADC_IER     (*(WoReg*)0xF8018024U) /**< \brief (ADC) Interrupt Enable Register */
#define REG_ADC_IDR     (*(WoReg*)0xF8018028U) /**< \brief (ADC) Interrupt Disable Register */
#define REG_ADC_IMR     (*(RoReg*)0xF801802CU) /**< \brief (ADC) Interrupt Mask Register */
#define REG_ADC_ISR     (*(RoReg*)0xF8018030U) /**< \brief (ADC) Interrupt Status Register */
#define REG_ADC_OVER    (*(RoReg*)0xF801803CU) /**< \brief (ADC) Overrun Status Register */
#define REG_ADC_EMR     (*(RwReg*)0xF8018040U) /**< \brief (ADC) Extended Mode Register */
#define REG_ADC_CWR     (*(RwReg*)0xF8018044U) /**< \brief (ADC) Compare Window Register */
#define REG_ADC_CGR     (*(RwReg*)0xF8018048U) /**< \brief (ADC) Channel Gain Register */
#define REG_ADC_COR     (*(RwReg*)0xF801804CU) /**< \brief (ADC) Channel Offset Register */
#define REG_ADC_CDR     (*(RoReg*)0xF8018050U) /**< \brief (ADC) Channel Data Register */
#define REG_ADC_ACR     (*(RwReg*)0xF8018094U) /**< \brief (ADC) Analog Control Register */
#define REG_ADC_TSMR    (*(RwReg*)0xF80180B0U) /**< \brief (ADC) Touchscreen Mode Register */
#define REG_ADC_XPOSR   (*(RoReg*)0xF80180B4U) /**< \brief (ADC) Touchscreen X Position Register */
#define REG_ADC_YPOSR   (*(RoReg*)0xF80180B8U) /**< \brief (ADC) Touchscreen Y Position Register */
#define REG_ADC_PRESSR  (*(RoReg*)0xF80180BCU) /**< \brief (ADC) Touchscreen Pressure Register */
#define REG_ADC_TRGR    (*(RwReg*)0xF80180C0U) /**< \brief (ADC) Trigger Register */
#define REG_ADC_WPMR    (*(RwReg*)0xF80180E4U) /**< \brief (ADC) Write Protect Mode Register */
#define REG_ADC_WPSR    (*(RoReg*)0xF80180E8U) /**< \brief (ADC) Write Protect Status Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_ADC_INSTANCE_ */
