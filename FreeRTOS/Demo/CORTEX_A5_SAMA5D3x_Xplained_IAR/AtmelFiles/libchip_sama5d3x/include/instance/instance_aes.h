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

#ifndef _SAMA5_AES_INSTANCE_
#define _SAMA5_AES_INSTANCE_

/* ========== Register definition for AES peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_AES_CR                 (0xF8038000U) /**< \brief (AES) Control Register */
#define REG_AES_MR                 (0xF8038004U) /**< \brief (AES) Mode Register */
#define REG_AES_IER                (0xF8038010U) /**< \brief (AES) Interrupt Enable Register */
#define REG_AES_IDR                (0xF8038014U) /**< \brief (AES) Interrupt Disable Register */
#define REG_AES_IMR                (0xF8038018U) /**< \brief (AES) Interrupt Mask Register */
#define REG_AES_ISR                (0xF803801CU) /**< \brief (AES) Interrupt Status Register */
#define REG_AES_KEYWR              (0xF8038020U) /**< \brief (AES) Key Word Register */
#define REG_AES_IDATAR             (0xF8038040U) /**< \brief (AES) Input Data Register */
#define REG_AES_ODATAR             (0xF8038050U) /**< \brief (AES) Output Data Register */
#define REG_AES_IVR                (0xF8038060U) /**< \brief (AES) Initialization Vector Register */
#else
#define REG_AES_CR        (*(WoReg*)0xF8038000U) /**< \brief (AES) Control Register */
#define REG_AES_MR        (*(RwReg*)0xF8038004U) /**< \brief (AES) Mode Register */
#define REG_AES_IER       (*(WoReg*)0xF8038010U) /**< \brief (AES) Interrupt Enable Register */
#define REG_AES_IDR       (*(WoReg*)0xF8038014U) /**< \brief (AES) Interrupt Disable Register */
#define REG_AES_IMR       (*(RoReg*)0xF8038018U) /**< \brief (AES) Interrupt Mask Register */
#define REG_AES_ISR       (*(RoReg*)0xF803801CU) /**< \brief (AES) Interrupt Status Register */
#define REG_AES_KEYWR     (*(WoReg*)0xF8038020U) /**< \brief (AES) Key Word Register */
#define REG_AES_IDATAR    (*(WoReg*)0xF8038040U) /**< \brief (AES) Input Data Register */
#define REG_AES_ODATAR    (*(RoReg*)0xF8038050U) /**< \brief (AES) Output Data Register */
#define REG_AES_IVR       (*(WoReg*)0xF8038060U) /**< \brief (AES) Initialization Vector Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_AES_INSTANCE_ */
