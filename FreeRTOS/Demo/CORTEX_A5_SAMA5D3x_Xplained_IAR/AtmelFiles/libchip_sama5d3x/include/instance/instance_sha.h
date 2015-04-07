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

#ifndef _SAMA5_SHA_INSTANCE_
#define _SAMA5_SHA_INSTANCE_

/* ========== Register definition for SHA peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_SHA_CR                   (0xF8034000U) /**< \brief (SHA) Control Register */
#define REG_SHA_MR                   (0xF8034004U) /**< \brief (SHA) Mode Register */
#define REG_SHA_IER                  (0xF8034010U) /**< \brief (SHA) Interrupt Enable Register */
#define REG_SHA_IDR                  (0xF8034014U) /**< \brief (SHA) Interrupt Disable Register */
#define REG_SHA_IMR                  (0xF8034018U) /**< \brief (SHA) Interrupt Mask Register */
#define REG_SHA_ISR                  (0xF803401CU) /**< \brief (SHA) Interrupt Status Register */
#define REG_SHA_IDATAR               (0xF8034040U) /**< \brief (SHA) Input Data 0 Register */
#define REG_SHA_IODATAR              (0xF8034080U) /**< \brief (SHA) Input/Output Data 0 Register */
#else
#define REG_SHA_CR          (*(WoReg*)0xF8034000U) /**< \brief (SHA) Control Register */
#define REG_SHA_MR          (*(RwReg*)0xF8034004U) /**< \brief (SHA) Mode Register */
#define REG_SHA_IER         (*(WoReg*)0xF8034010U) /**< \brief (SHA) Interrupt Enable Register */
#define REG_SHA_IDR         (*(WoReg*)0xF8034014U) /**< \brief (SHA) Interrupt Disable Register */
#define REG_SHA_IMR         (*(RoReg*)0xF8034018U) /**< \brief (SHA) Interrupt Mask Register */
#define REG_SHA_ISR         (*(RoReg*)0xF803401CU) /**< \brief (SHA) Interrupt Status Register */
#define REG_SHA_IDATAR      (*(WoReg*)0xF8034040U) /**< \brief (SHA) Input Data 0 Register */
#define REG_SHA_IODATAR     (*(RwReg*)0xF8034080U) /**< \brief (SHA) Input/Output Data 0 Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_SHA_INSTANCE_ */
