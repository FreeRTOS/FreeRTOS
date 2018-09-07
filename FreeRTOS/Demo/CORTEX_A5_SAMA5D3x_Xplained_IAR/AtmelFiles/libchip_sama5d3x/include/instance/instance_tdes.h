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

#ifndef _SAMA5_TDES_INSTANCE_
#define _SAMA5_TDES_INSTANCE_

/* ========== Register definition for TDES peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_TDES_CR                 (0xF803C000U) /**< \brief (TDES) Control Register */
#define REG_TDES_MR                 (0xF803C004U) /**< \brief (TDES) Mode Register */
#define REG_TDES_IER                (0xF803C010U) /**< \brief (TDES) Interrupt Enable Register */
#define REG_TDES_IDR                (0xF803C014U) /**< \brief (TDES) Interrupt Disable Register */
#define REG_TDES_IMR                (0xF803C018U) /**< \brief (TDES) Interrupt Mask Register */
#define REG_TDES_ISR                (0xF803C01CU) /**< \brief (TDES) Interrupt Status Register */
#define REG_TDES_KEY1WR             (0xF803C020U) /**< \brief (TDES) Key 1 Word Register */
#define REG_TDES_KEY2WR             (0xF803C028U) /**< \brief (TDES) Key 2 Word Register */
#define REG_TDES_KEY3WR             (0xF803C030U) /**< \brief (TDES) Key 3 Word Register */
#define REG_TDES_IDATAR             (0xF803C040U) /**< \brief (TDES) Input Data Register */
#define REG_TDES_ODATAR             (0xF803C050U) /**< \brief (TDES) Output Data Register */
#define REG_TDES_IVR                (0xF803C060U) /**< \brief (TDES) Initialization Vector Register */
#define REG_TDES_XTEARNDR           (0xF803C070U) /**< \brief (TDES) XTEA Rounds Register */
#else
#define REG_TDES_CR        (*(WoReg*)0xF803C000U) /**< \brief (TDES) Control Register */
#define REG_TDES_MR        (*(RwReg*)0xF803C004U) /**< \brief (TDES) Mode Register */
#define REG_TDES_IER       (*(WoReg*)0xF803C010U) /**< \brief (TDES) Interrupt Enable Register */
#define REG_TDES_IDR       (*(WoReg*)0xF803C014U) /**< \brief (TDES) Interrupt Disable Register */
#define REG_TDES_IMR       (*(RoReg*)0xF803C018U) /**< \brief (TDES) Interrupt Mask Register */
#define REG_TDES_ISR       (*(RoReg*)0xF803C01CU) /**< \brief (TDES) Interrupt Status Register */
#define REG_TDES_KEY1WR    (*(WoReg*)0xF803C020U) /**< \brief (TDES) Key 1 Word Register */
#define REG_TDES_KEY2WR    (*(WoReg*)0xF803C028U) /**< \brief (TDES) Key 2 Word Register */
#define REG_TDES_KEY3WR    (*(WoReg*)0xF803C030U) /**< \brief (TDES) Key 3 Word Register */
#define REG_TDES_IDATAR    (*(WoReg*)0xF803C040U) /**< \brief (TDES) Input Data Register */
#define REG_TDES_ODATAR    (*(RoReg*)0xF803C050U) /**< \brief (TDES) Output Data Register */
#define REG_TDES_IVR       (*(WoReg*)0xF803C060U) /**< \brief (TDES) Initialization Vector Register */
#define REG_TDES_XTEARNDR  (*(RwReg*)0xF803C070U) /**< \brief (TDES) XTEA Rounds Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_TDES_INSTANCE_ */
