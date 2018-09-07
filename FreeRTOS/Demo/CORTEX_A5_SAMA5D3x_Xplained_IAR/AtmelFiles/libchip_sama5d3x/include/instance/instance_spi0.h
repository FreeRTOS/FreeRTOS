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

#ifndef _SAMA5_SPI0_INSTANCE_
#define _SAMA5_SPI0_INSTANCE_

/* ========== Register definition for SPI0 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_SPI0_CR              (0xF0004000U) /**< \brief (SPI0) Control Register */
#define REG_SPI0_MR              (0xF0004004U) /**< \brief (SPI0) Mode Register */
#define REG_SPI0_RDR             (0xF0004008U) /**< \brief (SPI0) Receive Data Register */
#define REG_SPI0_TDR             (0xF000400CU) /**< \brief (SPI0) Transmit Data Register */
#define REG_SPI0_SR              (0xF0004010U) /**< \brief (SPI0) Status Register */
#define REG_SPI0_IER             (0xF0004014U) /**< \brief (SPI0) Interrupt Enable Register */
#define REG_SPI0_IDR             (0xF0004018U) /**< \brief (SPI0) Interrupt Disable Register */
#define REG_SPI0_IMR             (0xF000401CU) /**< \brief (SPI0) Interrupt Mask Register */
#define REG_SPI0_CSR             (0xF0004030U) /**< \brief (SPI0) Chip Select Register */
#define REG_SPI0_WPMR            (0xF00040E4U) /**< \brief (SPI0) Write Protection Control Register */
#define REG_SPI0_WPSR            (0xF00040E8U) /**< \brief (SPI0) Write Protection Status Register */
#else
#define REG_SPI0_CR     (*(WoReg*)0xF0004000U) /**< \brief (SPI0) Control Register */
#define REG_SPI0_MR     (*(RwReg*)0xF0004004U) /**< \brief (SPI0) Mode Register */
#define REG_SPI0_RDR    (*(RoReg*)0xF0004008U) /**< \brief (SPI0) Receive Data Register */
#define REG_SPI0_TDR    (*(WoReg*)0xF000400CU) /**< \brief (SPI0) Transmit Data Register */
#define REG_SPI0_SR     (*(RoReg*)0xF0004010U) /**< \brief (SPI0) Status Register */
#define REG_SPI0_IER    (*(WoReg*)0xF0004014U) /**< \brief (SPI0) Interrupt Enable Register */
#define REG_SPI0_IDR    (*(WoReg*)0xF0004018U) /**< \brief (SPI0) Interrupt Disable Register */
#define REG_SPI0_IMR    (*(RoReg*)0xF000401CU) /**< \brief (SPI0) Interrupt Mask Register */
#define REG_SPI0_CSR    (*(RwReg*)0xF0004030U) /**< \brief (SPI0) Chip Select Register */
#define REG_SPI0_WPMR   (*(RwReg*)0xF00040E4U) /**< \brief (SPI0) Write Protection Control Register */
#define REG_SPI0_WPSR   (*(RoReg*)0xF00040E8U) /**< \brief (SPI0) Write Protection Status Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_SPI0_INSTANCE_ */
