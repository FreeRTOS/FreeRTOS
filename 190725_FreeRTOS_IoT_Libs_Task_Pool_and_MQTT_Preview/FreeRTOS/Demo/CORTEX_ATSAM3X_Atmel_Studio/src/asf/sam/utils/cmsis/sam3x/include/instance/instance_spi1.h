/**
 * \file
 *
 * Copyright (c) 2012 Atmel Corporation. All rights reserved.
 *
 * \asf_license_start
 *
 * \page License
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 *
 * 3. The name of Atmel may not be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * 4. This software may only be redistributed and used in connection with an
 *    Atmel microcontroller product.
 *
 * THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * EXPRESSLY AND SPECIFICALLY DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
 * ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *
 * \asf_license_stop
 *
 */

#ifndef _SAM3XA_SPI1_INSTANCE_
#define _SAM3XA_SPI1_INSTANCE_

/* ========== Register definition for SPI1 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_SPI1_CR              (0x4000C000U) /**< \brief (SPI1) Control Register */
#define REG_SPI1_MR              (0x4000C004U) /**< \brief (SPI1) Mode Register */
#define REG_SPI1_RDR             (0x4000C008U) /**< \brief (SPI1) Receive Data Register */
#define REG_SPI1_TDR             (0x4000C00CU) /**< \brief (SPI1) Transmit Data Register */
#define REG_SPI1_SR              (0x4000C010U) /**< \brief (SPI1) Status Register */
#define REG_SPI1_IER             (0x4000C014U) /**< \brief (SPI1) Interrupt Enable Register */
#define REG_SPI1_IDR             (0x4000C018U) /**< \brief (SPI1) Interrupt Disable Register */
#define REG_SPI1_IMR             (0x4000C01CU) /**< \brief (SPI1) Interrupt Mask Register */
#define REG_SPI1_CSR             (0x4000C030U) /**< \brief (SPI1) Chip Select Register */
#define REG_SPI1_WPMR            (0x4000C0E4U) /**< \brief (SPI1) Write Protection Control Register */
#define REG_SPI1_WPSR            (0x4000C0E8U) /**< \brief (SPI1) Write Protection Status Register */
#else
#define REG_SPI1_CR     (*(WoReg*)0x4000C000U) /**< \brief (SPI1) Control Register */
#define REG_SPI1_MR     (*(RwReg*)0x4000C004U) /**< \brief (SPI1) Mode Register */
#define REG_SPI1_RDR    (*(RoReg*)0x4000C008U) /**< \brief (SPI1) Receive Data Register */
#define REG_SPI1_TDR    (*(WoReg*)0x4000C00CU) /**< \brief (SPI1) Transmit Data Register */
#define REG_SPI1_SR     (*(RoReg*)0x4000C010U) /**< \brief (SPI1) Status Register */
#define REG_SPI1_IER    (*(WoReg*)0x4000C014U) /**< \brief (SPI1) Interrupt Enable Register */
#define REG_SPI1_IDR    (*(WoReg*)0x4000C018U) /**< \brief (SPI1) Interrupt Disable Register */
#define REG_SPI1_IMR    (*(RoReg*)0x4000C01CU) /**< \brief (SPI1) Interrupt Mask Register */
#define REG_SPI1_CSR    (*(RwReg*)0x4000C030U) /**< \brief (SPI1) Chip Select Register */
#define REG_SPI1_WPMR   (*(RwReg*)0x4000C0E4U) /**< \brief (SPI1) Write Protection Control Register */
#define REG_SPI1_WPSR   (*(RoReg*)0x4000C0E8U) /**< \brief (SPI1) Write Protection Status Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAM3XA_SPI1_INSTANCE_ */
