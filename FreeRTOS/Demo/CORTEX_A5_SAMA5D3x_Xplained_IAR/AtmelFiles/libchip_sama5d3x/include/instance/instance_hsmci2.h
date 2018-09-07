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

#ifndef _SAMA5_HSMCI2_INSTANCE_
#define _SAMA5_HSMCI2_INSTANCE_

/* ========== Register definition for HSMCI2 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_HSMCI2_CR                 (0xF8004000U) /**< \brief (HSMCI2) Control Register */
#define REG_HSMCI2_MR                 (0xF8004004U) /**< \brief (HSMCI2) Mode Register */
#define REG_HSMCI2_DTOR               (0xF8004008U) /**< \brief (HSMCI2) Data Timeout Register */
#define REG_HSMCI2_SDCR               (0xF800400CU) /**< \brief (HSMCI2) SD/SDIO Card Register */
#define REG_HSMCI2_ARGR               (0xF8004010U) /**< \brief (HSMCI2) Argument Register */
#define REG_HSMCI2_CMDR               (0xF8004014U) /**< \brief (HSMCI2) Command Register */
#define REG_HSMCI2_BLKR               (0xF8004018U) /**< \brief (HSMCI2) Block Register */
#define REG_HSMCI2_CSTOR              (0xF800401CU) /**< \brief (HSMCI2) Completion Signal Timeout Register */
#define REG_HSMCI2_RSPR               (0xF8004020U) /**< \brief (HSMCI2) Response Register */
#define REG_HSMCI2_RDR                (0xF8004030U) /**< \brief (HSMCI2) Receive Data Register */
#define REG_HSMCI2_TDR                (0xF8004034U) /**< \brief (HSMCI2) Transmit Data Register */
#define REG_HSMCI2_SR                 (0xF8004040U) /**< \brief (HSMCI2) Status Register */
#define REG_HSMCI2_IER                (0xF8004044U) /**< \brief (HSMCI2) Interrupt Enable Register */
#define REG_HSMCI2_IDR                (0xF8004048U) /**< \brief (HSMCI2) Interrupt Disable Register */
#define REG_HSMCI2_IMR                (0xF800404CU) /**< \brief (HSMCI2) Interrupt Mask Register */
#define REG_HSMCI2_DMA                (0xF8004050U) /**< \brief (HSMCI2) DMA Configuration Register */
#define REG_HSMCI2_CFG                (0xF8004054U) /**< \brief (HSMCI2) Configuration Register */
#define REG_HSMCI2_WPMR               (0xF80040E4U) /**< \brief (HSMCI2) Write Protection Mode Register */
#define REG_HSMCI2_WPSR               (0xF80040E8U) /**< \brief (HSMCI2) Write Protection Status Register */
#define REG_HSMCI2_FIFO               (0xF8004200U) /**< \brief (HSMCI2) FIFO Memory Aperture0 */
#else
#define REG_HSMCI2_CR        (*(WoReg*)0xF8004000U) /**< \brief (HSMCI2) Control Register */
#define REG_HSMCI2_MR        (*(RwReg*)0xF8004004U) /**< \brief (HSMCI2) Mode Register */
#define REG_HSMCI2_DTOR      (*(RwReg*)0xF8004008U) /**< \brief (HSMCI2) Data Timeout Register */
#define REG_HSMCI2_SDCR      (*(RwReg*)0xF800400CU) /**< \brief (HSMCI2) SD/SDIO Card Register */
#define REG_HSMCI2_ARGR      (*(RwReg*)0xF8004010U) /**< \brief (HSMCI2) Argument Register */
#define REG_HSMCI2_CMDR      (*(WoReg*)0xF8004014U) /**< \brief (HSMCI2) Command Register */
#define REG_HSMCI2_BLKR      (*(RwReg*)0xF8004018U) /**< \brief (HSMCI2) Block Register */
#define REG_HSMCI2_CSTOR     (*(RwReg*)0xF800401CU) /**< \brief (HSMCI2) Completion Signal Timeout Register */
#define REG_HSMCI2_RSPR      (*(RoReg*)0xF8004020U) /**< \brief (HSMCI2) Response Register */
#define REG_HSMCI2_RDR       (*(RoReg*)0xF8004030U) /**< \brief (HSMCI2) Receive Data Register */
#define REG_HSMCI2_TDR       (*(WoReg*)0xF8004034U) /**< \brief (HSMCI2) Transmit Data Register */
#define REG_HSMCI2_SR        (*(RoReg*)0xF8004040U) /**< \brief (HSMCI2) Status Register */
#define REG_HSMCI2_IER       (*(WoReg*)0xF8004044U) /**< \brief (HSMCI2) Interrupt Enable Register */
#define REG_HSMCI2_IDR       (*(WoReg*)0xF8004048U) /**< \brief (HSMCI2) Interrupt Disable Register */
#define REG_HSMCI2_IMR       (*(RoReg*)0xF800404CU) /**< \brief (HSMCI2) Interrupt Mask Register */
#define REG_HSMCI2_DMA       (*(RwReg*)0xF8004050U) /**< \brief (HSMCI2) DMA Configuration Register */
#define REG_HSMCI2_CFG       (*(RwReg*)0xF8004054U) /**< \brief (HSMCI2) Configuration Register */
#define REG_HSMCI2_WPMR      (*(RwReg*)0xF80040E4U) /**< \brief (HSMCI2) Write Protection Mode Register */
#define REG_HSMCI2_WPSR      (*(RoReg*)0xF80040E8U) /**< \brief (HSMCI2) Write Protection Status Register */
#define REG_HSMCI2_FIFO      (*(RwReg*)0xF8004200U) /**< \brief (HSMCI2) FIFO Memory Aperture0 */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_HSMCI2_INSTANCE_ */
