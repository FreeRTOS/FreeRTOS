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

#ifndef _SAMA5_HSMCI1_INSTANCE_
#define _SAMA5_HSMCI1_INSTANCE_

/* ========== Register definition for HSMCI1 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_HSMCI1_CR                 (0xF8000000U) /**< \brief (HSMCI1) Control Register */
#define REG_HSMCI1_MR                 (0xF8000004U) /**< \brief (HSMCI1) Mode Register */
#define REG_HSMCI1_DTOR               (0xF8000008U) /**< \brief (HSMCI1) Data Timeout Register */
#define REG_HSMCI1_SDCR               (0xF800000CU) /**< \brief (HSMCI1) SD/SDIO Card Register */
#define REG_HSMCI1_ARGR               (0xF8000010U) /**< \brief (HSMCI1) Argument Register */
#define REG_HSMCI1_CMDR               (0xF8000014U) /**< \brief (HSMCI1) Command Register */
#define REG_HSMCI1_BLKR               (0xF8000018U) /**< \brief (HSMCI1) Block Register */
#define REG_HSMCI1_CSTOR              (0xF800001CU) /**< \brief (HSMCI1) Completion Signal Timeout Register */
#define REG_HSMCI1_RSPR               (0xF8000020U) /**< \brief (HSMCI1) Response Register */
#define REG_HSMCI1_RDR                (0xF8000030U) /**< \brief (HSMCI1) Receive Data Register */
#define REG_HSMCI1_TDR                (0xF8000034U) /**< \brief (HSMCI1) Transmit Data Register */
#define REG_HSMCI1_SR                 (0xF8000040U) /**< \brief (HSMCI1) Status Register */
#define REG_HSMCI1_IER                (0xF8000044U) /**< \brief (HSMCI1) Interrupt Enable Register */
#define REG_HSMCI1_IDR                (0xF8000048U) /**< \brief (HSMCI1) Interrupt Disable Register */
#define REG_HSMCI1_IMR                (0xF800004CU) /**< \brief (HSMCI1) Interrupt Mask Register */
#define REG_HSMCI1_DMA                (0xF8000050U) /**< \brief (HSMCI1) DMA Configuration Register */
#define REG_HSMCI1_CFG                (0xF8000054U) /**< \brief (HSMCI1) Configuration Register */
#define REG_HSMCI1_WPMR               (0xF80000E4U) /**< \brief (HSMCI1) Write Protection Mode Register */
#define REG_HSMCI1_WPSR               (0xF80000E8U) /**< \brief (HSMCI1) Write Protection Status Register */
#define REG_HSMCI1_FIFO               (0xF8000200U) /**< \brief (HSMCI1) FIFO Memory Aperture0 */
#else
#define REG_HSMCI1_CR        (*(WoReg*)0xF8000000U) /**< \brief (HSMCI1) Control Register */
#define REG_HSMCI1_MR        (*(RwReg*)0xF8000004U) /**< \brief (HSMCI1) Mode Register */
#define REG_HSMCI1_DTOR      (*(RwReg*)0xF8000008U) /**< \brief (HSMCI1) Data Timeout Register */
#define REG_HSMCI1_SDCR      (*(RwReg*)0xF800000CU) /**< \brief (HSMCI1) SD/SDIO Card Register */
#define REG_HSMCI1_ARGR      (*(RwReg*)0xF8000010U) /**< \brief (HSMCI1) Argument Register */
#define REG_HSMCI1_CMDR      (*(WoReg*)0xF8000014U) /**< \brief (HSMCI1) Command Register */
#define REG_HSMCI1_BLKR      (*(RwReg*)0xF8000018U) /**< \brief (HSMCI1) Block Register */
#define REG_HSMCI1_CSTOR     (*(RwReg*)0xF800001CU) /**< \brief (HSMCI1) Completion Signal Timeout Register */
#define REG_HSMCI1_RSPR      (*(RoReg*)0xF8000020U) /**< \brief (HSMCI1) Response Register */
#define REG_HSMCI1_RDR       (*(RoReg*)0xF8000030U) /**< \brief (HSMCI1) Receive Data Register */
#define REG_HSMCI1_TDR       (*(WoReg*)0xF8000034U) /**< \brief (HSMCI1) Transmit Data Register */
#define REG_HSMCI1_SR        (*(RoReg*)0xF8000040U) /**< \brief (HSMCI1) Status Register */
#define REG_HSMCI1_IER       (*(WoReg*)0xF8000044U) /**< \brief (HSMCI1) Interrupt Enable Register */
#define REG_HSMCI1_IDR       (*(WoReg*)0xF8000048U) /**< \brief (HSMCI1) Interrupt Disable Register */
#define REG_HSMCI1_IMR       (*(RoReg*)0xF800004CU) /**< \brief (HSMCI1) Interrupt Mask Register */
#define REG_HSMCI1_DMA       (*(RwReg*)0xF8000050U) /**< \brief (HSMCI1) DMA Configuration Register */
#define REG_HSMCI1_CFG       (*(RwReg*)0xF8000054U) /**< \brief (HSMCI1) Configuration Register */
#define REG_HSMCI1_WPMR      (*(RwReg*)0xF80000E4U) /**< \brief (HSMCI1) Write Protection Mode Register */
#define REG_HSMCI1_WPSR      (*(RoReg*)0xF80000E8U) /**< \brief (HSMCI1) Write Protection Status Register */
#define REG_HSMCI1_FIFO      (*(RwReg*)0xF8000200U) /**< \brief (HSMCI1) FIFO Memory Aperture0 */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_HSMCI1_INSTANCE_ */
