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

#ifndef _SAMA5_HSMCI0_INSTANCE_
#define _SAMA5_HSMCI0_INSTANCE_

/* ========== Register definition for HSMCI0 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_HSMCI0_CR                 (0xF0000000U) /**< \brief (HSMCI0) Control Register */
#define REG_HSMCI0_MR                 (0xF0000004U) /**< \brief (HSMCI0) Mode Register */
#define REG_HSMCI0_DTOR               (0xF0000008U) /**< \brief (HSMCI0) Data Timeout Register */
#define REG_HSMCI0_SDCR               (0xF000000CU) /**< \brief (HSMCI0) SD/SDIO Card Register */
#define REG_HSMCI0_ARGR               (0xF0000010U) /**< \brief (HSMCI0) Argument Register */
#define REG_HSMCI0_CMDR               (0xF0000014U) /**< \brief (HSMCI0) Command Register */
#define REG_HSMCI0_BLKR               (0xF0000018U) /**< \brief (HSMCI0) Block Register */
#define REG_HSMCI0_CSTOR              (0xF000001CU) /**< \brief (HSMCI0) Completion Signal Timeout Register */
#define REG_HSMCI0_RSPR               (0xF0000020U) /**< \brief (HSMCI0) Response Register */
#define REG_HSMCI0_RDR                (0xF0000030U) /**< \brief (HSMCI0) Receive Data Register */
#define REG_HSMCI0_TDR                (0xF0000034U) /**< \brief (HSMCI0) Transmit Data Register */
#define REG_HSMCI0_SR                 (0xF0000040U) /**< \brief (HSMCI0) Status Register */
#define REG_HSMCI0_IER                (0xF0000044U) /**< \brief (HSMCI0) Interrupt Enable Register */
#define REG_HSMCI0_IDR                (0xF0000048U) /**< \brief (HSMCI0) Interrupt Disable Register */
#define REG_HSMCI0_IMR                (0xF000004CU) /**< \brief (HSMCI0) Interrupt Mask Register */
#define REG_HSMCI0_DMA                (0xF0000050U) /**< \brief (HSMCI0) DMA Configuration Register */
#define REG_HSMCI0_CFG                (0xF0000054U) /**< \brief (HSMCI0) Configuration Register */
#define REG_HSMCI0_WPMR               (0xF00000E4U) /**< \brief (HSMCI0) Write Protection Mode Register */
#define REG_HSMCI0_WPSR               (0xF00000E8U) /**< \brief (HSMCI0) Write Protection Status Register */
#define REG_HSMCI0_FIFO               (0xF0000200U) /**< \brief (HSMCI0) FIFO Memory Aperture0 */
#else
#define REG_HSMCI0_CR        (*(WoReg*)0xF0000000U) /**< \brief (HSMCI0) Control Register */
#define REG_HSMCI0_MR        (*(RwReg*)0xF0000004U) /**< \brief (HSMCI0) Mode Register */
#define REG_HSMCI0_DTOR      (*(RwReg*)0xF0000008U) /**< \brief (HSMCI0) Data Timeout Register */
#define REG_HSMCI0_SDCR      (*(RwReg*)0xF000000CU) /**< \brief (HSMCI0) SD/SDIO Card Register */
#define REG_HSMCI0_ARGR      (*(RwReg*)0xF0000010U) /**< \brief (HSMCI0) Argument Register */
#define REG_HSMCI0_CMDR      (*(WoReg*)0xF0000014U) /**< \brief (HSMCI0) Command Register */
#define REG_HSMCI0_BLKR      (*(RwReg*)0xF0000018U) /**< \brief (HSMCI0) Block Register */
#define REG_HSMCI0_CSTOR     (*(RwReg*)0xF000001CU) /**< \brief (HSMCI0) Completion Signal Timeout Register */
#define REG_HSMCI0_RSPR      (*(RoReg*)0xF0000020U) /**< \brief (HSMCI0) Response Register */
#define REG_HSMCI0_RDR       (*(RoReg*)0xF0000030U) /**< \brief (HSMCI0) Receive Data Register */
#define REG_HSMCI0_TDR       (*(WoReg*)0xF0000034U) /**< \brief (HSMCI0) Transmit Data Register */
#define REG_HSMCI0_SR        (*(RoReg*)0xF0000040U) /**< \brief (HSMCI0) Status Register */
#define REG_HSMCI0_IER       (*(WoReg*)0xF0000044U) /**< \brief (HSMCI0) Interrupt Enable Register */
#define REG_HSMCI0_IDR       (*(WoReg*)0xF0000048U) /**< \brief (HSMCI0) Interrupt Disable Register */
#define REG_HSMCI0_IMR       (*(RoReg*)0xF000004CU) /**< \brief (HSMCI0) Interrupt Mask Register */
#define REG_HSMCI0_DMA       (*(RwReg*)0xF0000050U) /**< \brief (HSMCI0) DMA Configuration Register */
#define REG_HSMCI0_CFG       (*(RwReg*)0xF0000054U) /**< \brief (HSMCI0) Configuration Register */
#define REG_HSMCI0_WPMR      (*(RwReg*)0xF00000E4U) /**< \brief (HSMCI0) Write Protection Mode Register */
#define REG_HSMCI0_WPSR      (*(RoReg*)0xF00000E8U) /**< \brief (HSMCI0) Write Protection Status Register */
#define REG_HSMCI0_FIFO      (*(RwReg*)0xF0000200U) /**< \brief (HSMCI0) FIFO Memory Aperture0 */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_HSMCI0_INSTANCE_ */
