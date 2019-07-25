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

#ifndef _SAMA5_SSC0_INSTANCE_
#define _SAMA5_SSC0_INSTANCE_

/* ========== Register definition for SSC0 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_SSC0_CR            (0xF0008000U) /**< \brief (SSC0) Control Register */
#define REG_SSC0_CMR           (0xF0008004U) /**< \brief (SSC0) Clock Mode Register */
#define REG_SSC0_RCMR          (0xF0008010U) /**< \brief (SSC0) Receive Clock Mode Register */
#define REG_SSC0_RFMR          (0xF0008014U) /**< \brief (SSC0) Receive Frame Mode Register */
#define REG_SSC0_TCMR          (0xF0008018U) /**< \brief (SSC0) Transmit Clock Mode Register */
#define REG_SSC0_TFMR          (0xF000801CU) /**< \brief (SSC0) Transmit Frame Mode Register */
#define REG_SSC0_RHR           (0xF0008020U) /**< \brief (SSC0) Receive Holding Register */
#define REG_SSC0_THR           (0xF0008024U) /**< \brief (SSC0) Transmit Holding Register */
#define REG_SSC0_RSHR          (0xF0008030U) /**< \brief (SSC0) Receive Sync. Holding Register */
#define REG_SSC0_TSHR          (0xF0008034U) /**< \brief (SSC0) Transmit Sync. Holding Register */
#define REG_SSC0_RC0R          (0xF0008038U) /**< \brief (SSC0) Receive Compare 0 Register */
#define REG_SSC0_RC1R          (0xF000803CU) /**< \brief (SSC0) Receive Compare 1 Register */
#define REG_SSC0_SR            (0xF0008040U) /**< \brief (SSC0) Status Register */
#define REG_SSC0_IER           (0xF0008044U) /**< \brief (SSC0) Interrupt Enable Register */
#define REG_SSC0_IDR           (0xF0008048U) /**< \brief (SSC0) Interrupt Disable Register */
#define REG_SSC0_IMR           (0xF000804CU) /**< \brief (SSC0) Interrupt Mask Register */
#define REG_SSC0_WPMR          (0xF00080E4U) /**< \brief (SSC0) Write Protect Mode Register */
#define REG_SSC0_WPSR          (0xF00080E8U) /**< \brief (SSC0) Write Protect Status Register */
#else
#define REG_SSC0_CR   (*(WoReg*)0xF0008000U) /**< \brief (SSC0) Control Register */
#define REG_SSC0_CMR  (*(RwReg*)0xF0008004U) /**< \brief (SSC0) Clock Mode Register */
#define REG_SSC0_RCMR (*(RwReg*)0xF0008010U) /**< \brief (SSC0) Receive Clock Mode Register */
#define REG_SSC0_RFMR (*(RwReg*)0xF0008014U) /**< \brief (SSC0) Receive Frame Mode Register */
#define REG_SSC0_TCMR (*(RwReg*)0xF0008018U) /**< \brief (SSC0) Transmit Clock Mode Register */
#define REG_SSC0_TFMR (*(RwReg*)0xF000801CU) /**< \brief (SSC0) Transmit Frame Mode Register */
#define REG_SSC0_RHR  (*(RoReg*)0xF0008020U) /**< \brief (SSC0) Receive Holding Register */
#define REG_SSC0_THR  (*(WoReg*)0xF0008024U) /**< \brief (SSC0) Transmit Holding Register */
#define REG_SSC0_RSHR (*(RoReg*)0xF0008030U) /**< \brief (SSC0) Receive Sync. Holding Register */
#define REG_SSC0_TSHR (*(RwReg*)0xF0008034U) /**< \brief (SSC0) Transmit Sync. Holding Register */
#define REG_SSC0_RC0R (*(RwReg*)0xF0008038U) /**< \brief (SSC0) Receive Compare 0 Register */
#define REG_SSC0_RC1R (*(RwReg*)0xF000803CU) /**< \brief (SSC0) Receive Compare 1 Register */
#define REG_SSC0_SR   (*(RoReg*)0xF0008040U) /**< \brief (SSC0) Status Register */
#define REG_SSC0_IER  (*(WoReg*)0xF0008044U) /**< \brief (SSC0) Interrupt Enable Register */
#define REG_SSC0_IDR  (*(WoReg*)0xF0008048U) /**< \brief (SSC0) Interrupt Disable Register */
#define REG_SSC0_IMR  (*(RoReg*)0xF000804CU) /**< \brief (SSC0) Interrupt Mask Register */
#define REG_SSC0_WPMR (*(RwReg*)0xF00080E4U) /**< \brief (SSC0) Write Protect Mode Register */
#define REG_SSC0_WPSR (*(RoReg*)0xF00080E8U) /**< \brief (SSC0) Write Protect Status Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_SSC0_INSTANCE_ */
