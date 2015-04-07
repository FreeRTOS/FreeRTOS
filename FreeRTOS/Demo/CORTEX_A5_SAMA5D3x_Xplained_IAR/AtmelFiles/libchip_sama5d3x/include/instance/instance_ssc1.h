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

#ifndef _SAMA5_SSC1_INSTANCE_
#define _SAMA5_SSC1_INSTANCE_

/* ========== Register definition for SSC1 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_SSC1_CR            (0xF800C000U) /**< \brief (SSC1) Control Register */
#define REG_SSC1_CMR           (0xF800C004U) /**< \brief (SSC1) Clock Mode Register */
#define REG_SSC1_RCMR          (0xF800C010U) /**< \brief (SSC1) Receive Clock Mode Register */
#define REG_SSC1_RFMR          (0xF800C014U) /**< \brief (SSC1) Receive Frame Mode Register */
#define REG_SSC1_TCMR          (0xF800C018U) /**< \brief (SSC1) Transmit Clock Mode Register */
#define REG_SSC1_TFMR          (0xF800C01CU) /**< \brief (SSC1) Transmit Frame Mode Register */
#define REG_SSC1_RHR           (0xF800C020U) /**< \brief (SSC1) Receive Holding Register */
#define REG_SSC1_THR           (0xF800C024U) /**< \brief (SSC1) Transmit Holding Register */
#define REG_SSC1_RSHR          (0xF800C030U) /**< \brief (SSC1) Receive Sync. Holding Register */
#define REG_SSC1_TSHR          (0xF800C034U) /**< \brief (SSC1) Transmit Sync. Holding Register */
#define REG_SSC1_RC0R          (0xF800C038U) /**< \brief (SSC1) Receive Compare 0 Register */
#define REG_SSC1_RC1R          (0xF800C03CU) /**< \brief (SSC1) Receive Compare 1 Register */
#define REG_SSC1_SR            (0xF800C040U) /**< \brief (SSC1) Status Register */
#define REG_SSC1_IER           (0xF800C044U) /**< \brief (SSC1) Interrupt Enable Register */
#define REG_SSC1_IDR           (0xF800C048U) /**< \brief (SSC1) Interrupt Disable Register */
#define REG_SSC1_IMR           (0xF800C04CU) /**< \brief (SSC1) Interrupt Mask Register */
#define REG_SSC1_WPMR          (0xF800C0E4U) /**< \brief (SSC1) Write Protect Mode Register */
#define REG_SSC1_WPSR          (0xF800C0E8U) /**< \brief (SSC1) Write Protect Status Register */
#else
#define REG_SSC1_CR   (*(WoReg*)0xF800C000U) /**< \brief (SSC1) Control Register */
#define REG_SSC1_CMR  (*(RwReg*)0xF800C004U) /**< \brief (SSC1) Clock Mode Register */
#define REG_SSC1_RCMR (*(RwReg*)0xF800C010U) /**< \brief (SSC1) Receive Clock Mode Register */
#define REG_SSC1_RFMR (*(RwReg*)0xF800C014U) /**< \brief (SSC1) Receive Frame Mode Register */
#define REG_SSC1_TCMR (*(RwReg*)0xF800C018U) /**< \brief (SSC1) Transmit Clock Mode Register */
#define REG_SSC1_TFMR (*(RwReg*)0xF800C01CU) /**< \brief (SSC1) Transmit Frame Mode Register */
#define REG_SSC1_RHR  (*(RoReg*)0xF800C020U) /**< \brief (SSC1) Receive Holding Register */
#define REG_SSC1_THR  (*(WoReg*)0xF800C024U) /**< \brief (SSC1) Transmit Holding Register */
#define REG_SSC1_RSHR (*(RoReg*)0xF800C030U) /**< \brief (SSC1) Receive Sync. Holding Register */
#define REG_SSC1_TSHR (*(RwReg*)0xF800C034U) /**< \brief (SSC1) Transmit Sync. Holding Register */
#define REG_SSC1_RC0R (*(RwReg*)0xF800C038U) /**< \brief (SSC1) Receive Compare 0 Register */
#define REG_SSC1_RC1R (*(RwReg*)0xF800C03CU) /**< \brief (SSC1) Receive Compare 1 Register */
#define REG_SSC1_SR   (*(RoReg*)0xF800C040U) /**< \brief (SSC1) Status Register */
#define REG_SSC1_IER  (*(WoReg*)0xF800C044U) /**< \brief (SSC1) Interrupt Enable Register */
#define REG_SSC1_IDR  (*(WoReg*)0xF800C048U) /**< \brief (SSC1) Interrupt Disable Register */
#define REG_SSC1_IMR  (*(RoReg*)0xF800C04CU) /**< \brief (SSC1) Interrupt Mask Register */
#define REG_SSC1_WPMR (*(RwReg*)0xF800C0E4U) /**< \brief (SSC1) Write Protect Mode Register */
#define REG_SSC1_WPSR (*(RoReg*)0xF800C0E8U) /**< \brief (SSC1) Write Protect Status Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_SSC1_INSTANCE_ */
