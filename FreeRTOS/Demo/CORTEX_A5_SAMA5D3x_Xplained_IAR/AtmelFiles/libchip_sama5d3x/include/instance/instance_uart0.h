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

#ifndef _SAMA5_UART0_INSTANCE_
#define _SAMA5_UART0_INSTANCE_

/* ========== Register definition for UART0 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_UART0_CR            (0xF0024000U) /**< \brief (UART0) Control Register */
#define REG_UART0_MR            (0xF0024004U) /**< \brief (UART0) Mode Register */
#define REG_UART0_IER           (0xF0024008U) /**< \brief (UART0) Interrupt Enable Register */
#define REG_UART0_IDR           (0xF002400CU) /**< \brief (UART0) Interrupt Disable Register */
#define REG_UART0_IMR           (0xF0024010U) /**< \brief (UART0) Interrupt Mask Register */
#define REG_UART0_SR            (0xF0024014U) /**< \brief (UART0) Status Register */
#define REG_UART0_RHR           (0xF0024018U) /**< \brief (UART0) Receive Holding Register */
#define REG_UART0_THR           (0xF002401CU) /**< \brief (UART0) Transmit Holding Register */
#define REG_UART0_BRGR          (0xF0024020U) /**< \brief (UART0) Baud Rate Generator Register */
#else
#define REG_UART0_CR   (*(WoReg*)0xF0024000U) /**< \brief (UART0) Control Register */
#define REG_UART0_MR   (*(RwReg*)0xF0024004U) /**< \brief (UART0) Mode Register */
#define REG_UART0_IER  (*(WoReg*)0xF0024008U) /**< \brief (UART0) Interrupt Enable Register */
#define REG_UART0_IDR  (*(WoReg*)0xF002400CU) /**< \brief (UART0) Interrupt Disable Register */
#define REG_UART0_IMR  (*(RoReg*)0xF0024010U) /**< \brief (UART0) Interrupt Mask Register */
#define REG_UART0_SR   (*(RoReg*)0xF0024014U) /**< \brief (UART0) Status Register */
#define REG_UART0_RHR  (*(RoReg*)0xF0024018U) /**< \brief (UART0) Receive Holding Register */
#define REG_UART0_THR  (*(WoReg*)0xF002401CU) /**< \brief (UART0) Transmit Holding Register */
#define REG_UART0_BRGR (*(RwReg*)0xF0024020U) /**< \brief (UART0) Baud Rate Generator Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_UART0_INSTANCE_ */
