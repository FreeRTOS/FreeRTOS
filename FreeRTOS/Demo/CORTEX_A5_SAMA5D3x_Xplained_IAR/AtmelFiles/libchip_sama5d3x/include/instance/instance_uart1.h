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

#ifndef _SAMA5_UART1_INSTANCE_
#define _SAMA5_UART1_INSTANCE_

/* ========== Register definition for UART1 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_UART1_CR            (0xF8028000U) /**< \brief (UART1) Control Register */
#define REG_UART1_MR            (0xF8028004U) /**< \brief (UART1) Mode Register */
#define REG_UART1_IER           (0xF8028008U) /**< \brief (UART1) Interrupt Enable Register */
#define REG_UART1_IDR           (0xF802800CU) /**< \brief (UART1) Interrupt Disable Register */
#define REG_UART1_IMR           (0xF8028010U) /**< \brief (UART1) Interrupt Mask Register */
#define REG_UART1_SR            (0xF8028014U) /**< \brief (UART1) Status Register */
#define REG_UART1_RHR           (0xF8028018U) /**< \brief (UART1) Receive Holding Register */
#define REG_UART1_THR           (0xF802801CU) /**< \brief (UART1) Transmit Holding Register */
#define REG_UART1_BRGR          (0xF8028020U) /**< \brief (UART1) Baud Rate Generator Register */
#else
#define REG_UART1_CR   (*(WoReg*)0xF8028000U) /**< \brief (UART1) Control Register */
#define REG_UART1_MR   (*(RwReg*)0xF8028004U) /**< \brief (UART1) Mode Register */
#define REG_UART1_IER  (*(WoReg*)0xF8028008U) /**< \brief (UART1) Interrupt Enable Register */
#define REG_UART1_IDR  (*(WoReg*)0xF802800CU) /**< \brief (UART1) Interrupt Disable Register */
#define REG_UART1_IMR  (*(RoReg*)0xF8028010U) /**< \brief (UART1) Interrupt Mask Register */
#define REG_UART1_SR   (*(RoReg*)0xF8028014U) /**< \brief (UART1) Status Register */
#define REG_UART1_RHR  (*(RoReg*)0xF8028018U) /**< \brief (UART1) Receive Holding Register */
#define REG_UART1_THR  (*(WoReg*)0xF802801CU) /**< \brief (UART1) Transmit Holding Register */
#define REG_UART1_BRGR (*(RwReg*)0xF8028020U) /**< \brief (UART1) Baud Rate Generator Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_UART1_INSTANCE_ */
