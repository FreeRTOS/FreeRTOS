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

#ifndef _SAMA5_USART2_INSTANCE_
#define _SAMA5_USART2_INSTANCE_

/* ========== Register definition for USART2 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_USART2_CR          (0xF8020000U) /**< \brief (USART2) Control Register */
#define REG_USART2_MR          (0xF8020004U) /**< \brief (USART2) Mode Register */
#define REG_USART2_IER          (0xF8020008U) /**< \brief (USART2) Interrupt Enable Register */
#define REG_USART2_IDR          (0xF802000CU) /**< \brief (USART2) Interrupt Disable Register */
#define REG_USART2_IMR          (0xF8020010U) /**< \brief (USART2) Interrupt Mask Register */
#define REG_USART2_CSR          (0xF8020014U) /**< \brief (USART2) Channel Status Register */
#define REG_USART2_RHR          (0xF8020018U) /**< \brief (USART2) Receiver Holding Register */
#define REG_USART2_THR          (0xF802001CU) /**< \brief (USART2) Transmitter Holding Register */
#define REG_USART2_BRGR          (0xF8020020U) /**< \brief (USART2) Baud Rate Generator Register */
#define REG_USART2_RTOR          (0xF8020024U) /**< \brief (USART2) Receiver Time-out Register */
#define REG_USART2_TTGR          (0xF8020028U) /**< \brief (USART2) Transmitter Timeguard Register */
#define REG_USART2_FIDI          (0xF8020040U) /**< \brief (USART2) FI DI Ratio Register */
#define REG_USART2_NER          (0xF8020044U) /**< \brief (USART2) Number of Errors Register */
#define REG_USART2_IF          (0xF802004CU) /**< \brief (USART2) IrDA Filter Register */
#define REG_USART2_MAN          (0xF8020050U) /**< \brief (USART2) Manchester Encoder Decoder Register */
#define REG_USART2_WPMR          (0xF80200E4U) /**< \brief (USART2) Write Protect Mode Register */
#define REG_USART2_WPSR          (0xF80200E8U) /**< \brief (USART2) Write Protect Status Register */
#else
#define REG_USART2_CR (*(WoReg*)0xF8020000U) /**< \brief (USART2) Control Register */
#define REG_USART2_MR (*(RwReg*)0xF8020004U) /**< \brief (USART2) Mode Register */
#define REG_USART2_IER (*(WoReg*)0xF8020008U) /**< \brief (USART2) Interrupt Enable Register */
#define REG_USART2_IDR (*(WoReg*)0xF802000CU) /**< \brief (USART2) Interrupt Disable Register */
#define REG_USART2_IMR (*(RoReg*)0xF8020010U) /**< \brief (USART2) Interrupt Mask Register */
#define REG_USART2_CSR (*(RoReg*)0xF8020014U) /**< \brief (USART2) Channel Status Register */
#define REG_USART2_RHR (*(RoReg*)0xF8020018U) /**< \brief (USART2) Receiver Holding Register */
#define REG_USART2_THR (*(WoReg*)0xF802001CU) /**< \brief (USART2) Transmitter Holding Register */
#define REG_USART2_BRGR (*(RwReg*)0xF8020020U) /**< \brief (USART2) Baud Rate Generator Register */
#define REG_USART2_RTOR (*(RwReg*)0xF8020024U) /**< \brief (USART2) Receiver Time-out Register */
#define REG_USART2_TTGR (*(RwReg*)0xF8020028U) /**< \brief (USART2) Transmitter Timeguard Register */
#define REG_USART2_FIDI (*(RwReg*)0xF8020040U) /**< \brief (USART2) FI DI Ratio Register */
#define REG_USART2_NER (*(RoReg*)0xF8020044U) /**< \brief (USART2) Number of Errors Register */
#define REG_USART2_IF (*(RwReg*)0xF802004CU) /**< \brief (USART2) IrDA Filter Register */
#define REG_USART2_MAN (*(RwReg*)0xF8020050U) /**< \brief (USART2) Manchester Encoder Decoder Register */
#define REG_USART2_WPMR (*(RwReg*)0xF80200E4U) /**< \brief (USART2) Write Protect Mode Register */
#define REG_USART2_WPSR (*(RoReg*)0xF80200E8U) /**< \brief (USART2) Write Protect Status Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_USART2_INSTANCE_ */
