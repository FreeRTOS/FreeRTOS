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

#ifndef _SAMA5_USART1_INSTANCE_
#define _SAMA5_USART1_INSTANCE_

/* ========== Register definition for USART1 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_USART1_CR          (0xF0020000U) /**< \brief (USART1) Control Register */
#define REG_USART1_MR          (0xF0020004U) /**< \brief (USART1) Mode Register */
#define REG_USART1_IER          (0xF0020008U) /**< \brief (USART1) Interrupt Enable Register */
#define REG_USART1_IDR          (0xF002000CU) /**< \brief (USART1) Interrupt Disable Register */
#define REG_USART1_IMR          (0xF0020010U) /**< \brief (USART1) Interrupt Mask Register */
#define REG_USART1_CSR          (0xF0020014U) /**< \brief (USART1) Channel Status Register */
#define REG_USART1_RHR          (0xF0020018U) /**< \brief (USART1) Receiver Holding Register */
#define REG_USART1_THR          (0xF002001CU) /**< \brief (USART1) Transmitter Holding Register */
#define REG_USART1_BRGR          (0xF0020020U) /**< \brief (USART1) Baud Rate Generator Register */
#define REG_USART1_RTOR          (0xF0020024U) /**< \brief (USART1) Receiver Time-out Register */
#define REG_USART1_TTGR          (0xF0020028U) /**< \brief (USART1) Transmitter Timeguard Register */
#define REG_USART1_FIDI          (0xF0020040U) /**< \brief (USART1) FI DI Ratio Register */
#define REG_USART1_NER          (0xF0020044U) /**< \brief (USART1) Number of Errors Register */
#define REG_USART1_IF          (0xF002004CU) /**< \brief (USART1) IrDA Filter Register */
#define REG_USART1_MAN          (0xF0020050U) /**< \brief (USART1) Manchester Encoder Decoder Register */
#define REG_USART1_WPMR          (0xF00200E4U) /**< \brief (USART1) Write Protect Mode Register */
#define REG_USART1_WPSR          (0xF00200E8U) /**< \brief (USART1) Write Protect Status Register */
#else
#define REG_USART1_CR (*(WoReg*)0xF0020000U) /**< \brief (USART1) Control Register */
#define REG_USART1_MR (*(RwReg*)0xF0020004U) /**< \brief (USART1) Mode Register */
#define REG_USART1_IER (*(WoReg*)0xF0020008U) /**< \brief (USART1) Interrupt Enable Register */
#define REG_USART1_IDR (*(WoReg*)0xF002000CU) /**< \brief (USART1) Interrupt Disable Register */
#define REG_USART1_IMR (*(RoReg*)0xF0020010U) /**< \brief (USART1) Interrupt Mask Register */
#define REG_USART1_CSR (*(RoReg*)0xF0020014U) /**< \brief (USART1) Channel Status Register */
#define REG_USART1_RHR (*(RoReg*)0xF0020018U) /**< \brief (USART1) Receiver Holding Register */
#define REG_USART1_THR (*(WoReg*)0xF002001CU) /**< \brief (USART1) Transmitter Holding Register */
#define REG_USART1_BRGR (*(RwReg*)0xF0020020U) /**< \brief (USART1) Baud Rate Generator Register */
#define REG_USART1_RTOR (*(RwReg*)0xF0020024U) /**< \brief (USART1) Receiver Time-out Register */
#define REG_USART1_TTGR (*(RwReg*)0xF0020028U) /**< \brief (USART1) Transmitter Timeguard Register */
#define REG_USART1_FIDI (*(RwReg*)0xF0020040U) /**< \brief (USART1) FI DI Ratio Register */
#define REG_USART1_NER (*(RoReg*)0xF0020044U) /**< \brief (USART1) Number of Errors Register */
#define REG_USART1_IF (*(RwReg*)0xF002004CU) /**< \brief (USART1) IrDA Filter Register */
#define REG_USART1_MAN (*(RwReg*)0xF0020050U) /**< \brief (USART1) Manchester Encoder Decoder Register */
#define REG_USART1_WPMR (*(RwReg*)0xF00200E4U) /**< \brief (USART1) Write Protect Mode Register */
#define REG_USART1_WPSR (*(RoReg*)0xF00200E8U) /**< \brief (USART1) Write Protect Status Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_USART1_INSTANCE_ */
