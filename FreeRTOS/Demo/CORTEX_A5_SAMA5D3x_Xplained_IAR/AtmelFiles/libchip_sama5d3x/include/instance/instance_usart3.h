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

#ifndef _SAMA5_USART3_INSTANCE_
#define _SAMA5_USART3_INSTANCE_

/* ========== Register definition for USART3 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_USART3_CR          (0xF8024000U) /**< \brief (USART3) Control Register */
#define REG_USART3_MR          (0xF8024004U) /**< \brief (USART3) Mode Register */
#define REG_USART3_IER          (0xF8024008U) /**< \brief (USART3) Interrupt Enable Register */
#define REG_USART3_IDR          (0xF802400CU) /**< \brief (USART3) Interrupt Disable Register */
#define REG_USART3_IMR          (0xF8024010U) /**< \brief (USART3) Interrupt Mask Register */
#define REG_USART3_CSR          (0xF8024014U) /**< \brief (USART3) Channel Status Register */
#define REG_USART3_RHR          (0xF8024018U) /**< \brief (USART3) Receiver Holding Register */
#define REG_USART3_THR          (0xF802401CU) /**< \brief (USART3) Transmitter Holding Register */
#define REG_USART3_BRGR          (0xF8024020U) /**< \brief (USART3) Baud Rate Generator Register */
#define REG_USART3_RTOR          (0xF8024024U) /**< \brief (USART3) Receiver Time-out Register */
#define REG_USART3_TTGR          (0xF8024028U) /**< \brief (USART3) Transmitter Timeguard Register */
#define REG_USART3_FIDI          (0xF8024040U) /**< \brief (USART3) FI DI Ratio Register */
#define REG_USART3_NER          (0xF8024044U) /**< \brief (USART3) Number of Errors Register */
#define REG_USART3_IF          (0xF802404CU) /**< \brief (USART3) IrDA Filter Register */
#define REG_USART3_MAN          (0xF8024050U) /**< \brief (USART3) Manchester Encoder Decoder Register */
#define REG_USART3_WPMR          (0xF80240E4U) /**< \brief (USART3) Write Protect Mode Register */
#define REG_USART3_WPSR          (0xF80240E8U) /**< \brief (USART3) Write Protect Status Register */
#else
#define REG_USART3_CR (*(WoReg*)0xF8024000U) /**< \brief (USART3) Control Register */
#define REG_USART3_MR (*(RwReg*)0xF8024004U) /**< \brief (USART3) Mode Register */
#define REG_USART3_IER (*(WoReg*)0xF8024008U) /**< \brief (USART3) Interrupt Enable Register */
#define REG_USART3_IDR (*(WoReg*)0xF802400CU) /**< \brief (USART3) Interrupt Disable Register */
#define REG_USART3_IMR (*(RoReg*)0xF8024010U) /**< \brief (USART3) Interrupt Mask Register */
#define REG_USART3_CSR (*(RoReg*)0xF8024014U) /**< \brief (USART3) Channel Status Register */
#define REG_USART3_RHR (*(RoReg*)0xF8024018U) /**< \brief (USART3) Receiver Holding Register */
#define REG_USART3_THR (*(WoReg*)0xF802401CU) /**< \brief (USART3) Transmitter Holding Register */
#define REG_USART3_BRGR (*(RwReg*)0xF8024020U) /**< \brief (USART3) Baud Rate Generator Register */
#define REG_USART3_RTOR (*(RwReg*)0xF8024024U) /**< \brief (USART3) Receiver Time-out Register */
#define REG_USART3_TTGR (*(RwReg*)0xF8024028U) /**< \brief (USART3) Transmitter Timeguard Register */
#define REG_USART3_FIDI (*(RwReg*)0xF8024040U) /**< \brief (USART3) FI DI Ratio Register */
#define REG_USART3_NER (*(RoReg*)0xF8024044U) /**< \brief (USART3) Number of Errors Register */
#define REG_USART3_IF (*(RwReg*)0xF802404CU) /**< \brief (USART3) IrDA Filter Register */
#define REG_USART3_MAN (*(RwReg*)0xF8024050U) /**< \brief (USART3) Manchester Encoder Decoder Register */
#define REG_USART3_WPMR (*(RwReg*)0xF80240E4U) /**< \brief (USART3) Write Protect Mode Register */
#define REG_USART3_WPSR (*(RoReg*)0xF80240E8U) /**< \brief (USART3) Write Protect Status Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_USART3_INSTANCE_ */
