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

#ifndef _SAMA5_TWI2_INSTANCE_
#define _SAMA5_TWI2_INSTANCE_

/* ========== Register definition for TWI2 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_TWI2_CR                    (0xF801C000U) /**< \brief (TWI2) Control Register */
#define REG_TWI2_MMR                   (0xF801C004U) /**< \brief (TWI2) Master Mode Register */
#define REG_TWI2_SMR                   (0xF801C008U) /**< \brief (TWI2) Slave Mode Register */
#define REG_TWI2_IADR                  (0xF801C00CU) /**< \brief (TWI2) Internal Address Register */
#define REG_TWI2_CWGR                  (0xF801C010U) /**< \brief (TWI2) Clock Waveform Generator Register */
#define REG_TWI2_SR                    (0xF801C020U) /**< \brief (TWI2) Status Register */
#define REG_TWI2_IER                   (0xF801C024U) /**< \brief (TWI2) Interrupt Enable Register */
#define REG_TWI2_IDR                   (0xF801C028U) /**< \brief (TWI2) Interrupt Disable Register */
#define REG_TWI2_IMR                   (0xF801C02CU) /**< \brief (TWI2) Interrupt Mask Register */
#define REG_TWI2_RHR                   (0xF801C030U) /**< \brief (TWI2) Receive Holding Register */
#define REG_TWI2_THR                   (0xF801C034U) /**< \brief (TWI2) Transmit Holding Register */
#define REG_TWI2_WPROT_MODE            (0xF801C0E4U) /**< \brief (TWI2) Protection Mode Register */
#define REG_TWI2_WPROT_STATUS          (0xF801C0E8U) /**< \brief (TWI2) Protection Status Register */
#else
#define REG_TWI2_CR           (*(WoReg*)0xF801C000U) /**< \brief (TWI2) Control Register */
#define REG_TWI2_MMR          (*(RwReg*)0xF801C004U) /**< \brief (TWI2) Master Mode Register */
#define REG_TWI2_SMR          (*(RwReg*)0xF801C008U) /**< \brief (TWI2) Slave Mode Register */
#define REG_TWI2_IADR         (*(RwReg*)0xF801C00CU) /**< \brief (TWI2) Internal Address Register */
#define REG_TWI2_CWGR         (*(RwReg*)0xF801C010U) /**< \brief (TWI2) Clock Waveform Generator Register */
#define REG_TWI2_SR           (*(RoReg*)0xF801C020U) /**< \brief (TWI2) Status Register */
#define REG_TWI2_IER          (*(WoReg*)0xF801C024U) /**< \brief (TWI2) Interrupt Enable Register */
#define REG_TWI2_IDR          (*(WoReg*)0xF801C028U) /**< \brief (TWI2) Interrupt Disable Register */
#define REG_TWI2_IMR          (*(RoReg*)0xF801C02CU) /**< \brief (TWI2) Interrupt Mask Register */
#define REG_TWI2_RHR          (*(RoReg*)0xF801C030U) /**< \brief (TWI2) Receive Holding Register */
#define REG_TWI2_THR          (*(WoReg*)0xF801C034U) /**< \brief (TWI2) Transmit Holding Register */
#define REG_TWI2_WPROT_MODE   (*(RwReg*)0xF801C0E4U) /**< \brief (TWI2) Protection Mode Register */
#define REG_TWI2_WPROT_STATUS (*(RoReg*)0xF801C0E8U) /**< \brief (TWI2) Protection Status Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_TWI2_INSTANCE_ */
