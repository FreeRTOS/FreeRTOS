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

#ifndef _SAMA5_TWI0_INSTANCE_
#define _SAMA5_TWI0_INSTANCE_

/* ========== Register definition for TWI0 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_TWI0_CR                    (0xF0014000U) /**< \brief (TWI0) Control Register */
#define REG_TWI0_MMR                   (0xF0014004U) /**< \brief (TWI0) Master Mode Register */
#define REG_TWI0_SMR                   (0xF0014008U) /**< \brief (TWI0) Slave Mode Register */
#define REG_TWI0_IADR                  (0xF001400CU) /**< \brief (TWI0) Internal Address Register */
#define REG_TWI0_CWGR                  (0xF0014010U) /**< \brief (TWI0) Clock Waveform Generator Register */
#define REG_TWI0_SR                    (0xF0014020U) /**< \brief (TWI0) Status Register */
#define REG_TWI0_IER                   (0xF0014024U) /**< \brief (TWI0) Interrupt Enable Register */
#define REG_TWI0_IDR                   (0xF0014028U) /**< \brief (TWI0) Interrupt Disable Register */
#define REG_TWI0_IMR                   (0xF001402CU) /**< \brief (TWI0) Interrupt Mask Register */
#define REG_TWI0_RHR                   (0xF0014030U) /**< \brief (TWI0) Receive Holding Register */
#define REG_TWI0_THR                   (0xF0014034U) /**< \brief (TWI0) Transmit Holding Register */
#define REG_TWI0_WPROT_MODE            (0xF00140E4U) /**< \brief (TWI0) Protection Mode Register */
#define REG_TWI0_WPROT_STATUS          (0xF00140E8U) /**< \brief (TWI0) Protection Status Register */
#else
#define REG_TWI0_CR           (*(WoReg*)0xF0014000U) /**< \brief (TWI0) Control Register */
#define REG_TWI0_MMR          (*(RwReg*)0xF0014004U) /**< \brief (TWI0) Master Mode Register */
#define REG_TWI0_SMR          (*(RwReg*)0xF0014008U) /**< \brief (TWI0) Slave Mode Register */
#define REG_TWI0_IADR         (*(RwReg*)0xF001400CU) /**< \brief (TWI0) Internal Address Register */
#define REG_TWI0_CWGR         (*(RwReg*)0xF0014010U) /**< \brief (TWI0) Clock Waveform Generator Register */
#define REG_TWI0_SR           (*(RoReg*)0xF0014020U) /**< \brief (TWI0) Status Register */
#define REG_TWI0_IER          (*(WoReg*)0xF0014024U) /**< \brief (TWI0) Interrupt Enable Register */
#define REG_TWI0_IDR          (*(WoReg*)0xF0014028U) /**< \brief (TWI0) Interrupt Disable Register */
#define REG_TWI0_IMR          (*(RoReg*)0xF001402CU) /**< \brief (TWI0) Interrupt Mask Register */
#define REG_TWI0_RHR          (*(RoReg*)0xF0014030U) /**< \brief (TWI0) Receive Holding Register */
#define REG_TWI0_THR          (*(WoReg*)0xF0014034U) /**< \brief (TWI0) Transmit Holding Register */
#define REG_TWI0_WPROT_MODE   (*(RwReg*)0xF00140E4U) /**< \brief (TWI0) Protection Mode Register */
#define REG_TWI0_WPROT_STATUS (*(RoReg*)0xF00140E8U) /**< \brief (TWI0) Protection Status Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_TWI0_INSTANCE_ */
