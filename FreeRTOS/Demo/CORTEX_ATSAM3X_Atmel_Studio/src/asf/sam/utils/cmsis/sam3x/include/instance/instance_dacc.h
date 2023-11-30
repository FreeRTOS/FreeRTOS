/**
 * \file
 *
 * Copyright (c) 2012 Atmel Corporation. All rights reserved.
 *
 * \asf_license_start
 *
 * \page License
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 *
 * 3. The name of Atmel may not be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * 4. This software may only be redistributed and used in connection with an
 *    Atmel microcontroller product.
 *
 * THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * EXPRESSLY AND SPECIFICALLY DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
 * ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *
 * \asf_license_stop
 *
 */

#ifndef _SAM3XA_DACC_INSTANCE_
#define _SAM3XA_DACC_INSTANCE_

/* ========== Register definition for DACC peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_DACC_CR            (0x400C8000U) /**< \brief (DACC) Control Register */
#define REG_DACC_MR            (0x400C8004U) /**< \brief (DACC) Mode Register */
#define REG_DACC_CHER          (0x400C8010U) /**< \brief (DACC) Channel Enable Register */
#define REG_DACC_CHDR          (0x400C8014U) /**< \brief (DACC) Channel Disable Register */
#define REG_DACC_CHSR          (0x400C8018U) /**< \brief (DACC) Channel Status Register */
#define REG_DACC_CDR           (0x400C8020U) /**< \brief (DACC) Conversion Data Register */
#define REG_DACC_IER           (0x400C8024U) /**< \brief (DACC) Interrupt Enable Register */
#define REG_DACC_IDR           (0x400C8028U) /**< \brief (DACC) Interrupt Disable Register */
#define REG_DACC_IMR           (0x400C802CU) /**< \brief (DACC) Interrupt Mask Register */
#define REG_DACC_ISR           (0x400C8030U) /**< \brief (DACC) Interrupt Status Register */
#define REG_DACC_ACR           (0x400C8094U) /**< \brief (DACC) Analog Current Register */
#define REG_DACC_WPMR          (0x400C80E4U) /**< \brief (DACC) Write Protect Mode register */
#define REG_DACC_WPSR          (0x400C80E8U) /**< \brief (DACC) Write Protect Status register */
#define REG_DACC_TPR           (0x400C8108U) /**< \brief (DACC) Transmit Pointer Register */
#define REG_DACC_TCR           (0x400C810CU) /**< \brief (DACC) Transmit Counter Register */
#define REG_DACC_TNPR          (0x400C8118U) /**< \brief (DACC) Transmit Next Pointer Register */
#define REG_DACC_TNCR          (0x400C811CU) /**< \brief (DACC) Transmit Next Counter Register */
#define REG_DACC_PTCR          (0x400C8120U) /**< \brief (DACC) Transfer Control Register */
#define REG_DACC_PTSR          (0x400C8124U) /**< \brief (DACC) Transfer Status Register */
#else
#define REG_DACC_CR   (*(WoReg*)0x400C8000U) /**< \brief (DACC) Control Register */
#define REG_DACC_MR   (*(RwReg*)0x400C8004U) /**< \brief (DACC) Mode Register */
#define REG_DACC_CHER (*(WoReg*)0x400C8010U) /**< \brief (DACC) Channel Enable Register */
#define REG_DACC_CHDR (*(WoReg*)0x400C8014U) /**< \brief (DACC) Channel Disable Register */
#define REG_DACC_CHSR (*(RoReg*)0x400C8018U) /**< \brief (DACC) Channel Status Register */
#define REG_DACC_CDR  (*(WoReg*)0x400C8020U) /**< \brief (DACC) Conversion Data Register */
#define REG_DACC_IER  (*(WoReg*)0x400C8024U) /**< \brief (DACC) Interrupt Enable Register */
#define REG_DACC_IDR  (*(WoReg*)0x400C8028U) /**< \brief (DACC) Interrupt Disable Register */
#define REG_DACC_IMR  (*(RoReg*)0x400C802CU) /**< \brief (DACC) Interrupt Mask Register */
#define REG_DACC_ISR  (*(RoReg*)0x400C8030U) /**< \brief (DACC) Interrupt Status Register */
#define REG_DACC_ACR  (*(RwReg*)0x400C8094U) /**< \brief (DACC) Analog Current Register */
#define REG_DACC_WPMR (*(RwReg*)0x400C80E4U) /**< \brief (DACC) Write Protect Mode register */
#define REG_DACC_WPSR (*(RoReg*)0x400C80E8U) /**< \brief (DACC) Write Protect Status register */
#define REG_DACC_TPR  (*(RwReg*)0x400C8108U) /**< \brief (DACC) Transmit Pointer Register */
#define REG_DACC_TCR  (*(RwReg*)0x400C810CU) /**< \brief (DACC) Transmit Counter Register */
#define REG_DACC_TNPR (*(RwReg*)0x400C8118U) /**< \brief (DACC) Transmit Next Pointer Register */
#define REG_DACC_TNCR (*(RwReg*)0x400C811CU) /**< \brief (DACC) Transmit Next Counter Register */
#define REG_DACC_PTCR (*(WoReg*)0x400C8120U) /**< \brief (DACC) Transfer Control Register */
#define REG_DACC_PTSR (*(RoReg*)0x400C8124U) /**< \brief (DACC) Transfer Status Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAM3XA_DACC_INSTANCE_ */
