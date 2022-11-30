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

#ifndef _SAM3S8_ACC_INSTANCE_
#define _SAM3S8_ACC_INSTANCE_

/* ========== Register definition for ACC peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_ACC_CR            (0x40040000U) /**< \brief (ACC) Control Register */
#define REG_ACC_MR            (0x40040004U) /**< \brief (ACC) Mode Register */
#define REG_ACC_IER           (0x40040024U) /**< \brief (ACC) Interrupt Enable Register */
#define REG_ACC_IDR           (0x40040028U) /**< \brief (ACC) Interrupt Disable Register */
#define REG_ACC_IMR           (0x4004002CU) /**< \brief (ACC) Interrupt Mask Register */
#define REG_ACC_ISR           (0x40040030U) /**< \brief (ACC) Interrupt Status Register */
#define REG_ACC_ACR           (0x40040094U) /**< \brief (ACC) Analog Control Register */
#define REG_ACC_WPMR          (0x400400E4U) /**< \brief (ACC) Write Protect Mode Register */
#define REG_ACC_WPSR          (0x400400E8U) /**< \brief (ACC) Write Protect Status Register */
#else
#define REG_ACC_CR   (*(WoReg*)0x40040000U) /**< \brief (ACC) Control Register */
#define REG_ACC_MR   (*(RwReg*)0x40040004U) /**< \brief (ACC) Mode Register */
#define REG_ACC_IER  (*(WoReg*)0x40040024U) /**< \brief (ACC) Interrupt Enable Register */
#define REG_ACC_IDR  (*(WoReg*)0x40040028U) /**< \brief (ACC) Interrupt Disable Register */
#define REG_ACC_IMR  (*(RoReg*)0x4004002CU) /**< \brief (ACC) Interrupt Mask Register */
#define REG_ACC_ISR  (*(RoReg*)0x40040030U) /**< \brief (ACC) Interrupt Status Register */
#define REG_ACC_ACR  (*(RwReg*)0x40040094U) /**< \brief (ACC) Analog Control Register */
#define REG_ACC_WPMR (*(RwReg*)0x400400E4U) /**< \brief (ACC) Write Protect Mode Register */
#define REG_ACC_WPSR (*(RoReg*)0x400400E8U) /**< \brief (ACC) Write Protect Status Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAM3S8_ACC_INSTANCE_ */
