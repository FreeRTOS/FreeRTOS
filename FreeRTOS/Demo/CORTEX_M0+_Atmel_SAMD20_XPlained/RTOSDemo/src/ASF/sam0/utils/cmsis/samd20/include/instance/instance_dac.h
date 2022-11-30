/**
 * \file
 *
 * \brief Instance description for DAC
 *
 * Copyright (c) 2013 Atmel Corporation. All rights reserved.
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

#ifndef _SAMD20_DAC_INSTANCE_
#define _SAMD20_DAC_INSTANCE_

/* ========== Register definition for DAC peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_DAC_CTRLA              (0x42004800U) /**< \brief (DAC) Control Register A */
#define REG_DAC_CTRLB              (0x42004801U) /**< \brief (DAC) Control Register B */
#define REG_DAC_EVCTRL             (0x42004802U) /**< \brief (DAC) Event Control Register */
#define REG_DAC_TEST               (0x42004803U) /**< \brief (DAC) Test Register */
#define REG_DAC_INTENCLR           (0x42004804U) /**< \brief (DAC) Interrupt Enable Clear Register */
#define REG_DAC_INTENSET           (0x42004805U) /**< \brief (DAC) Interrupt Enable Set Register */
#define REG_DAC_INTFLAG            (0x42004806U) /**< \brief (DAC) Interrupt Flag Status and Clear Register */
#define REG_DAC_STATUS             (0x42004807U) /**< \brief (DAC) Status Register */
#define REG_DAC_DATA               (0x42004808U) /**< \brief (DAC) Data Register */
#define REG_DAC_DATABUF            (0x4200480CU) /**< \brief (DAC) Data Buffer Register */
#else
#define REG_DAC_CTRLA              (*(RwReg8 *)0x42004800U) /**< \brief (DAC) Control Register A */
#define REG_DAC_CTRLB              (*(RwReg8 *)0x42004801U) /**< \brief (DAC) Control Register B */
#define REG_DAC_EVCTRL             (*(RwReg8 *)0x42004802U) /**< \brief (DAC) Event Control Register */
#define REG_DAC_TEST               (*(RwReg8 *)0x42004803U) /**< \brief (DAC) Test Register */
#define REG_DAC_INTENCLR           (*(RwReg8 *)0x42004804U) /**< \brief (DAC) Interrupt Enable Clear Register */
#define REG_DAC_INTENSET           (*(RwReg8 *)0x42004805U) /**< \brief (DAC) Interrupt Enable Set Register */
#define REG_DAC_INTFLAG            (*(RwReg8 *)0x42004806U) /**< \brief (DAC) Interrupt Flag Status and Clear Register */
#define REG_DAC_STATUS             (*(RoReg8 *)0x42004807U) /**< \brief (DAC) Status Register */
#define REG_DAC_DATA               (*(RwReg16*)0x42004808U) /**< \brief (DAC) Data Register */
#define REG_DAC_DATABUF            (*(RwReg16*)0x4200480CU) /**< \brief (DAC) Data Buffer Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

/* ========== Instance parameters for DAC peripheral ========== */
#define DAC_GCLK_ID                 26

#endif /* _SAMD20_DAC_INSTANCE_ */
