/**
 * \file
 *
 * \brief Instance description for TC4
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

#ifndef _SAMD20_TC4_INSTANCE_
#define _SAMD20_TC4_INSTANCE_

/* ========== Register definition for TC4 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_TC4_CTRLA              (0x42003000U) /**< \brief (TC4) Control A Register */
#define REG_TC4_READREQ            (0x42003002U) /**< \brief (TC4) Read Request Register */
#define REG_TC4_CTRLBCLR           (0x42003004U) /**< \brief (TC4) Control B Clear Register */
#define REG_TC4_CTRLBSET           (0x42003005U) /**< \brief (TC4) Control B Set Register */
#define REG_TC4_CTRLC              (0x42003006U) /**< \brief (TC4) Control C Register */
#define REG_TC4_DBGCTRL            (0x42003008U) /**< \brief (TC4) Debug Register */
#define REG_TC4_EVCTRL             (0x4200300AU) /**< \brief (TC4) Event Control Register */
#define REG_TC4_INTENCLR           (0x4200300CU) /**< \brief (TC4) Interrupt Enable Clear Register */
#define REG_TC4_INTENSET           (0x4200300DU) /**< \brief (TC4) Interrupt Enable Set Register */
#define REG_TC4_INTFLAG            (0x4200300EU) /**< \brief (TC4) Interrupt Flag Status and Clear Register */
#define REG_TC4_STATUS             (0x4200300FU) /**< \brief (TC4) Status Register */
#define REG_TC4_COUNT8_COUNT       (0x42003010U) /**< \brief (TC4) COUNT8 Count Register */
#define REG_TC4_COUNT16_COUNT      (0x42003010U) /**< \brief (TC4) COUNT16 Count Register */
#define REG_TC4_COUNT32_COUNT      (0x42003010U) /**< \brief (TC4) COUNT32 Count Register */
#define REG_TC4_COUNT8_PER         (0x42003014U) /**< \brief (TC4) COUNT8 Period Register */
#define REG_TC4_COUNT32_PER        (0x42003014U) /**< \brief (TC4) COUNT32 Period Register */
#define REG_TC4_COUNT8_CC0         (0x42003018U) /**< \brief (TC4) COUNT8 Compare and Capture Register 0 */
#define REG_TC4_COUNT8_CC1         (0x42003019U) /**< \brief (TC4) COUNT8 Compare and Capture Register 1 */
#define REG_TC4_COUNT16_CC0        (0x42003018U) /**< \brief (TC4) COUNT16 Compare and Capture Register 0 */
#define REG_TC4_COUNT16_CC1        (0x4200301AU) /**< \brief (TC4) COUNT16 Compare and Capture Register 1 */
#define REG_TC4_COUNT32_CC0        (0x42003018U) /**< \brief (TC4) COUNT32 Compare and Capture Register 0 */
#define REG_TC4_COUNT32_CC1        (0x4200301CU) /**< \brief (TC4) COUNT32 Compare and Capture Register 1 */
#else
#define REG_TC4_CTRLA              (*(RwReg16*)0x42003000U) /**< \brief (TC4) Control A Register */
#define REG_TC4_READREQ            (*(RwReg16*)0x42003002U) /**< \brief (TC4) Read Request Register */
#define REG_TC4_CTRLBCLR           (*(RwReg8 *)0x42003004U) /**< \brief (TC4) Control B Clear Register */
#define REG_TC4_CTRLBSET           (*(RwReg8 *)0x42003005U) /**< \brief (TC4) Control B Set Register */
#define REG_TC4_CTRLC              (*(RwReg8 *)0x42003006U) /**< \brief (TC4) Control C Register */
#define REG_TC4_DBGCTRL            (*(RwReg8 *)0x42003008U) /**< \brief (TC4) Debug Register */
#define REG_TC4_EVCTRL             (*(RwReg16*)0x4200300AU) /**< \brief (TC4) Event Control Register */
#define REG_TC4_INTENCLR           (*(RwReg8 *)0x4200300CU) /**< \brief (TC4) Interrupt Enable Clear Register */
#define REG_TC4_INTENSET           (*(RwReg8 *)0x4200300DU) /**< \brief (TC4) Interrupt Enable Set Register */
#define REG_TC4_INTFLAG            (*(RwReg8 *)0x4200300EU) /**< \brief (TC4) Interrupt Flag Status and Clear Register */
#define REG_TC4_STATUS             (*(RoReg8 *)0x4200300FU) /**< \brief (TC4) Status Register */
#define REG_TC4_COUNT8_COUNT       (*(RwReg8 *)0x42003010U) /**< \brief (TC4) COUNT8 Count Register */
#define REG_TC4_COUNT16_COUNT      (*(RwReg16*)0x42003010U) /**< \brief (TC4) COUNT16 Count Register */
#define REG_TC4_COUNT32_COUNT      (*(RwReg  *)0x42003010U) /**< \brief (TC4) COUNT32 Count Register */
#define REG_TC4_COUNT8_PER         (*(RwReg8 *)0x42003014U) /**< \brief (TC4) COUNT8 Period Register */
#define REG_TC4_COUNT32_PER        (*(RwReg  *)0x42003014U) /**< \brief (TC4) COUNT32 Period Register */
#define REG_TC4_COUNT8_CC0         (*(RwReg8 *)0x42003018U) /**< \brief (TC4) COUNT8 Compare and Capture Register 0 */
#define REG_TC4_COUNT8_CC1         (*(RwReg8 *)0x42003019U) /**< \brief (TC4) COUNT8 Compare and Capture Register 1 */
#define REG_TC4_COUNT16_CC0        (*(RwReg16*)0x42003018U) /**< \brief (TC4) COUNT16 Compare and Capture Register 0 */
#define REG_TC4_COUNT16_CC1        (*(RwReg16*)0x4200301AU) /**< \brief (TC4) COUNT16 Compare and Capture Register 1 */
#define REG_TC4_COUNT32_CC0        (*(RwReg  *)0x42003018U) /**< \brief (TC4) COUNT32 Compare and Capture Register 0 */
#define REG_TC4_COUNT32_CC1        (*(RwReg  *)0x4200301CU) /**< \brief (TC4) COUNT32 Compare and Capture Register 1 */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

/* ========== Instance parameters for TC4 peripheral ========== */
#define TC4_CC8_NUM                 2
#define TC4_CC16_NUM                2
#define TC4_CC32_NUM                2
#define TC4_DITHERING_EXT           0
#define TC4_GCLK_ID                 21
#define TC4_OW_NUM                  2
#define TC4_PERIOD_EXT              0
#define TC4_SHADOW_EXT              0

#endif /* _SAMD20_TC4_INSTANCE_ */
