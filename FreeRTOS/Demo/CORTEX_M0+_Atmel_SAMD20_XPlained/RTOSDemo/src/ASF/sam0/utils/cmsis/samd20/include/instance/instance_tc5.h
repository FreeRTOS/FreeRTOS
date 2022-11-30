/**
 * \file
 *
 * \brief Instance description for TC5
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

#ifndef _SAMD20_TC5_INSTANCE_
#define _SAMD20_TC5_INSTANCE_

/* ========== Register definition for TC5 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_TC5_CTRLA              (0x42003400U) /**< \brief (TC5) Control A Register */
#define REG_TC5_READREQ            (0x42003402U) /**< \brief (TC5) Read Request Register */
#define REG_TC5_CTRLBCLR           (0x42003404U) /**< \brief (TC5) Control B Clear Register */
#define REG_TC5_CTRLBSET           (0x42003405U) /**< \brief (TC5) Control B Set Register */
#define REG_TC5_CTRLC              (0x42003406U) /**< \brief (TC5) Control C Register */
#define REG_TC5_DBGCTRL            (0x42003408U) /**< \brief (TC5) Debug Register */
#define REG_TC5_EVCTRL             (0x4200340AU) /**< \brief (TC5) Event Control Register */
#define REG_TC5_INTENCLR           (0x4200340CU) /**< \brief (TC5) Interrupt Enable Clear Register */
#define REG_TC5_INTENSET           (0x4200340DU) /**< \brief (TC5) Interrupt Enable Set Register */
#define REG_TC5_INTFLAG            (0x4200340EU) /**< \brief (TC5) Interrupt Flag Status and Clear Register */
#define REG_TC5_STATUS             (0x4200340FU) /**< \brief (TC5) Status Register */
#define REG_TC5_COUNT8_COUNT       (0x42003410U) /**< \brief (TC5) COUNT8 Count Register */
#define REG_TC5_COUNT16_COUNT      (0x42003410U) /**< \brief (TC5) COUNT16 Count Register */
#define REG_TC5_COUNT32_COUNT      (0x42003410U) /**< \brief (TC5) COUNT32 Count Register */
#define REG_TC5_COUNT8_PER         (0x42003414U) /**< \brief (TC5) COUNT8 Period Register */
#define REG_TC5_COUNT32_PER        (0x42003414U) /**< \brief (TC5) COUNT32 Period Register */
#define REG_TC5_COUNT8_CC0         (0x42003418U) /**< \brief (TC5) COUNT8 Compare and Capture Register 0 */
#define REG_TC5_COUNT8_CC1         (0x42003419U) /**< \brief (TC5) COUNT8 Compare and Capture Register 1 */
#define REG_TC5_COUNT16_CC0        (0x42003418U) /**< \brief (TC5) COUNT16 Compare and Capture Register 0 */
#define REG_TC5_COUNT16_CC1        (0x4200341AU) /**< \brief (TC5) COUNT16 Compare and Capture Register 1 */
#define REG_TC5_COUNT32_CC0        (0x42003418U) /**< \brief (TC5) COUNT32 Compare and Capture Register 0 */
#define REG_TC5_COUNT32_CC1        (0x4200341CU) /**< \brief (TC5) COUNT32 Compare and Capture Register 1 */
#else
#define REG_TC5_CTRLA              (*(RwReg16*)0x42003400U) /**< \brief (TC5) Control A Register */
#define REG_TC5_READREQ            (*(RwReg16*)0x42003402U) /**< \brief (TC5) Read Request Register */
#define REG_TC5_CTRLBCLR           (*(RwReg8 *)0x42003404U) /**< \brief (TC5) Control B Clear Register */
#define REG_TC5_CTRLBSET           (*(RwReg8 *)0x42003405U) /**< \brief (TC5) Control B Set Register */
#define REG_TC5_CTRLC              (*(RwReg8 *)0x42003406U) /**< \brief (TC5) Control C Register */
#define REG_TC5_DBGCTRL            (*(RwReg8 *)0x42003408U) /**< \brief (TC5) Debug Register */
#define REG_TC5_EVCTRL             (*(RwReg16*)0x4200340AU) /**< \brief (TC5) Event Control Register */
#define REG_TC5_INTENCLR           (*(RwReg8 *)0x4200340CU) /**< \brief (TC5) Interrupt Enable Clear Register */
#define REG_TC5_INTENSET           (*(RwReg8 *)0x4200340DU) /**< \brief (TC5) Interrupt Enable Set Register */
#define REG_TC5_INTFLAG            (*(RwReg8 *)0x4200340EU) /**< \brief (TC5) Interrupt Flag Status and Clear Register */
#define REG_TC5_STATUS             (*(RoReg8 *)0x4200340FU) /**< \brief (TC5) Status Register */
#define REG_TC5_COUNT8_COUNT       (*(RwReg8 *)0x42003410U) /**< \brief (TC5) COUNT8 Count Register */
#define REG_TC5_COUNT16_COUNT      (*(RwReg16*)0x42003410U) /**< \brief (TC5) COUNT16 Count Register */
#define REG_TC5_COUNT32_COUNT      (*(RwReg  *)0x42003410U) /**< \brief (TC5) COUNT32 Count Register */
#define REG_TC5_COUNT8_PER         (*(RwReg8 *)0x42003414U) /**< \brief (TC5) COUNT8 Period Register */
#define REG_TC5_COUNT32_PER        (*(RwReg  *)0x42003414U) /**< \brief (TC5) COUNT32 Period Register */
#define REG_TC5_COUNT8_CC0         (*(RwReg8 *)0x42003418U) /**< \brief (TC5) COUNT8 Compare and Capture Register 0 */
#define REG_TC5_COUNT8_CC1         (*(RwReg8 *)0x42003419U) /**< \brief (TC5) COUNT8 Compare and Capture Register 1 */
#define REG_TC5_COUNT16_CC0        (*(RwReg16*)0x42003418U) /**< \brief (TC5) COUNT16 Compare and Capture Register 0 */
#define REG_TC5_COUNT16_CC1        (*(RwReg16*)0x4200341AU) /**< \brief (TC5) COUNT16 Compare and Capture Register 1 */
#define REG_TC5_COUNT32_CC0        (*(RwReg  *)0x42003418U) /**< \brief (TC5) COUNT32 Compare and Capture Register 0 */
#define REG_TC5_COUNT32_CC1        (*(RwReg  *)0x4200341CU) /**< \brief (TC5) COUNT32 Compare and Capture Register 1 */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

/* ========== Instance parameters for TC5 peripheral ========== */
#define TC5_CC8_NUM                 2
#define TC5_CC16_NUM                2
#define TC5_CC32_NUM                2
#define TC5_DITHERING_EXT           0
#define TC5_GCLK_ID                 21
#define TC5_OW_NUM                  2
#define TC5_PERIOD_EXT              0
#define TC5_SHADOW_EXT              0

#endif /* _SAMD20_TC5_INSTANCE_ */
