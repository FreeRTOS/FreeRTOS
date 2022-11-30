/**
 * \file
 *
 * \brief Instance description for TC6
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

#ifndef _SAMD20_TC6_INSTANCE_
#define _SAMD20_TC6_INSTANCE_

/* ========== Register definition for TC6 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_TC6_CTRLA              (0x42003800U) /**< \brief (TC6) Control A Register */
#define REG_TC6_READREQ            (0x42003802U) /**< \brief (TC6) Read Request Register */
#define REG_TC6_CTRLBCLR           (0x42003804U) /**< \brief (TC6) Control B Clear Register */
#define REG_TC6_CTRLBSET           (0x42003805U) /**< \brief (TC6) Control B Set Register */
#define REG_TC6_CTRLC              (0x42003806U) /**< \brief (TC6) Control C Register */
#define REG_TC6_DBGCTRL            (0x42003808U) /**< \brief (TC6) Debug Register */
#define REG_TC6_EVCTRL             (0x4200380AU) /**< \brief (TC6) Event Control Register */
#define REG_TC6_INTENCLR           (0x4200380CU) /**< \brief (TC6) Interrupt Enable Clear Register */
#define REG_TC6_INTENSET           (0x4200380DU) /**< \brief (TC6) Interrupt Enable Set Register */
#define REG_TC6_INTFLAG            (0x4200380EU) /**< \brief (TC6) Interrupt Flag Status and Clear Register */
#define REG_TC6_STATUS             (0x4200380FU) /**< \brief (TC6) Status Register */
#define REG_TC6_COUNT8_COUNT       (0x42003810U) /**< \brief (TC6) COUNT8 Count Register */
#define REG_TC6_COUNT16_COUNT      (0x42003810U) /**< \brief (TC6) COUNT16 Count Register */
#define REG_TC6_COUNT32_COUNT      (0x42003810U) /**< \brief (TC6) COUNT32 Count Register */
#define REG_TC6_COUNT8_PER         (0x42003814U) /**< \brief (TC6) COUNT8 Period Register */
#define REG_TC6_COUNT32_PER        (0x42003814U) /**< \brief (TC6) COUNT32 Period Register */
#define REG_TC6_COUNT8_CC0         (0x42003818U) /**< \brief (TC6) COUNT8 Compare and Capture Register 0 */
#define REG_TC6_COUNT8_CC1         (0x42003819U) /**< \brief (TC6) COUNT8 Compare and Capture Register 1 */
#define REG_TC6_COUNT16_CC0        (0x42003818U) /**< \brief (TC6) COUNT16 Compare and Capture Register 0 */
#define REG_TC6_COUNT16_CC1        (0x4200381AU) /**< \brief (TC6) COUNT16 Compare and Capture Register 1 */
#define REG_TC6_COUNT32_CC0        (0x42003818U) /**< \brief (TC6) COUNT32 Compare and Capture Register 0 */
#define REG_TC6_COUNT32_CC1        (0x4200381CU) /**< \brief (TC6) COUNT32 Compare and Capture Register 1 */
#else
#define REG_TC6_CTRLA              (*(RwReg16*)0x42003800U) /**< \brief (TC6) Control A Register */
#define REG_TC6_READREQ            (*(RwReg16*)0x42003802U) /**< \brief (TC6) Read Request Register */
#define REG_TC6_CTRLBCLR           (*(RwReg8 *)0x42003804U) /**< \brief (TC6) Control B Clear Register */
#define REG_TC6_CTRLBSET           (*(RwReg8 *)0x42003805U) /**< \brief (TC6) Control B Set Register */
#define REG_TC6_CTRLC              (*(RwReg8 *)0x42003806U) /**< \brief (TC6) Control C Register */
#define REG_TC6_DBGCTRL            (*(RwReg8 *)0x42003808U) /**< \brief (TC6) Debug Register */
#define REG_TC6_EVCTRL             (*(RwReg16*)0x4200380AU) /**< \brief (TC6) Event Control Register */
#define REG_TC6_INTENCLR           (*(RwReg8 *)0x4200380CU) /**< \brief (TC6) Interrupt Enable Clear Register */
#define REG_TC6_INTENSET           (*(RwReg8 *)0x4200380DU) /**< \brief (TC6) Interrupt Enable Set Register */
#define REG_TC6_INTFLAG            (*(RwReg8 *)0x4200380EU) /**< \brief (TC6) Interrupt Flag Status and Clear Register */
#define REG_TC6_STATUS             (*(RoReg8 *)0x4200380FU) /**< \brief (TC6) Status Register */
#define REG_TC6_COUNT8_COUNT       (*(RwReg8 *)0x42003810U) /**< \brief (TC6) COUNT8 Count Register */
#define REG_TC6_COUNT16_COUNT      (*(RwReg16*)0x42003810U) /**< \brief (TC6) COUNT16 Count Register */
#define REG_TC6_COUNT32_COUNT      (*(RwReg  *)0x42003810U) /**< \brief (TC6) COUNT32 Count Register */
#define REG_TC6_COUNT8_PER         (*(RwReg8 *)0x42003814U) /**< \brief (TC6) COUNT8 Period Register */
#define REG_TC6_COUNT32_PER        (*(RwReg  *)0x42003814U) /**< \brief (TC6) COUNT32 Period Register */
#define REG_TC6_COUNT8_CC0         (*(RwReg8 *)0x42003818U) /**< \brief (TC6) COUNT8 Compare and Capture Register 0 */
#define REG_TC6_COUNT8_CC1         (*(RwReg8 *)0x42003819U) /**< \brief (TC6) COUNT8 Compare and Capture Register 1 */
#define REG_TC6_COUNT16_CC0        (*(RwReg16*)0x42003818U) /**< \brief (TC6) COUNT16 Compare and Capture Register 0 */
#define REG_TC6_COUNT16_CC1        (*(RwReg16*)0x4200381AU) /**< \brief (TC6) COUNT16 Compare and Capture Register 1 */
#define REG_TC6_COUNT32_CC0        (*(RwReg  *)0x42003818U) /**< \brief (TC6) COUNT32 Compare and Capture Register 0 */
#define REG_TC6_COUNT32_CC1        (*(RwReg  *)0x4200381CU) /**< \brief (TC6) COUNT32 Compare and Capture Register 1 */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

/* ========== Instance parameters for TC6 peripheral ========== */
#define TC6_CC8_NUM                 2
#define TC6_CC16_NUM                2
#define TC6_CC32_NUM                2
#define TC6_DITHERING_EXT           0
#define TC6_GCLK_ID                 22
#define TC6_OW_NUM                  2
#define TC6_PERIOD_EXT              0
#define TC6_SHADOW_EXT              0

#endif /* _SAMD20_TC6_INSTANCE_ */
