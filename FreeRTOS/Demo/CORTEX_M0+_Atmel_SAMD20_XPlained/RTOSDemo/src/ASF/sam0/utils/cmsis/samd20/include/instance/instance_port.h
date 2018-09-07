/**
 * \file
 *
 * \brief Instance description for PORT
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

#ifndef _SAMD20_PORT_INSTANCE_
#define _SAMD20_PORT_INSTANCE_

/* ========== Register definition for PORT peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_PORT_DIR0              (0x41004400U) /**< \brief (PORT) Data Direction Register 0 */
#define REG_PORT_DIRCLR0           (0x41004404U) /**< \brief (PORT) Data Direction Clear Register 0 */
#define REG_PORT_DIRSET0           (0x41004408U) /**< \brief (PORT) Data Direction Set Register 0 */
#define REG_PORT_DIRTGL0           (0x4100440CU) /**< \brief (PORT) Data Direction Toggle Register 0 */
#define REG_PORT_OUT0              (0x41004410U) /**< \brief (PORT) Data Output Value Register 0 */
#define REG_PORT_OUTCLR0           (0x41004414U) /**< \brief (PORT) Data Output Value Clear Register 0 */
#define REG_PORT_OUTSET0           (0x41004418U) /**< \brief (PORT) Data Output Value Set Register 0 */
#define REG_PORT_OUTTGL0           (0x4100441CU) /**< \brief (PORT) Data Output Value Toggle Register 0 */
#define REG_PORT_IN0               (0x41004420U) /**< \brief (PORT) Data Input Value Register 0 */
#define REG_PORT_CTRL0             (0x41004424U) /**< \brief (PORT) Control Register 0 */
#define REG_PORT_WRCONFIG0         (0x41004428U) /**< \brief (PORT) Write Configuration Register 0 */
#define REG_PORT_PMUX0             (0x41004430U) /**< \brief (PORT) Peripheral Multiplexing Register 0 */
#define REG_PORT_PINCFG0           (0x41004440U) /**< \brief (PORT) Pin Configuration Register 0 */
#define REG_PORT_DIR1              (0x41004480U) /**< \brief (PORT) Data Direction Register 1 */
#define REG_PORT_DIRCLR1           (0x41004484U) /**< \brief (PORT) Data Direction Clear Register 1 */
#define REG_PORT_DIRSET1           (0x41004488U) /**< \brief (PORT) Data Direction Set Register 1 */
#define REG_PORT_DIRTGL1           (0x4100448CU) /**< \brief (PORT) Data Direction Toggle Register 1 */
#define REG_PORT_OUT1              (0x41004490U) /**< \brief (PORT) Data Output Value Register 1 */
#define REG_PORT_OUTCLR1           (0x41004494U) /**< \brief (PORT) Data Output Value Clear Register 1 */
#define REG_PORT_OUTSET1           (0x41004498U) /**< \brief (PORT) Data Output Value Set Register 1 */
#define REG_PORT_OUTTGL1           (0x4100449CU) /**< \brief (PORT) Data Output Value Toggle Register 1 */
#define REG_PORT_IN1               (0x410044A0U) /**< \brief (PORT) Data Input Value Register 1 */
#define REG_PORT_CTRL1             (0x410044A4U) /**< \brief (PORT) Control Register 1 */
#define REG_PORT_WRCONFIG1         (0x410044A8U) /**< \brief (PORT) Write Configuration Register 1 */
#define REG_PORT_PMUX1             (0x410044B0U) /**< \brief (PORT) Peripheral Multiplexing Register 1 */
#define REG_PORT_PINCFG1           (0x410044C0U) /**< \brief (PORT) Pin Configuration Register 1 */
#else
#define REG_PORT_DIR0              (*(RwReg  *)0x41004400U) /**< \brief (PORT) Data Direction Register 0 */
#define REG_PORT_DIRCLR0           (*(RwReg  *)0x41004404U) /**< \brief (PORT) Data Direction Clear Register 0 */
#define REG_PORT_DIRSET0           (*(RwReg  *)0x41004408U) /**< \brief (PORT) Data Direction Set Register 0 */
#define REG_PORT_DIRTGL0           (*(RwReg  *)0x4100440CU) /**< \brief (PORT) Data Direction Toggle Register 0 */
#define REG_PORT_OUT0              (*(RwReg  *)0x41004410U) /**< \brief (PORT) Data Output Value Register 0 */
#define REG_PORT_OUTCLR0           (*(RwReg  *)0x41004414U) /**< \brief (PORT) Data Output Value Clear Register 0 */
#define REG_PORT_OUTSET0           (*(RwReg  *)0x41004418U) /**< \brief (PORT) Data Output Value Set Register 0 */
#define REG_PORT_OUTTGL0           (*(RwReg  *)0x4100441CU) /**< \brief (PORT) Data Output Value Toggle Register 0 */
#define REG_PORT_IN0               (*(RoReg  *)0x41004420U) /**< \brief (PORT) Data Input Value Register 0 */
#define REG_PORT_CTRL0             (*(RwReg  *)0x41004424U) /**< \brief (PORT) Control Register 0 */
#define REG_PORT_WRCONFIG0         (*(WoReg  *)0x41004428U) /**< \brief (PORT) Write Configuration Register 0 */
#define REG_PORT_PMUX0             (*(RwReg  *)0x41004430U) /**< \brief (PORT) Peripheral Multiplexing Register 0 */
#define REG_PORT_PINCFG0           (*(RwReg  *)0x41004440U) /**< \brief (PORT) Pin Configuration Register 0 */
#define REG_PORT_DIR1              (*(RwReg  *)0x41004480U) /**< \brief (PORT) Data Direction Register 1 */
#define REG_PORT_DIRCLR1           (*(RwReg  *)0x41004484U) /**< \brief (PORT) Data Direction Clear Register 1 */
#define REG_PORT_DIRSET1           (*(RwReg  *)0x41004488U) /**< \brief (PORT) Data Direction Set Register 1 */
#define REG_PORT_DIRTGL1           (*(RwReg  *)0x4100448CU) /**< \brief (PORT) Data Direction Toggle Register 1 */
#define REG_PORT_OUT1              (*(RwReg  *)0x41004490U) /**< \brief (PORT) Data Output Value Register 1 */
#define REG_PORT_OUTCLR1           (*(RwReg  *)0x41004494U) /**< \brief (PORT) Data Output Value Clear Register 1 */
#define REG_PORT_OUTSET1           (*(RwReg  *)0x41004498U) /**< \brief (PORT) Data Output Value Set Register 1 */
#define REG_PORT_OUTTGL1           (*(RwReg  *)0x4100449CU) /**< \brief (PORT) Data Output Value Toggle Register 1 */
#define REG_PORT_IN1               (*(RoReg  *)0x410044A0U) /**< \brief (PORT) Data Input Value Register 1 */
#define REG_PORT_CTRL1             (*(RwReg  *)0x410044A4U) /**< \brief (PORT) Control Register 1 */
#define REG_PORT_WRCONFIG1         (*(WoReg  *)0x410044A8U) /**< \brief (PORT) Write Configuration Register 1 */
#define REG_PORT_PMUX1             (*(RwReg  *)0x410044B0U) /**< \brief (PORT) Peripheral Multiplexing Register 1 */
#define REG_PORT_PINCFG1           (*(RwReg  *)0x410044C0U) /**< \brief (PORT) Pin Configuration Register 1 */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

/* ========== Instance parameters for PORT peripheral ========== */
#define PORT_BITS                   64
#define PORT_DIR_DEFAULT_VAL        { 0x00000000, 0x00000000 }
#define PORT_DIR_IMPLEMENTED        { 0xDBFFFFFF, 0xC0C3FFFF }
#define PORT_DRVSTR_DEFAULT_VAL     { 0x00000000, 0x00000000 }
#define PORT_DRVSTR_IMPLEMENTED     { 0x00000000, 0x00000000 }
#define PORT_GROUPS                 2
#define PORT_INEN_DEFAULT_VAL       { 0x00000000, 0x00000000 }
#define PORT_INEN_IMPLEMENTED       { 0xDBFFFFFF, 0xC0C3FFFF }
#define PORT_ODRAIN_DEFAULT_VAL     { 0x00000000, 0x00000000 }
#define PORT_ODRAIN_IMPLEMENTED     { 0x00000000, 0x00000000 }
#define PORT_OUT_DEFAULT_VAL        { 0x00000000, 0x00000000 }
#define PORT_OUT_IMPLEMENTED        { 0xDBFFFFFF, 0xC0C3FFFF }
#define PORT_PIN_IMPLEMENTED        { 0xDBFFFFFF, 0xC0C3FFFF }
#define PORT_PMUXBIT0_DEFAULT_VAL   { 0x00000000, 0x00000000 }
#define PORT_PMUXBIT0_IMPLEMENTED   { 0xDBFFFFFF, 0xC0C3FFFF }
#define PORT_PMUXBIT1_DEFAULT_VAL   { 0x40000000, 0x00000000 }
#define PORT_PMUXBIT1_IMPLEMENTED   { 0xDBFFFFF3, 0xC0C3FF0F }
#define PORT_PMUXBIT2_DEFAULT_VAL   { 0x40000000, 0x00000000 }
#define PORT_PMUXBIT2_IMPLEMENTED   { 0xDBFFFFF3, 0xC0C3FF0F }
#define PORT_PMUXBIT3_DEFAULT_VAL   { 0x00000000, 0x00000000 }
#define PORT_PMUXBIT3_IMPLEMENTED   { 0x00000000, 0x00000000 }
#define PORT_PMUXEN_DEFAULT_VAL     { 0x64000000, 0x3F3C0000 }
#define PORT_PMUXEN_IMPLEMENTED     { 0xDBFFFFFF, 0xC0C3FFFF }
#define PORT_PULLEN_DEFAULT_VAL     { 0x00000000, 0x00000000 }
#define PORT_PULLEN_IMPLEMENTED     { 0xDBFFFFFF, 0xC0C3FFFF }
#define PORT_SLEWLIM_DEFAULT_VAL    { 0x00000000, 0x00000000 }
#define PORT_SLEWLIM_IMPLEMENTED    { 0x00000000, 0x00000000 }

#endif /* _SAMD20_PORT_INSTANCE_ */
