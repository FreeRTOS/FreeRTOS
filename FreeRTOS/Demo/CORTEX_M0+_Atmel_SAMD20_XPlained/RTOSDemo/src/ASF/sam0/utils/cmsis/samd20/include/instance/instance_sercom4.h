/**
 * \file
 *
 * \brief Instance description for SERCOM4
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

#ifndef _SAMD20_SERCOM4_INSTANCE_
#define _SAMD20_SERCOM4_INSTANCE_

/* ========== Register definition for SERCOM4 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_SERCOM4_I2CM_CTRLA     (0x42001800U) /**< \brief (SERCOM4) I2CM Control Register A */
#define REG_SERCOM4_I2CS_CTRLA     (0x42001800U) /**< \brief (SERCOM4) I2CS Control Register A */
#define REG_SERCOM4_SPI_CTRLA      (0x42001800U) /**< \brief (SERCOM4) SPI Control Register A */
#define REG_SERCOM4_USART_CTRLA    (0x42001800U) /**< \brief (SERCOM4) USART Control Register A */
#define REG_SERCOM4_I2CM_CTRLB     (0x42001804U) /**< \brief (SERCOM4) I2CM Control Register B */
#define REG_SERCOM4_I2CS_CTRLB     (0x42001804U) /**< \brief (SERCOM4) I2CS Control Register B */
#define REG_SERCOM4_SPI_CTRLB      (0x42001804U) /**< \brief (SERCOM4) SPI Control Register B */
#define REG_SERCOM4_USART_CTRLB    (0x42001804U) /**< \brief (SERCOM4) USART Control Register B */
#define REG_SERCOM4_I2CM_DBGCTRL   (0x42001808U) /**< \brief (SERCOM4) I2CM Debug Register */
#define REG_SERCOM4_SPI_DBGCTRL    (0x42001808U) /**< \brief (SERCOM4) SPI Debug Register */
#define REG_SERCOM4_USART_DBGCTRL  (0x42001808U) /**< \brief (SERCOM4) USART Debug Register */
#define REG_SERCOM4_I2CM_BAUD      (0x4200180AU) /**< \brief (SERCOM4) I2CM Baud Rate Register */
#define REG_SERCOM4_SPI_BAUD       (0x4200180AU) /**< \brief (SERCOM4) SPI Baud Rate Register */
#define REG_SERCOM4_USART_BAUD     (0x4200180AU) /**< \brief (SERCOM4) USART Baud Rate Register */
#define REG_SERCOM4_I2CM_INTENCLR  (0x4200180CU) /**< \brief (SERCOM4) I2CM Interrupt Enable Clear Register */
#define REG_SERCOM4_I2CS_INTENCLR  (0x4200180CU) /**< \brief (SERCOM4) I2CS Interrupt Enable Clear Register */
#define REG_SERCOM4_SPI_INTENCLR   (0x4200180CU) /**< \brief (SERCOM4) SPI Interrupt Enable Clear Register */
#define REG_SERCOM4_USART_INTENCLR (0x4200180CU) /**< \brief (SERCOM4) USART Interrupt Enable Clear Register */
#define REG_SERCOM4_I2CM_INTENSET  (0x4200180DU) /**< \brief (SERCOM4) I2CM Interrupt Enable Set Register */
#define REG_SERCOM4_I2CS_INTENSET  (0x4200180DU) /**< \brief (SERCOM4) I2CS Interrupt Enable Set Register */
#define REG_SERCOM4_SPI_INTENSET   (0x4200180DU) /**< \brief (SERCOM4) SPI Interrupt Enable Set Register */
#define REG_SERCOM4_USART_INTENSET (0x4200180DU) /**< \brief (SERCOM4) USART Interrupt Enable Set Register */
#define REG_SERCOM4_I2CM_INTFLAG   (0x4200180EU) /**< \brief (SERCOM4) I2CM Interrupt Flag Status and Clear Register */
#define REG_SERCOM4_I2CS_INTFLAG   (0x4200180EU) /**< \brief (SERCOM4) I2CS Interrupt Flag Status and Clear Register */
#define REG_SERCOM4_SPI_INTFLAG    (0x4200180EU) /**< \brief (SERCOM4) SPI Interrupt Flag Status and Clear Register */
#define REG_SERCOM4_USART_INTFLAG  (0x4200180EU) /**< \brief (SERCOM4) USART Interrupt Flag Status and Clear Register */
#define REG_SERCOM4_I2CM_STATUS    (0x42001810U) /**< \brief (SERCOM4) I2CM Status Register */
#define REG_SERCOM4_I2CS_STATUS    (0x42001810U) /**< \brief (SERCOM4) I2CS Status Register */
#define REG_SERCOM4_SPI_STATUS     (0x42001810U) /**< \brief (SERCOM4) SPI Status Register */
#define REG_SERCOM4_USART_STATUS   (0x42001810U) /**< \brief (SERCOM4) USART Status Register */
#define REG_SERCOM4_I2CM_ADDR      (0x42001814U) /**< \brief (SERCOM4) I2CM Address Register */
#define REG_SERCOM4_I2CS_ADDR      (0x42001814U) /**< \brief (SERCOM4) I2CS Address Register */
#define REG_SERCOM4_SPI_ADDR       (0x42001814U) /**< \brief (SERCOM4) SPI Address Register */
#define REG_SERCOM4_I2CM_DATA      (0x42001818U) /**< \brief (SERCOM4) I2CM Data Register */
#define REG_SERCOM4_I2CS_DATA      (0x42001818U) /**< \brief (SERCOM4) I2CS Data Register */
#define REG_SERCOM4_SPI_DATA       (0x42001818U) /**< \brief (SERCOM4) SPI Data Register */
#define REG_SERCOM4_USART_DATA     (0x42001818U) /**< \brief (SERCOM4) USART Data Register */
#else
#define REG_SERCOM4_I2CM_CTRLA     (*(RwReg  *)0x42001800U) /**< \brief (SERCOM4) I2CM Control Register A */
#define REG_SERCOM4_I2CS_CTRLA     (*(RwReg  *)0x42001800U) /**< \brief (SERCOM4) I2CS Control Register A */
#define REG_SERCOM4_SPI_CTRLA      (*(RwReg  *)0x42001800U) /**< \brief (SERCOM4) SPI Control Register A */
#define REG_SERCOM4_USART_CTRLA    (*(RwReg  *)0x42001800U) /**< \brief (SERCOM4) USART Control Register A */
#define REG_SERCOM4_I2CM_CTRLB     (*(RwReg  *)0x42001804U) /**< \brief (SERCOM4) I2CM Control Register B */
#define REG_SERCOM4_I2CS_CTRLB     (*(RwReg  *)0x42001804U) /**< \brief (SERCOM4) I2CS Control Register B */
#define REG_SERCOM4_SPI_CTRLB      (*(RwReg  *)0x42001804U) /**< \brief (SERCOM4) SPI Control Register B */
#define REG_SERCOM4_USART_CTRLB    (*(RwReg  *)0x42001804U) /**< \brief (SERCOM4) USART Control Register B */
#define REG_SERCOM4_I2CM_DBGCTRL   (*(RwReg8 *)0x42001808U) /**< \brief (SERCOM4) I2CM Debug Register */
#define REG_SERCOM4_SPI_DBGCTRL    (*(RwReg8 *)0x42001808U) /**< \brief (SERCOM4) SPI Debug Register */
#define REG_SERCOM4_USART_DBGCTRL  (*(RwReg8 *)0x42001808U) /**< \brief (SERCOM4) USART Debug Register */
#define REG_SERCOM4_I2CM_BAUD      (*(RwReg16*)0x4200180AU) /**< \brief (SERCOM4) I2CM Baud Rate Register */
#define REG_SERCOM4_SPI_BAUD       (*(RwReg8 *)0x4200180AU) /**< \brief (SERCOM4) SPI Baud Rate Register */
#define REG_SERCOM4_USART_BAUD     (*(RwReg16*)0x4200180AU) /**< \brief (SERCOM4) USART Baud Rate Register */
#define REG_SERCOM4_I2CM_INTENCLR  (*(RwReg8 *)0x4200180CU) /**< \brief (SERCOM4) I2CM Interrupt Enable Clear Register */
#define REG_SERCOM4_I2CS_INTENCLR  (*(RwReg8 *)0x4200180CU) /**< \brief (SERCOM4) I2CS Interrupt Enable Clear Register */
#define REG_SERCOM4_SPI_INTENCLR   (*(RwReg8 *)0x4200180CU) /**< \brief (SERCOM4) SPI Interrupt Enable Clear Register */
#define REG_SERCOM4_USART_INTENCLR (*(RwReg8 *)0x4200180CU) /**< \brief (SERCOM4) USART Interrupt Enable Clear Register */
#define REG_SERCOM4_I2CM_INTENSET  (*(RwReg8 *)0x4200180DU) /**< \brief (SERCOM4) I2CM Interrupt Enable Set Register */
#define REG_SERCOM4_I2CS_INTENSET  (*(RwReg8 *)0x4200180DU) /**< \brief (SERCOM4) I2CS Interrupt Enable Set Register */
#define REG_SERCOM4_SPI_INTENSET   (*(RwReg8 *)0x4200180DU) /**< \brief (SERCOM4) SPI Interrupt Enable Set Register */
#define REG_SERCOM4_USART_INTENSET (*(RwReg8 *)0x4200180DU) /**< \brief (SERCOM4) USART Interrupt Enable Set Register */
#define REG_SERCOM4_I2CM_INTFLAG   (*(RwReg8 *)0x4200180EU) /**< \brief (SERCOM4) I2CM Interrupt Flag Status and Clear Register */
#define REG_SERCOM4_I2CS_INTFLAG   (*(RwReg8 *)0x4200180EU) /**< \brief (SERCOM4) I2CS Interrupt Flag Status and Clear Register */
#define REG_SERCOM4_SPI_INTFLAG    (*(RwReg8 *)0x4200180EU) /**< \brief (SERCOM4) SPI Interrupt Flag Status and Clear Register */
#define REG_SERCOM4_USART_INTFLAG  (*(RwReg8 *)0x4200180EU) /**< \brief (SERCOM4) USART Interrupt Flag Status and Clear Register */
#define REG_SERCOM4_I2CM_STATUS    (*(RwReg16*)0x42001810U) /**< \brief (SERCOM4) I2CM Status Register */
#define REG_SERCOM4_I2CS_STATUS    (*(RwReg16*)0x42001810U) /**< \brief (SERCOM4) I2CS Status Register */
#define REG_SERCOM4_SPI_STATUS     (*(RwReg16*)0x42001810U) /**< \brief (SERCOM4) SPI Status Register */
#define REG_SERCOM4_USART_STATUS   (*(RwReg16*)0x42001810U) /**< \brief (SERCOM4) USART Status Register */
#define REG_SERCOM4_I2CM_ADDR      (*(RwReg8 *)0x42001814U) /**< \brief (SERCOM4) I2CM Address Register */
#define REG_SERCOM4_I2CS_ADDR      (*(RwReg  *)0x42001814U) /**< \brief (SERCOM4) I2CS Address Register */
#define REG_SERCOM4_SPI_ADDR       (*(RwReg  *)0x42001814U) /**< \brief (SERCOM4) SPI Address Register */
#define REG_SERCOM4_I2CM_DATA      (*(RwReg8 *)0x42001818U) /**< \brief (SERCOM4) I2CM Data Register */
#define REG_SERCOM4_I2CS_DATA      (*(RwReg8 *)0x42001818U) /**< \brief (SERCOM4) I2CS Data Register */
#define REG_SERCOM4_SPI_DATA       (*(RwReg16*)0x42001818U) /**< \brief (SERCOM4) SPI Data Register */
#define REG_SERCOM4_USART_DATA     (*(RwReg16*)0x42001818U) /**< \brief (SERCOM4) USART Data Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

/* ========== Instance parameters for SERCOM4 peripheral ========== */
#define SERCOM4_GCLK_ID_CORE        17
#define SERCOM4_GCLK_ID_SLOW        12
#define SERCOM4_INT_MSB             3
#define SERCOM4_PMSB                3

#endif /* _SAMD20_SERCOM4_INSTANCE_ */
