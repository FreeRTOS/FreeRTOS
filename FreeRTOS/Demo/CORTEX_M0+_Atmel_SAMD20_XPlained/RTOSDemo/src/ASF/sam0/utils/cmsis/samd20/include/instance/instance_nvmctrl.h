/**
 * \file
 *
 * \brief Instance description for NVMCTRL
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

#ifndef _SAMD20_NVMCTRL_INSTANCE_
#define _SAMD20_NVMCTRL_INSTANCE_

/* ========== Register definition for NVMCTRL peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_NVMCTRL_CTRLA          (0x41004000U) /**< \brief (NVMCTRL) NVM Control Register A */
#define REG_NVMCTRL_CTRLB          (0x41004004U) /**< \brief (NVMCTRL) NVM Control Register B */
#define REG_NVMCTRL_PARAM          (0x41004008U) /**< \brief (NVMCTRL) Parameter Register */
#define REG_NVMCTRL_INTENCLR       (0x4100400CU) /**< \brief (NVMCTRL) Interrupt Enable Clear Register */
#define REG_NVMCTRL_INTENSET       (0x41004010U) /**< \brief (NVMCTRL) Interrupt Enable Set Register */
#define REG_NVMCTRL_INTFLAG        (0x41004014U) /**< \brief (NVMCTRL) Interrupt Flag Status and Clear Register */
#define REG_NVMCTRL_STATUS         (0x41004018U) /**< \brief (NVMCTRL) Status Register */
#define REG_NVMCTRL_ADDR           (0x4100401CU) /**< \brief (NVMCTRL) Address Register */
#define REG_NVMCTRL_LOCK           (0x41004020U) /**< \brief (NVMCTRL) Lock Register */
#else
#define REG_NVMCTRL_CTRLA          (*(RwReg16*)0x41004000U) /**< \brief (NVMCTRL) NVM Control Register A */
#define REG_NVMCTRL_CTRLB          (*(RwReg  *)0x41004004U) /**< \brief (NVMCTRL) NVM Control Register B */
#define REG_NVMCTRL_PARAM          (*(RwReg  *)0x41004008U) /**< \brief (NVMCTRL) Parameter Register */
#define REG_NVMCTRL_INTENCLR       (*(RwReg8 *)0x4100400CU) /**< \brief (NVMCTRL) Interrupt Enable Clear Register */
#define REG_NVMCTRL_INTENSET       (*(RwReg8 *)0x41004010U) /**< \brief (NVMCTRL) Interrupt Enable Set Register */
#define REG_NVMCTRL_INTFLAG        (*(RwReg8 *)0x41004014U) /**< \brief (NVMCTRL) Interrupt Flag Status and Clear Register */
#define REG_NVMCTRL_STATUS         (*(RwReg16*)0x41004018U) /**< \brief (NVMCTRL) Status Register */
#define REG_NVMCTRL_ADDR           (*(RwReg  *)0x4100401CU) /**< \brief (NVMCTRL) Address Register */
#define REG_NVMCTRL_LOCK           (*(RwReg16*)0x41004020U) /**< \brief (NVMCTRL) Lock Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

/* ========== Instance parameters for NVMCTRL peripheral ========== */
#define NVMCTRL_AUX0_ADDRESS        (NVMCTRL_USER_PAGE_ADDRESS + 0x00004000)
#define NVMCTRL_AUX1_ADDRESS        (NVMCTRL_USER_PAGE_ADDRESS + 0x00006000)
#define NVMCTRL_AUX2_ADDRESS        (NVMCTRL_USER_PAGE_ADDRESS + 0x00008000)
#define NVMCTRL_AUX3_ADDRESS        (NVMCTRL_USER_PAGE_ADDRESS + 0x0000A000)
#define NVMCTRL_CLK_AHB_ID          4
#define NVMCTRL_FACTORY_WORD_IMPLEMENTED_MASK 0XC0000007FFFFFFFF
#define NVMCTRL_FLASH_SIZE          (NVMCTRL_PAGES*NVMCTRL_PAGE_SIZE)
#define NVMCTRL_FUSES_SECURE_NVM    
#define NVMCTRL_FUSES_SECURE_RAM    
#define NVMCTRL_FUSES_SECURE_STATE  
#define NVMCTRL_LOCKBIT_ADDRESS     (NVMCTRL_USER_PAGE_ADDRESS + 0x00002000)
#define NVMCTRL_PAGES               4096
#define NVMCTRL_PAGE_HW             (NVMCTRL_PAGE_SIZE/2)
#define NVMCTRL_PAGE_SIZE           (1<<NVMCTRL_PSZ_BITS)
#define NVMCTRL_PAGE_W              (NVMCTRL_PAGE_SIZE/4)
#define NVMCTRL_PMSB                3
#define NVMCTRL_PSZ_BITS            6
#define NVMCTRL_ROW_PAGES           (NVMCTRL_ROW_SIZE/NVMCTRL_PAGE_SIZE)
#define NVMCTRL_ROW_SIZE            (NVMCTRL_PAGE_SIZE*4)
#define NVMCTRL_USER_PAGE_ADDRESS   (FLASH_ADDR + NVMCTRL_USER_PAGE_OFFSET)
#define NVMCTRL_USER_PAGE_OFFSET    0x00800000
#define NVMCTRL_USER_WORD_IMPLEMENTED_MASK 0XC01FFFFFFFFFFFFF

#endif /* _SAMD20_NVMCTRL_INSTANCE_ */
