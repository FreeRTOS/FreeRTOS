/**
 * \file
 *
 * Copyright (c) 2015 Atmel Corporation. All rights reserved.
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
/*
 * Support and FAQ: visit <a href="http://www.atmel.com/design-support/">Atmel Support</a>
 */

#ifndef _SAME70_SMC_INSTANCE_
#define _SAME70_SMC_INSTANCE_

/* ========== Register definition for SMC peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
  #define REG_SMC_SETUP0                  (0x40080000U) /**< \brief (SMC) SMC Setup Register (CS_number = 0) */
  #define REG_SMC_PULSE0                  (0x40080004U) /**< \brief (SMC) SMC Pulse Register (CS_number = 0) */
  #define REG_SMC_CYCLE0                  (0x40080008U) /**< \brief (SMC) SMC Cycle Register (CS_number = 0) */
  #define REG_SMC_MODE0                   (0x4008000CU) /**< \brief (SMC) SMC MODE Register (CS_number = 0) */
  #define REG_SMC_SETUP1                  (0x40080010U) /**< \brief (SMC) SMC Setup Register (CS_number = 1) */
  #define REG_SMC_PULSE1                  (0x40080014U) /**< \brief (SMC) SMC Pulse Register (CS_number = 1) */
  #define REG_SMC_CYCLE1                  (0x40080018U) /**< \brief (SMC) SMC Cycle Register (CS_number = 1) */
  #define REG_SMC_MODE1                   (0x4008001CU) /**< \brief (SMC) SMC MODE Register (CS_number = 1) */
  #define REG_SMC_SETUP2                  (0x40080020U) /**< \brief (SMC) SMC Setup Register (CS_number = 2) */
  #define REG_SMC_PULSE2                  (0x40080024U) /**< \brief (SMC) SMC Pulse Register (CS_number = 2) */
  #define REG_SMC_CYCLE2                  (0x40080028U) /**< \brief (SMC) SMC Cycle Register (CS_number = 2) */
  #define REG_SMC_MODE2                   (0x4008002CU) /**< \brief (SMC) SMC MODE Register (CS_number = 2) */
  #define REG_SMC_SETUP3                  (0x40080030U) /**< \brief (SMC) SMC Setup Register (CS_number = 3) */
  #define REG_SMC_PULSE3                  (0x40080034U) /**< \brief (SMC) SMC Pulse Register (CS_number = 3) */
  #define REG_SMC_CYCLE3                  (0x40080038U) /**< \brief (SMC) SMC Cycle Register (CS_number = 3) */
  #define REG_SMC_MODE3                   (0x4008003CU) /**< \brief (SMC) SMC MODE Register (CS_number = 3) */
  #define REG_SMC_OCMS                    (0x40080080U) /**< \brief (SMC) SMC OCMS MODE Register */
  #define REG_SMC_KEY1                    (0x40080084U) /**< \brief (SMC) SMC OCMS KEY1 Register */
  #define REG_SMC_KEY2                    (0x40080088U) /**< \brief (SMC) SMC OCMS KEY2 Register */
  #define REG_SMC_WPMR                    (0x400800E4U) /**< \brief (SMC) SMC Write Protection Mode Register */
  #define REG_SMC_WPSR                    (0x400800E8U) /**< \brief (SMC) SMC Write Protection Status Register */
#else
  #define REG_SMC_SETUP0 (*(__IO uint32_t*)0x40080000U) /**< \brief (SMC) SMC Setup Register (CS_number = 0) */
  #define REG_SMC_PULSE0 (*(__IO uint32_t*)0x40080004U) /**< \brief (SMC) SMC Pulse Register (CS_number = 0) */
  #define REG_SMC_CYCLE0 (*(__IO uint32_t*)0x40080008U) /**< \brief (SMC) SMC Cycle Register (CS_number = 0) */
  #define REG_SMC_MODE0  (*(__IO uint32_t*)0x4008000CU) /**< \brief (SMC) SMC MODE Register (CS_number = 0) */
  #define REG_SMC_SETUP1 (*(__IO uint32_t*)0x40080010U) /**< \brief (SMC) SMC Setup Register (CS_number = 1) */
  #define REG_SMC_PULSE1 (*(__IO uint32_t*)0x40080014U) /**< \brief (SMC) SMC Pulse Register (CS_number = 1) */
  #define REG_SMC_CYCLE1 (*(__IO uint32_t*)0x40080018U) /**< \brief (SMC) SMC Cycle Register (CS_number = 1) */
  #define REG_SMC_MODE1  (*(__IO uint32_t*)0x4008001CU) /**< \brief (SMC) SMC MODE Register (CS_number = 1) */
  #define REG_SMC_SETUP2 (*(__IO uint32_t*)0x40080020U) /**< \brief (SMC) SMC Setup Register (CS_number = 2) */
  #define REG_SMC_PULSE2 (*(__IO uint32_t*)0x40080024U) /**< \brief (SMC) SMC Pulse Register (CS_number = 2) */
  #define REG_SMC_CYCLE2 (*(__IO uint32_t*)0x40080028U) /**< \brief (SMC) SMC Cycle Register (CS_number = 2) */
  #define REG_SMC_MODE2  (*(__IO uint32_t*)0x4008002CU) /**< \brief (SMC) SMC MODE Register (CS_number = 2) */
  #define REG_SMC_SETUP3 (*(__IO uint32_t*)0x40080030U) /**< \brief (SMC) SMC Setup Register (CS_number = 3) */
  #define REG_SMC_PULSE3 (*(__IO uint32_t*)0x40080034U) /**< \brief (SMC) SMC Pulse Register (CS_number = 3) */
  #define REG_SMC_CYCLE3 (*(__IO uint32_t*)0x40080038U) /**< \brief (SMC) SMC Cycle Register (CS_number = 3) */
  #define REG_SMC_MODE3  (*(__IO uint32_t*)0x4008003CU) /**< \brief (SMC) SMC MODE Register (CS_number = 3) */
  #define REG_SMC_OCMS   (*(__IO uint32_t*)0x40080080U) /**< \brief (SMC) SMC OCMS MODE Register */
  #define REG_SMC_KEY1   (*(__O  uint32_t*)0x40080084U) /**< \brief (SMC) SMC OCMS KEY1 Register */
  #define REG_SMC_KEY2   (*(__O  uint32_t*)0x40080088U) /**< \brief (SMC) SMC OCMS KEY2 Register */
  #define REG_SMC_WPMR   (*(__IO uint32_t*)0x400800E4U) /**< \brief (SMC) SMC Write Protection Mode Register */
  #define REG_SMC_WPSR   (*(__I  uint32_t*)0x400800E8U) /**< \brief (SMC) SMC Write Protection Status Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAME70_SMC_INSTANCE_ */
