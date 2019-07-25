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

#ifndef _SAME70_SDRAMC_INSTANCE_
#define _SAME70_SDRAMC_INSTANCE_

/* ========== Register definition for SDRAMC peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
  #define REG_SDRAMC_MR                         (0x40084000U) /**< \brief (SDRAMC) SDRAMC Mode Register */
  #define REG_SDRAMC_TR                         (0x40084004U) /**< \brief (SDRAMC) SDRAMC Refresh Timer Register */
  #define REG_SDRAMC_CR                         (0x40084008U) /**< \brief (SDRAMC) SDRAMC Configuration Register */
  #define REG_SDRAMC_LPR                        (0x40084010U) /**< \brief (SDRAMC) SDRAMC Low Power Register */
  #define REG_SDRAMC_IER                        (0x40084014U) /**< \brief (SDRAMC) SDRAMC Interrupt Enable Register */
  #define REG_SDRAMC_IDR                        (0x40084018U) /**< \brief (SDRAMC) SDRAMC Interrupt Disable Register */
  #define REG_SDRAMC_IMR                        (0x4008401CU) /**< \brief (SDRAMC) SDRAMC Interrupt Mask Register */
  #define REG_SDRAMC_ISR                        (0x40084020U) /**< \brief (SDRAMC) SDRAMC Interrupt Status Register */
  #define REG_SDRAMC_MDR                        (0x40084024U) /**< \brief (SDRAMC) SDRAMC Memory Device Register */
  #define REG_SDRAMC_CFR1                       (0x40084028U) /**< \brief (SDRAMC) SDRAMC Configuration Register 1 */
  #define REG_SDRAMC_OCMS                       (0x4008402CU) /**< \brief (SDRAMC) SDRAMC OCMS Register */
  #define REG_SDRAMC_OCMS_KEY1                  (0x40084030U) /**< \brief (SDRAMC) SDRAMC OCMS KEY1 Register */
  #define REG_SDRAMC_OCMS_KEY2                  (0x40084034U) /**< \brief (SDRAMC) SDRAMC OCMS KEY2 Register */
#else
  #define REG_SDRAMC_MR        (*(__IO uint32_t*)0x40084000U) /**< \brief (SDRAMC) SDRAMC Mode Register */
  #define REG_SDRAMC_TR        (*(__IO uint32_t*)0x40084004U) /**< \brief (SDRAMC) SDRAMC Refresh Timer Register */
  #define REG_SDRAMC_CR        (*(__IO uint32_t*)0x40084008U) /**< \brief (SDRAMC) SDRAMC Configuration Register */
  #define REG_SDRAMC_LPR       (*(__IO uint32_t*)0x40084010U) /**< \brief (SDRAMC) SDRAMC Low Power Register */
  #define REG_SDRAMC_IER       (*(__O  uint32_t*)0x40084014U) /**< \brief (SDRAMC) SDRAMC Interrupt Enable Register */
  #define REG_SDRAMC_IDR       (*(__O  uint32_t*)0x40084018U) /**< \brief (SDRAMC) SDRAMC Interrupt Disable Register */
  #define REG_SDRAMC_IMR       (*(__I  uint32_t*)0x4008401CU) /**< \brief (SDRAMC) SDRAMC Interrupt Mask Register */
  #define REG_SDRAMC_ISR       (*(__I  uint32_t*)0x40084020U) /**< \brief (SDRAMC) SDRAMC Interrupt Status Register */
  #define REG_SDRAMC_MDR       (*(__IO uint32_t*)0x40084024U) /**< \brief (SDRAMC) SDRAMC Memory Device Register */
  #define REG_SDRAMC_CFR1      (*(__IO uint32_t*)0x40084028U) /**< \brief (SDRAMC) SDRAMC Configuration Register 1 */
  #define REG_SDRAMC_OCMS      (*(__IO uint32_t*)0x4008402CU) /**< \brief (SDRAMC) SDRAMC OCMS Register */
  #define REG_SDRAMC_OCMS_KEY1 (*(__O  uint32_t*)0x40084030U) /**< \brief (SDRAMC) SDRAMC OCMS KEY1 Register */
  #define REG_SDRAMC_OCMS_KEY2 (*(__O  uint32_t*)0x40084034U) /**< \brief (SDRAMC) SDRAMC OCMS KEY2 Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAME70_SDRAMC_INSTANCE_ */
