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

#ifndef _SAME70_TRNG_INSTANCE_
#define _SAME70_TRNG_INSTANCE_

/* ========== Register definition for TRNG peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
  #define REG_TRNG_CR                    (0x40070000U) /**< \brief (TRNG) Control Register */
  #define REG_TRNG_IER                   (0x40070010U) /**< \brief (TRNG) Interrupt Enable Register */
  #define REG_TRNG_IDR                   (0x40070014U) /**< \brief (TRNG) Interrupt Disable Register */
  #define REG_TRNG_IMR                   (0x40070018U) /**< \brief (TRNG) Interrupt Mask Register */
  #define REG_TRNG_ISR                   (0x4007001CU) /**< \brief (TRNG) Interrupt Status Register */
  #define REG_TRNG_ODATA                 (0x40070050U) /**< \brief (TRNG) Output Data Register */
#else
  #define REG_TRNG_CR    (*(__O uint32_t*)0x40070000U) /**< \brief (TRNG) Control Register */
  #define REG_TRNG_IER   (*(__O uint32_t*)0x40070010U) /**< \brief (TRNG) Interrupt Enable Register */
  #define REG_TRNG_IDR   (*(__O uint32_t*)0x40070014U) /**< \brief (TRNG) Interrupt Disable Register */
  #define REG_TRNG_IMR   (*(__I uint32_t*)0x40070018U) /**< \brief (TRNG) Interrupt Mask Register */
  #define REG_TRNG_ISR   (*(__I uint32_t*)0x4007001CU) /**< \brief (TRNG) Interrupt Status Register */
  #define REG_TRNG_ODATA (*(__I uint32_t*)0x40070050U) /**< \brief (TRNG) Output Data Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAME70_TRNG_INSTANCE_ */
