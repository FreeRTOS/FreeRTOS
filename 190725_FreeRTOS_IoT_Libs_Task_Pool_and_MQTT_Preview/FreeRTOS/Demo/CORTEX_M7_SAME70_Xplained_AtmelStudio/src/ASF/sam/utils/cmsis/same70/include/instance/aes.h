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

#ifndef _SAME70_AES_INSTANCE_
#define _SAME70_AES_INSTANCE_

/* ========== Register definition for AES peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
  #define REG_AES_CR                       (0x4006C000U) /**< \brief (AES) Control Register */
  #define REG_AES_MR                       (0x4006C004U) /**< \brief (AES) Mode Register */
  #define REG_AES_IER                      (0x4006C010U) /**< \brief (AES) Interrupt Enable Register */
  #define REG_AES_IDR                      (0x4006C014U) /**< \brief (AES) Interrupt Disable Register */
  #define REG_AES_IMR                      (0x4006C018U) /**< \brief (AES) Interrupt Mask Register */
  #define REG_AES_ISR                      (0x4006C01CU) /**< \brief (AES) Interrupt Status Register */
  #define REG_AES_KEYWR                    (0x4006C020U) /**< \brief (AES) Key Word Register */
  #define REG_AES_IDATAR                   (0x4006C040U) /**< \brief (AES) Input Data Register */
  #define REG_AES_ODATAR                   (0x4006C050U) /**< \brief (AES) Output Data Register */
  #define REG_AES_IVR                      (0x4006C060U) /**< \brief (AES) Initialization Vector Register */
  #define REG_AES_AADLENR                  (0x4006C070U) /**< \brief (AES) Additional Authenticated Data Length Register */
  #define REG_AES_CLENR                    (0x4006C074U) /**< \brief (AES) Plaintext/Ciphertext Length Register */
  #define REG_AES_GHASHR                   (0x4006C078U) /**< \brief (AES) GCM Intermediate Hash Word Register */
  #define REG_AES_TAGR                     (0x4006C088U) /**< \brief (AES) GCM Authentication Tag Word Register */
  #define REG_AES_CTRR                     (0x4006C098U) /**< \brief (AES) GCM Encryption Counter Value Register */
  #define REG_AES_GCMHR                    (0x4006C09CU) /**< \brief (AES) GCM H Word Register */
#else
  #define REG_AES_CR      (*(__O  uint32_t*)0x4006C000U) /**< \brief (AES) Control Register */
  #define REG_AES_MR      (*(__IO uint32_t*)0x4006C004U) /**< \brief (AES) Mode Register */
  #define REG_AES_IER     (*(__O  uint32_t*)0x4006C010U) /**< \brief (AES) Interrupt Enable Register */
  #define REG_AES_IDR     (*(__O  uint32_t*)0x4006C014U) /**< \brief (AES) Interrupt Disable Register */
  #define REG_AES_IMR     (*(__I  uint32_t*)0x4006C018U) /**< \brief (AES) Interrupt Mask Register */
  #define REG_AES_ISR     (*(__I  uint32_t*)0x4006C01CU) /**< \brief (AES) Interrupt Status Register */
  #define REG_AES_KEYWR   (*(__O  uint32_t*)0x4006C020U) /**< \brief (AES) Key Word Register */
  #define REG_AES_IDATAR  (*(__O  uint32_t*)0x4006C040U) /**< \brief (AES) Input Data Register */
  #define REG_AES_ODATAR  (*(__I  uint32_t*)0x4006C050U) /**< \brief (AES) Output Data Register */
  #define REG_AES_IVR     (*(__O  uint32_t*)0x4006C060U) /**< \brief (AES) Initialization Vector Register */
  #define REG_AES_AADLENR (*(__IO uint32_t*)0x4006C070U) /**< \brief (AES) Additional Authenticated Data Length Register */
  #define REG_AES_CLENR   (*(__IO uint32_t*)0x4006C074U) /**< \brief (AES) Plaintext/Ciphertext Length Register */
  #define REG_AES_GHASHR  (*(__IO uint32_t*)0x4006C078U) /**< \brief (AES) GCM Intermediate Hash Word Register */
  #define REG_AES_TAGR    (*(__I  uint32_t*)0x4006C088U) /**< \brief (AES) GCM Authentication Tag Word Register */
  #define REG_AES_CTRR    (*(__I  uint32_t*)0x4006C098U) /**< \brief (AES) GCM Encryption Counter Value Register */
  #define REG_AES_GCMHR   (*(__IO uint32_t*)0x4006C09CU) /**< \brief (AES) GCM H Word Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAME70_AES_INSTANCE_ */
