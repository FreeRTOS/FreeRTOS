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

#ifndef _SAME70_AFEC1_INSTANCE_
#define _SAME70_AFEC1_INSTANCE_

/* ========== Register definition for AFEC1 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
  #define REG_AFEC1_CR                       (0x40064000U) /**< \brief (AFEC1) AFEC Control Register */
  #define REG_AFEC1_MR                       (0x40064004U) /**< \brief (AFEC1) AFEC Mode Register */
  #define REG_AFEC1_EMR                      (0x40064008U) /**< \brief (AFEC1) AFEC Extended Mode Register */
  #define REG_AFEC1_SEQ1R                    (0x4006400CU) /**< \brief (AFEC1) AFEC Channel Sequence 1 Register */
  #define REG_AFEC1_SEQ2R                    (0x40064010U) /**< \brief (AFEC1) AFEC Channel Sequence 2 Register */
  #define REG_AFEC1_CHER                     (0x40064014U) /**< \brief (AFEC1) AFEC Channel Enable Register */
  #define REG_AFEC1_CHDR                     (0x40064018U) /**< \brief (AFEC1) AFEC Channel Disable Register */
  #define REG_AFEC1_CHSR                     (0x4006401CU) /**< \brief (AFEC1) AFEC Channel Status Register */
  #define REG_AFEC1_LCDR                     (0x40064020U) /**< \brief (AFEC1) AFEC Last Converted Data Register */
  #define REG_AFEC1_IER                      (0x40064024U) /**< \brief (AFEC1) AFEC Interrupt Enable Register */
  #define REG_AFEC1_IDR                      (0x40064028U) /**< \brief (AFEC1) AFEC Interrupt Disable Register */
  #define REG_AFEC1_IMR                      (0x4006402CU) /**< \brief (AFEC1) AFEC Interrupt Mask Register */
  #define REG_AFEC1_ISR                      (0x40064030U) /**< \brief (AFEC1) AFEC Interrupt Status Register */
  #define REG_AFEC1_OVER                     (0x4006404CU) /**< \brief (AFEC1) AFEC Overrun Status Register */
  #define REG_AFEC1_CWR                      (0x40064050U) /**< \brief (AFEC1) AFEC Compare Window Register */
  #define REG_AFEC1_CGR                      (0x40064054U) /**< \brief (AFEC1) AFEC Channel Gain Register */
  #define REG_AFEC1_DIFFR                    (0x40064060U) /**< \brief (AFEC1) AFEC Channel Differential Register */
  #define REG_AFEC1_CSELR                    (0x40064064U) /**< \brief (AFEC1) AFEC Channel Selection Register */
  #define REG_AFEC1_CDR                      (0x40064068U) /**< \brief (AFEC1) AFEC Channel Data Register */
  #define REG_AFEC1_COCR                     (0x4006406CU) /**< \brief (AFEC1) AFEC Channel Offset Compensation Register */
  #define REG_AFEC1_TEMPMR                   (0x40064070U) /**< \brief (AFEC1) AFEC Temperature Sensor Mode Register */
  #define REG_AFEC1_TEMPCWR                  (0x40064074U) /**< \brief (AFEC1) AFEC Temperature Compare Window Register */
  #define REG_AFEC1_ACR                      (0x40064094U) /**< \brief (AFEC1) AFEC Analog Control Register */
  #define REG_AFEC1_SHMR                     (0x400640A0U) /**< \brief (AFEC1) AFEC Sample & Hold Mode Register */
  #define REG_AFEC1_COSR                     (0x400640D0U) /**< \brief (AFEC1) AFEC Correction Select Register */
  #define REG_AFEC1_CVR                      (0x400640D4U) /**< \brief (AFEC1) AFEC Correction Values Register */
  #define REG_AFEC1_CECR                     (0x400640D8U) /**< \brief (AFEC1) AFEC Channel Error Correction Register */
  #define REG_AFEC1_WPMR                     (0x400640E4U) /**< \brief (AFEC1) AFEC Write Protection Mode Register */
  #define REG_AFEC1_WPSR                     (0x400640E8U) /**< \brief (AFEC1) AFEC Write Protection Status Register */
#else
  #define REG_AFEC1_CR      (*(__O  uint32_t*)0x40064000U) /**< \brief (AFEC1) AFEC Control Register */
  #define REG_AFEC1_MR      (*(__IO uint32_t*)0x40064004U) /**< \brief (AFEC1) AFEC Mode Register */
  #define REG_AFEC1_EMR     (*(__IO uint32_t*)0x40064008U) /**< \brief (AFEC1) AFEC Extended Mode Register */
  #define REG_AFEC1_SEQ1R   (*(__IO uint32_t*)0x4006400CU) /**< \brief (AFEC1) AFEC Channel Sequence 1 Register */
  #define REG_AFEC1_SEQ2R   (*(__IO uint32_t*)0x40064010U) /**< \brief (AFEC1) AFEC Channel Sequence 2 Register */
  #define REG_AFEC1_CHER    (*(__O  uint32_t*)0x40064014U) /**< \brief (AFEC1) AFEC Channel Enable Register */
  #define REG_AFEC1_CHDR    (*(__O  uint32_t*)0x40064018U) /**< \brief (AFEC1) AFEC Channel Disable Register */
  #define REG_AFEC1_CHSR    (*(__I  uint32_t*)0x4006401CU) /**< \brief (AFEC1) AFEC Channel Status Register */
  #define REG_AFEC1_LCDR    (*(__I  uint32_t*)0x40064020U) /**< \brief (AFEC1) AFEC Last Converted Data Register */
  #define REG_AFEC1_IER     (*(__O  uint32_t*)0x40064024U) /**< \brief (AFEC1) AFEC Interrupt Enable Register */
  #define REG_AFEC1_IDR     (*(__O  uint32_t*)0x40064028U) /**< \brief (AFEC1) AFEC Interrupt Disable Register */
  #define REG_AFEC1_IMR     (*(__I  uint32_t*)0x4006402CU) /**< \brief (AFEC1) AFEC Interrupt Mask Register */
  #define REG_AFEC1_ISR     (*(__I  uint32_t*)0x40064030U) /**< \brief (AFEC1) AFEC Interrupt Status Register */
  #define REG_AFEC1_OVER    (*(__I  uint32_t*)0x4006404CU) /**< \brief (AFEC1) AFEC Overrun Status Register */
  #define REG_AFEC1_CWR     (*(__IO uint32_t*)0x40064050U) /**< \brief (AFEC1) AFEC Compare Window Register */
  #define REG_AFEC1_CGR     (*(__IO uint32_t*)0x40064054U) /**< \brief (AFEC1) AFEC Channel Gain Register */
  #define REG_AFEC1_DIFFR   (*(__IO uint32_t*)0x40064060U) /**< \brief (AFEC1) AFEC Channel Differential Register */
  #define REG_AFEC1_CSELR   (*(__IO uint32_t*)0x40064064U) /**< \brief (AFEC1) AFEC Channel Selection Register */
  #define REG_AFEC1_CDR     (*(__I  uint32_t*)0x40064068U) /**< \brief (AFEC1) AFEC Channel Data Register */
  #define REG_AFEC1_COCR    (*(__IO uint32_t*)0x4006406CU) /**< \brief (AFEC1) AFEC Channel Offset Compensation Register */
  #define REG_AFEC1_TEMPMR  (*(__IO uint32_t*)0x40064070U) /**< \brief (AFEC1) AFEC Temperature Sensor Mode Register */
  #define REG_AFEC1_TEMPCWR (*(__IO uint32_t*)0x40064074U) /**< \brief (AFEC1) AFEC Temperature Compare Window Register */
  #define REG_AFEC1_ACR     (*(__IO uint32_t*)0x40064094U) /**< \brief (AFEC1) AFEC Analog Control Register */
  #define REG_AFEC1_SHMR    (*(__IO uint32_t*)0x400640A0U) /**< \brief (AFEC1) AFEC Sample & Hold Mode Register */
  #define REG_AFEC1_COSR    (*(__IO uint32_t*)0x400640D0U) /**< \brief (AFEC1) AFEC Correction Select Register */
  #define REG_AFEC1_CVR     (*(__IO uint32_t*)0x400640D4U) /**< \brief (AFEC1) AFEC Correction Values Register */
  #define REG_AFEC1_CECR    (*(__IO uint32_t*)0x400640D8U) /**< \brief (AFEC1) AFEC Channel Error Correction Register */
  #define REG_AFEC1_WPMR    (*(__IO uint32_t*)0x400640E4U) /**< \brief (AFEC1) AFEC Write Protection Mode Register */
  #define REG_AFEC1_WPSR    (*(__I  uint32_t*)0x400640E8U) /**< \brief (AFEC1) AFEC Write Protection Status Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAME70_AFEC1_INSTANCE_ */
