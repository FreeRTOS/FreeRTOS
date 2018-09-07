/* ---------------------------------------------------------------------------- */
/*                  Atmel Microcontroller Software Support                      */
/*                       SAM Software Package License                           */
/* ---------------------------------------------------------------------------- */
/* Copyright (c) 2014, Atmel Corporation                                        */
/*                                                                              */
/* All rights reserved.                                                         */
/*                                                                              */
/* Redistribution and use in source and binary forms, with or without           */
/* modification, are permitted provided that the following condition is met:    */
/*                                                                              */
/* - Redistributions of source code must retain the above copyright notice,     */
/* this list of conditions and the disclaimer below.                            */
/*                                                                              */
/* Atmel's name may not be used to endorse or promote products derived from     */
/* this software without specific prior written permission.                     */
/*                                                                              */
/* DISCLAIMER:  THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR   */
/* IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF */
/* MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE   */
/* DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,      */
/* INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT */
/* LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,  */
/* OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF    */
/* LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING         */
/* NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, */
/* EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                           */
/* ---------------------------------------------------------------------------- */

#ifndef _SAMV71_SDRAMC_INSTANCE_
#define _SAMV71_SDRAMC_INSTANCE_

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

#endif /* _SAMV71_SDRAMC_INSTANCE_ */
