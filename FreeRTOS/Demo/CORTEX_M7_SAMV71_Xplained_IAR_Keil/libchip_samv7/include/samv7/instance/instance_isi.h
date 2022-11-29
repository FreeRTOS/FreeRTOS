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

#ifndef _SAM_ISI_INSTANCE_
#define _SAM_ISI_INSTANCE_

/* ========== Register definition for ISI peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
  #define REG_ISI_CFG1                        (0x4004C000U) /**< \brief (ISI) ISI Configuration 1 Register */
  #define REG_ISI_CFG2                        (0x4004C004U) /**< \brief (ISI) ISI Configuration 2 Register */
  #define REG_ISI_PSIZE                       (0x4004C008U) /**< \brief (ISI) ISI Preview Size Register */
  #define REG_ISI_PDECF                       (0x4004C00CU) /**< \brief (ISI) ISI Preview Decimation Factor Register */
  #define REG_ISI_Y2R_SET0                    (0x4004C010U) /**< \brief (ISI) ISI Color Space Conversion YCrCb To RGB Set 0 Register */
  #define REG_ISI_Y2R_SET1                    (0x4004C014U) /**< \brief (ISI) ISI Color Space Conversion YCrCb To RGB Set 1 Register */
  #define REG_ISI_R2Y_SET0                    (0x4004C018U) /**< \brief (ISI) ISI Color Space Conversion RGB To YCrCb Set 0 Register */
  #define REG_ISI_R2Y_SET1                    (0x4004C01CU) /**< \brief (ISI) ISI Color Space Conversion RGB To YCrCb Set 1 Register */
  #define REG_ISI_R2Y_SET2                    (0x4004C020U) /**< \brief (ISI) ISI Color Space Conversion RGB To YCrCb Set 2 Register */
  #define REG_ISI_CR                          (0x4004C024U) /**< \brief (ISI) ISI Control Register */
  #define REG_ISI_SR                          (0x4004C028U) /**< \brief (ISI) ISI Status Register */
  #define REG_ISI_IER                         (0x4004C02CU) /**< \brief (ISI) ISI Interrupt Enable Register */
  #define REG_ISI_IDR                         (0x4004C030U) /**< \brief (ISI) ISI Interrupt Disable Register */
  #define REG_ISI_IMR                         (0x4004C034U) /**< \brief (ISI) ISI Interrupt Mask Register */
  #define REG_ISI_DMA_CHER                    (0x4004C038U) /**< \brief (ISI) DMA Channel Enable Register */
  #define REG_ISI_DMA_CHDR                    (0x4004C03CU) /**< \brief (ISI) DMA Channel Disable Register */
  #define REG_ISI_DMA_CHSR                    (0x4004C040U) /**< \brief (ISI) DMA Channel Status Register */
  #define REG_ISI_DMA_P_ADDR                  (0x4004C044U) /**< \brief (ISI) DMA Preview Base Address Register */
  #define REG_ISI_DMA_P_CTRL                  (0x4004C048U) /**< \brief (ISI) DMA Preview Control Register */
  #define REG_ISI_DMA_P_DSCR                  (0x4004C04CU) /**< \brief (ISI) DMA Preview Descriptor Address Register */
  #define REG_ISI_DMA_C_ADDR                  (0x4004C050U) /**< \brief (ISI) DMA Codec Base Address Register */
  #define REG_ISI_DMA_C_CTRL                  (0x4004C054U) /**< \brief (ISI) DMA Codec Control Register */
  #define REG_ISI_DMA_C_DSCR                  (0x4004C058U) /**< \brief (ISI) DMA Codec Descriptor Address Register */
  #define REG_ISI_WPCR                        (0x4004C0E4U) /**< \brief (ISI) Write Protection Control Register */
  #define REG_ISI_WPSR                        (0x4004C0E8U) /**< \brief (ISI) Write Protection Status Register */
  #define REG_ISI_VERSION                     (0x4004C0FCU) /**< \brief (ISI) Version Register */
#else
  #define REG_ISI_CFG1       (*(__IO uint32_t*)0x4004C000U) /**< \brief (ISI) ISI Configuration 1 Register */
  #define REG_ISI_CFG2       (*(__IO uint32_t*)0x4004C004U) /**< \brief (ISI) ISI Configuration 2 Register */
  #define REG_ISI_PSIZE      (*(__IO uint32_t*)0x4004C008U) /**< \brief (ISI) ISI Preview Size Register */
  #define REG_ISI_PDECF      (*(__IO uint32_t*)0x4004C00CU) /**< \brief (ISI) ISI Preview Decimation Factor Register */
  #define REG_ISI_Y2R_SET0   (*(__IO uint32_t*)0x4004C010U) /**< \brief (ISI) ISI Color Space Conversion YCrCb To RGB Set 0 Register */
  #define REG_ISI_Y2R_SET1   (*(__IO uint32_t*)0x4004C014U) /**< \brief (ISI) ISI Color Space Conversion YCrCb To RGB Set 1 Register */
  #define REG_ISI_R2Y_SET0   (*(__IO uint32_t*)0x4004C018U) /**< \brief (ISI) ISI Color Space Conversion RGB To YCrCb Set 0 Register */
  #define REG_ISI_R2Y_SET1   (*(__IO uint32_t*)0x4004C01CU) /**< \brief (ISI) ISI Color Space Conversion RGB To YCrCb Set 1 Register */
  #define REG_ISI_R2Y_SET2   (*(__IO uint32_t*)0x4004C020U) /**< \brief (ISI) ISI Color Space Conversion RGB To YCrCb Set 2 Register */
  #define REG_ISI_CR         (*(__O  uint32_t*)0x4004C024U) /**< \brief (ISI) ISI Control Register */
  #define REG_ISI_SR         (*(__I  uint32_t*)0x4004C028U) /**< \brief (ISI) ISI Status Register */
  #define REG_ISI_IER        (*(__O  uint32_t*)0x4004C02CU) /**< \brief (ISI) ISI Interrupt Enable Register */
  #define REG_ISI_IDR        (*(__O  uint32_t*)0x4004C030U) /**< \brief (ISI) ISI Interrupt Disable Register */
  #define REG_ISI_IMR        (*(__I  uint32_t*)0x4004C034U) /**< \brief (ISI) ISI Interrupt Mask Register */
  #define REG_ISI_DMA_CHER   (*(__O  uint32_t*)0x4004C038U) /**< \brief (ISI) DMA Channel Enable Register */
  #define REG_ISI_DMA_CHDR   (*(__O  uint32_t*)0x4004C03CU) /**< \brief (ISI) DMA Channel Disable Register */
  #define REG_ISI_DMA_CHSR   (*(__I  uint32_t*)0x4004C040U) /**< \brief (ISI) DMA Channel Status Register */
  #define REG_ISI_DMA_P_ADDR (*(__IO uint32_t*)0x4004C044U) /**< \brief (ISI) DMA Preview Base Address Register */
  #define REG_ISI_DMA_P_CTRL (*(__IO uint32_t*)0x4004C048U) /**< \brief (ISI) DMA Preview Control Register */
  #define REG_ISI_DMA_P_DSCR (*(__IO uint32_t*)0x4004C04CU) /**< \brief (ISI) DMA Preview Descriptor Address Register */
  #define REG_ISI_DMA_C_ADDR (*(__IO uint32_t*)0x4004C050U) /**< \brief (ISI) DMA Codec Base Address Register */
  #define REG_ISI_DMA_C_CTRL (*(__IO uint32_t*)0x4004C054U) /**< \brief (ISI) DMA Codec Control Register */
  #define REG_ISI_DMA_C_DSCR (*(__IO uint32_t*)0x4004C058U) /**< \brief (ISI) DMA Codec Descriptor Address Register */
  #define REG_ISI_WPCR       (*(__IO uint32_t*)0x4004C0E4U) /**< \brief (ISI) Write Protection Control Register */
  #define REG_ISI_WPSR       (*(__I  uint32_t*)0x4004C0E8U) /**< \brief (ISI) Write Protection Status Register */
  #define REG_ISI_VERSION    (*(__I  uint32_t*)0x4004C0FCU) /**< \brief (ISI) Version Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAM_ISI_INSTANCE_ */
