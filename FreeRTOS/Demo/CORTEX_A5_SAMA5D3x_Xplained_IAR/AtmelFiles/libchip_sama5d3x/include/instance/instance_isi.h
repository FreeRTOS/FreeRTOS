/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2012, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following condition is met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

#ifndef _SAMA5_ISI_INSTANCE_
#define _SAMA5_ISI_INSTANCE_

/* ========== Register definition for ISI peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_ISI_CFG1                (0xF0034000U) /**< \brief (ISI) ISI Configuration 1 Register */
#define REG_ISI_CFG2                (0xF0034004U) /**< \brief (ISI) ISI Configuration 2 Register */
#define REG_ISI_PSIZE               (0xF0034008U) /**< \brief (ISI) ISI Preview Size Register */
#define REG_ISI_PDECF               (0xF003400CU) /**< \brief (ISI) ISI Preview Decimation Factor Register */
#define REG_ISI_Y2R_SET0            (0xF0034010U) /**< \brief (ISI) ISI CSC YCrCb To RGB Set 0 Register */
#define REG_ISI_Y2R_SET1            (0xF0034014U) /**< \brief (ISI) ISI CSC YCrCb To RGB Set 1 Register */
#define REG_ISI_R2Y_SET0            (0xF0034018U) /**< \brief (ISI) ISI CSC RGB To YCrCb Set 0 Register */
#define REG_ISI_R2Y_SET1            (0xF003401CU) /**< \brief (ISI) ISI CSC RGB To YCrCb Set 1 Register */
#define REG_ISI_R2Y_SET2            (0xF0034020U) /**< \brief (ISI) ISI CSC RGB To YCrCb Set 2 Register */
#define REG_ISI_CR                  (0xF0034024U) /**< \brief (ISI) ISI Control Register */
#define REG_ISI_SR                  (0xF0034028U) /**< \brief (ISI) ISI Status Register */
#define REG_ISI_IER                 (0xF003402CU) /**< \brief (ISI) ISI Interrupt Enable Register */
#define REG_ISI_IDR                 (0xF0034030U) /**< \brief (ISI) ISI Interrupt Disable Register */
#define REG_ISI_IMR                 (0xF0034034U) /**< \brief (ISI) ISI Interrupt Mask Register */
#define REG_ISI_DMA_CHER            (0xF0034038U) /**< \brief (ISI) DMA Channel Enable Register */
#define REG_ISI_DMA_CHDR            (0xF003403CU) /**< \brief (ISI) DMA Channel Disable Register */
#define REG_ISI_DMA_CHSR            (0xF0034040U) /**< \brief (ISI) DMA Channel Status Register */
#define REG_ISI_DMA_P_ADDR          (0xF0034044U) /**< \brief (ISI) DMA Preview Base Address Register */
#define REG_ISI_DMA_P_CTRL          (0xF0034048U) /**< \brief (ISI) DMA Preview Control Register */
#define REG_ISI_DMA_P_DSCR          (0xF003404CU) /**< \brief (ISI) DMA Preview Descriptor Address Register */
#define REG_ISI_DMA_C_ADDR          (0xF0034050U) /**< \brief (ISI) DMA Codec Base Address Register */
#define REG_ISI_DMA_C_CTRL          (0xF0034054U) /**< \brief (ISI) DMA Codec Control Register */
#define REG_ISI_DMA_C_DSCR          (0xF0034058U) /**< \brief (ISI) DMA Codec Descriptor Address Register */
#define REG_ISI_WPCR                (0xF00340E4U) /**< \brief (ISI) Write Protection Control Register */
#define REG_ISI_WPSR                (0xF00340E8U) /**< \brief (ISI) Write Protection Status Register */
#else
#define REG_ISI_CFG1       (*(RwReg*)0xF0034000U) /**< \brief (ISI) ISI Configuration 1 Register */
#define REG_ISI_CFG2       (*(RwReg*)0xF0034004U) /**< \brief (ISI) ISI Configuration 2 Register */
#define REG_ISI_PSIZE      (*(RwReg*)0xF0034008U) /**< \brief (ISI) ISI Preview Size Register */
#define REG_ISI_PDECF      (*(RwReg*)0xF003400CU) /**< \brief (ISI) ISI Preview Decimation Factor Register */
#define REG_ISI_Y2R_SET0   (*(RwReg*)0xF0034010U) /**< \brief (ISI) ISI CSC YCrCb To RGB Set 0 Register */
#define REG_ISI_Y2R_SET1   (*(RwReg*)0xF0034014U) /**< \brief (ISI) ISI CSC YCrCb To RGB Set 1 Register */
#define REG_ISI_R2Y_SET0   (*(RwReg*)0xF0034018U) /**< \brief (ISI) ISI CSC RGB To YCrCb Set 0 Register */
#define REG_ISI_R2Y_SET1   (*(RwReg*)0xF003401CU) /**< \brief (ISI) ISI CSC RGB To YCrCb Set 1 Register */
#define REG_ISI_R2Y_SET2   (*(RwReg*)0xF0034020U) /**< \brief (ISI) ISI CSC RGB To YCrCb Set 2 Register */
#define REG_ISI_CR         (*(WoReg*)0xF0034024U) /**< \brief (ISI) ISI Control Register */
#define REG_ISI_SR         (*(RoReg*)0xF0034028U) /**< \brief (ISI) ISI Status Register */
#define REG_ISI_IER        (*(WoReg*)0xF003402CU) /**< \brief (ISI) ISI Interrupt Enable Register */
#define REG_ISI_IDR        (*(WoReg*)0xF0034030U) /**< \brief (ISI) ISI Interrupt Disable Register */
#define REG_ISI_IMR        (*(RoReg*)0xF0034034U) /**< \brief (ISI) ISI Interrupt Mask Register */
#define REG_ISI_DMA_CHER   (*(WoReg*)0xF0034038U) /**< \brief (ISI) DMA Channel Enable Register */
#define REG_ISI_DMA_CHDR   (*(WoReg*)0xF003403CU) /**< \brief (ISI) DMA Channel Disable Register */
#define REG_ISI_DMA_CHSR   (*(RoReg*)0xF0034040U) /**< \brief (ISI) DMA Channel Status Register */
#define REG_ISI_DMA_P_ADDR (*(RwReg*)0xF0034044U) /**< \brief (ISI) DMA Preview Base Address Register */
#define REG_ISI_DMA_P_CTRL (*(RwReg*)0xF0034048U) /**< \brief (ISI) DMA Preview Control Register */
#define REG_ISI_DMA_P_DSCR (*(RwReg*)0xF003404CU) /**< \brief (ISI) DMA Preview Descriptor Address Register */
#define REG_ISI_DMA_C_ADDR (*(RwReg*)0xF0034050U) /**< \brief (ISI) DMA Codec Base Address Register */
#define REG_ISI_DMA_C_CTRL (*(RwReg*)0xF0034054U) /**< \brief (ISI) DMA Codec Control Register */
#define REG_ISI_DMA_C_DSCR (*(RwReg*)0xF0034058U) /**< \brief (ISI) DMA Codec Descriptor Address Register */
#define REG_ISI_WPCR       (*(RwReg*)0xF00340E4U) /**< \brief (ISI) Write Protection Control Register */
#define REG_ISI_WPSR       (*(RoReg*)0xF00340E8U) /**< \brief (ISI) Write Protection Status Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_ISI_INSTANCE_ */
