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

#ifndef _SAMA5_ISI_COMPONENT_
#define _SAMA5_ISI_COMPONENT_

/* ============================================================================= */
/**  SOFTWARE API DEFINITION FOR Image Sensor Interface */
/* ============================================================================= */
/** \addtogroup SAMA5_ISI Image Sensor Interface */
/*@{*/

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
/** \brief Isi hardware registers */
typedef struct {
  RwReg ISI_CFG1;       /**< \brief (Isi Offset: 0x00) ISI Configuration 1 Register */
  RwReg ISI_CFG2;       /**< \brief (Isi Offset: 0x04) ISI Configuration 2 Register */
  RwReg ISI_PSIZE;      /**< \brief (Isi Offset: 0x08) ISI Preview Size Register */
  RwReg ISI_PDECF;      /**< \brief (Isi Offset: 0x0C) ISI Preview Decimation Factor Register */
  RwReg ISI_Y2R_SET0;   /**< \brief (Isi Offset: 0x10) ISI CSC YCrCb To RGB Set 0 Register */
  RwReg ISI_Y2R_SET1;   /**< \brief (Isi Offset: 0x14) ISI CSC YCrCb To RGB Set 1 Register */
  RwReg ISI_R2Y_SET0;   /**< \brief (Isi Offset: 0x18) ISI CSC RGB To YCrCb Set 0 Register */
  RwReg ISI_R2Y_SET1;   /**< \brief (Isi Offset: 0x1C) ISI CSC RGB To YCrCb Set 1 Register */
  RwReg ISI_R2Y_SET2;   /**< \brief (Isi Offset: 0x20) ISI CSC RGB To YCrCb Set 2 Register */
  WoReg ISI_CR;         /**< \brief (Isi Offset: 0x24) ISI Control Register */
  RoReg ISI_SR;         /**< \brief (Isi Offset: 0x28) ISI Status Register */
  WoReg ISI_IER;        /**< \brief (Isi Offset: 0x2C) ISI Interrupt Enable Register */
  WoReg ISI_IDR;        /**< \brief (Isi Offset: 0x30) ISI Interrupt Disable Register */
  RoReg ISI_IMR;        /**< \brief (Isi Offset: 0x34) ISI Interrupt Mask Register */
  WoReg ISI_DMA_CHER;   /**< \brief (Isi Offset: 0x38) DMA Channel Enable Register */
  WoReg ISI_DMA_CHDR;   /**< \brief (Isi Offset: 0x3C) DMA Channel Disable Register */
  RoReg ISI_DMA_CHSR;   /**< \brief (Isi Offset: 0x40) DMA Channel Status Register */
  RwReg ISI_DMA_P_ADDR; /**< \brief (Isi Offset: 0x44) DMA Preview Base Address Register */
  RwReg ISI_DMA_P_CTRL; /**< \brief (Isi Offset: 0x48) DMA Preview Control Register */
  RwReg ISI_DMA_P_DSCR; /**< \brief (Isi Offset: 0x4C) DMA Preview Descriptor Address Register */
  RwReg ISI_DMA_C_ADDR; /**< \brief (Isi Offset: 0x50) DMA Codec Base Address Register */
  RwReg ISI_DMA_C_CTRL; /**< \brief (Isi Offset: 0x54) DMA Codec Control Register */
  RwReg ISI_DMA_C_DSCR; /**< \brief (Isi Offset: 0x58) DMA Codec Descriptor Address Register */
  RoReg Reserved1[34];
  RwReg ISI_WPCR;       /**< \brief (Isi Offset: 0xE4) Write Protection Control Register */
  RoReg ISI_WPSR;       /**< \brief (Isi Offset: 0xE8) Write Protection Status Register */
} Isi;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */
/* -------- ISI_CFG1 : (ISI Offset: 0x00) ISI Configuration 1 Register -------- */
#define ISI_CFG1_HSYNC_POL (0x1u << 2) /**< \brief (ISI_CFG1) Horizontal Synchronization Polarity */
#define ISI_CFG1_VSYNC_POL (0x1u << 3) /**< \brief (ISI_CFG1) Vertical Synchronization Polarity */
#define ISI_CFG1_PIXCLK_POL (0x1u << 4) /**< \brief (ISI_CFG1) Pixel Clock Polarity */
#define ISI_CFG1_EMB_SYNC (0x1u << 6) /**< \brief (ISI_CFG1) Embedded Synchronization */
#define ISI_CFG1_CRC_SYNC (0x1u << 7) /**< \brief (ISI_CFG1) Embedded Synchronization Correction */
#define ISI_CFG1_FRATE_Pos 8
#define ISI_CFG1_FRATE_Msk (0x7u << ISI_CFG1_FRATE_Pos) /**< \brief (ISI_CFG1) Frame Rate [0..7] */
#define ISI_CFG1_FRATE(value) ((ISI_CFG1_FRATE_Msk & ((value) << ISI_CFG1_FRATE_Pos)))
#define ISI_CFG1_DISCR (0x1u << 11) /**< \brief (ISI_CFG1) Disable Codec Request */
#define ISI_CFG1_FULL (0x1u << 12) /**< \brief (ISI_CFG1) Full Mode is Allowed */
#define ISI_CFG1_THMASK_Pos 13
#define ISI_CFG1_THMASK_Msk (0x3u << ISI_CFG1_THMASK_Pos) /**< \brief (ISI_CFG1) Threshold Mask */
#define   ISI_CFG1_THMASK_BEATS_4 (0x0u << 13) /**< \brief (ISI_CFG1) Only 4 beats AHB burst allowed */
#define   ISI_CFG1_THMASK_BEATS_8 (0x1u << 13) /**< \brief (ISI_CFG1) Only 4 and 8 beats AHB burst allowed */
#define   ISI_CFG1_THMASK_BEATS_16 (0x2u << 13) /**< \brief (ISI_CFG1) 4, 8 and 16 beats AHB burst allowed */
#define ISI_CFG1_SLD_Pos 16
#define ISI_CFG1_SLD_Msk (0xffu << ISI_CFG1_SLD_Pos) /**< \brief (ISI_CFG1) Start of Line Delay */
#define ISI_CFG1_SLD(value) ((ISI_CFG1_SLD_Msk & ((value) << ISI_CFG1_SLD_Pos)))
#define ISI_CFG1_SFD_Pos 24
#define ISI_CFG1_SFD_Msk (0xffu << ISI_CFG1_SFD_Pos) /**< \brief (ISI_CFG1) Start of Frame Delay */
#define ISI_CFG1_SFD(value) ((ISI_CFG1_SFD_Msk & ((value) << ISI_CFG1_SFD_Pos)))
/* -------- ISI_CFG2 : (ISI Offset: 0x04) ISI Configuration 2 Register -------- */
#define ISI_CFG2_IM_VSIZE_Pos 0
#define ISI_CFG2_IM_VSIZE_Msk (0x7ffu << ISI_CFG2_IM_VSIZE_Pos) /**< \brief (ISI_CFG2) Vertical Size of the Image Sensor [0..2047]: */
#define ISI_CFG2_IM_VSIZE(value) ((ISI_CFG2_IM_VSIZE_Msk & ((value) << ISI_CFG2_IM_VSIZE_Pos)))
#define ISI_CFG2_GS_MODE (0x1u << 11) /**< \brief (ISI_CFG2)  */
#define ISI_CFG2_RGB_MODE (0x1u << 12) /**< \brief (ISI_CFG2) RGB Input Mode: */
#define ISI_CFG2_GRAYSCALE (0x1u << 13) /**< \brief (ISI_CFG2)  */
#define ISI_CFG2_RGB_SWAP (0x1u << 14) /**< \brief (ISI_CFG2)  */
#define ISI_CFG2_COL_SPACE (0x1u << 15) /**< \brief (ISI_CFG2) Color Space for the Image Data */
#define ISI_CFG2_IM_HSIZE_Pos 16
#define ISI_CFG2_IM_HSIZE_Msk (0x7ffu << ISI_CFG2_IM_HSIZE_Pos) /**< \brief (ISI_CFG2) Horizontal Size of the Image Sensor [0..2047] */
#define ISI_CFG2_IM_HSIZE(value) ((ISI_CFG2_IM_HSIZE_Msk & ((value) << ISI_CFG2_IM_HSIZE_Pos)))
#define ISI_CFG2_YCC_SWAP_Pos 28
#define ISI_CFG2_YCC_SWAP_Msk (0x3u << ISI_CFG2_YCC_SWAP_Pos) /**< \brief (ISI_CFG2) Defines the YCC Image Data */
#define ISI_CFG2_YCC_SWAP(value) ((ISI_CFG2_YCC_SWAP_Msk & ((value) << ISI_CFG2_YCC_SWAP_Pos)))
#define ISI_CFG2_RGB_CFG_Pos 30
#define ISI_CFG2_RGB_CFG_Msk (0x3u << ISI_CFG2_RGB_CFG_Pos) /**< \brief (ISI_CFG2) Defines RGB Pattern when RGB_MODE is set to 1 */
#define ISI_CFG2_RGB_CFG(value) ((ISI_CFG2_RGB_CFG_Msk & ((value) << ISI_CFG2_RGB_CFG_Pos)))
/* -------- ISI_PSIZE : (ISI Offset: 0x08) ISI Preview Size Register -------- */
#define ISI_PSIZE_PREV_VSIZE_Pos 0
#define ISI_PSIZE_PREV_VSIZE_Msk (0x3ffu << ISI_PSIZE_PREV_VSIZE_Pos) /**< \brief (ISI_PSIZE) Vertical Size for the Preview Path */
#define ISI_PSIZE_PREV_VSIZE(value) ((ISI_PSIZE_PREV_VSIZE_Msk & ((value) << ISI_PSIZE_PREV_VSIZE_Pos)))
#define ISI_PSIZE_PREV_HSIZE_Pos 16
#define ISI_PSIZE_PREV_HSIZE_Msk (0x3ffu << ISI_PSIZE_PREV_HSIZE_Pos) /**< \brief (ISI_PSIZE) Horizontal Size for the Preview Path */
#define ISI_PSIZE_PREV_HSIZE(value) ((ISI_PSIZE_PREV_HSIZE_Msk & ((value) << ISI_PSIZE_PREV_HSIZE_Pos)))
/* -------- ISI_PDECF : (ISI Offset: 0x0C) ISI Preview Decimation Factor Register -------- */
#define ISI_PDECF_DEC_FACTOR_Pos 0
#define ISI_PDECF_DEC_FACTOR_Msk (0xffu << ISI_PDECF_DEC_FACTOR_Pos) /**< \brief (ISI_PDECF) Decimation Factor */
#define ISI_PDECF_DEC_FACTOR(value) ((ISI_PDECF_DEC_FACTOR_Msk & ((value) << ISI_PDECF_DEC_FACTOR_Pos)))
/* -------- ISI_Y2R_SET0 : (ISI Offset: 0x10) ISI CSC YCrCb To RGB Set 0 Register -------- */
#define ISI_Y2R_SET0_C0_Pos 0
#define ISI_Y2R_SET0_C0_Msk (0xffu << ISI_Y2R_SET0_C0_Pos) /**< \brief (ISI_Y2R_SET0) Color Space Conversion Matrix Coefficient C0 */
#define ISI_Y2R_SET0_C0(value) ((ISI_Y2R_SET0_C0_Msk & ((value) << ISI_Y2R_SET0_C0_Pos)))
#define ISI_Y2R_SET0_C1_Pos 8
#define ISI_Y2R_SET0_C1_Msk (0xffu << ISI_Y2R_SET0_C1_Pos) /**< \brief (ISI_Y2R_SET0) Color Space Conversion Matrix Coefficient C1 */
#define ISI_Y2R_SET0_C1(value) ((ISI_Y2R_SET0_C1_Msk & ((value) << ISI_Y2R_SET0_C1_Pos)))
#define ISI_Y2R_SET0_C2_Pos 16
#define ISI_Y2R_SET0_C2_Msk (0xffu << ISI_Y2R_SET0_C2_Pos) /**< \brief (ISI_Y2R_SET0) Color Space Conversion Matrix Coefficient C2 */
#define ISI_Y2R_SET0_C2(value) ((ISI_Y2R_SET0_C2_Msk & ((value) << ISI_Y2R_SET0_C2_Pos)))
#define ISI_Y2R_SET0_C3_Pos 24
#define ISI_Y2R_SET0_C3_Msk (0xffu << ISI_Y2R_SET0_C3_Pos) /**< \brief (ISI_Y2R_SET0) Color Space Conversion Matrix Coefficient C3 */
#define ISI_Y2R_SET0_C3(value) ((ISI_Y2R_SET0_C3_Msk & ((value) << ISI_Y2R_SET0_C3_Pos)))
/* -------- ISI_Y2R_SET1 : (ISI Offset: 0x14) ISI CSC YCrCb To RGB Set 1 Register -------- */
#define ISI_Y2R_SET1_C4_Pos 0
#define ISI_Y2R_SET1_C4_Msk (0x1ffu << ISI_Y2R_SET1_C4_Pos) /**< \brief (ISI_Y2R_SET1) Color Space Conversion Matrix Coefficient C4 */
#define ISI_Y2R_SET1_C4(value) ((ISI_Y2R_SET1_C4_Msk & ((value) << ISI_Y2R_SET1_C4_Pos)))
#define ISI_Y2R_SET1_Yoff (0x1u << 12) /**< \brief (ISI_Y2R_SET1) Color Space Conversion Luminance Default Offset */
#define ISI_Y2R_SET1_Croff (0x1u << 13) /**< \brief (ISI_Y2R_SET1) Color Space Conversion Red Chrominance Default Offset */
#define ISI_Y2R_SET1_Cboff (0x1u << 14) /**< \brief (ISI_Y2R_SET1) Color Space Conversion Blue Chrominance Default Offset */
/* -------- ISI_R2Y_SET0 : (ISI Offset: 0x18) ISI CSC RGB To YCrCb Set 0 Register -------- */
#define ISI_R2Y_SET0_C0_Pos 0
#define ISI_R2Y_SET0_C0_Msk (0x7fu << ISI_R2Y_SET0_C0_Pos) /**< \brief (ISI_R2Y_SET0) Color Space Conversion Matrix Coefficient C0 */
#define ISI_R2Y_SET0_C0(value) ((ISI_R2Y_SET0_C0_Msk & ((value) << ISI_R2Y_SET0_C0_Pos)))
#define ISI_R2Y_SET0_C1_Pos 8
#define ISI_R2Y_SET0_C1_Msk (0x7fu << ISI_R2Y_SET0_C1_Pos) /**< \brief (ISI_R2Y_SET0) Color Space Conversion Matrix Coefficient C1 */
#define ISI_R2Y_SET0_C1(value) ((ISI_R2Y_SET0_C1_Msk & ((value) << ISI_R2Y_SET0_C1_Pos)))
#define ISI_R2Y_SET0_C2_Pos 16
#define ISI_R2Y_SET0_C2_Msk (0x7fu << ISI_R2Y_SET0_C2_Pos) /**< \brief (ISI_R2Y_SET0) Color Space Conversion Matrix Coefficient C2 */
#define ISI_R2Y_SET0_C2(value) ((ISI_R2Y_SET0_C2_Msk & ((value) << ISI_R2Y_SET0_C2_Pos)))
#define ISI_R2Y_SET0_Roff (0x1u << 24) /**< \brief (ISI_R2Y_SET0) Color Space Conversion Red Component Offset */
/* -------- ISI_R2Y_SET1 : (ISI Offset: 0x1C) ISI CSC RGB To YCrCb Set 1 Register -------- */
#define ISI_R2Y_SET1_C3_Pos 0
#define ISI_R2Y_SET1_C3_Msk (0x7fu << ISI_R2Y_SET1_C3_Pos) /**< \brief (ISI_R2Y_SET1) Color Space Conversion Matrix Coefficient C3 */
#define ISI_R2Y_SET1_C3(value) ((ISI_R2Y_SET1_C3_Msk & ((value) << ISI_R2Y_SET1_C3_Pos)))
#define ISI_R2Y_SET1_C4_Pos 8
#define ISI_R2Y_SET1_C4_Msk (0x7fu << ISI_R2Y_SET1_C4_Pos) /**< \brief (ISI_R2Y_SET1) Color Space Conversion Matrix Coefficient C4 */
#define ISI_R2Y_SET1_C4(value) ((ISI_R2Y_SET1_C4_Msk & ((value) << ISI_R2Y_SET1_C4_Pos)))
#define ISI_R2Y_SET1_C5_Pos 16
#define ISI_R2Y_SET1_C5_Msk (0x7fu << ISI_R2Y_SET1_C5_Pos) /**< \brief (ISI_R2Y_SET1) Color Space Conversion Matrix Coefficient C5 */
#define ISI_R2Y_SET1_C5(value) ((ISI_R2Y_SET1_C5_Msk & ((value) << ISI_R2Y_SET1_C5_Pos)))
#define ISI_R2Y_SET1_Goff (0x1u << 24) /**< \brief (ISI_R2Y_SET1) Color Space Conversion Green Component Offset */
/* -------- ISI_R2Y_SET2 : (ISI Offset: 0x20) ISI CSC RGB To YCrCb Set 2 Register -------- */
#define ISI_R2Y_SET2_C6_Pos 0
#define ISI_R2Y_SET2_C6_Msk (0x7fu << ISI_R2Y_SET2_C6_Pos) /**< \brief (ISI_R2Y_SET2) Color Space Conversion Matrix Coefficient C6 */
#define ISI_R2Y_SET2_C6(value) ((ISI_R2Y_SET2_C6_Msk & ((value) << ISI_R2Y_SET2_C6_Pos)))
#define ISI_R2Y_SET2_C7_Pos 8
#define ISI_R2Y_SET2_C7_Msk (0x7fu << ISI_R2Y_SET2_C7_Pos) /**< \brief (ISI_R2Y_SET2) Color Space Conversion Matrix Coefficient C7 */
#define ISI_R2Y_SET2_C7(value) ((ISI_R2Y_SET2_C7_Msk & ((value) << ISI_R2Y_SET2_C7_Pos)))
#define ISI_R2Y_SET2_C8_Pos 16
#define ISI_R2Y_SET2_C8_Msk (0x7fu << ISI_R2Y_SET2_C8_Pos) /**< \brief (ISI_R2Y_SET2) Color Space Conversion Matrix Coefficient C8 */
#define ISI_R2Y_SET2_C8(value) ((ISI_R2Y_SET2_C8_Msk & ((value) << ISI_R2Y_SET2_C8_Pos)))
#define ISI_R2Y_SET2_Boff (0x1u << 24) /**< \brief (ISI_R2Y_SET2) Color Space Conversion Blue Component Offset */
/* -------- ISI_CR : (ISI Offset: 0x24) ISI Control Register -------- */
#define ISI_CR_ISI_EN (0x1u << 0) /**< \brief (ISI_CR) ISI Module Enable Request */
#define ISI_CR_ISI_DIS (0x1u << 1) /**< \brief (ISI_CR) ISI Module Disable Request */
#define ISI_CR_ISI_SRST (0x1u << 2) /**< \brief (ISI_CR) ISI Software Reset Request */
#define ISI_CR_ISI_CDC (0x1u << 8) /**< \brief (ISI_CR) ISI Codec Request */
/* -------- ISI_SR : (ISI Offset: 0x28) ISI Status Register -------- */
#define ISI_SR_ENABLE (0x1u << 0) /**< \brief (ISI_SR)  */
#define ISI_SR_DIS_DONE (0x1u << 1) /**< \brief (ISI_SR) Module Disable Request has Terminated */
#define ISI_SR_SRST (0x1u << 2) /**< \brief (ISI_SR) Module Software Reset Request has Terminated */
#define ISI_SR_CDC_PND (0x1u << 8) /**< \brief (ISI_SR) Pending Codec Request (this bit is a status bit) */
#define ISI_SR_VSYNC (0x1u << 10) /**< \brief (ISI_SR) Vertical Synchronization */
#define ISI_SR_PXFR_DONE (0x1u << 16) /**< \brief (ISI_SR) Preview DMA Transfer has Terminated. */
#define ISI_SR_CXFR_DONE (0x1u << 17) /**< \brief (ISI_SR) Codec DMA Transfer has Terminated. */
#define ISI_SR_SIP (0x1u << 19) /**< \brief (ISI_SR) Synchronization in Progress (this is a status bit) */
#define ISI_SR_P_OVR (0x1u << 24) /**< \brief (ISI_SR) Preview Datapath Overflow */
#define ISI_SR_C_OVR (0x1u << 25) /**< \brief (ISI_SR) Codec Datapath Overflow */
#define ISI_SR_CRC_ERR (0x1u << 26) /**< \brief (ISI_SR) CRC Synchronization Error */
#define ISI_SR_FR_OVR (0x1u << 27) /**< \brief (ISI_SR) Frame Rate Overrun */
/* -------- ISI_IER : (ISI Offset: 0x2C) ISI Interrupt Enable Register -------- */
#define ISI_IER_DIS_DONE (0x1u << 1) /**< \brief (ISI_IER) Disable Done Interrupt Enable */
#define ISI_IER_SRST (0x1u << 2) /**< \brief (ISI_IER) Software Reset Interrupt Enable */
#define ISI_IER_VSYNC (0x1u << 10) /**< \brief (ISI_IER) Vertical Synchronization Interrupt Enable */
#define ISI_IER_PXFR_DONE (0x1u << 16) /**< \brief (ISI_IER) Preview DMA Transfer Done Interrupt Enable */
#define ISI_IER_CXFR_DONE (0x1u << 17) /**< \brief (ISI_IER) Codec DMA Transfer Done Interrupt Enable */
#define ISI_IER_P_OVR (0x1u << 24) /**< \brief (ISI_IER) Preview Datapath Overflow Interrupt Enable */
#define ISI_IER_C_OVR (0x1u << 25) /**< \brief (ISI_IER) Codec Datapath Overflow Interrupt Enable */
#define ISI_IER_CRC_ERR (0x1u << 26) /**< \brief (ISI_IER) Embedded Synchronization CRC Error Interrupt Enable */
#define ISI_IER_FR_OVR (0x1u << 27) /**< \brief (ISI_IER) Frame Rate Overflow Interrupt Enable */
/* -------- ISI_IDR : (ISI Offset: 0x30) ISI Interrupt Disable Register -------- */
#define ISI_IDR_DIS_DONE (0x1u << 1) /**< \brief (ISI_IDR) Disable Done Interrupt Disable */
#define ISI_IDR_SRST (0x1u << 2) /**< \brief (ISI_IDR) Software Reset Interrupt Disable */
#define ISI_IDR_VSYNC (0x1u << 10) /**< \brief (ISI_IDR) Vertical Synchronization Interrupt Disable */
#define ISI_IDR_PXFR_DONE (0x1u << 16) /**< \brief (ISI_IDR) Preview DMA Transfer Done Interrupt Disable */
#define ISI_IDR_CXFR_DONE (0x1u << 17) /**< \brief (ISI_IDR) Codec DMA Transfer Done Interrupt Disable */
#define ISI_IDR_P_OVR (0x1u << 24) /**< \brief (ISI_IDR) Preview Datapath Overflow Interrupt Disable */
#define ISI_IDR_C_OVR (0x1u << 25) /**< \brief (ISI_IDR) Codec Datapath Overflow Interrupt Disable */
#define ISI_IDR_CRC_ERR (0x1u << 26) /**< \brief (ISI_IDR) Embedded Synchronization CRC Error Interrupt Disable */
#define ISI_IDR_FR_OVR (0x1u << 27) /**< \brief (ISI_IDR) Frame Rate Overflow Interrupt Disable */
/* -------- ISI_IMR : (ISI Offset: 0x34) ISI Interrupt Mask Register -------- */
#define ISI_IMR_DIS_DONE (0x1u << 1) /**< \brief (ISI_IMR) Module Disable Operation Completed */
#define ISI_IMR_SRST (0x1u << 2) /**< \brief (ISI_IMR) Software Reset Completed */
#define ISI_IMR_VSYNC (0x1u << 10) /**< \brief (ISI_IMR) Vertical Synchronization */
#define ISI_IMR_PXFR_DONE (0x1u << 16) /**< \brief (ISI_IMR) Preview DMA Transfer Interrupt */
#define ISI_IMR_CXFR_DONE (0x1u << 17) /**< \brief (ISI_IMR) Codec DMA Transfer Interrupt */
#define ISI_IMR_P_OVR (0x1u << 24) /**< \brief (ISI_IMR) FIFO Preview Overflow */
#define ISI_IMR_C_OVR (0x1u << 25) /**< \brief (ISI_IMR) FIFO Codec Overflow */
#define ISI_IMR_CRC_ERR (0x1u << 26) /**< \brief (ISI_IMR) CRC Synchronization Error */
#define ISI_IMR_FR_OVR (0x1u << 27) /**< \brief (ISI_IMR) Frame Rate Overrun */
/* -------- ISI_DMA_CHER : (ISI Offset: 0x38) DMA Channel Enable Register -------- */
#define ISI_DMA_CHER_P_CH_EN (0x1u << 0) /**< \brief (ISI_DMA_CHER) Preview Channel Enable */
#define ISI_DMA_CHER_C_CH_EN (0x1u << 1) /**< \brief (ISI_DMA_CHER) Codec Channel Enable */
/* -------- ISI_DMA_CHDR : (ISI Offset: 0x3C) DMA Channel Disable Register -------- */
#define ISI_DMA_CHDR_P_CH_DIS (0x1u << 0) /**< \brief (ISI_DMA_CHDR)  */
#define ISI_DMA_CHDR_C_CH_DIS (0x1u << 1) /**< \brief (ISI_DMA_CHDR)  */
/* -------- ISI_DMA_CHSR : (ISI Offset: 0x40) DMA Channel Status Register -------- */
#define ISI_DMA_CHSR_P_CH_S (0x1u << 0) /**< \brief (ISI_DMA_CHSR)  */
#define ISI_DMA_CHSR_C_CH_S (0x1u << 1) /**< \brief (ISI_DMA_CHSR)  */
/* -------- ISI_DMA_P_ADDR : (ISI Offset: 0x44) DMA Preview Base Address Register -------- */
#define ISI_DMA_P_ADDR_P_ADDR_Pos 2
#define ISI_DMA_P_ADDR_P_ADDR_Msk (0x3fffffffu << ISI_DMA_P_ADDR_P_ADDR_Pos) /**< \brief (ISI_DMA_P_ADDR) Preview Image Base Address. (This address is word aligned.) */
#define ISI_DMA_P_ADDR_P_ADDR(value) ((ISI_DMA_P_ADDR_P_ADDR_Msk & ((value) << ISI_DMA_P_ADDR_P_ADDR_Pos)))
/* -------- ISI_DMA_P_CTRL : (ISI Offset: 0x48) DMA Preview Control Register -------- */
#define ISI_DMA_P_CTRL_P_FETCH (0x1u << 0) /**< \brief (ISI_DMA_P_CTRL) Descriptor Fetch Control Field */
#define ISI_DMA_P_CTRL_P_WB (0x1u << 1) /**< \brief (ISI_DMA_P_CTRL) Descriptor Writeback Control Field */
#define ISI_DMA_P_CTRL_P_IEN (0x1u << 2) /**< \brief (ISI_DMA_P_CTRL) Transfer Done Flag Control */
#define ISI_DMA_P_CTRL_P_DONE (0x1u << 3) /**< \brief (ISI_DMA_P_CTRL) (This field is only updated in the memory.) */
/* -------- ISI_DMA_P_DSCR : (ISI Offset: 0x4C) DMA Preview Descriptor Address Register -------- */
#define ISI_DMA_P_DSCR_P_DSCR_Pos 2
#define ISI_DMA_P_DSCR_P_DSCR_Msk (0x3fffffffu << ISI_DMA_P_DSCR_P_DSCR_Pos) /**< \brief (ISI_DMA_P_DSCR) Preview Descriptor Base Address (This address is word aligned.) */
#define ISI_DMA_P_DSCR_P_DSCR(value) ((ISI_DMA_P_DSCR_P_DSCR_Msk & ((value) << ISI_DMA_P_DSCR_P_DSCR_Pos)))
/* -------- ISI_DMA_C_ADDR : (ISI Offset: 0x50) DMA Codec Base Address Register -------- */
#define ISI_DMA_C_ADDR_C_ADDR_Pos 2
#define ISI_DMA_C_ADDR_C_ADDR_Msk (0x3fffffffu << ISI_DMA_C_ADDR_C_ADDR_Pos) /**< \brief (ISI_DMA_C_ADDR) Codec Image Base Address (This address is word aligned.) */
#define ISI_DMA_C_ADDR_C_ADDR(value) ((ISI_DMA_C_ADDR_C_ADDR_Msk & ((value) << ISI_DMA_C_ADDR_C_ADDR_Pos)))
/* -------- ISI_DMA_C_CTRL : (ISI Offset: 0x54) DMA Codec Control Register -------- */
#define ISI_DMA_C_CTRL_C_FETCH (0x1u << 0) /**< \brief (ISI_DMA_C_CTRL) Descriptor Fetch Control Field */
#define ISI_DMA_C_CTRL_C_WB (0x1u << 1) /**< \brief (ISI_DMA_C_CTRL) Descriptor Writeback Control Field */
#define ISI_DMA_C_CTRL_C_IEN (0x1u << 2) /**< \brief (ISI_DMA_C_CTRL) Transfer Done flag control */
#define ISI_DMA_C_CTRL_C_DONE (0x1u << 3) /**< \brief (ISI_DMA_C_CTRL) (This field is only updated in the memory.) */
/* -------- ISI_DMA_C_DSCR : (ISI Offset: 0x58) DMA Codec Descriptor Address Register -------- */
#define ISI_DMA_C_DSCR_C_DSCR_Pos 2
#define ISI_DMA_C_DSCR_C_DSCR_Msk (0x3fffffffu << ISI_DMA_C_DSCR_C_DSCR_Pos) /**< \brief (ISI_DMA_C_DSCR) Codec Descriptor Base Address (This address is word aligned.) */
#define ISI_DMA_C_DSCR_C_DSCR(value) ((ISI_DMA_C_DSCR_C_DSCR_Msk & ((value) << ISI_DMA_C_DSCR_C_DSCR_Pos)))
/* -------- ISI_WPCR : (ISI Offset: 0xE4) Write Protection Control Register -------- */
#define ISI_WPCR_WP_EN (0x1u << 0) /**< \brief (ISI_WPCR) Write Protection Enable */
#define ISI_WPCR_WP_KEY_Pos 8
#define ISI_WPCR_WP_KEY_Msk (0xffffffu << ISI_WPCR_WP_KEY_Pos) /**< \brief (ISI_WPCR) Write Protection KEY Password */
#define ISI_WPCR_WP_KEY(value) ((ISI_WPCR_WP_KEY_Msk & ((value) << ISI_WPCR_WP_KEY_Pos)))
/* -------- ISI_WPSR : (ISI Offset: 0xE8) Write Protection Status Register -------- */
#define ISI_WPSR_WP_VS_Pos 0
#define ISI_WPSR_WP_VS_Msk (0xfu << ISI_WPSR_WP_VS_Pos) /**< \brief (ISI_WPSR) Write Protection Violation Status */
#define ISI_WPSR_WP_VSRC_Pos 8
#define ISI_WPSR_WP_VSRC_Msk (0xffffu << ISI_WPSR_WP_VSRC_Pos) /**< \brief (ISI_WPSR) Write Protection Violation Source */

/*@}*/


#endif /* _SAMA5_ISI_COMPONENT_ */
