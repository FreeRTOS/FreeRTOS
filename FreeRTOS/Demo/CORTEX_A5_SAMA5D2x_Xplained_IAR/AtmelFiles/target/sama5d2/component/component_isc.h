/* ---------------------------------------------------------------------------- */
/*                  Atmel Microcontroller Software Support                      */
/*                       SAM Software Package License                           */
/* ---------------------------------------------------------------------------- */
/* Copyright (c) 2015, Atmel Corporation                                        */
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

#ifndef _SAMA5D2_ISC_COMPONENT_
#define _SAMA5D2_ISC_COMPONENT_

/* ============================================================================= */
/**  SOFTWARE API DEFINITION FOR Image Sensor Controller */
/* ============================================================================= */
/** \addtogroup SAMA5D2_ISC Image Sensor Controller */
/*@{*/

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
/** \brief IscSub0 hardware registers */
typedef struct {
  __IO uint32_t ISC_DAD; /**< \brief (IscSub0 Offset: 0x0) DMA Address 0 Register */
  __IO uint32_t ISC_DST; /**< \brief (IscSub0 Offset: 0x4) DMA Stride 0 Register */
} IscSub0;
/** \brief Isc hardware registers */
#define ISCSUB0_NUMBER 3
typedef struct {
  __O  uint32_t ISC_CTRLEN;               /**< \brief (Isc Offset: 0x00) Control Enable Register */
  __O  uint32_t ISC_CTRLDIS;              /**< \brief (Isc Offset: 0x04) Control Disable Register */
  __I  uint32_t ISC_CTRLSR;               /**< \brief (Isc Offset: 0x08) Control Status Register */
  __IO uint32_t ISC_PFE_CFG0;             /**< \brief (Isc Offset: 0x0C) Parallel Front End Configuration 0 Register */
  __IO uint32_t ISC_PFE_CFG1;             /**< \brief (Isc Offset: 0x10) Parallel Front End Configuration 1 Register */
  __IO uint32_t ISC_PFE_CFG2;             /**< \brief (Isc Offset: 0x14) Parallel Front End Configuration 2 Register */
  __O  uint32_t ISC_CLKEN;                /**< \brief (Isc Offset: 0x18) Clock Enable Register */
  __O  uint32_t ISC_CLKDIS;               /**< \brief (Isc Offset: 0x1C) Clock Disable Register */
  __I  uint32_t ISC_CLKSR;                /**< \brief (Isc Offset: 0x20) Clock Status Register */
  __IO uint32_t ISC_CLKCFG;               /**< \brief (Isc Offset: 0x24) Clock Configuration Register */
  __O  uint32_t ISC_INTEN;                /**< \brief (Isc Offset: 0x28) Interrupt Enable Register */
  __O  uint32_t ISC_INTDIS;               /**< \brief (Isc Offset: 0x2C) Interrupt Disable Register */
  __I  uint32_t ISC_INTMASK;              /**< \brief (Isc Offset: 0x30) Interrupt Mask Register */
  __I  uint32_t ISC_INTSR;                /**< \brief (Isc Offset: 0x34) Interrupt Status Register */
  __I  uint32_t Reserved1[8];
  __IO uint32_t ISC_WB_CTRL;              /**< \brief (Isc Offset: 0x58) White Balance Control Register */
  __IO uint32_t ISC_WB_CFG;               /**< \brief (Isc Offset: 0x5C) White Balance Configuration Register */
  __IO uint32_t ISC_WB_O_RGR;             /**< \brief (Isc Offset: 0x60) White Balance Offset for R, GR Register */
  __IO uint32_t ISC_WB_O_BGB;             /**< \brief (Isc Offset: 0x64) White Balance Offset for B, GB Register */
  __IO uint32_t ISC_WB_G_RGR;             /**< \brief (Isc Offset: 0x68) White Balance Gain for R, GR Register */
  __IO uint32_t ISC_WB_G_BGB;             /**< \brief (Isc Offset: 0x6C) White Balance Gain for B, GB Register */
  __IO uint32_t ISC_CFA_CTRL;             /**< \brief (Isc Offset: 0x70) Color Filter Array Control Register */
  __IO uint32_t ISC_CFA_CFG;              /**< \brief (Isc Offset: 0x74) Color Filter Array Configuration Register */
  __IO uint32_t ISC_CC_CTRL;              /**< \brief (Isc Offset: 0x78) Color Correction Control Register */
  __IO uint32_t ISC_CC_RR_RG;             /**< \brief (Isc Offset: 0x7C) Color Correction RR RG Register */
  __IO uint32_t ISC_CC_RB_OR;             /**< \brief (Isc Offset: 0x80) Color Correction RB OR Register */
  __IO uint32_t ISC_CC_GR_GG;             /**< \brief (Isc Offset: 0x84) Color Correction GR GG Register */
  __IO uint32_t ISC_CC_GB_OG;             /**< \brief (Isc Offset: 0x88) Color Correction GB OG Register */
  __IO uint32_t ISC_CC_BR_BG;             /**< \brief (Isc Offset: 0x8C) Color Correction BR BG Register */
  __IO uint32_t ISC_CC_BB_OB;             /**< \brief (Isc Offset: 0x90) Color Correction BB OB Register */
  __IO uint32_t ISC_GAM_CTRL;             /**< \brief (Isc Offset: 0x94) Gamma Correction Control Register */
  __IO uint32_t ISC_GAM_BENTRY[64];       /**< \brief (Isc Offset: 0x98) Gamma Correction Blue Entry */
  __IO uint32_t ISC_GAM_GENTRY[64];       /**< \brief (Isc Offset: 0x198) Gamma Correction Green Entry */
  __IO uint32_t ISC_GAM_RENTRY[64];       /**< \brief (Isc Offset: 0x298) Gamma Correction Red Entry */
  __IO uint32_t ISC_CSC_CTRL;             /**< \brief (Isc Offset: 0x398) Color Space Conversion Control Register */
  __IO uint32_t ISC_CSC_YR_YG;            /**< \brief (Isc Offset: 0x39C) Color Space Conversion YR, YG Register */
  __IO uint32_t ISC_CSC_YB_OY;            /**< \brief (Isc Offset: 0x3A0) Color Space Conversion YB, OY Register */
  __IO uint32_t ISC_CSC_CBR_CBG;          /**< \brief (Isc Offset: 0x3A4) Color Space Conversion CBR CBG Register */
  __IO uint32_t ISC_CSC_CBB_OCB;          /**< \brief (Isc Offset: 0x3A8) Color Space Conversion CBB OCB Register */
  __IO uint32_t ISC_CSC_CRR_CRG;          /**< \brief (Isc Offset: 0x3AC) Color Space Conversion CRR CRG Register */
  __IO uint32_t ISC_CSC_CRB_OCR;          /**< \brief (Isc Offset: 0x3B0) Color Space Conversion CRB OCR Register */
  __IO uint32_t ISC_CBC_CTRL;             /**< \brief (Isc Offset: 0x3B4) Contrast and Brightness Control Register */
  __IO uint32_t ISC_CBC_CFG;              /**< \brief (Isc Offset: 0x3B8) Contrast and Brightness Configuration Register */
  __IO uint32_t ISC_CBC_BRIGHT;           /**< \brief (Isc Offset: 0x3BC) Contrast and Brightness, Brightness Register */
  __IO uint32_t ISC_CBC_CONTRAST;         /**< \brief (Isc Offset: 0x3C0) Contrast and Brightness, Contrast Register */
  __IO uint32_t ISC_SUB422_CTRL;          /**< \brief (Isc Offset: 0x3C4) Subsampling 4:4:4 to 4:2:2 Control Register */
  __IO uint32_t ISC_SUB422_CFG;           /**< \brief (Isc Offset: 0x3C8) Subsampling 4:4:4 to 4:2:2 Configuration Register */
  __IO uint32_t ISC_SUB420_CTRL;          /**< \brief (Isc Offset: 0x3CC) Subsampling 4:2:2 to 4:2:0 Control Register */
  __IO uint32_t ISC_RLP_CFG;              /**< \brief (Isc Offset: 0x3D0) Rounding, Limiting and Packing Config Register */
  __IO uint32_t ISC_HIS_CTRL;             /**< \brief (Isc Offset: 0x3D4) Histogram Control Register */
  __IO uint32_t ISC_HIS_CFG;              /**< \brief (Isc Offset: 0x3D8) Histogram Configuration Register */
  __I  uint32_t Reserved2[1];
  __IO uint32_t ISC_DCFG;                 /**< \brief (Isc Offset: 0x3E0) DMA Configuration Register */
  __IO uint32_t ISC_DCTRL;                /**< \brief (Isc Offset: 0x3E4) DMA Control Register */
  __IO uint32_t ISC_DNDA;                 /**< \brief (Isc Offset: 0x3E8) DMA Descriptor Address Register */
       IscSub0  ISC_SUB0[ISCSUB0_NUMBER]; /**< \brief (Isc Offset: 0x3EC) 0 .. 2 */
  __I  uint32_t Reserved3[2];
  __I  uint32_t IPB_VERSION;              /**< \brief (Isc Offset: 0x40C) Version Register */
  __I  uint32_t ISC_HIS_ENTRY[512];       /**< \brief (Isc Offset: 0x410) Histogram Entry */
} Isc;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */
/* -------- ISC_CTRLEN : (ISC Offset: 0x00) Control Enable Register -------- */
#define ISC_CTRLEN_CAPTURE (0x1u << 0) /**< \brief (ISC_CTRLEN) Capture Input Stream Command */
#define ISC_CTRLEN_UPPRO (0x1u << 1) /**< \brief (ISC_CTRLEN) Update Profile */
#define ISC_CTRLEN_HISREQ (0x1u << 2) /**< \brief (ISC_CTRLEN) Histogram Request */
#define ISC_CTRLEN_HISCLR (0x1u << 3) /**< \brief (ISC_CTRLEN) Histogram Clear */
/* -------- ISC_CTRLDIS : (ISC Offset: 0x04) Control Disable Register -------- */
#define ISC_CTRLDIS_DISABLE (0x1u << 0) /**< \brief (ISC_CTRLDIS) Capture Disable */
#define ISC_CTRLDIS_SWRST (0x1u << 8) /**< \brief (ISC_CTRLDIS) Software Reset */
/* -------- ISC_CTRLSR : (ISC Offset: 0x08) Control Status Register -------- */
#define ISC_CTRLSR_CAPTURE (0x1u << 0) /**< \brief (ISC_CTRLSR) Capture pending */
#define ISC_CTRLSR_UPPRO (0x1u << 1) /**< \brief (ISC_CTRLSR) Profile Update Pending */
#define ISC_CTRLSR_HISREQ (0x1u << 2) /**< \brief (ISC_CTRLSR) Histogram Request Pending */
#define ISC_CTRLSR_FIELD (0x1u << 4) /**< \brief (ISC_CTRLSR) Field Status (only relevant when the video stream is interlaced) */
#define ISC_CTRLSR_SIP (0x1u << 31) /**< \brief (ISC_CTRLSR) Synchronization In Progress */
/* -------- ISC_PFE_CFG0 : (ISC Offset: 0x0C) Parallel Front End Configuration 0 Register -------- */
#define ISC_PFE_CFG0_HPOL (0x1u << 0) /**< \brief (ISC_PFE_CFG0) Horizontal Synchronization Polarity */
#define ISC_PFE_CFG0_VPOL (0x1u << 1) /**< \brief (ISC_PFE_CFG0) Vertical Synchronization Polarity */
#define ISC_PFE_CFG0_PPOL (0x1u << 2) /**< \brief (ISC_PFE_CFG0) Pixel Clock Polarity */
#define ISC_PFE_CFG0_FPOL (0x1u << 3) /**< \brief (ISC_PFE_CFG0) Field Polarity */
#define ISC_PFE_CFG0_MODE_Pos 4
#define ISC_PFE_CFG0_MODE_Msk (0x7u << ISC_PFE_CFG0_MODE_Pos) /**< \brief (ISC_PFE_CFG0) Parallel Front End Mode */
#define ISC_PFE_CFG0_MODE(value) ((ISC_PFE_CFG0_MODE_Msk & ((value) << ISC_PFE_CFG0_MODE_Pos)))
#define   ISC_PFE_CFG0_MODE_PROGRESSIVE (0x0u << 4) /**< \brief (ISC_PFE_CFG0) Video source is progressive. */
#define   ISC_PFE_CFG0_MODE_DF_TOP (0x1u << 4) /**< \brief (ISC_PFE_CFG0) Video source is interlaced, two fields are captured starting with top field. */
#define   ISC_PFE_CFG0_MODE_DF_BOTTOM (0x2u << 4) /**< \brief (ISC_PFE_CFG0) Video source is interlaced, two fields are captured starting with bottom field. */
#define   ISC_PFE_CFG0_MODE_DF_IMMEDIATE (0x3u << 4) /**< \brief (ISC_PFE_CFG0) Video source is interlaced, two fields are captured immediately. */
#define   ISC_PFE_CFG0_MODE_SF_TOP (0x4u << 4) /**< \brief (ISC_PFE_CFG0) Video source is interlaced, one field is captured starting with the top field. */
#define   ISC_PFE_CFG0_MODE_SF_BOTTOM (0x5u << 4) /**< \brief (ISC_PFE_CFG0) Video source is interlaced, one field is captured starting with the bottom field. */
#define   ISC_PFE_CFG0_MODE_SF_IMMEDIATE (0x6u << 4) /**< \brief (ISC_PFE_CFG0) Video source is interlaced, one field is captured starting immediately. */
#define ISC_PFE_CFG0_CONT (0x1u << 7) /**< \brief (ISC_PFE_CFG0) Continuous Acquisition */
#define ISC_PFE_CFG0_GATED (0x1u << 8) /**< \brief (ISC_PFE_CFG0) Gated input clock */
#define ISC_PFE_CFG0_CCIR656 (0x1u << 9) /**< \brief (ISC_PFE_CFG0) CCIR656 input mode */
#define ISC_PFE_CFG0_CCIR_CRC (0x1u << 10) /**< \brief (ISC_PFE_CFG0) CCIR656 CRC Decoder */
#define ISC_PFE_CFG0_CCIR10_8N (0x1u << 11) /**< \brief (ISC_PFE_CFG0) CCIR 10 bits or 8 bits */
#define ISC_PFE_CFG0_COLEN (0x1u << 12) /**< \brief (ISC_PFE_CFG0) Column Cropping Enable */
#define ISC_PFE_CFG0_ROWEN (0x1u << 13) /**< \brief (ISC_PFE_CFG0) Row Cropping Enable */
#define ISC_PFE_CFG0_SKIPCNT_Pos 16
#define ISC_PFE_CFG0_SKIPCNT_Msk (0xffu << ISC_PFE_CFG0_SKIPCNT_Pos) /**< \brief (ISC_PFE_CFG0) Frame Skipping Counter */
#define ISC_PFE_CFG0_SKIPCNT(value) ((ISC_PFE_CFG0_SKIPCNT_Msk & ((value) << ISC_PFE_CFG0_SKIPCNT_Pos)))
#define ISC_PFE_CFG0_CCIR_REP (0x1u << 27) /**< \brief (ISC_PFE_CFG0) CCIR Replication */
#define ISC_PFE_CFG0_BPS_Pos 28
#define ISC_PFE_CFG0_BPS_Msk (0x7u << ISC_PFE_CFG0_BPS_Pos) /**< \brief (ISC_PFE_CFG0) Bits Per Sample */
#define ISC_PFE_CFG0_BPS(value) ((ISC_PFE_CFG0_BPS_Msk & ((value) << ISC_PFE_CFG0_BPS_Pos)))
#define   ISC_PFE_CFG0_BPS_TWELVE (0x0u << 28) /**< \brief (ISC_PFE_CFG0) 12-bit input */
#define   ISC_PFE_CFG0_BPS_ELEVEN (0x1u << 28) /**< \brief (ISC_PFE_CFG0) 11-bit input */
#define   ISC_PFE_CFG0_BPS_TEN (0x2u << 28) /**< \brief (ISC_PFE_CFG0) 10-bit input */
#define   ISC_PFE_CFG0_BPS_NINE (0x3u << 28) /**< \brief (ISC_PFE_CFG0) 9-bit input */
#define   ISC_PFE_CFG0_BPS_EIGHT (0x4u << 28) /**< \brief (ISC_PFE_CFG0) 8-bit input */
#define ISC_PFE_CFG0_REP (0x1u << 31) /**< \brief (ISC_PFE_CFG0) Up Multiply with Replication */
/* -------- ISC_PFE_CFG1 : (ISC Offset: 0x10) Parallel Front End Configuration 1 Register -------- */
#define ISC_PFE_CFG1_COLMIN_Pos 0
#define ISC_PFE_CFG1_COLMIN_Msk (0xffffu << ISC_PFE_CFG1_COLMIN_Pos) /**< \brief (ISC_PFE_CFG1) Column Minimum Limit */
#define ISC_PFE_CFG1_COLMIN(value) ((ISC_PFE_CFG1_COLMIN_Msk & ((value) << ISC_PFE_CFG1_COLMIN_Pos)))
#define ISC_PFE_CFG1_COLMAX_Pos 16
#define ISC_PFE_CFG1_COLMAX_Msk (0xffffu << ISC_PFE_CFG1_COLMAX_Pos) /**< \brief (ISC_PFE_CFG1) Column Maximum Limit */
#define ISC_PFE_CFG1_COLMAX(value) ((ISC_PFE_CFG1_COLMAX_Msk & ((value) << ISC_PFE_CFG1_COLMAX_Pos)))
/* -------- ISC_PFE_CFG2 : (ISC Offset: 0x14) Parallel Front End Configuration 2 Register -------- */
#define ISC_PFE_CFG2_ROWMIN_Pos 0
#define ISC_PFE_CFG2_ROWMIN_Msk (0xffffu << ISC_PFE_CFG2_ROWMIN_Pos) /**< \brief (ISC_PFE_CFG2) Row Minimum Limit */
#define ISC_PFE_CFG2_ROWMIN(value) ((ISC_PFE_CFG2_ROWMIN_Msk & ((value) << ISC_PFE_CFG2_ROWMIN_Pos)))
#define ISC_PFE_CFG2_ROWMAX_Pos 16
#define ISC_PFE_CFG2_ROWMAX_Msk (0xffffu << ISC_PFE_CFG2_ROWMAX_Pos) /**< \brief (ISC_PFE_CFG2) Row Maximum Limit */
#define ISC_PFE_CFG2_ROWMAX(value) ((ISC_PFE_CFG2_ROWMAX_Msk & ((value) << ISC_PFE_CFG2_ROWMAX_Pos)))
/* -------- ISC_CLKEN : (ISC Offset: 0x18) Clock Enable Register -------- */
#define ISC_CLKEN_ICEN (0x1u << 0) /**< \brief (ISC_CLKEN) ISP Clock Enable */
#define ISC_CLKEN_MCEN (0x1u << 1) /**< \brief (ISC_CLKEN) Master Clock Enable */
/* -------- ISC_CLKDIS : (ISC Offset: 0x1C) Clock Disable Register -------- */
#define ISC_CLKDIS_ICDIS (0x1u << 0) /**< \brief (ISC_CLKDIS) ISP Clock Disable */
#define ISC_CLKDIS_MCDIS (0x1u << 1) /**< \brief (ISC_CLKDIS) Master Clock Disable */
#define ISC_CLKDIS_ICSWRST (0x1u << 8) /**< \brief (ISC_CLKDIS) ISP Clock Software Reset */
#define ISC_CLKDIS_MCSWRST (0x1u << 9) /**< \brief (ISC_CLKDIS) Master Clock Software Reset */
/* -------- ISC_CLKSR : (ISC Offset: 0x20) Clock Status Register -------- */
#define ISC_CLKSR_ICSR (0x1u << 0) /**< \brief (ISC_CLKSR) ISP Clock Status Register */
#define ISC_CLKSR_MCSR (0x1u << 1) /**< \brief (ISC_CLKSR) Master Clock Status Register */
#define ISC_CLKSR_SIP (0x1u << 31) /**< \brief (ISC_CLKSR) Synchronization In Progress */
/* -------- ISC_CLKCFG : (ISC Offset: 0x24) Clock Configuration Register -------- */
#define ISC_CLKCFG_ICDIV_Pos 0
#define ISC_CLKCFG_ICDIV_Msk (0xffu << ISC_CLKCFG_ICDIV_Pos) /**< \brief (ISC_CLKCFG) ISP Clock Divider */
#define ISC_CLKCFG_ICDIV(value) ((ISC_CLKCFG_ICDIV_Msk & ((value) << ISC_CLKCFG_ICDIV_Pos)))
#define ISC_CLKCFG_ICSEL (0x1u << 8) /**< \brief (ISC_CLKCFG) ISP Clock Selection */
#define ISC_CLKCFG_MCDIV_Pos 16
#define ISC_CLKCFG_MCDIV_Msk (0xffu << ISC_CLKCFG_MCDIV_Pos) /**< \brief (ISC_CLKCFG) Master Clock Divider */
#define ISC_CLKCFG_MCDIV(value) ((ISC_CLKCFG_MCDIV_Msk & ((value) << ISC_CLKCFG_MCDIV_Pos)))
#define ISC_CLKCFG_MCSEL_Pos 24
#define ISC_CLKCFG_MCSEL_Msk (0x3u << ISC_CLKCFG_MCSEL_Pos) /**< \brief (ISC_CLKCFG) Master Clock Reference Clock Selection */
#define ISC_CLKCFG_MCSEL(value) ((ISC_CLKCFG_MCSEL_Msk & ((value) << ISC_CLKCFG_MCSEL_Pos)))
/* -------- ISC_INTEN : (ISC Offset: 0x28) Interrupt Enable Register -------- */
#define ISC_INTEN_VD (0x1u << 0) /**< \brief (ISC_INTEN) Vertical Synchronization Detection Interrupt Enable */
#define ISC_INTEN_HD (0x1u << 1) /**< \brief (ISC_INTEN) Horizontal Synchronization Detection Interrupt Enable */
#define ISC_INTEN_SWRST (0x1u << 4) /**< \brief (ISC_INTEN) Software Reset Completed Interrupt Enable */
#define ISC_INTEN_DIS (0x1u << 5) /**< \brief (ISC_INTEN) Disable Completed Interrupt Enable */
#define ISC_INTEN_DDONE (0x1u << 8) /**< \brief (ISC_INTEN) DMA Done Interrupt Enable */
#define ISC_INTEN_LDONE (0x1u << 9) /**< \brief (ISC_INTEN) DMA List Done Interrupt Enable */
#define ISC_INTEN_HISDONE (0x1u << 12) /**< \brief (ISC_INTEN) Histogram Completed Interrupt Enable */
#define ISC_INTEN_HISCLR (0x1u << 13) /**< \brief (ISC_INTEN) Histogram Clear Interrupt Enable */
#define ISC_INTEN_WERR (0x1u << 16) /**< \brief (ISC_INTEN) Write Channel Error Interrupt Enable */
#define ISC_INTEN_RERR (0x1u << 20) /**< \brief (ISC_INTEN) Read Channel Error Interrupt Enable */
#define ISC_INTEN_VFPOV (0x1u << 24) /**< \brief (ISC_INTEN) Vertical Front Porch Overflow Interrupt Enable */
#define ISC_INTEN_DAOV (0x1u << 25) /**< \brief (ISC_INTEN) Data Overflow Interrupt Enable */
#define ISC_INTEN_VDTO (0x1u << 26) /**< \brief (ISC_INTEN) Vertical Synchronization Timeout Interrupt Enable */
#define ISC_INTEN_HDTO (0x1u << 27) /**< \brief (ISC_INTEN) Horizontal Synchronization Timeout Interrupt Enable */
#define ISC_INTEN_CCIRERR (0x1u << 28) /**< \brief (ISC_INTEN) CCIR Decoder Error Interrupt Enable */
/* -------- ISC_INTDIS : (ISC Offset: 0x2C) Interrupt Disable Register -------- */
#define ISC_INTDIS_VD (0x1u << 0) /**< \brief (ISC_INTDIS) Vertical Synchronization Detection Interrupt Disable */
#define ISC_INTDIS_HD (0x1u << 1) /**< \brief (ISC_INTDIS) Horizontal Synchronization Detection Interrupt Disable */
#define ISC_INTDIS_SWRST (0x1u << 4) /**< \brief (ISC_INTDIS) Software Reset Completed Interrupt Disable */
#define ISC_INTDIS_DIS (0x1u << 5) /**< \brief (ISC_INTDIS) Disable Completed Interrupt Disable */
#define ISC_INTDIS_DDONE (0x1u << 8) /**< \brief (ISC_INTDIS) DMA Done Interrupt Disable */
#define ISC_INTDIS_LDONE (0x1u << 9) /**< \brief (ISC_INTDIS) DMA List Done Interrupt Disable */
#define ISC_INTDIS_HISDONE (0x1u << 12) /**< \brief (ISC_INTDIS) Histogram Completed Interrupt Disable */
#define ISC_INTDIS_HISCLR (0x1u << 13) /**< \brief (ISC_INTDIS) Histogram Clear Interrupt Disable */
#define ISC_INTDIS_WERR (0x1u << 16) /**< \brief (ISC_INTDIS) Write Channel Error Interrupt Disable */
#define ISC_INTDIS_RERR (0x1u << 20) /**< \brief (ISC_INTDIS) Read Channel Error Interrupt Disable */
#define ISC_INTDIS_VFPOV (0x1u << 24) /**< \brief (ISC_INTDIS) Vertical Front Porch Overflow Interrupt Disable */
#define ISC_INTDIS_DAOV (0x1u << 25) /**< \brief (ISC_INTDIS) Data Overflow Interrupt Disable */
#define ISC_INTDIS_VDTO (0x1u << 26) /**< \brief (ISC_INTDIS) Vertical Synchronization Timeout Interrupt Disable */
#define ISC_INTDIS_HDTO (0x1u << 27) /**< \brief (ISC_INTDIS) Horizontal Synchronization Timeout Interrupt Disable */
#define ISC_INTDIS_CCIRERR (0x1u << 28) /**< \brief (ISC_INTDIS) CCIR Decoder Error Interrupt Disable */
/* -------- ISC_INTMASK : (ISC Offset: 0x30) Interrupt Mask Register -------- */
#define ISC_INTMASK_VD (0x1u << 0) /**< \brief (ISC_INTMASK) Vertical Synchronization Detection Interrupt Mask */
#define ISC_INTMASK_HD (0x1u << 1) /**< \brief (ISC_INTMASK) Horizontal Synchronization Detection Interrupt Mask */
#define ISC_INTMASK_SWRST (0x1u << 4) /**< \brief (ISC_INTMASK) Software Reset Completed Interrupt Mask */
#define ISC_INTMASK_DIS (0x1u << 5) /**< \brief (ISC_INTMASK) Disable Completed Interrupt Mask */
#define ISC_INTMASK_DDONE (0x1u << 8) /**< \brief (ISC_INTMASK) DMA Done Interrupt Mask */
#define ISC_INTMASK_LDONE (0x1u << 9) /**< \brief (ISC_INTMASK) DMA List Done Interrupt Mask */
#define ISC_INTMASK_HISDONE (0x1u << 12) /**< \brief (ISC_INTMASK) Histogram Completed Interrupt Mask */
#define ISC_INTMASK_HISCLR (0x1u << 13) /**< \brief (ISC_INTMASK) Histogram Clear Interrupt Mask */
#define ISC_INTMASK_WERR (0x1u << 16) /**< \brief (ISC_INTMASK) Write Channel Error Interrupt Mask */
#define ISC_INTMASK_RERR (0x1u << 20) /**< \brief (ISC_INTMASK) Read Channel Error Interrupt Mask */
#define ISC_INTMASK_VFPOV (0x1u << 24) /**< \brief (ISC_INTMASK) Vertical Front Porch Overflow Interrupt Mask */
#define ISC_INTMASK_DAOV (0x1u << 25) /**< \brief (ISC_INTMASK) Data Overflow Interrupt Mask */
#define ISC_INTMASK_VDTO (0x1u << 26) /**< \brief (ISC_INTMASK) Vertical Synchronization Timeout Interrupt Mask */
#define ISC_INTMASK_HDTO (0x1u << 27) /**< \brief (ISC_INTMASK) Horizontal Synchronization Timeout Interrupt Mask */
#define ISC_INTMASK_CCIRERR (0x1u << 28) /**< \brief (ISC_INTMASK) CCIR Decoder Error Interrupt Mask */
/* -------- ISC_INTSR : (ISC Offset: 0x34) Interrupt Status Register -------- */
#define ISC_INTSR_VD (0x1u << 0) /**< \brief (ISC_INTSR) Vertical Synchronization Detected Interrupt */
#define ISC_INTSR_HD (0x1u << 1) /**< \brief (ISC_INTSR) Horizontal Synchronization Detected Interrupt */
#define ISC_INTSR_SWRST (0x1u << 4) /**< \brief (ISC_INTSR) Software Reset Completed Interrupt */
#define ISC_INTSR_DIS (0x1u << 5) /**< \brief (ISC_INTSR) Disable Completed Interrupt */
#define ISC_INTSR_DDONE (0x1u << 8) /**< \brief (ISC_INTSR) DMA Done Interrupt */
#define ISC_INTSR_LDONE (0x1u << 9) /**< \brief (ISC_INTSR) DMA List Done Interrupt */
#define ISC_INTSR_HISDONE (0x1u << 12) /**< \brief (ISC_INTSR) Histogram Completed Interrupt */
#define ISC_INTSR_HISCLR (0x1u << 13) /**< \brief (ISC_INTSR) Histogram Clear Interrupt */
#define ISC_INTSR_WERR (0x1u << 16) /**< \brief (ISC_INTSR) Write Channel Error Interrupt */
#define ISC_INTSR_WERRID_Pos 17
#define ISC_INTSR_WERRID_Msk (0x3u << ISC_INTSR_WERRID_Pos) /**< \brief (ISC_INTSR) Write Channel Error Identifier */
#define   ISC_INTSR_WERRID_CH0 (0x0u << 17) /**< \brief (ISC_INTSR) An error occurred for Channel 0 (RAW/RGB/Y) */
#define   ISC_INTSR_WERRID_CH1 (0x1u << 17) /**< \brief (ISC_INTSR) An error occurred for Channel 1 (CbCr/Cb) */
#define   ISC_INTSR_WERRID_CH2 (0x2u << 17) /**< \brief (ISC_INTSR) An error occurred for Channel 2 (Cr) */
#define   ISC_INTSR_WERRID_WB (0x3u << 17) /**< \brief (ISC_INTSR) Write back channel error */
#define ISC_INTSR_RERR (0x1u << 20) /**< \brief (ISC_INTSR) Read Channel Error Interrupt */
#define ISC_INTSR_VFPOV (0x1u << 24) /**< \brief (ISC_INTSR) Vertical Front Porch Overflow Interrupt */
#define ISC_INTSR_DAOV (0x1u << 25) /**< \brief (ISC_INTSR) Data Overflow Interrupt */
#define ISC_INTSR_VDTO (0x1u << 26) /**< \brief (ISC_INTSR) Vertical Synchronization Timeout Interrupt */
#define ISC_INTSR_HDTO (0x1u << 27) /**< \brief (ISC_INTSR) Horizontal Synchronization Timeout Interrupt */
#define ISC_INTSR_CCIRERR (0x1u << 28) /**< \brief (ISC_INTSR) CCIR Decoder Error Interrupt */
/* -------- ISC_WB_CTRL : (ISC Offset: 0x58) White Balance Control Register -------- */
#define ISC_WB_CTRL_ENABLE (0x1u << 0) /**< \brief (ISC_WB_CTRL) White Balance Enable */
/* -------- ISC_WB_CFG : (ISC Offset: 0x5C) White Balance Configuration Register -------- */
#define ISC_WB_CFG_BAYCFG_Pos 0
#define ISC_WB_CFG_BAYCFG_Msk (0x3u << ISC_WB_CFG_BAYCFG_Pos) /**< \brief (ISC_WB_CFG) White Balance Bayer Configuration (Pixel Color Pattern) */
#define ISC_WB_CFG_BAYCFG(value) ((ISC_WB_CFG_BAYCFG_Msk & ((value) << ISC_WB_CFG_BAYCFG_Pos)))
#define   ISC_WB_CFG_BAYCFG_GRGR (0x0u << 0) /**< \brief (ISC_WB_CFG) Starting Row configuration is G R G R (Red Row) */
#define   ISC_WB_CFG_BAYCFG_RGRG (0x1u << 0) /**< \brief (ISC_WB_CFG) Starting Row configuration is R G R G (Red Row */
#define   ISC_WB_CFG_BAYCFG_GBGB (0x2u << 0) /**< \brief (ISC_WB_CFG) Starting Row configuration is G B G B (Blue Row */
#define   ISC_WB_CFG_BAYCFG_BGBG (0x3u << 0) /**< \brief (ISC_WB_CFG) Starting Row configuration is B G B G (Blue Row) */
/* -------- ISC_WB_O_RGR : (ISC Offset: 0x60) White Balance Offset for R, GR Register -------- */
#define ISC_WB_O_RGR_ROFST_Pos 0
#define ISC_WB_O_RGR_ROFST_Msk (0x1fffu << ISC_WB_O_RGR_ROFST_Pos) /**< \brief (ISC_WB_O_RGR) Offset Red Component (signed 13 bits 1:12:0) */
#define ISC_WB_O_RGR_ROFST(value) ((ISC_WB_O_RGR_ROFST_Msk & ((value) << ISC_WB_O_RGR_ROFST_Pos)))
#define ISC_WB_O_RGR_GROFST_Pos 16
#define ISC_WB_O_RGR_GROFST_Msk (0x1fffu << ISC_WB_O_RGR_GROFST_Pos) /**< \brief (ISC_WB_O_RGR) Offset Green Component for Red Row (signed 13 bits 1:12:0) */
#define ISC_WB_O_RGR_GROFST(value) ((ISC_WB_O_RGR_GROFST_Msk & ((value) << ISC_WB_O_RGR_GROFST_Pos)))
/* -------- ISC_WB_O_BGB : (ISC Offset: 0x64) White Balance Offset for B, GB Register -------- */
#define ISC_WB_O_BGB_BOFST_Pos 0
#define ISC_WB_O_BGB_BOFST_Msk (0x1fffu << ISC_WB_O_BGB_BOFST_Pos) /**< \brief (ISC_WB_O_BGB) Offset Blue Component (signed 13 bits, 1:12:0) */
#define ISC_WB_O_BGB_BOFST(value) ((ISC_WB_O_BGB_BOFST_Msk & ((value) << ISC_WB_O_BGB_BOFST_Pos)))
#define ISC_WB_O_BGB_GBOFST_Pos 16
#define ISC_WB_O_BGB_GBOFST_Msk (0x1fffu << ISC_WB_O_BGB_GBOFST_Pos) /**< \brief (ISC_WB_O_BGB) Offset Green Component for Blue Row (signed 13 bits, 1:12:0) */
#define ISC_WB_O_BGB_GBOFST(value) ((ISC_WB_O_BGB_GBOFST_Msk & ((value) << ISC_WB_O_BGB_GBOFST_Pos)))
/* -------- ISC_WB_G_RGR : (ISC Offset: 0x68) White Balance Gain for R, GR Register -------- */
#define ISC_WB_G_RGR_RGAIN_Pos 0
#define ISC_WB_G_RGR_RGAIN_Msk (0x1fffu << ISC_WB_G_RGR_RGAIN_Pos) /**< \brief (ISC_WB_G_RGR) Red Component Gain (unsigned 13 bits, 0:4:9) */
#define ISC_WB_G_RGR_RGAIN(value) ((ISC_WB_G_RGR_RGAIN_Msk & ((value) << ISC_WB_G_RGR_RGAIN_Pos)))
#define ISC_WB_G_RGR_GRGAIN_Pos 16
#define ISC_WB_G_RGR_GRGAIN_Msk (0x1fffu << ISC_WB_G_RGR_GRGAIN_Pos) /**< \brief (ISC_WB_G_RGR) Green Component (Red row) Gain (unsigned 13 bits, 0:4:9) */
#define ISC_WB_G_RGR_GRGAIN(value) ((ISC_WB_G_RGR_GRGAIN_Msk & ((value) << ISC_WB_G_RGR_GRGAIN_Pos)))
/* -------- ISC_WB_G_BGB : (ISC Offset: 0x6C) White Balance Gain for B, GB Register -------- */
#define ISC_WB_G_BGB_BGAIN_Pos 0
#define ISC_WB_G_BGB_BGAIN_Msk (0x1fffu << ISC_WB_G_BGB_BGAIN_Pos) /**< \brief (ISC_WB_G_BGB) Blue Component Gain (unsigned 13 bits, 0:4:9) */
#define ISC_WB_G_BGB_BGAIN(value) ((ISC_WB_G_BGB_BGAIN_Msk & ((value) << ISC_WB_G_BGB_BGAIN_Pos)))
#define ISC_WB_G_BGB_GBGAIN_Pos 16
#define ISC_WB_G_BGB_GBGAIN_Msk (0x1fffu << ISC_WB_G_BGB_GBGAIN_Pos) /**< \brief (ISC_WB_G_BGB) Green Component (Blue row) Gain (unsigned 13 bits, 0:4:9) */
#define ISC_WB_G_BGB_GBGAIN(value) ((ISC_WB_G_BGB_GBGAIN_Msk & ((value) << ISC_WB_G_BGB_GBGAIN_Pos)))
/* -------- ISC_CFA_CTRL : (ISC Offset: 0x70) Color Filter Array Control Register -------- */
#define ISC_CFA_CTRL_ENABLE (0x1u << 0) /**< \brief (ISC_CFA_CTRL) Color Filter Array Interpolation Enable */
/* -------- ISC_CFA_CFG : (ISC Offset: 0x74) Color Filter Array Configuration Register -------- */
#define ISC_CFA_CFG_BAYCFG_Pos 0
#define ISC_CFA_CFG_BAYCFG_Msk (0x3u << ISC_CFA_CFG_BAYCFG_Pos) /**< \brief (ISC_CFA_CFG) Color Filter Array Pattern */
#define ISC_CFA_CFG_BAYCFG(value) ((ISC_CFA_CFG_BAYCFG_Msk & ((value) << ISC_CFA_CFG_BAYCFG_Pos)))
#define   ISC_CFA_CFG_BAYCFG_GRGR (0x0u << 0) /**< \brief (ISC_CFA_CFG) Starting row configuration is G R G R (red row) */
#define   ISC_CFA_CFG_BAYCFG_RGRG (0x1u << 0) /**< \brief (ISC_CFA_CFG) Starting row configuration is R G R G (red row */
#define   ISC_CFA_CFG_BAYCFG_GBGB (0x2u << 0) /**< \brief (ISC_CFA_CFG) Starting row configuration is G B G B (blue row */
#define   ISC_CFA_CFG_BAYCFG_BGBG (0x3u << 0) /**< \brief (ISC_CFA_CFG) Starting row configuration is B G B G (blue row) */
#define ISC_CFA_CFG_EITPOL (0x1u << 4) /**< \brief (ISC_CFA_CFG) Edge Interpolation */
/* -------- ISC_CC_CTRL : (ISC Offset: 0x78) Color Correction Control Register -------- */
#define ISC_CC_CTRL_ENABLE (0x1u << 0) /**< \brief (ISC_CC_CTRL) Color Correction Enable */
/* -------- ISC_CC_RR_RG : (ISC Offset: 0x7C) Color Correction RR RG Register -------- */
#define ISC_CC_RR_RG_RRGAIN_Pos 0
#define ISC_CC_RR_RG_RRGAIN_Msk (0xfffu << ISC_CC_RR_RG_RRGAIN_Pos) /**< \brief (ISC_CC_RR_RG) Red Gain for Red Component (signed 12 bits, 1:3:8) */
#define ISC_CC_RR_RG_RRGAIN(value) ((ISC_CC_RR_RG_RRGAIN_Msk & ((value) << ISC_CC_RR_RG_RRGAIN_Pos)))
#define ISC_CC_RR_RG_RGGAIN_Pos 16
#define ISC_CC_RR_RG_RGGAIN_Msk (0xfffu << ISC_CC_RR_RG_RGGAIN_Pos) /**< \brief (ISC_CC_RR_RG) Green Gain for Red Component (signed 12 bits, 1:3:8) */
#define ISC_CC_RR_RG_RGGAIN(value) ((ISC_CC_RR_RG_RGGAIN_Msk & ((value) << ISC_CC_RR_RG_RGGAIN_Pos)))
/* -------- ISC_CC_RB_OR : (ISC Offset: 0x80) Color Correction RB OR Register -------- */
#define ISC_CC_RB_OR_RBGAIN_Pos 0
#define ISC_CC_RB_OR_RBGAIN_Msk (0xfffu << ISC_CC_RB_OR_RBGAIN_Pos) /**< \brief (ISC_CC_RB_OR) Blue Gain for Red Component (signed 12 bits, 1:3:8) */
#define ISC_CC_RB_OR_RBGAIN(value) ((ISC_CC_RB_OR_RBGAIN_Msk & ((value) << ISC_CC_RB_OR_RBGAIN_Pos)))
#define ISC_CC_RB_OR_ROFST_Pos 16
#define ISC_CC_RB_OR_ROFST_Msk (0x1fffu << ISC_CC_RB_OR_ROFST_Pos) /**< \brief (ISC_CC_RB_OR) Red Component Offset (signed 13 bits, 1:12:0) */
#define ISC_CC_RB_OR_ROFST(value) ((ISC_CC_RB_OR_ROFST_Msk & ((value) << ISC_CC_RB_OR_ROFST_Pos)))
/* -------- ISC_CC_GR_GG : (ISC Offset: 0x84) Color Correction GR GG Register -------- */
#define ISC_CC_GR_GG_GRGAIN_Pos 0
#define ISC_CC_GR_GG_GRGAIN_Msk (0xfffu << ISC_CC_GR_GG_GRGAIN_Pos) /**< \brief (ISC_CC_GR_GG) Red Gain for Green Component (signed 12 bits, 1:3:8) */
#define ISC_CC_GR_GG_GRGAIN(value) ((ISC_CC_GR_GG_GRGAIN_Msk & ((value) << ISC_CC_GR_GG_GRGAIN_Pos)))
#define ISC_CC_GR_GG_GGGAIN_Pos 16
#define ISC_CC_GR_GG_GGGAIN_Msk (0xfffu << ISC_CC_GR_GG_GGGAIN_Pos) /**< \brief (ISC_CC_GR_GG) Green Gain for Green Component (signed 12 bits, 1:3:8) */
#define ISC_CC_GR_GG_GGGAIN(value) ((ISC_CC_GR_GG_GGGAIN_Msk & ((value) << ISC_CC_GR_GG_GGGAIN_Pos)))
/* -------- ISC_CC_GB_OG : (ISC Offset: 0x88) Color Correction GB OG Register -------- */
#define ISC_CC_GB_OG_GBGAIN_Pos 0
#define ISC_CC_GB_OG_GBGAIN_Msk (0xfffu << ISC_CC_GB_OG_GBGAIN_Pos) /**< \brief (ISC_CC_GB_OG) Blue Gain for Green Component (signed 12 bits, 1:3:8) */
#define ISC_CC_GB_OG_GBGAIN(value) ((ISC_CC_GB_OG_GBGAIN_Msk & ((value) << ISC_CC_GB_OG_GBGAIN_Pos)))
#define ISC_CC_GB_OG_ROFST_Pos 16
#define ISC_CC_GB_OG_ROFST_Msk (0x1fffu << ISC_CC_GB_OG_ROFST_Pos) /**< \brief (ISC_CC_GB_OG) Green Component Offset (signed 13 bits, 1:12:0) */
#define ISC_CC_GB_OG_ROFST(value) ((ISC_CC_GB_OG_ROFST_Msk & ((value) << ISC_CC_GB_OG_ROFST_Pos)))
/* -------- ISC_CC_BR_BG : (ISC Offset: 0x8C) Color Correction BR BG Register -------- */
#define ISC_CC_BR_BG_BRGAIN_Pos 0
#define ISC_CC_BR_BG_BRGAIN_Msk (0xfffu << ISC_CC_BR_BG_BRGAIN_Pos) /**< \brief (ISC_CC_BR_BG) Red Gain for Blue Component (signed 12 bits, 1:3:8) */
#define ISC_CC_BR_BG_BRGAIN(value) ((ISC_CC_BR_BG_BRGAIN_Msk & ((value) << ISC_CC_BR_BG_BRGAIN_Pos)))
#define ISC_CC_BR_BG_BGGAIN_Pos 16
#define ISC_CC_BR_BG_BGGAIN_Msk (0xfffu << ISC_CC_BR_BG_BGGAIN_Pos) /**< \brief (ISC_CC_BR_BG) Green Gain for Blue Component (signed 12 bits, 1:3:8) */
#define ISC_CC_BR_BG_BGGAIN(value) ((ISC_CC_BR_BG_BGGAIN_Msk & ((value) << ISC_CC_BR_BG_BGGAIN_Pos)))
/* -------- ISC_CC_BB_OB : (ISC Offset: 0x90) Color Correction BB OB Register -------- */
#define ISC_CC_BB_OB_BBGAIN_Pos 0
#define ISC_CC_BB_OB_BBGAIN_Msk (0xfffu << ISC_CC_BB_OB_BBGAIN_Pos) /**< \brief (ISC_CC_BB_OB) Blue Gain for Blue Component (signed 12 bits, 1:3:8) */
#define ISC_CC_BB_OB_BBGAIN(value) ((ISC_CC_BB_OB_BBGAIN_Msk & ((value) << ISC_CC_BB_OB_BBGAIN_Pos)))
#define ISC_CC_BB_OB_BOFST_Pos 16
#define ISC_CC_BB_OB_BOFST_Msk (0x1fffu << ISC_CC_BB_OB_BOFST_Pos) /**< \brief (ISC_CC_BB_OB) Blue Component Offset (signed 13 bits, 1:12:0) */
#define ISC_CC_BB_OB_BOFST(value) ((ISC_CC_BB_OB_BOFST_Msk & ((value) << ISC_CC_BB_OB_BOFST_Pos)))
/* -------- ISC_GAM_CTRL : (ISC Offset: 0x94) Gamma Correction Control Register -------- */
#define ISC_GAM_CTRL_ENABLE (0x1u << 0) /**< \brief (ISC_GAM_CTRL) Gamma Correction Enable */
#define ISC_GAM_CTRL_BENABLE (0x1u << 1) /**< \brief (ISC_GAM_CTRL) Gamma Correction Enable for B Channel */
#define ISC_GAM_CTRL_GENABLE (0x1u << 2) /**< \brief (ISC_GAM_CTRL) Gamma Correction Enable for G Channel */
#define ISC_GAM_CTRL_RENABLE (0x1u << 3) /**< \brief (ISC_GAM_CTRL) Gamma Correction Enable for R Channel */
/* -------- ISC_GAM_BENTRY[64] : (ISC Offset: 0x98) Gamma Correction Blue Entry -------- */
#define ISC_GAM_BENTRY_BSLOPE_Pos 0
#define ISC_GAM_BENTRY_BSLOPE_Msk (0x3ffu << ISC_GAM_BENTRY_BSLOPE_Pos) /**< \brief (ISC_GAM_BENTRY[64]) Blue Color Slope for Piecewise Interpolation (signed 10 bits 1:3:6) */
#define ISC_GAM_BENTRY_BSLOPE(value) ((ISC_GAM_BENTRY_BSLOPE_Msk & ((value) << ISC_GAM_BENTRY_BSLOPE_Pos)))
#define ISC_GAM_BENTRY_BCONSTANT_Pos 16
#define ISC_GAM_BENTRY_BCONSTANT_Msk (0x3ffu << ISC_GAM_BENTRY_BCONSTANT_Pos) /**< \brief (ISC_GAM_BENTRY[64]) Blue Color Constant for Piecewise Interpolation (unsigned 10 bits 0:10:0) */
#define ISC_GAM_BENTRY_BCONSTANT(value) ((ISC_GAM_BENTRY_BCONSTANT_Msk & ((value) << ISC_GAM_BENTRY_BCONSTANT_Pos)))
/* -------- ISC_GAM_GENTRY[64] : (ISC Offset: 0x198) Gamma Correction Green Entry -------- */
#define ISC_GAM_GENTRY_GSLOPE_Pos 0
#define ISC_GAM_GENTRY_GSLOPE_Msk (0x3ffu << ISC_GAM_GENTRY_GSLOPE_Pos) /**< \brief (ISC_GAM_GENTRY[64]) Green Color Slope for Piecewise Interpolation (signed 10 bits 1:3:6) */
#define ISC_GAM_GENTRY_GSLOPE(value) ((ISC_GAM_GENTRY_GSLOPE_Msk & ((value) << ISC_GAM_GENTRY_GSLOPE_Pos)))
#define ISC_GAM_GENTRY_GCONSTANT_Pos 16
#define ISC_GAM_GENTRY_GCONSTANT_Msk (0x3ffu << ISC_GAM_GENTRY_GCONSTANT_Pos) /**< \brief (ISC_GAM_GENTRY[64]) Green Color Constant for Piecewise Interpolation (unsigned 10 bits 0:10:0) */
#define ISC_GAM_GENTRY_GCONSTANT(value) ((ISC_GAM_GENTRY_GCONSTANT_Msk & ((value) << ISC_GAM_GENTRY_GCONSTANT_Pos)))
/* -------- ISC_GAM_RENTRY[64] : (ISC Offset: 0x298) Gamma Correction Red Entry -------- */
#define ISC_GAM_RENTRY_RSLOPE_Pos 0
#define ISC_GAM_RENTRY_RSLOPE_Msk (0x3ffu << ISC_GAM_RENTRY_RSLOPE_Pos) /**< \brief (ISC_GAM_RENTRY[64]) Red Color Slope for Piecewise Interpolation (signed 10 bits 1:3:6) */
#define ISC_GAM_RENTRY_RSLOPE(value) ((ISC_GAM_RENTRY_RSLOPE_Msk & ((value) << ISC_GAM_RENTRY_RSLOPE_Pos)))
#define ISC_GAM_RENTRY_RCONSTANT_Pos 16
#define ISC_GAM_RENTRY_RCONSTANT_Msk (0x3ffu << ISC_GAM_RENTRY_RCONSTANT_Pos) /**< \brief (ISC_GAM_RENTRY[64]) Red Color Constant for Piecewise Interpolation (unsigned 10 bits 0:10:0) */
#define ISC_GAM_RENTRY_RCONSTANT(value) ((ISC_GAM_RENTRY_RCONSTANT_Msk & ((value) << ISC_GAM_RENTRY_RCONSTANT_Pos)))
/* -------- ISC_CSC_CTRL : (ISC Offset: 0x398) Color Space Conversion Control Register -------- */
#define ISC_CSC_CTRL_ENABLE (0x1u << 0) /**< \brief (ISC_CSC_CTRL) RGB to YCbCr Color Space Conversion Enable */
/* -------- ISC_CSC_YR_YG : (ISC Offset: 0x39C) Color Space Conversion YR, YG Register -------- */
#define ISC_CSC_YR_YG_YRGAIN_Pos 0
#define ISC_CSC_YR_YG_YRGAIN_Msk (0xfffu << ISC_CSC_YR_YG_YRGAIN_Pos) /**< \brief (ISC_CSC_YR_YG) Reg Gain for Luminance (signed 12 bits 1:3:8) */
#define ISC_CSC_YR_YG_YRGAIN(value) ((ISC_CSC_YR_YG_YRGAIN_Msk & ((value) << ISC_CSC_YR_YG_YRGAIN_Pos)))
#define ISC_CSC_YR_YG_YGGAIN_Pos 16
#define ISC_CSC_YR_YG_YGGAIN_Msk (0xfffu << ISC_CSC_YR_YG_YGGAIN_Pos) /**< \brief (ISC_CSC_YR_YG) Green Gain for Luminance (signed 12 bits 1:3:8) */
#define ISC_CSC_YR_YG_YGGAIN(value) ((ISC_CSC_YR_YG_YGGAIN_Msk & ((value) << ISC_CSC_YR_YG_YGGAIN_Pos)))
/* -------- ISC_CSC_YB_OY : (ISC Offset: 0x3A0) Color Space Conversion YB, OY Register -------- */
#define ISC_CSC_YB_OY_YBGAIN_Pos 0
#define ISC_CSC_YB_OY_YBGAIN_Msk (0xfffu << ISC_CSC_YB_OY_YBGAIN_Pos) /**< \brief (ISC_CSC_YB_OY) Blue Gain for Luminance Component (12 bits signed 1:3:8) */
#define ISC_CSC_YB_OY_YBGAIN(value) ((ISC_CSC_YB_OY_YBGAIN_Msk & ((value) << ISC_CSC_YB_OY_YBGAIN_Pos)))
#define ISC_CSC_YB_OY_YOFST_Pos 16
#define ISC_CSC_YB_OY_YOFST_Msk (0x7ffu << ISC_CSC_YB_OY_YOFST_Pos) /**< \brief (ISC_CSC_YB_OY) Luminance Offset (11 bits signed 1:10:0) */
#define ISC_CSC_YB_OY_YOFST(value) ((ISC_CSC_YB_OY_YOFST_Msk & ((value) << ISC_CSC_YB_OY_YOFST_Pos)))
/* -------- ISC_CSC_CBR_CBG : (ISC Offset: 0x3A4) Color Space Conversion CBR CBG Register -------- */
#define ISC_CSC_CBR_CBG_CBRGAIN_Pos 0
#define ISC_CSC_CBR_CBG_CBRGAIN_Msk (0xfffu << ISC_CSC_CBR_CBG_CBRGAIN_Pos) /**< \brief (ISC_CSC_CBR_CBG) Red Gain for Blue Chrominance (signed 12 bits, 1:3:8) */
#define ISC_CSC_CBR_CBG_CBRGAIN(value) ((ISC_CSC_CBR_CBG_CBRGAIN_Msk & ((value) << ISC_CSC_CBR_CBG_CBRGAIN_Pos)))
#define ISC_CSC_CBR_CBG_CBGGAIN_Pos 16
#define ISC_CSC_CBR_CBG_CBGGAIN_Msk (0xfffu << ISC_CSC_CBR_CBG_CBGGAIN_Pos) /**< \brief (ISC_CSC_CBR_CBG) Green Gain for Blue Chrominance (signed 12 bits 1:3:8) */
#define ISC_CSC_CBR_CBG_CBGGAIN(value) ((ISC_CSC_CBR_CBG_CBGGAIN_Msk & ((value) << ISC_CSC_CBR_CBG_CBGGAIN_Pos)))
/* -------- ISC_CSC_CBB_OCB : (ISC Offset: 0x3A8) Color Space Conversion CBB OCB Register -------- */
#define ISC_CSC_CBB_OCB_CBBGAIN_Pos 0
#define ISC_CSC_CBB_OCB_CBBGAIN_Msk (0xfffu << ISC_CSC_CBB_OCB_CBBGAIN_Pos) /**< \brief (ISC_CSC_CBB_OCB) Blue Gain for Blue Chrominance (signed 12 bits 1:3:8) */
#define ISC_CSC_CBB_OCB_CBBGAIN(value) ((ISC_CSC_CBB_OCB_CBBGAIN_Msk & ((value) << ISC_CSC_CBB_OCB_CBBGAIN_Pos)))
#define ISC_CSC_CBB_OCB_CBOFST_Pos 16
#define ISC_CSC_CBB_OCB_CBOFST_Msk (0x7ffu << ISC_CSC_CBB_OCB_CBOFST_Pos) /**< \brief (ISC_CSC_CBB_OCB) Blue Chrominance Offset (signed 11 bits 1:10:0) */
#define ISC_CSC_CBB_OCB_CBOFST(value) ((ISC_CSC_CBB_OCB_CBOFST_Msk & ((value) << ISC_CSC_CBB_OCB_CBOFST_Pos)))
/* -------- ISC_CSC_CRR_CRG : (ISC Offset: 0x3AC) Color Space Conversion CRR CRG Register -------- */
#define ISC_CSC_CRR_CRG_CRRGAIN_Pos 0
#define ISC_CSC_CRR_CRG_CRRGAIN_Msk (0xfffu << ISC_CSC_CRR_CRG_CRRGAIN_Pos) /**< \brief (ISC_CSC_CRR_CRG) Red Gain for Red Chrominance (signed 12 bits 1:3:8) */
#define ISC_CSC_CRR_CRG_CRRGAIN(value) ((ISC_CSC_CRR_CRG_CRRGAIN_Msk & ((value) << ISC_CSC_CRR_CRG_CRRGAIN_Pos)))
#define ISC_CSC_CRR_CRG_CRGGAIN_Pos 16
#define ISC_CSC_CRR_CRG_CRGGAIN_Msk (0xfffu << ISC_CSC_CRR_CRG_CRGGAIN_Pos) /**< \brief (ISC_CSC_CRR_CRG) Green Gain for Red Chrominance (signed 12 bits 1:3:8) */
#define ISC_CSC_CRR_CRG_CRGGAIN(value) ((ISC_CSC_CRR_CRG_CRGGAIN_Msk & ((value) << ISC_CSC_CRR_CRG_CRGGAIN_Pos)))
/* -------- ISC_CSC_CRB_OCR : (ISC Offset: 0x3B0) Color Space Conversion CRB OCR Register -------- */
#define ISC_CSC_CRB_OCR_CRBGAIN_Pos 0
#define ISC_CSC_CRB_OCR_CRBGAIN_Msk (0xfffu << ISC_CSC_CRB_OCR_CRBGAIN_Pos) /**< \brief (ISC_CSC_CRB_OCR) Blue Gain for Red Chrominance (signed 12 bits 1:3:8) */
#define ISC_CSC_CRB_OCR_CRBGAIN(value) ((ISC_CSC_CRB_OCR_CRBGAIN_Msk & ((value) << ISC_CSC_CRB_OCR_CRBGAIN_Pos)))
#define ISC_CSC_CRB_OCR_CROFST_Pos 16
#define ISC_CSC_CRB_OCR_CROFST_Msk (0x7ffu << ISC_CSC_CRB_OCR_CROFST_Pos) /**< \brief (ISC_CSC_CRB_OCR) Red Chrominance Offset (signed 11 bits 1:10:0) */
#define ISC_CSC_CRB_OCR_CROFST(value) ((ISC_CSC_CRB_OCR_CROFST_Msk & ((value) << ISC_CSC_CRB_OCR_CROFST_Pos)))
/* -------- ISC_CBC_CTRL : (ISC Offset: 0x3B4) Contrast and Brightness Control Register -------- */
#define ISC_CBC_CTRL_ENABLE (0x1u << 0) /**< \brief (ISC_CBC_CTRL) Contrast and Brightness Control Enable */
/* -------- ISC_CBC_CFG : (ISC Offset: 0x3B8) Contrast and Brightness Configuration Register -------- */
#define ISC_CBC_CFG_CCIR (0x1u << 0) /**< \brief (ISC_CBC_CFG) CCIR656 Stream Enable */
#define ISC_CBC_CFG_CCIRMODE_Pos 1
#define ISC_CBC_CFG_CCIRMODE_Msk (0x3u << ISC_CBC_CFG_CCIRMODE_Pos) /**< \brief (ISC_CBC_CFG) CCIR656 Byte Ordering */
#define ISC_CBC_CFG_CCIRMODE(value) ((ISC_CBC_CFG_CCIRMODE_Msk & ((value) << ISC_CBC_CFG_CCIRMODE_Pos)))
#define   ISC_CBC_CFG_CCIRMODE_CBY (0x0u << 1) /**< \brief (ISC_CBC_CFG) Byte ordering Cb0, Y0, Cr0, Y1 */
#define   ISC_CBC_CFG_CCIRMODE_CRY (0x1u << 1) /**< \brief (ISC_CBC_CFG) Byte ordering Cr0, Y0, Cb0, Y1 */
#define   ISC_CBC_CFG_CCIRMODE_YCB (0x2u << 1) /**< \brief (ISC_CBC_CFG) Byte ordering Y0, Cb0, Y1, Cr0 */
#define   ISC_CBC_CFG_CCIRMODE_YCR (0x3u << 1) /**< \brief (ISC_CBC_CFG) Byte ordering Y0, Cr0, Y1, Cb0 */
/* -------- ISC_CBC_BRIGHT : (ISC Offset: 0x3BC) Contrast and Brightness, Brightness Register -------- */
#define ISC_CBC_BRIGHT_BRIGHT_Pos 0
#define ISC_CBC_BRIGHT_BRIGHT_Msk (0x7ffu << ISC_CBC_BRIGHT_BRIGHT_Pos) /**< \brief (ISC_CBC_BRIGHT) Brightness Control (signed 11 bits 1:10:0) */
#define ISC_CBC_BRIGHT_BRIGHT(value) ((ISC_CBC_BRIGHT_BRIGHT_Msk & ((value) << ISC_CBC_BRIGHT_BRIGHT_Pos)))
/* -------- ISC_CBC_CONTRAST : (ISC Offset: 0x3C0) Contrast and Brightness, Contrast Register -------- */
#define ISC_CBC_CONTRAST_CONTRAST_Pos 0
#define ISC_CBC_CONTRAST_CONTRAST_Msk (0xfffu << ISC_CBC_CONTRAST_CONTRAST_Pos) /**< \brief (ISC_CBC_CONTRAST) Contrast (signed 12 bits 1:3:8) */
#define ISC_CBC_CONTRAST_CONTRAST(value) ((ISC_CBC_CONTRAST_CONTRAST_Msk & ((value) << ISC_CBC_CONTRAST_CONTRAST_Pos)))
/* -------- ISC_SUB422_CTRL : (ISC Offset: 0x3C4) Subsampling 4:4:4 to 4:2:2 Control Register -------- */
#define ISC_SUB422_CTRL_ENABLE (0x1u << 0) /**< \brief (ISC_SUB422_CTRL) 4:4:4 to 4:2:2 Chrominance Horizontal Subsampling Filter Enable */
/* -------- ISC_SUB422_CFG : (ISC Offset: 0x3C8) Subsampling 4:4:4 to 4:2:2 Configuration Register -------- */
#define ISC_SUB422_CFG_CCIR (0x1u << 0) /**< \brief (ISC_SUB422_CFG) CCIR656 Input Stream */
#define ISC_SUB422_CFG_CCIRMODE_Pos 1
#define ISC_SUB422_CFG_CCIRMODE_Msk (0x3u << ISC_SUB422_CFG_CCIRMODE_Pos) /**< \brief (ISC_SUB422_CFG) CCIR656 Byte Ordering */
#define ISC_SUB422_CFG_CCIRMODE(value) ((ISC_SUB422_CFG_CCIRMODE_Msk & ((value) << ISC_SUB422_CFG_CCIRMODE_Pos)))
#define   ISC_SUB422_CFG_CCIRMODE_CBY (0x0u << 1) /**< \brief (ISC_SUB422_CFG) Byte ordering Cb0, Y0, Cr0, Y1 */
#define   ISC_SUB422_CFG_CCIRMODE_CRY (0x1u << 1) /**< \brief (ISC_SUB422_CFG) Byte ordering Cr0, Y0, Cb0, Y1 */
#define   ISC_SUB422_CFG_CCIRMODE_YCB (0x2u << 1) /**< \brief (ISC_SUB422_CFG) Byte ordering Y0, Cb0, Y1, Cr0 */
#define   ISC_SUB422_CFG_CCIRMODE_YCR (0x3u << 1) /**< \brief (ISC_SUB422_CFG) Byte ordering Y0, Cr0, Y1, Cb0 */
#define ISC_SUB422_CFG_FILTER_Pos 4
#define ISC_SUB422_CFG_FILTER_Msk (0x3u << ISC_SUB422_CFG_FILTER_Pos) /**< \brief (ISC_SUB422_CFG) Low Pass Filter Selection */
#define ISC_SUB422_CFG_FILTER(value) ((ISC_SUB422_CFG_FILTER_Msk & ((value) << ISC_SUB422_CFG_FILTER_Pos)))
#define   ISC_SUB422_CFG_FILTER_FILT0CO (0x0u << 4) /**< \brief (ISC_SUB422_CFG) Cosited, {1} */
#define   ISC_SUB422_CFG_FILTER_FILT1CE (0x1u << 4) /**< \brief (ISC_SUB422_CFG) Centered {1, 1} */
#define   ISC_SUB422_CFG_FILTER_FILT2CO (0x2u << 4) /**< \brief (ISC_SUB422_CFG) Cosited {1,2,1} */
#define   ISC_SUB422_CFG_FILTER_FILT3CE (0x3u << 4) /**< \brief (ISC_SUB422_CFG) Centered {1, 3, 3, 1} */
/* -------- ISC_SUB420_CTRL : (ISC Offset: 0x3CC) Subsampling 4:2:2 to 4:2:0 Control Register -------- */
#define ISC_SUB420_CTRL_ENABLE (0x1u << 0) /**< \brief (ISC_SUB420_CTRL) 4:2:2 to 4:2:0 Vertical Subsampling Filter Enable (Center Aligned) */
#define ISC_SUB420_CTRL_FILTER (0x1u << 4) /**< \brief (ISC_SUB420_CTRL) Interlaced or Progressive Chrominance Filter */
/* -------- ISC_RLP_CFG : (ISC Offset: 0x3D0) Rounding, Limiting and Packing Config Register -------- */
#define ISC_RLP_CFG_MODE_Pos 0
#define ISC_RLP_CFG_MODE_Msk (0xfu << ISC_RLP_CFG_MODE_Pos) /**< \brief (ISC_RLP_CFG) Rounding, Limiting and Packing Mode */
#define ISC_RLP_CFG_MODE(value) ((ISC_RLP_CFG_MODE_Msk & ((value) << ISC_RLP_CFG_MODE_Pos)))
#define   ISC_RLP_CFG_MODE_DAT8 (0x0u << 0) /**< \brief (ISC_RLP_CFG) 8-bit data */
#define   ISC_RLP_CFG_MODE_DAT9 (0x1u << 0) /**< \brief (ISC_RLP_CFG) 9-bit data */
#define   ISC_RLP_CFG_MODE_DAT10 (0x2u << 0) /**< \brief (ISC_RLP_CFG) 10-bit data */
#define   ISC_RLP_CFG_MODE_DAT11 (0x3u << 0) /**< \brief (ISC_RLP_CFG) 11-bit data */
#define   ISC_RLP_CFG_MODE_DAT12 (0x4u << 0) /**< \brief (ISC_RLP_CFG) 12-bit data */
#define   ISC_RLP_CFG_MODE_DATY8 (0x5u << 0) /**< \brief (ISC_RLP_CFG) 8-bit luminance only */
#define   ISC_RLP_CFG_MODE_DATY10 (0x6u << 0) /**< \brief (ISC_RLP_CFG) 10-bit luminance only */
#define   ISC_RLP_CFG_MODE_ARGB444 (0x7u << 0) /**< \brief (ISC_RLP_CFG) 12-bit RGB+4-bit Alpha (MSB) */
#define   ISC_RLP_CFG_MODE_ARGB555 (0x8u << 0) /**< \brief (ISC_RLP_CFG) 15-bit RGB+1-bit Alpha (MSB) */
#define   ISC_RLP_CFG_MODE_RGB565 (0x9u << 0) /**< \brief (ISC_RLP_CFG) 16-bit RGB */
#define   ISC_RLP_CFG_MODE_ARGB32 (0xAu << 0) /**< \brief (ISC_RLP_CFG) 24-bits RGB mode+8-bit Alpha */
#define   ISC_RLP_CFG_MODE_YYCC (0xBu << 0) /**< \brief (ISC_RLP_CFG) YCbCr mode (full range, [0-255]) */
#define   ISC_RLP_CFG_MODE_YYCC_LIMITED (0xCu << 0) /**< \brief (ISC_RLP_CFG) YCbCr mode (limited range) */
#define ISC_RLP_CFG_ALPHA_Pos 8
#define ISC_RLP_CFG_ALPHA_Msk (0xffu << ISC_RLP_CFG_ALPHA_Pos) /**< \brief (ISC_RLP_CFG) Alpha Value for Alpha-enabled RGB Mode */
#define ISC_RLP_CFG_ALPHA(value) ((ISC_RLP_CFG_ALPHA_Msk & ((value) << ISC_RLP_CFG_ALPHA_Pos)))
/* -------- ISC_HIS_CTRL : (ISC Offset: 0x3D4) Histogram Control Register -------- */
#define ISC_HIS_CTRL_ENABLE (0x1u << 0) /**< \brief (ISC_HIS_CTRL) Histogram Sub Module Enable */
/* -------- ISC_HIS_CFG : (ISC Offset: 0x3D8) Histogram Configuration Register -------- */
#define ISC_HIS_CFG_MODE_Pos 0
#define ISC_HIS_CFG_MODE_Msk (0x7u << ISC_HIS_CFG_MODE_Pos) /**< \brief (ISC_HIS_CFG) Histogram Operating Mode */
#define ISC_HIS_CFG_MODE(value) ((ISC_HIS_CFG_MODE_Msk & ((value) << ISC_HIS_CFG_MODE_Pos)))
#define   ISC_HIS_CFG_MODE_Gr (0x0u << 0) /**< \brief (ISC_HIS_CFG) Gr sampling */
#define   ISC_HIS_CFG_MODE_R (0x1u << 0) /**< \brief (ISC_HIS_CFG) R sampling */
#define   ISC_HIS_CFG_MODE_Gb (0x2u << 0) /**< \brief (ISC_HIS_CFG) Gb sampling */
#define   ISC_HIS_CFG_MODE_B (0x3u << 0) /**< \brief (ISC_HIS_CFG) B sampling */
#define   ISC_HIS_CFG_MODE_Y (0x4u << 0) /**< \brief (ISC_HIS_CFG) Luminance-only mode */
#define   ISC_HIS_CFG_MODE_RAW (0x5u << 0) /**< \brief (ISC_HIS_CFG) Raw sampling */
#define   ISC_HIS_CFG_MODE_YCCIR656 (0x6u << 0) /**< \brief (ISC_HIS_CFG) Luminance only with CCIR656 10-bit or 8-bit mode */
#define ISC_HIS_CFG_BAYSEL_Pos 4
#define ISC_HIS_CFG_BAYSEL_Msk (0x3u << ISC_HIS_CFG_BAYSEL_Pos) /**< \brief (ISC_HIS_CFG) Bayer Color Component Selection */
#define ISC_HIS_CFG_BAYSEL(value) ((ISC_HIS_CFG_BAYSEL_Msk & ((value) << ISC_HIS_CFG_BAYSEL_Pos)))
#define   ISC_HIS_CFG_BAYSEL_GRGR (0x0u << 4) /**< \brief (ISC_HIS_CFG) Starting row configuration is G R G R (red row) */
#define   ISC_HIS_CFG_BAYSEL_RGRG (0x1u << 4) /**< \brief (ISC_HIS_CFG) Starting row configuration is R G R G (red row */
#define   ISC_HIS_CFG_BAYSEL_GBGB (0x2u << 4) /**< \brief (ISC_HIS_CFG) Starting row configuration is G B G B (blue row */
#define   ISC_HIS_CFG_BAYSEL_BGBG (0x3u << 4) /**< \brief (ISC_HIS_CFG) Starting row configuration is B G B G (blue row) */
#define ISC_HIS_CFG_RAR (0x1u << 8) /**< \brief (ISC_HIS_CFG) Histogram Reset After Read */
/* -------- ISC_DCFG : (ISC Offset: 0x3E0) DMA Configuration Register -------- */
#define ISC_DCFG_IMODE_Pos 0
#define ISC_DCFG_IMODE_Msk (0x7u << ISC_DCFG_IMODE_Pos) /**< \brief (ISC_DCFG) DMA Input Mode Selection */
#define ISC_DCFG_IMODE(value) ((ISC_DCFG_IMODE_Msk & ((value) << ISC_DCFG_IMODE_Pos)))
#define   ISC_DCFG_IMODE_PACKED8 (0x0u << 0) /**< \brief (ISC_DCFG) 8 bits, single channel packed */
#define   ISC_DCFG_IMODE_PACKED16 (0x1u << 0) /**< \brief (ISC_DCFG) 16 bits, single channel packed */
#define   ISC_DCFG_IMODE_PACKED32 (0x2u << 0) /**< \brief (ISC_DCFG) 32 bits, single channel packed */
#define   ISC_DCFG_IMODE_YC422SP (0x3u << 0) /**< \brief (ISC_DCFG) 32 bits, dual channel */
#define   ISC_DCFG_IMODE_YC422P (0x4u << 0) /**< \brief (ISC_DCFG) 32 bits, triple channel */
#define   ISC_DCFG_IMODE_YC420SP (0x5u << 0) /**< \brief (ISC_DCFG) 32 bits, dual channel */
#define   ISC_DCFG_IMODE_YC420P (0x6u << 0) /**< \brief (ISC_DCFG) 32 bits, triple channel */
#define ISC_DCFG_YMBSIZE_Pos 4
#define ISC_DCFG_YMBSIZE_Msk (0x3u << ISC_DCFG_YMBSIZE_Pos) /**< \brief (ISC_DCFG) DMA Memory Burst Size Y channel */
#define ISC_DCFG_YMBSIZE(value) ((ISC_DCFG_YMBSIZE_Msk & ((value) << ISC_DCFG_YMBSIZE_Pos)))
#define   ISC_DCFG_YMBSIZE_SINGLE (0x0u << 4) /**< \brief (ISC_DCFG) DMA single access */
#define   ISC_DCFG_YMBSIZE_BEATS4 (0x1u << 4) /**< \brief (ISC_DCFG) 4-beat burst access */
#define   ISC_DCFG_YMBSIZE_BEATS8 (0x2u << 4) /**< \brief (ISC_DCFG) 8-beat burst access */
#define   ISC_DCFG_YMBSIZE_BEATS16 (0x3u << 4) /**< \brief (ISC_DCFG) 16-beat burst access */
#define ISC_DCFG_CMBSIZE_Pos 8
#define ISC_DCFG_CMBSIZE_Msk (0x3u << ISC_DCFG_CMBSIZE_Pos) /**< \brief (ISC_DCFG) DMA Memory Burst Size C channel */
#define ISC_DCFG_CMBSIZE(value) ((ISC_DCFG_CMBSIZE_Msk & ((value) << ISC_DCFG_CMBSIZE_Pos)))
#define   ISC_DCFG_CMBSIZE_SINGLE (0x0u << 8) /**< \brief (ISC_DCFG) DMA single access */
#define   ISC_DCFG_CMBSIZE_BEATS4 (0x1u << 8) /**< \brief (ISC_DCFG) 4-beat burst access */
#define   ISC_DCFG_CMBSIZE_BEATS8 (0x2u << 8) /**< \brief (ISC_DCFG) 8-beat burst access */
#define   ISC_DCFG_CMBSIZE_BEATS16 (0x3u << 8) /**< \brief (ISC_DCFG) 16-beat burst access */
/* -------- ISC_DCTRL : (ISC Offset: 0x3E4) DMA Control Register -------- */
#define ISC_DCTRL_DE (0x1u << 0) /**< \brief (ISC_DCTRL) Descriptor Enable */
#define ISC_DCTRL_DVIEW_Pos 1
#define ISC_DCTRL_DVIEW_Msk (0x3u << ISC_DCTRL_DVIEW_Pos) /**< \brief (ISC_DCTRL) Descriptor View */
#define ISC_DCTRL_DVIEW(value) ((ISC_DCTRL_DVIEW_Msk & ((value) << ISC_DCTRL_DVIEW_Pos)))
#define   ISC_DCTRL_DVIEW_PACKED (0x0u << 1) /**< \brief (ISC_DCTRL) Address {0} Stride {0} are updated */
#define   ISC_DCTRL_DVIEW_SEMIPLANAR (0x1u << 1) /**< \brief (ISC_DCTRL) Address {0,1} Stride {0,1} are updated */
#define   ISC_DCTRL_DVIEW_PLANAR (0x2u << 1) /**< \brief (ISC_DCTRL) Address {0,1,2} Stride {0,1,2} are updated */
#define ISC_DCTRL_IE (0x1u << 4) /**< \brief (ISC_DCTRL) Interrupt Enable */
#define ISC_DCTRL_WB (0x1u << 5) /**< \brief (ISC_DCTRL) Write Back Operation Enable */
/* -------- ISC_DNDA : (ISC Offset: 0x3E8) DMA Descriptor Address Register -------- */
#define ISC_DNDA_NDA_Pos 2
#define ISC_DNDA_NDA_Msk (0x3fffffffu << ISC_DNDA_NDA_Pos) /**< \brief (ISC_DNDA) Next Descriptor Address Register */
#define ISC_DNDA_NDA(value) ((ISC_DNDA_NDA_Msk & ((value) << ISC_DNDA_NDA_Pos)))
/* -------- ISC_DAD : (ISC Offset: N/A) DMA Address 0 Register -------- */
#define ISC_DAD_AD0_Pos 0
#define ISC_DAD_AD0_Msk (0xffffffffu << ISC_DAD_AD0_Pos) /**< \brief (ISC_DAD) Channel 0 Address */
#define ISC_DAD_AD0(value) ((ISC_DAD_AD0_Msk & ((value) << ISC_DAD_AD0_Pos)))
/* -------- ISC_DST : (ISC Offset: N/A) DMA Stride 0 Register -------- */
#define ISC_DST_ST0_Pos 0
#define ISC_DST_ST0_Msk (0xffffffffu << ISC_DST_ST0_Pos) /**< \brief (ISC_DST) Channel 0 Stride */
#define ISC_DST_ST0(value) ((ISC_DST_ST0_Msk & ((value) << ISC_DST_ST0_Pos)))
/* -------- IPB_VERSION : (ISC Offset: 0x40C) Version Register -------- */
#define IPB_VERSION_VERSION_Pos 0
#define IPB_VERSION_VERSION_Msk (0xfffu << IPB_VERSION_VERSION_Pos) /**< \brief (IPB_VERSION)  */
#define IPB_VERSION_MFN_Pos 16
#define IPB_VERSION_MFN_Msk (0x7u << IPB_VERSION_MFN_Pos) /**< \brief (IPB_VERSION)  */
/* -------- ISC_HIS_ENTRY[512] : (ISC Offset: 0x410) Histogram Entry -------- */
#define ISC_HIS_ENTRY_COUNT_Pos 0
#define ISC_HIS_ENTRY_COUNT_Msk (0xfffffu << ISC_HIS_ENTRY_COUNT_Pos) /**< \brief (ISC_HIS_ENTRY[512]) Entry Counter */

/*@}*/


#endif /* _SAMA5D2_ISC_COMPONENT_ */
