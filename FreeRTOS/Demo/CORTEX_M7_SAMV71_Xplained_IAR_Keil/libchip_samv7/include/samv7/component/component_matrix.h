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

#ifndef _SAM_MATRIX_COMPONENT_
#define _SAM_MATRIX_COMPONENT_

/* ============================================================================= */
/**  SOFTWARE API DEFINITION FOR AHB Bus Matrix */
/* ============================================================================= */
/** \addtogroup SAM_MATRIX AHB Bus Matrix */
/*@{*/

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
/** \brief MatrixPr hardware registers */
typedef struct {
  __IO uint32_t MATRIX_PRAS; /**< \brief (MatrixPr Offset: 0x0) Priority Register A for Slave 0 */
  __IO uint32_t MATRIX_PRBS; /**< \brief (MatrixPr Offset: 0x4) Priority Register B for Slave 0 */
} MatrixPr;
/** \brief Matrix hardware registers */
#define MATRIXPR_NUMBER 16
typedef struct {
  __IO uint32_t MATRIX_MCFG[16];            /**< \brief (Matrix Offset: 0x0000) Master Configuration Register */
  __IO uint32_t MATRIX_SCFG[16];            /**< \brief (Matrix Offset: 0x0040) Slave Configuration Register */
       MatrixPr MATRIX_PR[MATRIXPR_NUMBER]; /**< \brief (Matrix Offset: 0x0080) 0 .. 15 */
  __IO uint32_t MATRIX_MRCR;                /**< \brief (Matrix Offset: 0x0100) Master Remap Control Register */
  __I  uint32_t Reserved1[3];
  __IO uint32_t MATRIX_SFR[16];             /**< \brief (Matrix Offset: 0x0110) Special Function Register */
  __O  uint32_t MATRIX_MEIER;               /**< \brief (Matrix Offset: 0x0150) Master Error Interrupt Enable Register */
  __O  uint32_t MATRIX_MEIDR;               /**< \brief (Matrix Offset: 0x0154) Master Error Interrupt Disable Register */
  __I  uint32_t MATRIX_MEIMR;               /**< \brief (Matrix Offset: 0x0158) Master Error Interrupt Mask Register */
  __I  uint32_t MATRIX_MESR;                /**< \brief (Matrix Offset: 0x015C) Master Error Status Register */
  __I  uint32_t MATRIX_MEAR[16];            /**< \brief (Matrix Offset: 0x0160) Master 0 Error Address Register */
  __I  uint32_t Reserved2[17];
  __IO uint32_t MATRIX_WPMR;                /**< \brief (Matrix Offset: 0x01E4) Write Protect Mode Register */
  __I  uint32_t MATRIX_WPSR;                /**< \brief (Matrix Offset: 0x01E8) Write Protect Status Register */
  __I  uint32_t Reserved3[4];
  __I  uint32_t MATRIX_VERSION;             /**< \brief (Matrix Offset: 0x01FC) Version Register */
  __IO uint32_t MATRIX_SSR[16];             /**< \brief (Matrix Offset: 0x0200) Security Slave 0 Register */
  __IO uint32_t MATRIX_SASSR[16];           /**< \brief (Matrix Offset: 0x0240) Security Areas Split Slave 0 Register */
  __IO uint32_t MATRIX_SRTSR[16];           /**< \brief (Matrix Offset: 0x0280) Security Region Top Slave 0 Register */
  __IO uint32_t MATRIX_SPSELR[3];           /**< \brief (Matrix Offset: 0x02C0) Security Peripheral Select 1 Register */
} Matrix;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */
/* -------- MATRIX_MCFG[16] : (MATRIX Offset: 0x0000) Master Configuration Register -------- */
#define MATRIX_MCFG_ULBT_Pos 0
#define MATRIX_MCFG_ULBT_Msk (0x7u << MATRIX_MCFG_ULBT_Pos) /**< \brief (MATRIX_MCFG[16]) Undefined Length Burst Type */
#define MATRIX_MCFG_ULBT(value) ((MATRIX_MCFG_ULBT_Msk & ((value) << MATRIX_MCFG_ULBT_Pos)))
/* -------- MATRIX_SCFG[16] : (MATRIX Offset: 0x0040) Slave Configuration Register -------- */
#define MATRIX_SCFG_SLOT_CYCLE_Pos 0
#define MATRIX_SCFG_SLOT_CYCLE_Msk (0x1ffu << MATRIX_SCFG_SLOT_CYCLE_Pos) /**< \brief (MATRIX_SCFG[16]) Maximum Bus Grant Duration for Masters */
#define MATRIX_SCFG_SLOT_CYCLE(value) ((MATRIX_SCFG_SLOT_CYCLE_Msk & ((value) << MATRIX_SCFG_SLOT_CYCLE_Pos)))
#define MATRIX_SCFG_DEFMSTR_TYPE_Pos 16
#define MATRIX_SCFG_DEFMSTR_TYPE_Msk (0x3u << MATRIX_SCFG_DEFMSTR_TYPE_Pos) /**< \brief (MATRIX_SCFG[16]) Default Master Type */
#define MATRIX_SCFG_DEFMSTR_TYPE(value) ((MATRIX_SCFG_DEFMSTR_TYPE_Msk & ((value) << MATRIX_SCFG_DEFMSTR_TYPE_Pos)))
#define MATRIX_SCFG_FIXED_DEFMSTR_Pos 18
#define MATRIX_SCFG_FIXED_DEFMSTR_Msk (0xfu << MATRIX_SCFG_FIXED_DEFMSTR_Pos) /**< \brief (MATRIX_SCFG[16]) Fixed Default Master */
#define MATRIX_SCFG_FIXED_DEFMSTR(value) ((MATRIX_SCFG_FIXED_DEFMSTR_Msk & ((value) << MATRIX_SCFG_FIXED_DEFMSTR_Pos)))
/* -------- MATRIX_PRAS : (MATRIX Offset: N/A) Priority Register A for Slave 0 -------- */
#define MATRIX_PRAS_M0PR_Pos 0
#define MATRIX_PRAS_M0PR_Msk (0x3u << MATRIX_PRAS_M0PR_Pos) /**< \brief (MATRIX_PRAS) Master 0 Priority */
#define MATRIX_PRAS_M0PR(value) ((MATRIX_PRAS_M0PR_Msk & ((value) << MATRIX_PRAS_M0PR_Pos)))
#define MATRIX_PRAS_M1PR_Pos 4
#define MATRIX_PRAS_M1PR_Msk (0x3u << MATRIX_PRAS_M1PR_Pos) /**< \brief (MATRIX_PRAS) Master 1 Priority */
#define MATRIX_PRAS_M1PR(value) ((MATRIX_PRAS_M1PR_Msk & ((value) << MATRIX_PRAS_M1PR_Pos)))
#define MATRIX_PRAS_M2PR_Pos 8
#define MATRIX_PRAS_M2PR_Msk (0x3u << MATRIX_PRAS_M2PR_Pos) /**< \brief (MATRIX_PRAS) Master 2 Priority */
#define MATRIX_PRAS_M2PR(value) ((MATRIX_PRAS_M2PR_Msk & ((value) << MATRIX_PRAS_M2PR_Pos)))
#define MATRIX_PRAS_M3PR_Pos 12
#define MATRIX_PRAS_M3PR_Msk (0x3u << MATRIX_PRAS_M3PR_Pos) /**< \brief (MATRIX_PRAS) Master 3 Priority */
#define MATRIX_PRAS_M3PR(value) ((MATRIX_PRAS_M3PR_Msk & ((value) << MATRIX_PRAS_M3PR_Pos)))
#define MATRIX_PRAS_M4PR_Pos 16
#define MATRIX_PRAS_M4PR_Msk (0x3u << MATRIX_PRAS_M4PR_Pos) /**< \brief (MATRIX_PRAS) Master 4 Priority */
#define MATRIX_PRAS_M4PR(value) ((MATRIX_PRAS_M4PR_Msk & ((value) << MATRIX_PRAS_M4PR_Pos)))
#define MATRIX_PRAS_M5PR_Pos 20
#define MATRIX_PRAS_M5PR_Msk (0x3u << MATRIX_PRAS_M5PR_Pos) /**< \brief (MATRIX_PRAS) Master 5 Priority */
#define MATRIX_PRAS_M5PR(value) ((MATRIX_PRAS_M5PR_Msk & ((value) << MATRIX_PRAS_M5PR_Pos)))
#define MATRIX_PRAS_M6PR_Pos 24
#define MATRIX_PRAS_M6PR_Msk (0x3u << MATRIX_PRAS_M6PR_Pos) /**< \brief (MATRIX_PRAS) Master 6 Priority */
#define MATRIX_PRAS_M6PR(value) ((MATRIX_PRAS_M6PR_Msk & ((value) << MATRIX_PRAS_M6PR_Pos)))
#define MATRIX_PRAS_M7PR_Pos 28
#define MATRIX_PRAS_M7PR_Msk (0x3u << MATRIX_PRAS_M7PR_Pos) /**< \brief (MATRIX_PRAS) Master 7 Priority */
#define MATRIX_PRAS_M7PR(value) ((MATRIX_PRAS_M7PR_Msk & ((value) << MATRIX_PRAS_M7PR_Pos)))
/* -------- MATRIX_PRBS : (MATRIX Offset: N/A) Priority Register B for Slave 0 -------- */
#define MATRIX_PRBS_M8PR_Pos 0
#define MATRIX_PRBS_M8PR_Msk (0x3u << MATRIX_PRBS_M8PR_Pos) /**< \brief (MATRIX_PRBS) Master 8 Priority */
#define MATRIX_PRBS_M8PR(value) ((MATRIX_PRBS_M8PR_Msk & ((value) << MATRIX_PRBS_M8PR_Pos)))
#define MATRIX_PRBS_M9PR_Pos 4
#define MATRIX_PRBS_M9PR_Msk (0x3u << MATRIX_PRBS_M9PR_Pos) /**< \brief (MATRIX_PRBS) Master 9 Priority */
#define MATRIX_PRBS_M9PR(value) ((MATRIX_PRBS_M9PR_Msk & ((value) << MATRIX_PRBS_M9PR_Pos)))
#define MATRIX_PRBS_M10PR_Pos 8
#define MATRIX_PRBS_M10PR_Msk (0x3u << MATRIX_PRBS_M10PR_Pos) /**< \brief (MATRIX_PRBS) Master 10 Priority */
#define MATRIX_PRBS_M10PR(value) ((MATRIX_PRBS_M10PR_Msk & ((value) << MATRIX_PRBS_M10PR_Pos)))
#define MATRIX_PRBS_M11PR_Pos 12
#define MATRIX_PRBS_M11PR_Msk (0x3u << MATRIX_PRBS_M11PR_Pos) /**< \brief (MATRIX_PRBS) Master 11 Priority */
#define MATRIX_PRBS_M11PR(value) ((MATRIX_PRBS_M11PR_Msk & ((value) << MATRIX_PRBS_M11PR_Pos)))
#define MATRIX_PRBS_M12PR_Pos 16
#define MATRIX_PRBS_M12PR_Msk (0x3u << MATRIX_PRBS_M12PR_Pos) /**< \brief (MATRIX_PRBS) Master 12 Priority */
#define MATRIX_PRBS_M12PR(value) ((MATRIX_PRBS_M12PR_Msk & ((value) << MATRIX_PRBS_M12PR_Pos)))
#define MATRIX_PRBS_M13PR_Pos 20
#define MATRIX_PRBS_M13PR_Msk (0x3u << MATRIX_PRBS_M13PR_Pos) /**< \brief (MATRIX_PRBS) Master 13 Priority */
#define MATRIX_PRBS_M13PR(value) ((MATRIX_PRBS_M13PR_Msk & ((value) << MATRIX_PRBS_M13PR_Pos)))
#define MATRIX_PRBS_M14PR_Pos 24
#define MATRIX_PRBS_M14PR_Msk (0x3u << MATRIX_PRBS_M14PR_Pos) /**< \brief (MATRIX_PRBS) Master 14 Priority */
#define MATRIX_PRBS_M14PR(value) ((MATRIX_PRBS_M14PR_Msk & ((value) << MATRIX_PRBS_M14PR_Pos)))
#define MATRIX_PRBS_M15PR_Pos 28
#define MATRIX_PRBS_M15PR_Msk (0x3u << MATRIX_PRBS_M15PR_Pos) /**< \brief (MATRIX_PRBS) Master 15 Priority */
#define MATRIX_PRBS_M15PR(value) ((MATRIX_PRBS_M15PR_Msk & ((value) << MATRIX_PRBS_M15PR_Pos)))
/* -------- MATRIX_MRCR : (MATRIX Offset: 0x0100) Master Remap Control Register -------- */
#define MATRIX_MRCR_RCB0 (0x1u << 0) /**< \brief (MATRIX_MRCR)  */
#define MATRIX_MRCR_RCB1 (0x1u << 1) /**< \brief (MATRIX_MRCR)  */
#define MATRIX_MRCR_RCB2 (0x1u << 2) /**< \brief (MATRIX_MRCR)  */
#define MATRIX_MRCR_RCB3 (0x1u << 3) /**< \brief (MATRIX_MRCR)  */
#define MATRIX_MRCR_RCB4 (0x1u << 4) /**< \brief (MATRIX_MRCR)  */
#define MATRIX_MRCR_RCB5 (0x1u << 5) /**< \brief (MATRIX_MRCR)  */
#define MATRIX_MRCR_RCB6 (0x1u << 6) /**< \brief (MATRIX_MRCR)  */
#define MATRIX_MRCR_RCB7 (0x1u << 7) /**< \brief (MATRIX_MRCR)  */
#define MATRIX_MRCR_RCB8 (0x1u << 8) /**< \brief (MATRIX_MRCR)  */
#define MATRIX_MRCR_RCB9 (0x1u << 9) /**< \brief (MATRIX_MRCR)  */
#define MATRIX_MRCR_RCB10 (0x1u << 10) /**< \brief (MATRIX_MRCR)  */
#define MATRIX_MRCR_RCB11 (0x1u << 11) /**< \brief (MATRIX_MRCR)  */
#define MATRIX_MRCR_RCB12 (0x1u << 12) /**< \brief (MATRIX_MRCR)  */
#define MATRIX_MRCR_RCB13 (0x1u << 13) /**< \brief (MATRIX_MRCR)  */
#define MATRIX_MRCR_RCB14 (0x1u << 14) /**< \brief (MATRIX_MRCR)  */
#define MATRIX_MRCR_RCB15 (0x1u << 15) /**< \brief (MATRIX_MRCR)  */
/* -------- MATRIX_SFR[16] : (MATRIX Offset: 0x0110) Special Function Register -------- */
#define MATRIX_SFR_SFR_Pos 0
#define MATRIX_SFR_SFR_Msk (0xffffffffu << MATRIX_SFR_SFR_Pos) /**< \brief (MATRIX_SFR[16]) Special Function Register Fields */
#define MATRIX_SFR_SFR(value) ((MATRIX_SFR_SFR_Msk & ((value) << MATRIX_SFR_SFR_Pos)))
/* -------- MATRIX_MEIER : (MATRIX Offset: 0x0150) Master Error Interrupt Enable Register -------- */
#define MATRIX_MEIER_MERR0 (0x1u << 0) /**< \brief (MATRIX_MEIER) Master 0 Access Error */
#define MATRIX_MEIER_MERR1 (0x1u << 1) /**< \brief (MATRIX_MEIER) Master 1 Access Error */
#define MATRIX_MEIER_MERR2 (0x1u << 2) /**< \brief (MATRIX_MEIER) Master 2 Access Error */
#define MATRIX_MEIER_MERR3 (0x1u << 3) /**< \brief (MATRIX_MEIER) Master 3 Access Error */
#define MATRIX_MEIER_MERR4 (0x1u << 4) /**< \brief (MATRIX_MEIER) Master 4 Access Error */
#define MATRIX_MEIER_MERR5 (0x1u << 5) /**< \brief (MATRIX_MEIER) Master 5 Access Error */
#define MATRIX_MEIER_MERR6 (0x1u << 6) /**< \brief (MATRIX_MEIER) Master 6 Access Error */
#define MATRIX_MEIER_MERR7 (0x1u << 7) /**< \brief (MATRIX_MEIER) Master 7 Access Error */
#define MATRIX_MEIER_MERR8 (0x1u << 8) /**< \brief (MATRIX_MEIER) Master 8 Access Error */
#define MATRIX_MEIER_MERR9 (0x1u << 9) /**< \brief (MATRIX_MEIER) Master 9 Access Error */
#define MATRIX_MEIER_MERR10 (0x1u << 10) /**< \brief (MATRIX_MEIER) Master 10 Access Error */
#define MATRIX_MEIER_MERR11 (0x1u << 11) /**< \brief (MATRIX_MEIER) Master 11 Access Error */
#define MATRIX_MEIER_MERR12 (0x1u << 12) /**< \brief (MATRIX_MEIER) Master 12 Access Error */
#define MATRIX_MEIER_MERR13 (0x1u << 13) /**< \brief (MATRIX_MEIER) Master 13 Access Error */
#define MATRIX_MEIER_MERR14 (0x1u << 14) /**< \brief (MATRIX_MEIER) Master 14 Access Error */
#define MATRIX_MEIER_MERR15 (0x1u << 15) /**< \brief (MATRIX_MEIER) Master 15 Access Error */
/* -------- MATRIX_MEIDR : (MATRIX Offset: 0x0154) Master Error Interrupt Disable Register -------- */
#define MATRIX_MEIDR_MERR0 (0x1u << 0) /**< \brief (MATRIX_MEIDR) Master 0 Access Error */
#define MATRIX_MEIDR_MERR1 (0x1u << 1) /**< \brief (MATRIX_MEIDR) Master 1 Access Error */
#define MATRIX_MEIDR_MERR2 (0x1u << 2) /**< \brief (MATRIX_MEIDR) Master 2 Access Error */
#define MATRIX_MEIDR_MERR3 (0x1u << 3) /**< \brief (MATRIX_MEIDR) Master 3 Access Error */
#define MATRIX_MEIDR_MERR4 (0x1u << 4) /**< \brief (MATRIX_MEIDR) Master 4 Access Error */
#define MATRIX_MEIDR_MERR5 (0x1u << 5) /**< \brief (MATRIX_MEIDR) Master 5 Access Error */
#define MATRIX_MEIDR_MERR6 (0x1u << 6) /**< \brief (MATRIX_MEIDR) Master 6 Access Error */
#define MATRIX_MEIDR_MERR7 (0x1u << 7) /**< \brief (MATRIX_MEIDR) Master 7 Access Error */
#define MATRIX_MEIDR_MERR8 (0x1u << 8) /**< \brief (MATRIX_MEIDR) Master 8 Access Error */
#define MATRIX_MEIDR_MERR9 (0x1u << 9) /**< \brief (MATRIX_MEIDR) Master 9 Access Error */
#define MATRIX_MEIDR_MERR10 (0x1u << 10) /**< \brief (MATRIX_MEIDR) Master 10 Access Error */
#define MATRIX_MEIDR_MERR11 (0x1u << 11) /**< \brief (MATRIX_MEIDR) Master 11 Access Error */
#define MATRIX_MEIDR_MERR12 (0x1u << 12) /**< \brief (MATRIX_MEIDR) Master 12 Access Error */
#define MATRIX_MEIDR_MERR13 (0x1u << 13) /**< \brief (MATRIX_MEIDR) Master 13 Access Error */
#define MATRIX_MEIDR_MERR14 (0x1u << 14) /**< \brief (MATRIX_MEIDR) Master 14 Access Error */
#define MATRIX_MEIDR_MERR15 (0x1u << 15) /**< \brief (MATRIX_MEIDR) Master 15 Access Error */
/* -------- MATRIX_MEIMR : (MATRIX Offset: 0x0158) Master Error Interrupt Mask Register -------- */
#define MATRIX_MEIMR_MERR0 (0x1u << 0) /**< \brief (MATRIX_MEIMR) Master 0 Access Error */
#define MATRIX_MEIMR_MERR1 (0x1u << 1) /**< \brief (MATRIX_MEIMR) Master 1 Access Error */
#define MATRIX_MEIMR_MERR2 (0x1u << 2) /**< \brief (MATRIX_MEIMR) Master 2 Access Error */
#define MATRIX_MEIMR_MERR3 (0x1u << 3) /**< \brief (MATRIX_MEIMR) Master 3 Access Error */
#define MATRIX_MEIMR_MERR4 (0x1u << 4) /**< \brief (MATRIX_MEIMR) Master 4 Access Error */
#define MATRIX_MEIMR_MERR5 (0x1u << 5) /**< \brief (MATRIX_MEIMR) Master 5 Access Error */
#define MATRIX_MEIMR_MERR6 (0x1u << 6) /**< \brief (MATRIX_MEIMR) Master 6 Access Error */
#define MATRIX_MEIMR_MERR7 (0x1u << 7) /**< \brief (MATRIX_MEIMR) Master 7 Access Error */
#define MATRIX_MEIMR_MERR8 (0x1u << 8) /**< \brief (MATRIX_MEIMR) Master 8 Access Error */
#define MATRIX_MEIMR_MERR9 (0x1u << 9) /**< \brief (MATRIX_MEIMR) Master 9 Access Error */
#define MATRIX_MEIMR_MERR10 (0x1u << 10) /**< \brief (MATRIX_MEIMR) Master 10 Access Error */
#define MATRIX_MEIMR_MERR11 (0x1u << 11) /**< \brief (MATRIX_MEIMR) Master 11 Access Error */
#define MATRIX_MEIMR_MERR12 (0x1u << 12) /**< \brief (MATRIX_MEIMR) Master 12 Access Error */
#define MATRIX_MEIMR_MERR13 (0x1u << 13) /**< \brief (MATRIX_MEIMR) Master 13 Access Error */
#define MATRIX_MEIMR_MERR14 (0x1u << 14) /**< \brief (MATRIX_MEIMR) Master 14 Access Error */
#define MATRIX_MEIMR_MERR15 (0x1u << 15) /**< \brief (MATRIX_MEIMR) Master 15 Access Error */
/* -------- MATRIX_MESR : (MATRIX Offset: 0x015C) Master Error Status Register -------- */
#define MATRIX_MESR_MERR0 (0x1u << 0) /**< \brief (MATRIX_MESR) Master 0 Access Error */
#define MATRIX_MESR_MERR1 (0x1u << 1) /**< \brief (MATRIX_MESR) Master 1 Access Error */
#define MATRIX_MESR_MERR2 (0x1u << 2) /**< \brief (MATRIX_MESR) Master 2 Access Error */
#define MATRIX_MESR_MERR3 (0x1u << 3) /**< \brief (MATRIX_MESR) Master 3 Access Error */
#define MATRIX_MESR_MERR4 (0x1u << 4) /**< \brief (MATRIX_MESR) Master 4 Access Error */
#define MATRIX_MESR_MERR5 (0x1u << 5) /**< \brief (MATRIX_MESR) Master 5 Access Error */
#define MATRIX_MESR_MERR6 (0x1u << 6) /**< \brief (MATRIX_MESR) Master 6 Access Error */
#define MATRIX_MESR_MERR7 (0x1u << 7) /**< \brief (MATRIX_MESR) Master 7 Access Error */
#define MATRIX_MESR_MERR8 (0x1u << 8) /**< \brief (MATRIX_MESR) Master 8 Access Error */
#define MATRIX_MESR_MERR9 (0x1u << 9) /**< \brief (MATRIX_MESR) Master 9 Access Error */
#define MATRIX_MESR_MERR10 (0x1u << 10) /**< \brief (MATRIX_MESR) Master 10 Access Error */
#define MATRIX_MESR_MERR11 (0x1u << 11) /**< \brief (MATRIX_MESR) Master 11 Access Error */
#define MATRIX_MESR_MERR12 (0x1u << 12) /**< \brief (MATRIX_MESR) Master 12 Access Error */
#define MATRIX_MESR_MERR13 (0x1u << 13) /**< \brief (MATRIX_MESR) Master 13 Access Error */
#define MATRIX_MESR_MERR14 (0x1u << 14) /**< \brief (MATRIX_MESR) Master 14 Access Error */
#define MATRIX_MESR_MERR15 (0x1u << 15) /**< \brief (MATRIX_MESR) Master 15 Access Error */
/* -------- MATRIX_MEAR[16] : (MATRIX Offset: 0x0160) Master 0 Error Address Register -------- */
#define MATRIX_MEAR_ERRADD_Pos 0
#define MATRIX_MEAR_ERRADD_Msk (0xffffffffu << MATRIX_MEAR_ERRADD_Pos) /**< \brief (MATRIX_MEAR[16]) Master Error Address */
/* -------- MATRIX_WPMR : (MATRIX Offset: 0x01E4) Write Protect Mode Register -------- */
#define MATRIX_WPMR_WPEN (0x1u << 0) /**< \brief (MATRIX_WPMR) Write Protect Enable */
#define MATRIX_WPMR_WPKEY_Pos 8
#define MATRIX_WPMR_WPKEY_Msk (0xffffffu << MATRIX_WPMR_WPKEY_Pos) /**< \brief (MATRIX_WPMR) Write Protect KEY (Write-only) */
#define MATRIX_WPMR_WPKEY(value) ((MATRIX_WPMR_WPKEY_Msk & ((value) << MATRIX_WPMR_WPKEY_Pos)))
/* -------- MATRIX_WPSR : (MATRIX Offset: 0x01E8) Write Protect Status Register -------- */
#define MATRIX_WPSR_WPVS (0x1u << 0) /**< \brief (MATRIX_WPSR) Write Protect Violation Status */
#define MATRIX_WPSR_WPVSRC_Pos 8
#define MATRIX_WPSR_WPVSRC_Msk (0xffffu << MATRIX_WPSR_WPVSRC_Pos) /**< \brief (MATRIX_WPSR) Write Protect Violation Source */
/* -------- MATRIX_VERSION : (MATRIX Offset: 0x01FC) Version Register -------- */
#define MATRIX_VERSION_VERSION_Pos 0
#define MATRIX_VERSION_VERSION_Msk (0xfffu << MATRIX_VERSION_VERSION_Pos) /**< \brief (MATRIX_VERSION)  */
#define MATRIX_VERSION_MFN_Pos 16
#define MATRIX_VERSION_MFN_Msk (0x7u << MATRIX_VERSION_MFN_Pos) /**< \brief (MATRIX_VERSION)  */
/* -------- MATRIX_SSR[16] : (MATRIX Offset: 0x0200) Security Slave 0 Register -------- */
#define MATRIX_SSR_LANSECH0 (0x1u << 0) /**< \brief (MATRIX_SSR[16]) Low Area Not Secured in HSELx Security Region */
#define MATRIX_SSR_LANSECH1 (0x1u << 1) /**< \brief (MATRIX_SSR[16]) Low Area Not Secured in HSELx Security Region */
#define MATRIX_SSR_LANSECH2 (0x1u << 2) /**< \brief (MATRIX_SSR[16]) Low Area Not Secured in HSELx Security Region */
#define MATRIX_SSR_LANSECH3 (0x1u << 3) /**< \brief (MATRIX_SSR[16]) Low Area Not Secured in HSELx Security Region */
#define MATRIX_SSR_LANSECH4 (0x1u << 4) /**< \brief (MATRIX_SSR[16]) Low Area Not Secured in HSELx Security Region */
#define MATRIX_SSR_LANSECH5 (0x1u << 5) /**< \brief (MATRIX_SSR[16]) Low Area Not Secured in HSELx Security Region */
#define MATRIX_SSR_LANSECH6 (0x1u << 6) /**< \brief (MATRIX_SSR[16]) Low Area Not Secured in HSELx Security Region */
#define MATRIX_SSR_LANSECH7 (0x1u << 7) /**< \brief (MATRIX_SSR[16]) Low Area Not Secured in HSELx Security Region */
#define MATRIX_SSR_RDNSECH0 (0x1u << 8) /**< \brief (MATRIX_SSR[16]) Read Not Secured for HSELx Security Region */
#define MATRIX_SSR_RDNSECH1 (0x1u << 9) /**< \brief (MATRIX_SSR[16]) Read Not Secured for HSELx Security Region */
#define MATRIX_SSR_RDNSECH2 (0x1u << 10) /**< \brief (MATRIX_SSR[16]) Read Not Secured for HSELx Security Region */
#define MATRIX_SSR_RDNSECH3 (0x1u << 11) /**< \brief (MATRIX_SSR[16]) Read Not Secured for HSELx Security Region */
#define MATRIX_SSR_RDNSECH4 (0x1u << 12) /**< \brief (MATRIX_SSR[16]) Read Not Secured for HSELx Security Region */
#define MATRIX_SSR_RDNSECH5 (0x1u << 13) /**< \brief (MATRIX_SSR[16]) Read Not Secured for HSELx Security Region */
#define MATRIX_SSR_RDNSECH6 (0x1u << 14) /**< \brief (MATRIX_SSR[16]) Read Not Secured for HSELx Security Region */
#define MATRIX_SSR_RDNSECH7 (0x1u << 15) /**< \brief (MATRIX_SSR[16]) Read Not Secured for HSELx Security Region */
#define MATRIX_SSR_WRNSECH0 (0x1u << 16) /**< \brief (MATRIX_SSR[16]) Write Not Secured for HSELx Security Region */
#define MATRIX_SSR_WRNSECH1 (0x1u << 17) /**< \brief (MATRIX_SSR[16]) Write Not Secured for HSELx Security Region */
#define MATRIX_SSR_WRNSECH2 (0x1u << 18) /**< \brief (MATRIX_SSR[16]) Write Not Secured for HSELx Security Region */
#define MATRIX_SSR_WRNSECH3 (0x1u << 19) /**< \brief (MATRIX_SSR[16]) Write Not Secured for HSELx Security Region */
#define MATRIX_SSR_WRNSECH4 (0x1u << 20) /**< \brief (MATRIX_SSR[16]) Write Not Secured for HSELx Security Region */
#define MATRIX_SSR_WRNSECH5 (0x1u << 21) /**< \brief (MATRIX_SSR[16]) Write Not Secured for HSELx Security Region */
#define MATRIX_SSR_WRNSECH6 (0x1u << 22) /**< \brief (MATRIX_SSR[16]) Write Not Secured for HSELx Security Region */
#define MATRIX_SSR_WRNSECH7 (0x1u << 23) /**< \brief (MATRIX_SSR[16]) Write Not Secured for HSELx Security Region */
/* -------- MATRIX_SASSR[16] : (MATRIX Offset: 0x0240) Security Areas Split Slave 0 Register -------- */
#define MATRIX_SASSR_SASPLIT0_Pos 0
#define MATRIX_SASSR_SASPLIT0_Msk (0xfu << MATRIX_SASSR_SASPLIT0_Pos) /**< \brief (MATRIX_SASSR[16]) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR_SASPLIT0(value) ((MATRIX_SASSR_SASPLIT0_Msk & ((value) << MATRIX_SASSR_SASPLIT0_Pos)))
#define MATRIX_SASSR_SASPLIT1_Pos 4
#define MATRIX_SASSR_SASPLIT1_Msk (0xfu << MATRIX_SASSR_SASPLIT1_Pos) /**< \brief (MATRIX_SASSR[16]) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR_SASPLIT1(value) ((MATRIX_SASSR_SASPLIT1_Msk & ((value) << MATRIX_SASSR_SASPLIT1_Pos)))
#define MATRIX_SASSR_SASPLIT2_Pos 8
#define MATRIX_SASSR_SASPLIT2_Msk (0xfu << MATRIX_SASSR_SASPLIT2_Pos) /**< \brief (MATRIX_SASSR[16]) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR_SASPLIT2(value) ((MATRIX_SASSR_SASPLIT2_Msk & ((value) << MATRIX_SASSR_SASPLIT2_Pos)))
#define MATRIX_SASSR_SASPLIT3_Pos 12
#define MATRIX_SASSR_SASPLIT3_Msk (0xfu << MATRIX_SASSR_SASPLIT3_Pos) /**< \brief (MATRIX_SASSR[16]) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR_SASPLIT3(value) ((MATRIX_SASSR_SASPLIT3_Msk & ((value) << MATRIX_SASSR_SASPLIT3_Pos)))
#define MATRIX_SASSR_SASPLIT4_Pos 16
#define MATRIX_SASSR_SASPLIT4_Msk (0xfu << MATRIX_SASSR_SASPLIT4_Pos) /**< \brief (MATRIX_SASSR[16]) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR_SASPLIT4(value) ((MATRIX_SASSR_SASPLIT4_Msk & ((value) << MATRIX_SASSR_SASPLIT4_Pos)))
#define MATRIX_SASSR_SASPLIT5_Pos 20
#define MATRIX_SASSR_SASPLIT5_Msk (0xfu << MATRIX_SASSR_SASPLIT5_Pos) /**< \brief (MATRIX_SASSR[16]) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR_SASPLIT5(value) ((MATRIX_SASSR_SASPLIT5_Msk & ((value) << MATRIX_SASSR_SASPLIT5_Pos)))
#define MATRIX_SASSR_SASPLIT6_Pos 24
#define MATRIX_SASSR_SASPLIT6_Msk (0xfu << MATRIX_SASSR_SASPLIT6_Pos) /**< \brief (MATRIX_SASSR[16]) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR_SASPLIT6(value) ((MATRIX_SASSR_SASPLIT6_Msk & ((value) << MATRIX_SASSR_SASPLIT6_Pos)))
#define MATRIX_SASSR_SASPLIT7_Pos 28
#define MATRIX_SASSR_SASPLIT7_Msk (0xfu << MATRIX_SASSR_SASPLIT7_Pos) /**< \brief (MATRIX_SASSR[16]) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR_SASPLIT7(value) ((MATRIX_SASSR_SASPLIT7_Msk & ((value) << MATRIX_SASSR_SASPLIT7_Pos)))
/* -------- MATRIX_SRTSR[16] : (MATRIX Offset: 0x0280) Security Region Top Slave 0 Register -------- */
#define MATRIX_SRTSR_SRTOP0_Pos 0
#define MATRIX_SRTSR_SRTOP0_Msk (0xfu << MATRIX_SRTSR_SRTOP0_Pos) /**< \brief (MATRIX_SRTSR[16]) HSELx Security Region Top */
#define MATRIX_SRTSR_SRTOP0(value) ((MATRIX_SRTSR_SRTOP0_Msk & ((value) << MATRIX_SRTSR_SRTOP0_Pos)))
#define MATRIX_SRTSR_SRTOP1_Pos 4
#define MATRIX_SRTSR_SRTOP1_Msk (0xfu << MATRIX_SRTSR_SRTOP1_Pos) /**< \brief (MATRIX_SRTSR[16]) HSELx Security Region Top */
#define MATRIX_SRTSR_SRTOP1(value) ((MATRIX_SRTSR_SRTOP1_Msk & ((value) << MATRIX_SRTSR_SRTOP1_Pos)))
#define MATRIX_SRTSR_SRTOP2_Pos 8
#define MATRIX_SRTSR_SRTOP2_Msk (0xfu << MATRIX_SRTSR_SRTOP2_Pos) /**< \brief (MATRIX_SRTSR[16]) HSELx Security Region Top */
#define MATRIX_SRTSR_SRTOP2(value) ((MATRIX_SRTSR_SRTOP2_Msk & ((value) << MATRIX_SRTSR_SRTOP2_Pos)))
#define MATRIX_SRTSR_SRTOP3_Pos 12
#define MATRIX_SRTSR_SRTOP3_Msk (0xfu << MATRIX_SRTSR_SRTOP3_Pos) /**< \brief (MATRIX_SRTSR[16]) HSELx Security Region Top */
#define MATRIX_SRTSR_SRTOP3(value) ((MATRIX_SRTSR_SRTOP3_Msk & ((value) << MATRIX_SRTSR_SRTOP3_Pos)))
#define MATRIX_SRTSR_SRTOP4_Pos 16
#define MATRIX_SRTSR_SRTOP4_Msk (0xfu << MATRIX_SRTSR_SRTOP4_Pos) /**< \brief (MATRIX_SRTSR[16]) HSELx Security Region Top */
#define MATRIX_SRTSR_SRTOP4(value) ((MATRIX_SRTSR_SRTOP4_Msk & ((value) << MATRIX_SRTSR_SRTOP4_Pos)))
#define MATRIX_SRTSR_SRTOP5_Pos 20
#define MATRIX_SRTSR_SRTOP5_Msk (0xfu << MATRIX_SRTSR_SRTOP5_Pos) /**< \brief (MATRIX_SRTSR[16]) HSELx Security Region Top */
#define MATRIX_SRTSR_SRTOP5(value) ((MATRIX_SRTSR_SRTOP5_Msk & ((value) << MATRIX_SRTSR_SRTOP5_Pos)))
#define MATRIX_SRTSR_SRTOP6_Pos 24
#define MATRIX_SRTSR_SRTOP6_Msk (0xfu << MATRIX_SRTSR_SRTOP6_Pos) /**< \brief (MATRIX_SRTSR[16]) HSELx Security Region Top */
#define MATRIX_SRTSR_SRTOP6(value) ((MATRIX_SRTSR_SRTOP6_Msk & ((value) << MATRIX_SRTSR_SRTOP6_Pos)))
#define MATRIX_SRTSR_SRTOP7_Pos 28
#define MATRIX_SRTSR_SRTOP7_Msk (0xfu << MATRIX_SRTSR_SRTOP7_Pos) /**< \brief (MATRIX_SRTSR[16]) HSELx Security Region Top */
#define MATRIX_SRTSR_SRTOP7(value) ((MATRIX_SRTSR_SRTOP7_Msk & ((value) << MATRIX_SRTSR_SRTOP7_Pos)))
/* -------- MATRIX_SPSELR[3] : (MATRIX Offset: 0x02C0) Security Peripheral Select 1 Register -------- */
#define MATRIX_SPSELR_NSECP0 (0x1u << 0) /**< \brief (MATRIX_SPSELR[3]) Not Secured PSELy Peripheral */
#define MATRIX_SPSELR_NSECP1 (0x1u << 1) /**< \brief (MATRIX_SPSELR[3]) Not Secured PSELy Peripheral */
#define MATRIX_SPSELR_NSECP2 (0x1u << 2) /**< \brief (MATRIX_SPSELR[3]) Not Secured PSELy Peripheral */
#define MATRIX_SPSELR_NSECP3 (0x1u << 3) /**< \brief (MATRIX_SPSELR[3]) Not Secured PSELy Peripheral */
#define MATRIX_SPSELR_NSECP4 (0x1u << 4) /**< \brief (MATRIX_SPSELR[3]) Not Secured PSELy Peripheral */
#define MATRIX_SPSELR_NSECP5 (0x1u << 5) /**< \brief (MATRIX_SPSELR[3]) Not Secured PSELy Peripheral */
#define MATRIX_SPSELR_NSECP6 (0x1u << 6) /**< \brief (MATRIX_SPSELR[3]) Not Secured PSELy Peripheral */
#define MATRIX_SPSELR_NSECP7 (0x1u << 7) /**< \brief (MATRIX_SPSELR[3]) Not Secured PSELy Peripheral */
#define MATRIX_SPSELR_NSECP8 (0x1u << 8) /**< \brief (MATRIX_SPSELR[3]) Not Secured PSELy Peripheral */
#define MATRIX_SPSELR_NSECP9 (0x1u << 9) /**< \brief (MATRIX_SPSELR[3]) Not Secured PSELy Peripheral */
#define MATRIX_SPSELR_NSECP10 (0x1u << 10) /**< \brief (MATRIX_SPSELR[3]) Not Secured PSELy Peripheral */
#define MATRIX_SPSELR_NSECP11 (0x1u << 11) /**< \brief (MATRIX_SPSELR[3]) Not Secured PSELy Peripheral */
#define MATRIX_SPSELR_NSECP12 (0x1u << 12) /**< \brief (MATRIX_SPSELR[3]) Not Secured PSELy Peripheral */
#define MATRIX_SPSELR_NSECP13 (0x1u << 13) /**< \brief (MATRIX_SPSELR[3]) Not Secured PSELy Peripheral */
#define MATRIX_SPSELR_NSECP14 (0x1u << 14) /**< \brief (MATRIX_SPSELR[3]) Not Secured PSELy Peripheral */
#define MATRIX_SPSELR_NSECP15 (0x1u << 15) /**< \brief (MATRIX_SPSELR[3]) Not Secured PSELy Peripheral */
#define MATRIX_SPSELR_NSECP16 (0x1u << 16) /**< \brief (MATRIX_SPSELR[3]) Not Secured PSELy Peripheral */
#define MATRIX_SPSELR_NSECP17 (0x1u << 17) /**< \brief (MATRIX_SPSELR[3]) Not Secured PSELy Peripheral */
#define MATRIX_SPSELR_NSECP18 (0x1u << 18) /**< \brief (MATRIX_SPSELR[3]) Not Secured PSELy Peripheral */
#define MATRIX_SPSELR_NSECP19 (0x1u << 19) /**< \brief (MATRIX_SPSELR[3]) Not Secured PSELy Peripheral */
#define MATRIX_SPSELR_NSECP20 (0x1u << 20) /**< \brief (MATRIX_SPSELR[3]) Not Secured PSELy Peripheral */
#define MATRIX_SPSELR_NSECP21 (0x1u << 21) /**< \brief (MATRIX_SPSELR[3]) Not Secured PSELy Peripheral */
#define MATRIX_SPSELR_NSECP22 (0x1u << 22) /**< \brief (MATRIX_SPSELR[3]) Not Secured PSELy Peripheral */
#define MATRIX_SPSELR_NSECP23 (0x1u << 23) /**< \brief (MATRIX_SPSELR[3]) Not Secured PSELy Peripheral */
#define MATRIX_SPSELR_NSECP24 (0x1u << 24) /**< \brief (MATRIX_SPSELR[3]) Not Secured PSELy Peripheral */
#define MATRIX_SPSELR_NSECP25 (0x1u << 25) /**< \brief (MATRIX_SPSELR[3]) Not Secured PSELy Peripheral */
#define MATRIX_SPSELR_NSECP26 (0x1u << 26) /**< \brief (MATRIX_SPSELR[3]) Not Secured PSELy Peripheral */
#define MATRIX_SPSELR_NSECP27 (0x1u << 27) /**< \brief (MATRIX_SPSELR[3]) Not Secured PSELy Peripheral */
#define MATRIX_SPSELR_NSECP28 (0x1u << 28) /**< \brief (MATRIX_SPSELR[3]) Not Secured PSELy Peripheral */
#define MATRIX_SPSELR_NSECP29 (0x1u << 29) /**< \brief (MATRIX_SPSELR[3]) Not Secured PSELy Peripheral */
#define MATRIX_SPSELR_NSECP30 (0x1u << 30) /**< \brief (MATRIX_SPSELR[3]) Not Secured PSELy Peripheral */
#define MATRIX_SPSELR_NSECP31 (0x1u << 31) /**< \brief (MATRIX_SPSELR[3]) Not Secured PSELy Peripheral */

/*@}*/


#endif /* _SAM_MATRIX_COMPONENT_ */
