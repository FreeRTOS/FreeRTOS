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

#ifndef _SAMA5_PMC_COMPONENT_
#define _SAMA5_PMC_COMPONENT_

/* ============================================================================= */
/**  SOFTWARE API DEFINITION FOR Power Management Controller */
/* ============================================================================= */
/** \addtogroup SAMA5_PMC Power Management Controller */
/*@{*/

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
/** \brief Pmc hardware registers */
typedef struct {
  WoReg PMC_SCER;      /**< \brief (Pmc Offset: 0x0000) System Clock Enable Register */
  WoReg PMC_SCDR;      /**< \brief (Pmc Offset: 0x0004) System Clock Disable Register */
  RoReg PMC_SCSR;      /**< \brief (Pmc Offset: 0x0008) System Clock Status Register */
  RoReg Reserved1[1];
  WoReg PMC_PCER0;     /**< \brief (Pmc Offset: 0x0010) Peripheral Clock Enable Register 0 */
  WoReg PMC_PCDR0;     /**< \brief (Pmc Offset: 0x0014) Peripheral Clock Disable Register 0 */
  RoReg PMC_PCSR0;     /**< \brief (Pmc Offset: 0x0018) Peripheral Clock Status Register 0 */
  RwReg CKGR_UCKR;     /**< \brief (Pmc Offset: 0x001C) UTMI Clock Register */
  RwReg CKGR_MOR;      /**< \brief (Pmc Offset: 0x0020) Main Oscillator Register */
  RoReg CKGR_MCFR;     /**< \brief (Pmc Offset: 0x0024) Main Clock Frequency Register */
  RwReg CKGR_PLLAR;    /**< \brief (Pmc Offset: 0x0028) PLLA Register */
  RoReg Reserved2[1];
  RwReg PMC_MCKR;      /**< \brief (Pmc Offset: 0x0030) Master Clock Register */
  RoReg Reserved3[1];
  RwReg PMC_USB;       /**< \brief (Pmc Offset: 0x0038) USB Clock Register */
  RwReg PMC_SMD;       /**< \brief (Pmc Offset: 0x003C) Soft Modem Clock Register */
  RwReg PMC_PCK[3];    /**< \brief (Pmc Offset: 0x0040) Programmable Clock 0 Register */
  RoReg Reserved4[5];
  WoReg PMC_IER;       /**< \brief (Pmc Offset: 0x0060) Interrupt Enable Register */
  WoReg PMC_IDR;       /**< \brief (Pmc Offset: 0x0064) Interrupt Disable Register */
  RoReg PMC_SR;        /**< \brief (Pmc Offset: 0x0068) Status Register */
  RoReg PMC_IMR;       /**< \brief (Pmc Offset: 0x006C) Interrupt Mask Register */
  RoReg Reserved5[4];
  WoReg PMC_PLLICPR;   /**< \brief (Pmc Offset: 0x0080) PLL Charge Pump Current Register */
  RoReg Reserved6[24];
  RwReg PMC_WPMR;      /**< \brief (Pmc Offset: 0x00E4) Write Protect Mode Register */
  RoReg PMC_WPSR;      /**< \brief (Pmc Offset: 0x00E8) Write Protect Status Register */
  RoReg Reserved7[5];
  WoReg PMC_PCER1;     /**< \brief (Pmc Offset: 0x00100) Peripheral Clock Enable Register 1 */
  WoReg PMC_PCDR1;     /**< \brief (Pmc Offset: 0x00104) Peripheral Clock Disable Register 1 */
  RoReg PMC_PCSR1;     /**< \brief (Pmc Offset: 0x00108) Peripheral Clock Status Register 1 */
  RwReg PMC_PCR;       /**< \brief (Pmc Offset: 0x010C) Peripheral Control Register */
} Pmc;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */
/* -------- PMC_SCER : (PMC Offset: 0x0000) System Clock Enable Register -------- */
#define PMC_SCER_DDRCK (0x1u << 2) /**< \brief (PMC_SCER) DDR Clock Enable */
#define PMC_SCER_SMDCK (0x1u << 4) /**< \brief (PMC_SCER) SMD Clock Enable */
#define PMC_SCER_UHP (0x1u << 6) /**< \brief (PMC_SCER) USB Host OHCI Clocks Enable */
#define PMC_SCER_UDP (0x1u << 7) /**< \brief (PMC_SCER) USB Device Clock Enable */
#define PMC_SCER_PCK0 (0x1u << 8) /**< \brief (PMC_SCER) Programmable Clock 0 Output Enable */
#define PMC_SCER_PCK1 (0x1u << 9) /**< \brief (PMC_SCER) Programmable Clock 1 Output Enable */
#define PMC_SCER_PCK2 (0x1u << 10) /**< \brief (PMC_SCER) Programmable Clock 2 Output Enable */
/* -------- PMC_SCDR : (PMC Offset: 0x0004) System Clock Disable Register -------- */
#define PMC_SCDR_PCK (0x1u << 0) /**< \brief (PMC_SCDR) Processor Clock Disable */
#define PMC_SCDR_DDRCK (0x1u << 2) /**< \brief (PMC_SCDR) DDR Clock Disable */
#define PMC_SCDR_SMDCK (0x1u << 4) /**< \brief (PMC_SCDR) SMD Clock Disable */
#define PMC_SCDR_UHP (0x1u << 6) /**< \brief (PMC_SCDR) USB Host OHCI Clock Disable */
#define PMC_SCDR_UDP (0x1u << 7) /**< \brief (PMC_SCDR) USB Device Clock Enable */
#define PMC_SCDR_PCK0 (0x1u << 8) /**< \brief (PMC_SCDR) Programmable Clock 0 Output Disable */
#define PMC_SCDR_PCK1 (0x1u << 9) /**< \brief (PMC_SCDR) Programmable Clock 1 Output Disable */
#define PMC_SCDR_PCK2 (0x1u << 10) /**< \brief (PMC_SCDR) Programmable Clock 2 Output Disable */
/* -------- PMC_SCSR : (PMC Offset: 0x0008) System Clock Status Register -------- */
#define PMC_SCSR_PCK (0x1u << 0) /**< \brief (PMC_SCSR) Processor Clock Status */
#define PMC_SCSR_DDRCK (0x1u << 2) /**< \brief (PMC_SCSR) DDR Clock Status */
#define PMC_SCSR_SMDCK (0x1u << 4) /**< \brief (PMC_SCSR) SMD Clock Status */
#define PMC_SCSR_UHP (0x1u << 6) /**< \brief (PMC_SCSR) USB Host Port Clock Status */
#define PMC_SCSR_UDP (0x1u << 7) /**< \brief (PMC_SCSR) USB Device Port Clock Status */
#define PMC_SCSR_PCK0 (0x1u << 8) /**< \brief (PMC_SCSR) Programmable Clock 0 Output Status */
#define PMC_SCSR_PCK1 (0x1u << 9) /**< \brief (PMC_SCSR) Programmable Clock 1 Output Status */
#define PMC_SCSR_PCK2 (0x1u << 10) /**< \brief (PMC_SCSR) Programmable Clock 2 Output Status */
/* -------- PMC_PCER0 : (PMC Offset: 0x0010) Peripheral Clock Enable Register 0 -------- */
#define PMC_PCER0_PID2 (0x1u << 2) /**< \brief (PMC_PCER0) Peripheral Clock 2 Enable */
#define PMC_PCER0_PID3 (0x1u << 3) /**< \brief (PMC_PCER0) Peripheral Clock 3 Enable */
#define PMC_PCER0_PID4 (0x1u << 4) /**< \brief (PMC_PCER0) Peripheral Clock 4 Enable */
#define PMC_PCER0_PID5 (0x1u << 5) /**< \brief (PMC_PCER0) Peripheral Clock 5 Enable */
#define PMC_PCER0_PID6 (0x1u << 6) /**< \brief (PMC_PCER0) Peripheral Clock 6 Enable */
#define PMC_PCER0_PID7 (0x1u << 7) /**< \brief (PMC_PCER0) Peripheral Clock 7 Enable */
#define PMC_PCER0_PID8 (0x1u << 8) /**< \brief (PMC_PCER0) Peripheral Clock 8 Enable */
#define PMC_PCER0_PID9 (0x1u << 9) /**< \brief (PMC_PCER0) Peripheral Clock 9 Enable */
#define PMC_PCER0_PID10 (0x1u << 10) /**< \brief (PMC_PCER0) Peripheral Clock 10 Enable */
#define PMC_PCER0_PID11 (0x1u << 11) /**< \brief (PMC_PCER0) Peripheral Clock 11 Enable */
#define PMC_PCER0_PID12 (0x1u << 12) /**< \brief (PMC_PCER0) Peripheral Clock 12 Enable */
#define PMC_PCER0_PID13 (0x1u << 13) /**< \brief (PMC_PCER0) Peripheral Clock 13 Enable */
#define PMC_PCER0_PID14 (0x1u << 14) /**< \brief (PMC_PCER0) Peripheral Clock 14 Enable */
#define PMC_PCER0_PID15 (0x1u << 15) /**< \brief (PMC_PCER0) Peripheral Clock 15 Enable */
#define PMC_PCER0_PID16 (0x1u << 16) /**< \brief (PMC_PCER0) Peripheral Clock 16 Enable */
#define PMC_PCER0_PID17 (0x1u << 17) /**< \brief (PMC_PCER0) Peripheral Clock 17 Enable */
#define PMC_PCER0_PID18 (0x1u << 18) /**< \brief (PMC_PCER0) Peripheral Clock 18 Enable */
#define PMC_PCER0_PID19 (0x1u << 19) /**< \brief (PMC_PCER0) Peripheral Clock 19 Enable */
#define PMC_PCER0_PID20 (0x1u << 20) /**< \brief (PMC_PCER0) Peripheral Clock 20 Enable */
#define PMC_PCER0_PID21 (0x1u << 21) /**< \brief (PMC_PCER0) Peripheral Clock 21 Enable */
#define PMC_PCER0_PID22 (0x1u << 22) /**< \brief (PMC_PCER0) Peripheral Clock 22 Enable */
#define PMC_PCER0_PID23 (0x1u << 23) /**< \brief (PMC_PCER0) Peripheral Clock 23 Enable */
#define PMC_PCER0_PID24 (0x1u << 24) /**< \brief (PMC_PCER0) Peripheral Clock 24 Enable */
#define PMC_PCER0_PID25 (0x1u << 25) /**< \brief (PMC_PCER0) Peripheral Clock 25 Enable */
#define PMC_PCER0_PID26 (0x1u << 26) /**< \brief (PMC_PCER0) Peripheral Clock 26 Enable */
#define PMC_PCER0_PID27 (0x1u << 27) /**< \brief (PMC_PCER0) Peripheral Clock 27 Enable */
#define PMC_PCER0_PID28 (0x1u << 28) /**< \brief (PMC_PCER0) Peripheral Clock 28 Enable */
#define PMC_PCER0_PID29 (0x1u << 29) /**< \brief (PMC_PCER0) Peripheral Clock 29 Enable */
#define PMC_PCER0_PID30 (0x1u << 30) /**< \brief (PMC_PCER0) Peripheral Clock 30 Enable */
#define PMC_PCER0_PID31 (0x1u << 31) /**< \brief (PMC_PCER0) Peripheral Clock 31 Enable */
/* -------- PMC_PCDR0 : (PMC Offset: 0x0014) Peripheral Clock Disable Register 0 -------- */
#define PMC_PCDR0_PID2 (0x1u << 2) /**< \brief (PMC_PCDR0) Peripheral Clock 2 Disable */
#define PMC_PCDR0_PID3 (0x1u << 3) /**< \brief (PMC_PCDR0) Peripheral Clock 3 Disable */
#define PMC_PCDR0_PID4 (0x1u << 4) /**< \brief (PMC_PCDR0) Peripheral Clock 4 Disable */
#define PMC_PCDR0_PID5 (0x1u << 5) /**< \brief (PMC_PCDR0) Peripheral Clock 5 Disable */
#define PMC_PCDR0_PID6 (0x1u << 6) /**< \brief (PMC_PCDR0) Peripheral Clock 6 Disable */
#define PMC_PCDR0_PID7 (0x1u << 7) /**< \brief (PMC_PCDR0) Peripheral Clock 7 Disable */
#define PMC_PCDR0_PID8 (0x1u << 8) /**< \brief (PMC_PCDR0) Peripheral Clock 8 Disable */
#define PMC_PCDR0_PID9 (0x1u << 9) /**< \brief (PMC_PCDR0) Peripheral Clock 9 Disable */
#define PMC_PCDR0_PID10 (0x1u << 10) /**< \brief (PMC_PCDR0) Peripheral Clock 10 Disable */
#define PMC_PCDR0_PID11 (0x1u << 11) /**< \brief (PMC_PCDR0) Peripheral Clock 11 Disable */
#define PMC_PCDR0_PID12 (0x1u << 12) /**< \brief (PMC_PCDR0) Peripheral Clock 12 Disable */
#define PMC_PCDR0_PID13 (0x1u << 13) /**< \brief (PMC_PCDR0) Peripheral Clock 13 Disable */
#define PMC_PCDR0_PID14 (0x1u << 14) /**< \brief (PMC_PCDR0) Peripheral Clock 14 Disable */
#define PMC_PCDR0_PID15 (0x1u << 15) /**< \brief (PMC_PCDR0) Peripheral Clock 15 Disable */
#define PMC_PCDR0_PID16 (0x1u << 16) /**< \brief (PMC_PCDR0) Peripheral Clock 16 Disable */
#define PMC_PCDR0_PID17 (0x1u << 17) /**< \brief (PMC_PCDR0) Peripheral Clock 17 Disable */
#define PMC_PCDR0_PID18 (0x1u << 18) /**< \brief (PMC_PCDR0) Peripheral Clock 18 Disable */
#define PMC_PCDR0_PID19 (0x1u << 19) /**< \brief (PMC_PCDR0) Peripheral Clock 19 Disable */
#define PMC_PCDR0_PID20 (0x1u << 20) /**< \brief (PMC_PCDR0) Peripheral Clock 20 Disable */
#define PMC_PCDR0_PID21 (0x1u << 21) /**< \brief (PMC_PCDR0) Peripheral Clock 21 Disable */
#define PMC_PCDR0_PID22 (0x1u << 22) /**< \brief (PMC_PCDR0) Peripheral Clock 22 Disable */
#define PMC_PCDR0_PID23 (0x1u << 23) /**< \brief (PMC_PCDR0) Peripheral Clock 23 Disable */
#define PMC_PCDR0_PID24 (0x1u << 24) /**< \brief (PMC_PCDR0) Peripheral Clock 24 Disable */
#define PMC_PCDR0_PID25 (0x1u << 25) /**< \brief (PMC_PCDR0) Peripheral Clock 25 Disable */
#define PMC_PCDR0_PID26 (0x1u << 26) /**< \brief (PMC_PCDR0) Peripheral Clock 26 Disable */
#define PMC_PCDR0_PID27 (0x1u << 27) /**< \brief (PMC_PCDR0) Peripheral Clock 27 Disable */
#define PMC_PCDR0_PID28 (0x1u << 28) /**< \brief (PMC_PCDR0) Peripheral Clock 28 Disable */
#define PMC_PCDR0_PID29 (0x1u << 29) /**< \brief (PMC_PCDR0) Peripheral Clock 29 Disable */
#define PMC_PCDR0_PID30 (0x1u << 30) /**< \brief (PMC_PCDR0) Peripheral Clock 30 Disable */
#define PMC_PCDR0_PID31 (0x1u << 31) /**< \brief (PMC_PCDR0) Peripheral Clock 31 Disable */
/* -------- PMC_PCSR0 : (PMC Offset: 0x0018) Peripheral Clock Status Register 0 -------- */
#define PMC_PCSR0_PID2 (0x1u << 2) /**< \brief (PMC_PCSR0) Peripheral Clock 2 Status */
#define PMC_PCSR0_PID3 (0x1u << 3) /**< \brief (PMC_PCSR0) Peripheral Clock 3 Status */
#define PMC_PCSR0_PID4 (0x1u << 4) /**< \brief (PMC_PCSR0) Peripheral Clock 4 Status */
#define PMC_PCSR0_PID5 (0x1u << 5) /**< \brief (PMC_PCSR0) Peripheral Clock 5 Status */
#define PMC_PCSR0_PID6 (0x1u << 6) /**< \brief (PMC_PCSR0) Peripheral Clock 6 Status */
#define PMC_PCSR0_PID7 (0x1u << 7) /**< \brief (PMC_PCSR0) Peripheral Clock 7 Status */
#define PMC_PCSR0_PID8 (0x1u << 8) /**< \brief (PMC_PCSR0) Peripheral Clock 8 Status */
#define PMC_PCSR0_PID9 (0x1u << 9) /**< \brief (PMC_PCSR0) Peripheral Clock 9 Status */
#define PMC_PCSR0_PID10 (0x1u << 10) /**< \brief (PMC_PCSR0) Peripheral Clock 10 Status */
#define PMC_PCSR0_PID11 (0x1u << 11) /**< \brief (PMC_PCSR0) Peripheral Clock 11 Status */
#define PMC_PCSR0_PID12 (0x1u << 12) /**< \brief (PMC_PCSR0) Peripheral Clock 12 Status */
#define PMC_PCSR0_PID13 (0x1u << 13) /**< \brief (PMC_PCSR0) Peripheral Clock 13 Status */
#define PMC_PCSR0_PID14 (0x1u << 14) /**< \brief (PMC_PCSR0) Peripheral Clock 14 Status */
#define PMC_PCSR0_PID15 (0x1u << 15) /**< \brief (PMC_PCSR0) Peripheral Clock 15 Status */
#define PMC_PCSR0_PID16 (0x1u << 16) /**< \brief (PMC_PCSR0) Peripheral Clock 16 Status */
#define PMC_PCSR0_PID17 (0x1u << 17) /**< \brief (PMC_PCSR0) Peripheral Clock 17 Status */
#define PMC_PCSR0_PID18 (0x1u << 18) /**< \brief (PMC_PCSR0) Peripheral Clock 18 Status */
#define PMC_PCSR0_PID19 (0x1u << 19) /**< \brief (PMC_PCSR0) Peripheral Clock 19 Status */
#define PMC_PCSR0_PID20 (0x1u << 20) /**< \brief (PMC_PCSR0) Peripheral Clock 20 Status */
#define PMC_PCSR0_PID21 (0x1u << 21) /**< \brief (PMC_PCSR0) Peripheral Clock 21 Status */
#define PMC_PCSR0_PID22 (0x1u << 22) /**< \brief (PMC_PCSR0) Peripheral Clock 22 Status */
#define PMC_PCSR0_PID23 (0x1u << 23) /**< \brief (PMC_PCSR0) Peripheral Clock 23 Status */
#define PMC_PCSR0_PID24 (0x1u << 24) /**< \brief (PMC_PCSR0) Peripheral Clock 24 Status */
#define PMC_PCSR0_PID25 (0x1u << 25) /**< \brief (PMC_PCSR0) Peripheral Clock 25 Status */
#define PMC_PCSR0_PID26 (0x1u << 26) /**< \brief (PMC_PCSR0) Peripheral Clock 26 Status */
#define PMC_PCSR0_PID27 (0x1u << 27) /**< \brief (PMC_PCSR0) Peripheral Clock 27 Status */
#define PMC_PCSR0_PID28 (0x1u << 28) /**< \brief (PMC_PCSR0) Peripheral Clock 28 Status */
#define PMC_PCSR0_PID29 (0x1u << 29) /**< \brief (PMC_PCSR0) Peripheral Clock 29 Status */
#define PMC_PCSR0_PID30 (0x1u << 30) /**< \brief (PMC_PCSR0) Peripheral Clock 30 Status */
#define PMC_PCSR0_PID31 (0x1u << 31) /**< \brief (PMC_PCSR0) Peripheral Clock 31 Status */
/* -------- CKGR_UCKR : (PMC Offset: 0x001C) UTMI Clock Register -------- */
#define CKGR_UCKR_UPLLEN (0x1u << 16) /**< \brief (CKGR_UCKR) UTMI PLL Enable */
#define CKGR_UCKR_UPLLCOUNT_Pos 20
#define CKGR_UCKR_UPLLCOUNT_Msk (0xfu << CKGR_UCKR_UPLLCOUNT_Pos) /**< \brief (CKGR_UCKR) UTMI PLL Start-up Time */
#define CKGR_UCKR_UPLLCOUNT(value) ((CKGR_UCKR_UPLLCOUNT_Msk & ((value) << CKGR_UCKR_UPLLCOUNT_Pos)))
#define CKGR_UCKR_BIASEN (0x1u << 24) /**< \brief (CKGR_UCKR) UTMI BIAS Enable */
#define CKGR_UCKR_BIASCOUNT_Pos 28
#define CKGR_UCKR_BIASCOUNT_Msk (0xfu << CKGR_UCKR_BIASCOUNT_Pos) /**< \brief (CKGR_UCKR) UTMI BIAS Start-up Time */
#define CKGR_UCKR_BIASCOUNT(value) ((CKGR_UCKR_BIASCOUNT_Msk & ((value) << CKGR_UCKR_BIASCOUNT_Pos)))
/* -------- CKGR_MOR : (PMC Offset: 0x0020) Main Oscillator Register -------- */
#define CKGR_MOR_MOSCXTEN (0x1u << 0) /**< \brief (CKGR_MOR) Main Crystal Oscillator Enable */
#define CKGR_MOR_MOSCXTBY (0x1u << 1) /**< \brief (CKGR_MOR) Main Crystal Oscillator Bypass */
#define CKGR_MOR_MOSCRCEN (0x1u << 3) /**< \brief (CKGR_MOR) Main On-Chip RC Oscillator Enable */
#define CKGR_MOR_MOSCXTST_Pos 8
#define CKGR_MOR_MOSCXTST_Msk (0xffu << CKGR_MOR_MOSCXTST_Pos) /**< \brief (CKGR_MOR) Main Crystal Oscillator Start-up Time */
#define CKGR_MOR_MOSCXTST(value) ((CKGR_MOR_MOSCXTST_Msk & ((value) << CKGR_MOR_MOSCXTST_Pos)))
#define CKGR_MOR_KEY_Pos 16
#define CKGR_MOR_KEY_Msk (0xffu << CKGR_MOR_KEY_Pos) /**< \brief (CKGR_MOR) Password */
#define CKGR_MOR_KEY(value) ((CKGR_MOR_KEY_Msk & ((value) << CKGR_MOR_KEY_Pos)))
#define CKGR_MOR_MOSCSEL (0x1u << 24) /**< \brief (CKGR_MOR) Main Oscillator Selection */
#define CKGR_MOR_CFDEN (0x1u << 25) /**< \brief (CKGR_MOR) Clock Failure Detector Enable */
/* -------- CKGR_MCFR : (PMC Offset: 0x0024) Main Clock Frequency Register -------- */
#define CKGR_MCFR_MAINF_Pos 0
#define CKGR_MCFR_MAINF_Msk (0xffffu << CKGR_MCFR_MAINF_Pos) /**< \brief (CKGR_MCFR) Main Clock Frequency */
#define CKGR_MCFR_MAINFRDY (0x1u << 16) /**< \brief (CKGR_MCFR) Main Clock Ready */
/* -------- CKGR_PLLAR : (PMC Offset: 0x0028) PLLA Register -------- */
#define CKGR_PLLAR_DIVA_Pos 0
#define CKGR_PLLAR_DIVA_Msk (0xffu << CKGR_PLLAR_DIVA_Pos) /**< \brief (CKGR_PLLAR) Divider A */
#define CKGR_PLLAR_DIVA(value) ((CKGR_PLLAR_DIVA_Msk & ((value) << CKGR_PLLAR_DIVA_Pos)))
#define CKGR_PLLAR_PLLACOUNT_Pos 8
#define CKGR_PLLAR_PLLACOUNT_Msk (0x3fu << CKGR_PLLAR_PLLACOUNT_Pos) /**< \brief (CKGR_PLLAR) PLLA Counter */
#define CKGR_PLLAR_PLLACOUNT(value) ((CKGR_PLLAR_PLLACOUNT_Msk & ((value) << CKGR_PLLAR_PLLACOUNT_Pos)))
#define CKGR_PLLAR_OUTA_Pos 14
#define CKGR_PLLAR_OUTA_Msk (0x3u << CKGR_PLLAR_OUTA_Pos) /**< \brief (CKGR_PLLAR) PLLA Clock Frequency Range */
#define CKGR_PLLAR_OUTA(value) ((CKGR_PLLAR_OUTA_Msk & ((value) << CKGR_PLLAR_OUTA_Pos)))
#define CKGR_PLLAR_MULA_Pos 18
#define CKGR_PLLAR_MULA_Msk (0x7ffu << CKGR_PLLAR_MULA_Pos) /**< \brief (CKGR_PLLAR) PLLA Multiplier */
#define CKGR_PLLAR_MULA(value) ((CKGR_PLLAR_MULA_Msk & ((value) << CKGR_PLLAR_MULA_Pos)))
#define CKGR_PLLAR_STUCKTO1 (0x1u << 29) /**< \brief (CKGR_PLLAR)  */
/* -------- PMC_MCKR : (PMC Offset: 0x0030) Master Clock Register -------- */
#define PMC_MCKR_CSS_Pos 0
#define PMC_MCKR_CSS_Msk (0x3u << PMC_MCKR_CSS_Pos) /**< \brief (PMC_MCKR) Master/Processor Clock Source Selection */
#define   PMC_MCKR_CSS_SLOW_CLK (0x0u << 0) /**< \brief (PMC_MCKR) Slow Clock is selected */
#define   PMC_MCKR_CSS_MAIN_CLK (0x1u << 0) /**< \brief (PMC_MCKR) Main Clock is selected */
#define   PMC_MCKR_CSS_PLLA_CLK (0x2u << 0) /**< \brief (PMC_MCKR) PLLACK/PLLADIV2 is selected */
#define   PMC_MCKR_CSS_UPLL_CLK (0x3u << 0) /**< \brief (PMC_MCKR) UPLL Clock is selected */
#define PMC_MCKR_PRES_Pos 4
#define PMC_MCKR_PRES_Msk (0x7u << PMC_MCKR_PRES_Pos) /**< \brief (PMC_MCKR) Master/Processor Clock Prescaler */
#define   PMC_MCKR_PRES_CLOCK (0x0u << 4) /**< \brief (PMC_MCKR) Selected clock */
#define   PMC_MCKR_PRES_CLOCK_DIV2 (0x1u << 4) /**< \brief (PMC_MCKR) Selected clock divided by 2 */
#define   PMC_MCKR_PRES_CLOCK_DIV4 (0x2u << 4) /**< \brief (PMC_MCKR) Selected clock divided by 4 */
#define   PMC_MCKR_PRES_CLOCK_DIV8 (0x3u << 4) /**< \brief (PMC_MCKR) Selected clock divided by 8 */
#define   PMC_MCKR_PRES_CLOCK_DIV16 (0x4u << 4) /**< \brief (PMC_MCKR) Selected clock divided by 16 */
#define   PMC_MCKR_PRES_CLOCK_DIV32 (0x5u << 4) /**< \brief (PMC_MCKR) Selected clock divided by 32 */
#define   PMC_MCKR_PRES_CLOCK_DIV64 (0x6u << 4) /**< \brief (PMC_MCKR) Selected clock divided by 64 */
#define PMC_MCKR_MDIV_Pos 8
#define PMC_MCKR_MDIV_Msk (0x3u << PMC_MCKR_MDIV_Pos) /**< \brief (PMC_MCKR) Master Clock Division */
#define   PMC_MCKR_MDIV_EQ_PCK (0x0u << 8) /**< \brief (PMC_MCKR) Master Clock is Prescaler Output Clock divided by 1.Warning: SysClk DDR and DDRCK are not available. */
#define   PMC_MCKR_MDIV_PCK_DIV2 (0x1u << 8) /**< \brief (PMC_MCKR) Master Clock is Prescaler Output Clock divided by 2.SysClk DDR is equal to 2 x MCK. DDRCK is equal to MCK. */
#define   PMC_MCKR_MDIV_PCK_DIV4 (0x2u << 8) /**< \brief (PMC_MCKR) Master Clock is Prescaler Output Clock divided by 4.SysClk DDR is equal to 2 x MCK. DDRCK is equal to MCK. */
#define   PMC_MCKR_MDIV_PCK_DIV3 (0x3u << 8) /**< \brief (PMC_MCKR) Master Clock is Prescaler Output Clock divided by 3.SysClk DDR is equal to 2 x MCK. DDRCK is equal to MCK. */
#define PMC_MCKR_PLLADIV2 (0x1u << 12) /**< \brief (PMC_MCKR) PLLA divisor by 2 */
#define   PMC_MCKR_PLLADIV2_NOT_DIV2 (0x0u << 12) /**< \brief (PMC_MCKR) PLLA clock frequency is divided by 1. */
#define   PMC_MCKR_PLLADIV2_DIV2 (0x1u << 12) /**< \brief (PMC_MCKR) PLLA clock frequency is divided by 2. */
/* -------- PMC_USB : (PMC Offset: 0x0038) USB Clock Register -------- */
#define PMC_USB_USBS (0x1u << 0) /**< \brief (PMC_USB) USB OHCI Input Clock Selection */
#define PMC_USB_USBDIV_Pos 8
#define PMC_USB_USBDIV_Msk (0xfu << PMC_USB_USBDIV_Pos) /**< \brief (PMC_USB) Divider for USB OHCI Clock. */
#define PMC_USB_USBDIV(value) ((PMC_USB_USBDIV_Msk & ((value) << PMC_USB_USBDIV_Pos)))
/* -------- PMC_SMD : (PMC Offset: 0x003C) Soft Modem Clock Register -------- */
#define PMC_SMD_SMDS (0x1u << 0) /**< \brief (PMC_SMD) SMD input clock selection */
#define PMC_SMD_SMDDIV_Pos 8
#define PMC_SMD_SMDDIV_Msk (0x1fu << PMC_SMD_SMDDIV_Pos) /**< \brief (PMC_SMD) Divider for SMD Clock. */
#define PMC_SMD_SMDDIV(value) ((PMC_SMD_SMDDIV_Msk & ((value) << PMC_SMD_SMDDIV_Pos)))
/* -------- PMC_PCK[3] : (PMC Offset: 0x0040) Programmable Clock 0 Register -------- */
#define PMC_PCK_CSS_Pos 0
#define PMC_PCK_CSS_Msk (0x7u << PMC_PCK_CSS_Pos) /**< \brief (PMC_PCK[3]) Master Clock Source Selection */
#define   PMC_PCK_CSS_SLOW_CLK (0x0u << 0) /**< \brief (PMC_PCK[3]) Slow Clock is selected */
#define   PMC_PCK_CSS_MAIN_CLK (0x1u << 0) /**< \brief (PMC_PCK[3]) Main Clock is selected */
#define   PMC_PCK_CSS_PLLA_CLK (0x2u << 0) /**< \brief (PMC_PCK[3]) PLLACK/PLLADIV2 is selected */
#define   PMC_PCK_CSS_UPLL_CLK (0x3u << 0) /**< \brief (PMC_PCK[3]) UPLL Clock is selected */
#define   PMC_PCK_CSS_MCK_CLK (0x4u << 0) /**< \brief (PMC_PCK[3]) Master Clock is selected */
#define PMC_PCK_PRES_Pos 4
#define PMC_PCK_PRES_Msk (0x7u << PMC_PCK_PRES_Pos) /**< \brief (PMC_PCK[3]) Programmable Clock Prescaler */
#define   PMC_PCK_PRES_CLOCK (0x0u << 4) /**< \brief (PMC_PCK[3]) Selected clock */
#define   PMC_PCK_PRES_CLOCK_DIV2 (0x1u << 4) /**< \brief (PMC_PCK[3]) Selected clock divided by 2 */
#define   PMC_PCK_PRES_CLOCK_DIV4 (0x2u << 4) /**< \brief (PMC_PCK[3]) Selected clock divided by 4 */
#define   PMC_PCK_PRES_CLOCK_DIV8 (0x3u << 4) /**< \brief (PMC_PCK[3]) Selected clock divided by 8 */
#define   PMC_PCK_PRES_CLOCK_DIV16 (0x4u << 4) /**< \brief (PMC_PCK[3]) Selected clock divided by 16 */
#define   PMC_PCK_PRES_CLOCK_DIV32 (0x5u << 4) /**< \brief (PMC_PCK[3]) Selected clock divided by 32 */
#define   PMC_PCK_PRES_CLOCK_DIV64 (0x6u << 4) /**< \brief (PMC_PCK[3]) Selected clock divided by 64 */
/* -------- PMC_IER : (PMC Offset: 0x0060) Interrupt Enable Register -------- */
#define PMC_IER_MOSCXTS (0x1u << 0) /**< \brief (PMC_IER) Main Crystal Oscillator Status Interrupt Enable */
#define PMC_IER_LOCKA (0x1u << 1) /**< \brief (PMC_IER) PLLA Lock Interrupt Enable */
#define PMC_IER_MCKRDY (0x1u << 3) /**< \brief (PMC_IER) Master Clock Ready Interrupt Enable */
#define PMC_IER_LOCKU (0x1u << 6) /**< \brief (PMC_IER) UTMI PLL Lock Interrupt Enable */
#define PMC_IER_PCKRDY0 (0x1u << 8) /**< \brief (PMC_IER) Programmable Clock Ready 0 Interrupt Enable */
#define PMC_IER_PCKRDY1 (0x1u << 9) /**< \brief (PMC_IER) Programmable Clock Ready 1 Interrupt Enable */
#define PMC_IER_MOSCSELS (0x1u << 16) /**< \brief (PMC_IER) Main Oscillator Selection Status Interrupt Enable */
#define PMC_IER_MOSCRCS (0x1u << 17) /**< \brief (PMC_IER) Main On-Chip RC Status Interrupt Enable */
#define PMC_IER_CFDEV (0x1u << 18) /**< \brief (PMC_IER) Clock Failure Detector Event Interrupt Enable */
/* -------- PMC_IDR : (PMC Offset: 0x0064) Interrupt Disable Register -------- */
#define PMC_IDR_MOSCXTS (0x1u << 0) /**< \brief (PMC_IDR) Main Crystal Oscillator Status Interrupt Disable */
#define PMC_IDR_LOCKA (0x1u << 1) /**< \brief (PMC_IDR) PLLA Lock Interrupt Disable */
#define PMC_IDR_MCKRDY (0x1u << 3) /**< \brief (PMC_IDR) Master Clock Ready Interrupt Disable */
#define PMC_IDR_LOCKU (0x1u << 6) /**< \brief (PMC_IDR) UTMI PLL Lock Interrupt Enable */
#define PMC_IDR_PCKRDY0 (0x1u << 8) /**< \brief (PMC_IDR) Programmable Clock Ready 0 Interrupt Disable */
#define PMC_IDR_PCKRDY1 (0x1u << 9) /**< \brief (PMC_IDR) Programmable Clock Ready 1 Interrupt Disable */
#define PMC_IDR_MOSCSELS (0x1u << 16) /**< \brief (PMC_IDR) Main Oscillator Selection Status Interrupt Disable */
#define PMC_IDR_MOSCRCS (0x1u << 17) /**< \brief (PMC_IDR) Main On-Chip RC Status Interrupt Disable */
#define PMC_IDR_CFDEV (0x1u << 18) /**< \brief (PMC_IDR) Clock Failure Detector Event Interrupt Disable */
/* -------- PMC_SR : (PMC Offset: 0x0068) Status Register -------- */
#define PMC_SR_MOSCXTS (0x1u << 0) /**< \brief (PMC_SR) Main XTAL Oscillator Status */
#define PMC_SR_LOCKA (0x1u << 1) /**< \brief (PMC_SR) PLLA Lock Status */
#define PMC_SR_MCKRDY (0x1u << 3) /**< \brief (PMC_SR) Master Clock Status */
#define PMC_SR_LOCKU (0x1u << 6) /**< \brief (PMC_SR) UPLL Clock Status */
#define PMC_SR_OSCSELS (0x1u << 7) /**< \brief (PMC_SR) Slow Clock Oscillator Selection */
#define PMC_SR_PCKRDY0 (0x1u << 8) /**< \brief (PMC_SR) Programmable Clock Ready Status */
#define PMC_SR_PCKRDY1 (0x1u << 9) /**< \brief (PMC_SR) Programmable Clock Ready Status */
#define PMC_SR_MOSCSELS (0x1u << 16) /**< \brief (PMC_SR) Main Oscillator Selection Status */
#define PMC_SR_MOSCRCS (0x1u << 17) /**< \brief (PMC_SR) Main On-Chip RC Oscillator Status */
#define PMC_SR_CFDEV (0x1u << 18) /**< \brief (PMC_SR) Clock Failure Detector Event */
#define PMC_SR_CFDS (0x1u << 19) /**< \brief (PMC_SR) Clock Failure Detector Status */
#define PMC_SR_FOS (0x1u << 20) /**< \brief (PMC_SR) Clock Failure Detector Fault Output Status */
/* -------- PMC_IMR : (PMC Offset: 0x006C) Interrupt Mask Register -------- */
#define PMC_IMR_MOSCXTS (0x1u << 0) /**< \brief (PMC_IMR) Main Crystal Oscillator Status Interrupt Mask */
#define PMC_IMR_LOCKA (0x1u << 1) /**< \brief (PMC_IMR) PLLA Lock Interrupt Mask */
#define PMC_IMR_MCKRDY (0x1u << 3) /**< \brief (PMC_IMR) Master Clock Ready Interrupt Mask */
#define PMC_IMR_PCKRDY0 (0x1u << 8) /**< \brief (PMC_IMR) Programmable Clock Ready 0 Interrupt Mask */
#define PMC_IMR_PCKRDY1 (0x1u << 9) /**< \brief (PMC_IMR) Programmable Clock Ready 1 Interrupt Mask */
#define PMC_IMR_MOSCSELS (0x1u << 16) /**< \brief (PMC_IMR) Main Oscillator Selection Status Interrupt Mask */
#define PMC_IMR_MOSCRCS (0x1u << 17) /**< \brief (PMC_IMR) Main On-Chip RC Status Interrupt Mask */
#define PMC_IMR_CFDEV (0x1u << 18) /**< \brief (PMC_IMR) Clock Failure Detector Event Interrupt Mask */
/* -------- PMC_PLLICPR : (PMC Offset: 0x0080) PLL Charge Pump Current Register -------- */
#define PMC_PLLICPR_ICPLLA (0x1u << 0) /**< \brief (PMC_PLLICPR) Charge Pump Current */
/* -------- PMC_WPMR : (PMC Offset: 0x00E4) Write Protect Mode Register -------- */
#define PMC_WPMR_WPEN (0x1u << 0) /**< \brief (PMC_WPMR) Write Protect Enable */
#define PMC_WPMR_WPKEY_Pos 8
#define PMC_WPMR_WPKEY_Msk (0xffffffu << PMC_WPMR_WPKEY_Pos) /**< \brief (PMC_WPMR) Write Protect KEY */
#define PMC_WPMR_WPKEY(value) ((PMC_WPMR_WPKEY_Msk & ((value) << PMC_WPMR_WPKEY_Pos)))
/* -------- PMC_WPSR : (PMC Offset: 0x00E8) Write Protect Status Register -------- */
#define PMC_WPSR_WPVS (0x1u << 0) /**< \brief (PMC_WPSR) Write Protect Violation Status */
#define PMC_WPSR_WPVSRC_Pos 8
#define PMC_WPSR_WPVSRC_Msk (0xffffu << PMC_WPSR_WPVSRC_Pos) /**< \brief (PMC_WPSR) Write Protect Violation Source */
/* -------- PMC_PCER1 : (PMC Offset: 0x00100) Peripheral Clock Enable Register 1 -------- */
#define PMC_PCER1_PID32 (0x1u << 0) /**< \brief (PMC_PCER1) Peripheral Clock 32 Enable */
#define PMC_PCER1_PID33 (0x1u << 1) /**< \brief (PMC_PCER1) Peripheral Clock 33 Enable */
#define PMC_PCER1_PID34 (0x1u << 2) /**< \brief (PMC_PCER1) Peripheral Clock 34 Enable */
#define PMC_PCER1_PID35 (0x1u << 3) /**< \brief (PMC_PCER1) Peripheral Clock 35 Enable */
#define PMC_PCER1_PID36 (0x1u << 4) /**< \brief (PMC_PCER1) Peripheral Clock 36 Enable */
#define PMC_PCER1_PID37 (0x1u << 5) /**< \brief (PMC_PCER1) Peripheral Clock 37 Enable */
#define PMC_PCER1_PID38 (0x1u << 6) /**< \brief (PMC_PCER1) Peripheral Clock 38 Enable */
#define PMC_PCER1_PID39 (0x1u << 7) /**< \brief (PMC_PCER1) Peripheral Clock 39 Enable */
#define PMC_PCER1_PID40 (0x1u << 8) /**< \brief (PMC_PCER1) Peripheral Clock 40 Enable */
#define PMC_PCER1_PID41 (0x1u << 9) /**< \brief (PMC_PCER1) Peripheral Clock 41 Enable */
#define PMC_PCER1_PID42 (0x1u << 10) /**< \brief (PMC_PCER1) Peripheral Clock 42 Enable */
#define PMC_PCER1_PID43 (0x1u << 11) /**< \brief (PMC_PCER1) Peripheral Clock 43 Enable */
#define PMC_PCER1_PID44 (0x1u << 12) /**< \brief (PMC_PCER1) Peripheral Clock 44 Enable */
#define PMC_PCER1_PID45 (0x1u << 13) /**< \brief (PMC_PCER1) Peripheral Clock 45 Enable */
#define PMC_PCER1_PID46 (0x1u << 14) /**< \brief (PMC_PCER1) Peripheral Clock 46 Enable */
#define PMC_PCER1_PID47 (0x1u << 15) /**< \brief (PMC_PCER1) Peripheral Clock 47 Enable */
#define PMC_PCER1_PID48 (0x1u << 16) /**< \brief (PMC_PCER1) Peripheral Clock 48 Enable */
#define PMC_PCER1_PID49 (0x1u << 17) /**< \brief (PMC_PCER1) Peripheral Clock 49 Enable */
#define PMC_PCER1_PID50 (0x1u << 18) /**< \brief (PMC_PCER1) Peripheral Clock 50 Enable */
#define PMC_PCER1_PID51 (0x1u << 19) /**< \brief (PMC_PCER1) Peripheral Clock 51 Enable */
#define PMC_PCER1_PID53_Pos 20
#define PMC_PCER1_PID53_Msk (0x3u << PMC_PCER1_PID53_Pos) /**< \brief (PMC_PCER1) Peripheral Clock 53 Enable */
#define PMC_PCER1_PID53(value) ((PMC_PCER1_PID53_Msk & ((value) << PMC_PCER1_PID53_Pos)))
#define PMC_PCER1_PID54 (0x1u << 22) /**< \brief (PMC_PCER1) Peripheral Clock 54 Enable */
#define PMC_PCER1_PID55 (0x1u << 23) /**< \brief (PMC_PCER1) Peripheral Clock 55 Enable */
#define PMC_PCER1_PID56 (0x1u << 24) /**< \brief (PMC_PCER1) Peripheral Clock 56 Enable */
#define PMC_PCER1_PID57 (0x1u << 25) /**< \brief (PMC_PCER1) Peripheral Clock 57 Enable */
#define PMC_PCER1_PID58 (0x1u << 26) /**< \brief (PMC_PCER1) Peripheral Clock 58 Enable */
#define PMC_PCER1_PID59 (0x1u << 27) /**< \brief (PMC_PCER1) Peripheral Clock 59 Enable */
#define PMC_PCER1_PID60 (0x1u << 28) /**< \brief (PMC_PCER1) Peripheral Clock 60 Enable */
#define PMC_PCER1_PID61 (0x1u << 29) /**< \brief (PMC_PCER1) Peripheral Clock 61 Enable */
#define PMC_PCER1_PID62 (0x1u << 30) /**< \brief (PMC_PCER1) Peripheral Clock 62 Enable */
#define PMC_PCER1_PID63 (0x1u << 31) /**< \brief (PMC_PCER1) Peripheral Clock 63 Enable */
/* -------- PMC_PCDR1 : (PMC Offset: 0x00104) Peripheral Clock Disable Register 1 -------- */
#define PMC_PCDR1_PID32 (0x1u << 0) /**< \brief (PMC_PCDR1) Peripheral Clock 32 Disable */
#define PMC_PCDR1_PID33 (0x1u << 1) /**< \brief (PMC_PCDR1) Peripheral Clock 33 Disable */
#define PMC_PCDR1_PID34 (0x1u << 2) /**< \brief (PMC_PCDR1) Peripheral Clock 34 Disable */
#define PMC_PCDR1_PID35 (0x1u << 3) /**< \brief (PMC_PCDR1) Peripheral Clock 35 Disable */
#define PMC_PCDR1_PID36 (0x1u << 4) /**< \brief (PMC_PCDR1) Peripheral Clock 36 Disable */
#define PMC_PCDR1_PID37 (0x1u << 5) /**< \brief (PMC_PCDR1) Peripheral Clock 37 Disable */
#define PMC_PCDR1_PID38 (0x1u << 6) /**< \brief (PMC_PCDR1) Peripheral Clock 38 Disable */
#define PMC_PCDR1_PID39 (0x1u << 7) /**< \brief (PMC_PCDR1) Peripheral Clock 39 Disable */
#define PMC_PCDR1_PID40 (0x1u << 8) /**< \brief (PMC_PCDR1) Peripheral Clock 40 Disable */
#define PMC_PCDR1_PID41 (0x1u << 9) /**< \brief (PMC_PCDR1) Peripheral Clock 41 Disable */
#define PMC_PCDR1_PID42 (0x1u << 10) /**< \brief (PMC_PCDR1) Peripheral Clock 42 Disable */
#define PMC_PCDR1_PID43 (0x1u << 11) /**< \brief (PMC_PCDR1) Peripheral Clock 43 Disable */
#define PMC_PCDR1_PID44 (0x1u << 12) /**< \brief (PMC_PCDR1) Peripheral Clock 44 Disable */
#define PMC_PCDR1_PID45 (0x1u << 13) /**< \brief (PMC_PCDR1) Peripheral Clock 45 Disable */
#define PMC_PCDR1_PID46 (0x1u << 14) /**< \brief (PMC_PCDR1) Peripheral Clock 46 Disable */
#define PMC_PCDR1_PID47 (0x1u << 15) /**< \brief (PMC_PCDR1) Peripheral Clock 47 Disable */
#define PMC_PCDR1_PID48 (0x1u << 16) /**< \brief (PMC_PCDR1) Peripheral Clock 48 Disable */
#define PMC_PCDR1_PID49 (0x1u << 17) /**< \brief (PMC_PCDR1) Peripheral Clock 49 Disable */
#define PMC_PCDR1_PID50 (0x1u << 18) /**< \brief (PMC_PCDR1) Peripheral Clock 50 Disable */
#define PMC_PCDR1_PID51 (0x1u << 19) /**< \brief (PMC_PCDR1) Peripheral Clock 51 Disable */
#define PMC_PCDR1_PID53_Pos 20
#define PMC_PCDR1_PID53_Msk (0x3u << PMC_PCDR1_PID53_Pos) /**< \brief (PMC_PCDR1) Peripheral Clock 53 Disable */
#define PMC_PCDR1_PID53(value) ((PMC_PCDR1_PID53_Msk & ((value) << PMC_PCDR1_PID53_Pos)))
#define PMC_PCDR1_PID54 (0x1u << 22) /**< \brief (PMC_PCDR1) Peripheral Clock 54 Disable */
#define PMC_PCDR1_PID55 (0x1u << 23) /**< \brief (PMC_PCDR1) Peripheral Clock 55 Disable */
#define PMC_PCDR1_PID56 (0x1u << 24) /**< \brief (PMC_PCDR1) Peripheral Clock 56 Disable */
#define PMC_PCDR1_PID57 (0x1u << 25) /**< \brief (PMC_PCDR1) Peripheral Clock 57 Disable */
#define PMC_PCDR1_PID58 (0x1u << 26) /**< \brief (PMC_PCDR1) Peripheral Clock 58 Disable */
#define PMC_PCDR1_PID59 (0x1u << 27) /**< \brief (PMC_PCDR1) Peripheral Clock 59 Disable */
#define PMC_PCDR1_PID60 (0x1u << 28) /**< \brief (PMC_PCDR1) Peripheral Clock 60 Disable */
#define PMC_PCDR1_PID61 (0x1u << 29) /**< \brief (PMC_PCDR1) Peripheral Clock 61 Disable */
#define PMC_PCDR1_PID62 (0x1u << 30) /**< \brief (PMC_PCDR1) Peripheral Clock 62 Disable */
#define PMC_PCDR1_PID63 (0x1u << 31) /**< \brief (PMC_PCDR1) Peripheral Clock 63 Disable */
/* -------- PMC_PCSR1 : (PMC Offset: 0x00108) Peripheral Clock Status Register 1 -------- */
#define PMC_PCSR1_PID32 (0x1u << 0) /**< \brief (PMC_PCSR1) Peripheral Clock 32 Status */
#define PMC_PCSR1_PID33 (0x1u << 1) /**< \brief (PMC_PCSR1) Peripheral Clock 33 Status */
#define PMC_PCSR1_PID34 (0x1u << 2) /**< \brief (PMC_PCSR1) Peripheral Clock 34 Status */
#define PMC_PCSR1_PID35 (0x1u << 3) /**< \brief (PMC_PCSR1) Peripheral Clock 35 Status */
#define PMC_PCSR1_PID36 (0x1u << 4) /**< \brief (PMC_PCSR1) Peripheral Clock 36 Status */
#define PMC_PCSR1_PID37 (0x1u << 5) /**< \brief (PMC_PCSR1) Peripheral Clock 37 Status */
#define PMC_PCSR1_PID38 (0x1u << 6) /**< \brief (PMC_PCSR1) Peripheral Clock 38 Status */
#define PMC_PCSR1_PID39 (0x1u << 7) /**< \brief (PMC_PCSR1) Peripheral Clock 39 Status */
#define PMC_PCSR1_PID40 (0x1u << 8) /**< \brief (PMC_PCSR1) Peripheral Clock 40 Status */
#define PMC_PCSR1_PID41 (0x1u << 9) /**< \brief (PMC_PCSR1) Peripheral Clock 41 Status */
#define PMC_PCSR1_PID42 (0x1u << 10) /**< \brief (PMC_PCSR1) Peripheral Clock 42 Status */
#define PMC_PCSR1_PID43 (0x1u << 11) /**< \brief (PMC_PCSR1) Peripheral Clock 43 Status */
#define PMC_PCSR1_PID44 (0x1u << 12) /**< \brief (PMC_PCSR1) Peripheral Clock 44 Status */
#define PMC_PCSR1_PID45 (0x1u << 13) /**< \brief (PMC_PCSR1) Peripheral Clock 45 Status */
#define PMC_PCSR1_PID46 (0x1u << 14) /**< \brief (PMC_PCSR1) Peripheral Clock 46 Status */
#define PMC_PCSR1_PID47 (0x1u << 15) /**< \brief (PMC_PCSR1) Peripheral Clock 47 Status */
#define PMC_PCSR1_PID48 (0x1u << 16) /**< \brief (PMC_PCSR1) Peripheral Clock 48 Status */
#define PMC_PCSR1_PID49 (0x1u << 17) /**< \brief (PMC_PCSR1) Peripheral Clock 49 Status */
#define PMC_PCSR1_PID50 (0x1u << 18) /**< \brief (PMC_PCSR1) Peripheral Clock 50 Status */
#define PMC_PCSR1_PID51 (0x1u << 19) /**< \brief (PMC_PCSR1) Peripheral Clock 51 Status */
#define PMC_PCSR1_PID53_Pos 20
#define PMC_PCSR1_PID53_Msk (0x3u << PMC_PCSR1_PID53_Pos) /**< \brief (PMC_PCSR1) Peripheral Clock 53 Status */
#define PMC_PCSR1_PID54 (0x1u << 22) /**< \brief (PMC_PCSR1) Peripheral Clock 54 Status */
#define PMC_PCSR1_PID55 (0x1u << 23) /**< \brief (PMC_PCSR1) Peripheral Clock 55 Status */
#define PMC_PCSR1_PID56 (0x1u << 24) /**< \brief (PMC_PCSR1) Peripheral Clock 56 Status */
#define PMC_PCSR1_PID57 (0x1u << 25) /**< \brief (PMC_PCSR1) Peripheral Clock 57 Status */
#define PMC_PCSR1_PID58 (0x1u << 26) /**< \brief (PMC_PCSR1) Peripheral Clock 58 Status */
#define PMC_PCSR1_PID59 (0x1u << 27) /**< \brief (PMC_PCSR1) Peripheral Clock 59 Status */
#define PMC_PCSR1_PID60 (0x1u << 28) /**< \brief (PMC_PCSR1) Peripheral Clock 60 Status */
#define PMC_PCSR1_PID61 (0x1u << 29) /**< \brief (PMC_PCSR1) Peripheral Clock 61 Status */
#define PMC_PCSR1_PID62 (0x1u << 30) /**< \brief (PMC_PCSR1) Peripheral Clock 62 Status */
#define PMC_PCSR1_PID63 (0x1u << 31) /**< \brief (PMC_PCSR1) Peripheral Clock 63 Status */
/* -------- PMC_PCR : (PMC Offset: 0x010C) Peripheral Control Register -------- */
#define PMC_PCR_PID_Pos 0
#define PMC_PCR_PID_Msk (0x3fu << PMC_PCR_PID_Pos) /**< \brief (PMC_PCR) Peripheral ID */
#define PMC_PCR_PID(value) ((PMC_PCR_PID_Msk & ((value) << PMC_PCR_PID_Pos)))
#define PMC_PCR_CMD (0x1u << 12) /**< \brief (PMC_PCR) Command */
#define PMC_PCR_DIV_Pos 16
#define PMC_PCR_DIV_Msk (0x3u << PMC_PCR_DIV_Pos) /**< \brief (PMC_PCR) Divisor Value */
#define   PMC_PCR_DIV_PERIPH_DIV_MCK (0x0u << 16) /**< \brief (PMC_PCR) Peripheral clock is MCK */
#define   PMC_PCR_DIV_PERIPH_DIV2_MCK (0x1u << 16) /**< \brief (PMC_PCR) Peripheral clock is MCK/2 */
#define   PMC_PCR_DIV_PERIPH_DIV4_MCK (0x2u << 16) /**< \brief (PMC_PCR) Peripheral clock is MCK/4 */
#define   PMC_PCR_DIV_PERIPH_DIV8_MCK (0x3u << 16) /**< \brief (PMC_PCR) Peripheral clock is MCK/8 */
#define PMC_PCR_EN (0x1u << 28) /**< \brief (PMC_PCR) Enable */

/*@}*/


#endif /* _SAMA5_PMC_COMPONENT_ */
