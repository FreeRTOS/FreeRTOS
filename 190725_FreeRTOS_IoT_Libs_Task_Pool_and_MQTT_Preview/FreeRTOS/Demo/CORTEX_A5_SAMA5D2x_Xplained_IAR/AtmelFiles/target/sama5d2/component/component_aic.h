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

#ifndef _SAMA5D2_AIC_COMPONENT_
#define _SAMA5D2_AIC_COMPONENT_

/* ============================================================================= */
/**  SOFTWARE API DEFINITION FOR Advanced Interrupt Controller */
/* ============================================================================= */
/** \addtogroup SAMA5D2_AIC Advanced Interrupt Controller */
/*@{*/

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
/** \brief Aic hardware registers */
typedef struct {
  __IO uint32_t AIC_SSR;       /**< \brief (Aic Offset: 0x00) Source Select Register */
  __IO uint32_t AIC_SMR;       /**< \brief (Aic Offset: 0x04) Source Mode Register */
  __IO uint32_t AIC_SVR;       /**< \brief (Aic Offset: 0x08) Source Vector Register */
  __I  uint32_t Reserved1[1];
  __I  uint32_t AIC_IVR;       /**< \brief (Aic Offset: 0x10) Interrupt Vector Register */
  __I  uint32_t AIC_FVR;       /**< \brief (Aic Offset: 0x14) FIQ Vector Register */
  __I  uint32_t AIC_ISR;       /**< \brief (Aic Offset: 0x18) Interrupt Status Register */
  __I  uint32_t Reserved2[1];
  __I  uint32_t AIC_IPR0;      /**< \brief (Aic Offset: 0x20) Interrupt Pending Register 0 */
  __I  uint32_t AIC_IPR1;      /**< \brief (Aic Offset: 0x24) Interrupt Pending Register 1 */
  __I  uint32_t AIC_IPR2;      /**< \brief (Aic Offset: 0x28) Interrupt Pending Register 2 */
  __I  uint32_t AIC_IPR3;      /**< \brief (Aic Offset: 0x2C) Interrupt Pending Register 3 */
  __I  uint32_t AIC_IMR;       /**< \brief (Aic Offset: 0x30) Interrupt Mask Register */
  __I  uint32_t AIC_CISR;      /**< \brief (Aic Offset: 0x34) Core Interrupt Status Register */
  __O  uint32_t AIC_EOICR;     /**< \brief (Aic Offset: 0x38) End of Interrupt Command Register */
  __IO uint32_t AIC_SPU;       /**< \brief (Aic Offset: 0x3C) Spurious Interrupt Vector Register */
  __O  uint32_t AIC_IECR;      /**< \brief (Aic Offset: 0x40) Interrupt Enable Command Register */
  __O  uint32_t AIC_IDCR;      /**< \brief (Aic Offset: 0x44) Interrupt Disable Command Register */
  __O  uint32_t AIC_ICCR;      /**< \brief (Aic Offset: 0x48) Interrupt Clear Command Register */
  __O  uint32_t AIC_ISCR;      /**< \brief (Aic Offset: 0x4C) Interrupt Set Command Register */
  __I  uint32_t Reserved3[7];
  __IO uint32_t AIC_DCR;       /**< \brief (Aic Offset: 0x6C) Debug Control Register */
  __I  uint32_t Reserved4[29];
  __IO uint32_t AIC_WPMR;      /**< \brief (Aic Offset: 0xE4) Write Protection Mode Register */
  __I  uint32_t AIC_WPSR;      /**< \brief (Aic Offset: 0xE8) Write Protection Status Register */
  __I  uint32_t Reserved5[4];
  __I  uint32_t AIC_VERSION;   /**< \brief (Aic Offset: 0XFC) AIC Version Register */
} Aic;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */
/* -------- AIC_SSR : (AIC Offset: 0x00) Source Select Register -------- */
#define AIC_SSR_INTSEL_Pos 0
#define AIC_SSR_INTSEL_Msk (0x7fu << AIC_SSR_INTSEL_Pos) /**< \brief (AIC_SSR) Interrupt Line Selection */
#define AIC_SSR_INTSEL(value) ((AIC_SSR_INTSEL_Msk & ((value) << AIC_SSR_INTSEL_Pos)))
/* -------- AIC_SMR : (AIC Offset: 0x04) Source Mode Register -------- */
#define AIC_SMR_PRIOR_Pos 0
#define AIC_SMR_PRIOR_Msk (0x7u << AIC_SMR_PRIOR_Pos) /**< \brief (AIC_SMR) Priority Level */
#define AIC_SMR_PRIOR(value) ((AIC_SMR_PRIOR_Msk & ((value) << AIC_SMR_PRIOR_Pos)))
#define AIC_SMR_SRCTYPE_Pos 5
#define AIC_SMR_SRCTYPE_Msk (0x3u << AIC_SMR_SRCTYPE_Pos) /**< \brief (AIC_SMR) Interrupt Source Type */
#define AIC_SMR_SRCTYPE(value) ((AIC_SMR_SRCTYPE_Msk & ((value) << AIC_SMR_SRCTYPE_Pos)))
#define   AIC_SMR_SRCTYPE_INT_LEVEL_SENSITIVE (0x0u << 5) /**< \brief (AIC_SMR) High level Sensitive for internal sourceLow level Sensitive for external source */
#define   AIC_SMR_SRCTYPE_INT_EDGE_TRIGGERED (0x1u << 5) /**< \brief (AIC_SMR) Positive edge triggered for internal sourceNegative edge triggered for external source */
#define   AIC_SMR_SRCTYPE_EXT_HIGH_LEVEL (0x2u << 5) /**< \brief (AIC_SMR) High level Sensitive for internal sourceHigh level Sensitive for external source */
#define   AIC_SMR_SRCTYPE_EXT_POSITIVE_EDGE (0x3u << 5) /**< \brief (AIC_SMR) Positive edge triggered for internal sourcePositive edge triggered for external source */
/* -------- AIC_SVR : (AIC Offset: 0x08) Source Vector Register -------- */
#define AIC_SVR_VECTOR_Pos 0
#define AIC_SVR_VECTOR_Msk (0xffffffffu << AIC_SVR_VECTOR_Pos) /**< \brief (AIC_SVR) Source Vector */
#define AIC_SVR_VECTOR(value) ((AIC_SVR_VECTOR_Msk & ((value) << AIC_SVR_VECTOR_Pos)))
/* -------- AIC_IVR : (AIC Offset: 0x10) Interrupt Vector Register -------- */
#define AIC_IVR_IRQV_Pos 0
#define AIC_IVR_IRQV_Msk (0xffffffffu << AIC_IVR_IRQV_Pos) /**< \brief (AIC_IVR) Interrupt Vector Register */
/* -------- AIC_FVR : (AIC Offset: 0x14) FIQ Vector Register -------- */
#define AIC_FVR_FIQV_Pos 0
#define AIC_FVR_FIQV_Msk (0xffffffffu << AIC_FVR_FIQV_Pos) /**< \brief (AIC_FVR) FIQ Vector Register */
/* -------- AIC_ISR : (AIC Offset: 0x18) Interrupt Status Register -------- */
#define AIC_ISR_IRQID_Pos 0
#define AIC_ISR_IRQID_Msk (0x7fu << AIC_ISR_IRQID_Pos) /**< \brief (AIC_ISR) Current Interrupt Identifier */
/* -------- AIC_IPR0 : (AIC Offset: 0x20) Interrupt Pending Register 0 -------- */
#define AIC_IPR0_FIQ (0x1u << 0) /**< \brief (AIC_IPR0) Interrupt Pending */
#define AIC_IPR0_SYS (0x1u << 1) /**< \brief (AIC_IPR0) Interrupt Pending */
#define AIC_IPR0_PID2 (0x1u << 2) /**< \brief (AIC_IPR0) Interrupt Pending */
#define AIC_IPR0_PID3 (0x1u << 3) /**< \brief (AIC_IPR0) Interrupt Pending */
#define AIC_IPR0_PID4 (0x1u << 4) /**< \brief (AIC_IPR0) Interrupt Pending */
#define AIC_IPR0_PID5 (0x1u << 5) /**< \brief (AIC_IPR0) Interrupt Pending */
#define AIC_IPR0_PID6 (0x1u << 6) /**< \brief (AIC_IPR0) Interrupt Pending */
#define AIC_IPR0_PID7 (0x1u << 7) /**< \brief (AIC_IPR0) Interrupt Pending */
#define AIC_IPR0_PID8 (0x1u << 8) /**< \brief (AIC_IPR0) Interrupt Pending */
#define AIC_IPR0_PID9 (0x1u << 9) /**< \brief (AIC_IPR0) Interrupt Pending */
#define AIC_IPR0_PID10 (0x1u << 10) /**< \brief (AIC_IPR0) Interrupt Pending */
#define AIC_IPR0_PID11 (0x1u << 11) /**< \brief (AIC_IPR0) Interrupt Pending */
#define AIC_IPR0_PID12 (0x1u << 12) /**< \brief (AIC_IPR0) Interrupt Pending */
#define AIC_IPR0_PID13 (0x1u << 13) /**< \brief (AIC_IPR0) Interrupt Pending */
#define AIC_IPR0_PID14 (0x1u << 14) /**< \brief (AIC_IPR0) Interrupt Pending */
#define AIC_IPR0_PID15 (0x1u << 15) /**< \brief (AIC_IPR0) Interrupt Pending */
#define AIC_IPR0_PID16 (0x1u << 16) /**< \brief (AIC_IPR0) Interrupt Pending */
#define AIC_IPR0_PID17 (0x1u << 17) /**< \brief (AIC_IPR0) Interrupt Pending */
#define AIC_IPR0_PID18 (0x1u << 18) /**< \brief (AIC_IPR0) Interrupt Pending */
#define AIC_IPR0_PID19 (0x1u << 19) /**< \brief (AIC_IPR0) Interrupt Pending */
#define AIC_IPR0_PID20 (0x1u << 20) /**< \brief (AIC_IPR0) Interrupt Pending */
#define AIC_IPR0_PID21 (0x1u << 21) /**< \brief (AIC_IPR0) Interrupt Pending */
#define AIC_IPR0_PID22 (0x1u << 22) /**< \brief (AIC_IPR0) Interrupt Pending */
#define AIC_IPR0_PID23 (0x1u << 23) /**< \brief (AIC_IPR0) Interrupt Pending */
#define AIC_IPR0_PID24 (0x1u << 24) /**< \brief (AIC_IPR0) Interrupt Pending */
#define AIC_IPR0_PID25 (0x1u << 25) /**< \brief (AIC_IPR0) Interrupt Pending */
#define AIC_IPR0_PID26 (0x1u << 26) /**< \brief (AIC_IPR0) Interrupt Pending */
#define AIC_IPR0_PID27 (0x1u << 27) /**< \brief (AIC_IPR0) Interrupt Pending */
#define AIC_IPR0_PID28 (0x1u << 28) /**< \brief (AIC_IPR0) Interrupt Pending */
#define AIC_IPR0_PID29 (0x1u << 29) /**< \brief (AIC_IPR0) Interrupt Pending */
#define AIC_IPR0_PID30 (0x1u << 30) /**< \brief (AIC_IPR0) Interrupt Pending */
#define AIC_IPR0_PID31 (0x1u << 31) /**< \brief (AIC_IPR0) Interrupt Pending */
/* -------- AIC_IPR1 : (AIC Offset: 0x24) Interrupt Pending Register 1 -------- */
#define AIC_IPR1_PID32 (0x1u << 0) /**< \brief (AIC_IPR1) Interrupt Pending */
#define AIC_IPR1_PID33 (0x1u << 1) /**< \brief (AIC_IPR1) Interrupt Pending */
#define AIC_IPR1_PID34 (0x1u << 2) /**< \brief (AIC_IPR1) Interrupt Pending */
#define AIC_IPR1_PID35 (0x1u << 3) /**< \brief (AIC_IPR1) Interrupt Pending */
#define AIC_IPR1_PID36 (0x1u << 4) /**< \brief (AIC_IPR1) Interrupt Pending */
#define AIC_IPR1_PID37 (0x1u << 5) /**< \brief (AIC_IPR1) Interrupt Pending */
#define AIC_IPR1_PID38 (0x1u << 6) /**< \brief (AIC_IPR1) Interrupt Pending */
#define AIC_IPR1_PID39 (0x1u << 7) /**< \brief (AIC_IPR1) Interrupt Pending */
#define AIC_IPR1_PID40 (0x1u << 8) /**< \brief (AIC_IPR1) Interrupt Pending */
#define AIC_IPR1_PID41 (0x1u << 9) /**< \brief (AIC_IPR1) Interrupt Pending */
#define AIC_IPR1_PID42 (0x1u << 10) /**< \brief (AIC_IPR1) Interrupt Pending */
#define AIC_IPR1_PID43 (0x1u << 11) /**< \brief (AIC_IPR1) Interrupt Pending */
#define AIC_IPR1_PID44 (0x1u << 12) /**< \brief (AIC_IPR1) Interrupt Pending */
#define AIC_IPR1_PID45 (0x1u << 13) /**< \brief (AIC_IPR1) Interrupt Pending */
#define AIC_IPR1_PID46 (0x1u << 14) /**< \brief (AIC_IPR1) Interrupt Pending */
#define AIC_IPR1_PID47 (0x1u << 15) /**< \brief (AIC_IPR1) Interrupt Pending */
#define AIC_IPR1_PID48 (0x1u << 16) /**< \brief (AIC_IPR1) Interrupt Pending */
#define AIC_IPR1_PID49 (0x1u << 17) /**< \brief (AIC_IPR1) Interrupt Pending */
#define AIC_IPR1_PID50 (0x1u << 18) /**< \brief (AIC_IPR1) Interrupt Pending */
#define AIC_IPR1_PID51 (0x1u << 19) /**< \brief (AIC_IPR1) Interrupt Pending */
#define AIC_IPR1_PID52 (0x1u << 20) /**< \brief (AIC_IPR1) Interrupt Pending */
#define AIC_IPR1_PID53 (0x1u << 21) /**< \brief (AIC_IPR1) Interrupt Pending */
#define AIC_IPR1_PID54 (0x1u << 22) /**< \brief (AIC_IPR1) Interrupt Pending */
#define AIC_IPR1_PID55 (0x1u << 23) /**< \brief (AIC_IPR1) Interrupt Pending */
#define AIC_IPR1_PID56 (0x1u << 24) /**< \brief (AIC_IPR1) Interrupt Pending */
#define AIC_IPR1_PID57 (0x1u << 25) /**< \brief (AIC_IPR1) Interrupt Pending */
#define AIC_IPR1_PID58 (0x1u << 26) /**< \brief (AIC_IPR1) Interrupt Pending */
#define AIC_IPR1_PID59 (0x1u << 27) /**< \brief (AIC_IPR1) Interrupt Pending */
#define AIC_IPR1_PID60 (0x1u << 28) /**< \brief (AIC_IPR1) Interrupt Pending */
#define AIC_IPR1_PID61 (0x1u << 29) /**< \brief (AIC_IPR1) Interrupt Pending */
#define AIC_IPR1_PID62 (0x1u << 30) /**< \brief (AIC_IPR1) Interrupt Pending */
#define AIC_IPR1_PID63 (0x1u << 31) /**< \brief (AIC_IPR1) Interrupt Pending */
/* -------- AIC_IPR2 : (AIC Offset: 0x28) Interrupt Pending Register 2 -------- */
#define AIC_IPR2_PID64 (0x1u << 0) /**< \brief (AIC_IPR2) Interrupt Pending */
#define AIC_IPR2_PID65 (0x1u << 1) /**< \brief (AIC_IPR2) Interrupt Pending */
#define AIC_IPR2_PID66 (0x1u << 2) /**< \brief (AIC_IPR2) Interrupt Pending */
#define AIC_IPR2_PID67 (0x1u << 3) /**< \brief (AIC_IPR2) Interrupt Pending */
#define AIC_IPR2_PID68 (0x1u << 4) /**< \brief (AIC_IPR2) Interrupt Pending */
#define AIC_IPR2_PID69 (0x1u << 5) /**< \brief (AIC_IPR2) Interrupt Pending */
#define AIC_IPR2_PID70 (0x1u << 6) /**< \brief (AIC_IPR2) Interrupt Pending */
#define AIC_IPR2_PID71 (0x1u << 7) /**< \brief (AIC_IPR2) Interrupt Pending */
#define AIC_IPR2_PID72 (0x1u << 8) /**< \brief (AIC_IPR2) Interrupt Pending */
#define AIC_IPR2_PID73 (0x1u << 9) /**< \brief (AIC_IPR2) Interrupt Pending */
#define AIC_IPR2_PID74 (0x1u << 10) /**< \brief (AIC_IPR2) Interrupt Pending */
#define AIC_IPR2_PID75 (0x1u << 11) /**< \brief (AIC_IPR2) Interrupt Pending */
#define AIC_IPR2_PID76 (0x1u << 12) /**< \brief (AIC_IPR2) Interrupt Pending */
#define AIC_IPR2_PID77 (0x1u << 13) /**< \brief (AIC_IPR2) Interrupt Pending */
#define AIC_IPR2_PID78 (0x1u << 14) /**< \brief (AIC_IPR2) Interrupt Pending */
#define AIC_IPR2_PID79 (0x1u << 15) /**< \brief (AIC_IPR2) Interrupt Pending */
#define AIC_IPR2_PID80 (0x1u << 16) /**< \brief (AIC_IPR2) Interrupt Pending */
#define AIC_IPR2_PID81 (0x1u << 17) /**< \brief (AIC_IPR2) Interrupt Pending */
#define AIC_IPR2_PID82 (0x1u << 18) /**< \brief (AIC_IPR2) Interrupt Pending */
#define AIC_IPR2_PID83 (0x1u << 19) /**< \brief (AIC_IPR2) Interrupt Pending */
#define AIC_IPR2_PID84 (0x1u << 20) /**< \brief (AIC_IPR2) Interrupt Pending */
#define AIC_IPR2_PID85 (0x1u << 21) /**< \brief (AIC_IPR2) Interrupt Pending */
#define AIC_IPR2_PID86 (0x1u << 22) /**< \brief (AIC_IPR2) Interrupt Pending */
#define AIC_IPR2_PID87 (0x1u << 23) /**< \brief (AIC_IPR2) Interrupt Pending */
#define AIC_IPR2_PID88 (0x1u << 24) /**< \brief (AIC_IPR2) Interrupt Pending */
#define AIC_IPR2_PID89 (0x1u << 25) /**< \brief (AIC_IPR2) Interrupt Pending */
#define AIC_IPR2_PID90 (0x1u << 26) /**< \brief (AIC_IPR2) Interrupt Pending */
#define AIC_IPR2_PID91 (0x1u << 27) /**< \brief (AIC_IPR2) Interrupt Pending */
#define AIC_IPR2_PID92 (0x1u << 28) /**< \brief (AIC_IPR2) Interrupt Pending */
#define AIC_IPR2_PID93 (0x1u << 29) /**< \brief (AIC_IPR2) Interrupt Pending */
#define AIC_IPR2_PID94 (0x1u << 30) /**< \brief (AIC_IPR2) Interrupt Pending */
#define AIC_IPR2_PID95 (0x1u << 31) /**< \brief (AIC_IPR2) Interrupt Pending */
/* -------- AIC_IPR3 : (AIC Offset: 0x2C) Interrupt Pending Register 3 -------- */
#define AIC_IPR3_PID96 (0x1u << 0) /**< \brief (AIC_IPR3) Interrupt Pending */
#define AIC_IPR3_PID97 (0x1u << 1) /**< \brief (AIC_IPR3) Interrupt Pending */
#define AIC_IPR3_PID98 (0x1u << 2) /**< \brief (AIC_IPR3) Interrupt Pending */
#define AIC_IPR3_PID99 (0x1u << 3) /**< \brief (AIC_IPR3) Interrupt Pending */
#define AIC_IPR3_PID100 (0x1u << 4) /**< \brief (AIC_IPR3) Interrupt Pending */
#define AIC_IPR3_PID101 (0x1u << 5) /**< \brief (AIC_IPR3) Interrupt Pending */
#define AIC_IPR3_PID102 (0x1u << 6) /**< \brief (AIC_IPR3) Interrupt Pending */
#define AIC_IPR3_PID103 (0x1u << 7) /**< \brief (AIC_IPR3) Interrupt Pending */
#define AIC_IPR3_PID104 (0x1u << 8) /**< \brief (AIC_IPR3) Interrupt Pending */
#define AIC_IPR3_PID105 (0x1u << 9) /**< \brief (AIC_IPR3) Interrupt Pending */
#define AIC_IPR3_PID106 (0x1u << 10) /**< \brief (AIC_IPR3) Interrupt Pending */
#define AIC_IPR3_PID107 (0x1u << 11) /**< \brief (AIC_IPR3) Interrupt Pending */
#define AIC_IPR3_PID108 (0x1u << 12) /**< \brief (AIC_IPR3) Interrupt Pending */
#define AIC_IPR3_PID109 (0x1u << 13) /**< \brief (AIC_IPR3) Interrupt Pending */
#define AIC_IPR3_PID110 (0x1u << 14) /**< \brief (AIC_IPR3) Interrupt Pending */
#define AIC_IPR3_PID111 (0x1u << 15) /**< \brief (AIC_IPR3) Interrupt Pending */
#define AIC_IPR3_PID112 (0x1u << 16) /**< \brief (AIC_IPR3) Interrupt Pending */
#define AIC_IPR3_PID113 (0x1u << 17) /**< \brief (AIC_IPR3) Interrupt Pending */
#define AIC_IPR3_PID114 (0x1u << 18) /**< \brief (AIC_IPR3) Interrupt Pending */
#define AIC_IPR3_PID115 (0x1u << 19) /**< \brief (AIC_IPR3) Interrupt Pending */
#define AIC_IPR3_PID116 (0x1u << 20) /**< \brief (AIC_IPR3) Interrupt Pending */
#define AIC_IPR3_PID117 (0x1u << 21) /**< \brief (AIC_IPR3) Interrupt Pending */
#define AIC_IPR3_PID118 (0x1u << 22) /**< \brief (AIC_IPR3) Interrupt Pending */
#define AIC_IPR3_PID119 (0x1u << 23) /**< \brief (AIC_IPR3) Interrupt Pending */
#define AIC_IPR3_PID120 (0x1u << 24) /**< \brief (AIC_IPR3) Interrupt Pending */
#define AIC_IPR3_PID121 (0x1u << 25) /**< \brief (AIC_IPR3) Interrupt Pending */
#define AIC_IPR3_PID122 (0x1u << 26) /**< \brief (AIC_IPR3) Interrupt Pending */
#define AIC_IPR3_PID123 (0x1u << 27) /**< \brief (AIC_IPR3) Interrupt Pending */
#define AIC_IPR3_PID124 (0x1u << 28) /**< \brief (AIC_IPR3) Interrupt Pending */
#define AIC_IPR3_PID125 (0x1u << 29) /**< \brief (AIC_IPR3) Interrupt Pending */
#define AIC_IPR3_PID126 (0x1u << 30) /**< \brief (AIC_IPR3) Interrupt Pending */
#define AIC_IPR3_PID127 (0x1u << 31) /**< \brief (AIC_IPR3) Interrupt Pending */
/* -------- AIC_IMR : (AIC Offset: 0x30) Interrupt Mask Register -------- */
#define AIC_IMR_INTM (0x1u << 0) /**< \brief (AIC_IMR) Interrupt Mask */
/* -------- AIC_CISR : (AIC Offset: 0x34) Core Interrupt Status Register -------- */
#define AIC_CISR_NFIQ (0x1u << 0) /**< \brief (AIC_CISR) NFIQ Status */
#define AIC_CISR_NIRQ (0x1u << 1) /**< \brief (AIC_CISR) NIRQ Status */
/* -------- AIC_EOICR : (AIC Offset: 0x38) End of Interrupt Command Register -------- */
#define AIC_EOICR_ENDIT (0x1u << 0) /**< \brief (AIC_EOICR) Interrupt Processing Complete Command */
/* -------- AIC_SPU : (AIC Offset: 0x3C) Spurious Interrupt Vector Register -------- */
#define AIC_SPU_SIVR_Pos 0
#define AIC_SPU_SIVR_Msk (0xffffffffu << AIC_SPU_SIVR_Pos) /**< \brief (AIC_SPU) Spurious Interrupt Vector Register */
#define AIC_SPU_SIVR(value) ((AIC_SPU_SIVR_Msk & ((value) << AIC_SPU_SIVR_Pos)))
/* -------- AIC_IECR : (AIC Offset: 0x40) Interrupt Enable Command Register -------- */
#define AIC_IECR_INTEN (0x1u << 0) /**< \brief (AIC_IECR) Interrupt Enable */
/* -------- AIC_IDCR : (AIC Offset: 0x44) Interrupt Disable Command Register -------- */
#define AIC_IDCR_INTD (0x1u << 0) /**< \brief (AIC_IDCR) Interrupt Disable */
/* -------- AIC_ICCR : (AIC Offset: 0x48) Interrupt Clear Command Register -------- */
#define AIC_ICCR_INTCLR (0x1u << 0) /**< \brief (AIC_ICCR) Interrupt Clear */
/* -------- AIC_ISCR : (AIC Offset: 0x4C) Interrupt Set Command Register -------- */
#define AIC_ISCR_INTSET (0x1u << 0) /**< \brief (AIC_ISCR) Interrupt Set */
/* -------- AIC_DCR : (AIC Offset: 0x6C) Debug Control Register -------- */
#define AIC_DCR_PROT (0x1u << 0) /**< \brief (AIC_DCR) Protection Mode */
#define AIC_DCR_GMSK (0x1u << 1) /**< \brief (AIC_DCR) General Interrupt Mask */
/* -------- AIC_WPMR : (AIC Offset: 0xE4) Write Protection Mode Register -------- */
#define AIC_WPMR_WPEN (0x1u << 0) /**< \brief (AIC_WPMR) Write Protection Enable */
#define AIC_WPMR_WPKEY_Pos 8
#define AIC_WPMR_WPKEY_Msk (0xffffffu << AIC_WPMR_WPKEY_Pos) /**< \brief (AIC_WPMR) Write Protection Key */
#define AIC_WPMR_WPKEY(value) ((AIC_WPMR_WPKEY_Msk & ((value) << AIC_WPMR_WPKEY_Pos)))
#define   AIC_WPMR_WPKEY_PASSWD (0x414943u << 8) /**< \brief (AIC_WPMR) Writing any other value in this field aborts the write operation of the WPEN bit.Always reads as 0. */
/* -------- AIC_WPSR : (AIC Offset: 0xE8) Write Protection Status Register -------- */
#define AIC_WPSR_WPVS (0x1u << 0) /**< \brief (AIC_WPSR) Write Protection Violation Status */
#define AIC_WPSR_WPVSRC_Pos 8
#define AIC_WPSR_WPVSRC_Msk (0xffffu << AIC_WPSR_WPVSRC_Pos) /**< \brief (AIC_WPSR) Write Protection Violation Source */
/* -------- AIC_VERSION : (AIC Offset: 0XFC) AIC Version Register -------- */
#define AIC_VERSION_VERSION_Pos 0
#define AIC_VERSION_VERSION_Msk (0xfffu << AIC_VERSION_VERSION_Pos) /**< \brief (AIC_VERSION) Version of the Hardware Module */
#define AIC_VERSION_MFN_Pos 16
#define AIC_VERSION_MFN_Msk (0x7u << AIC_VERSION_MFN_Pos) /**< \brief (AIC_VERSION) Metal Fix Number */

/*@}*/


#endif /* _SAMA5D2_AIC_COMPONENT_ */
