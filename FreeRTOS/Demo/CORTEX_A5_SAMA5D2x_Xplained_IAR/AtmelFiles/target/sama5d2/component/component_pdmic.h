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

#ifndef _SAMA5D2_PDMIC_COMPONENT_
#define _SAMA5D2_PDMIC_COMPONENT_

/* ============================================================================= */
/**  SOFTWARE API DEFINITION FOR Pulse Density Modulation Interface Controller */
/* ============================================================================= */
/** \addtogroup SAMA5D2_PDMIC Pulse Density Modulation Interface Controller */
/*@{*/

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
/** \brief Pdmic hardware registers */
typedef struct {
  __IO uint32_t PDMIC_CR;      /**< \brief (Pdmic Offset: 0x00) Control Register */
  __IO uint32_t PDMIC_MR;      /**< \brief (Pdmic Offset: 0x04) Mode Register */
  __I  uint32_t Reserved1[3];
  __I  uint32_t PDMIC_CDR;     /**< \brief (Pdmic Offset: 0x14) Converted Data Register */
  __O  uint32_t PDMIC_IER;     /**< \brief (Pdmic Offset: 0x18) Interrupt Enable Register */
  __O  uint32_t PDMIC_IDR;     /**< \brief (Pdmic Offset: 0x1C) Interrupt Disable Register */
  __I  uint32_t PDMIC_IMR;     /**< \brief (Pdmic Offset: 0x20) Interrupt Mask Register */
  __I  uint32_t PDMIC_ISR;     /**< \brief (Pdmic Offset: 0x24) Interrupt Status Register */
  __I  uint32_t Reserved2[12];
  __IO uint32_t PDMIC_DSPR0;   /**< \brief (Pdmic Offset: 0x58) DSP Configuration Register 0 */
  __IO uint32_t PDMIC_DSPR1;   /**< \brief (Pdmic Offset: 0x5C) DSP Configuration Register 1 */
  __I  uint32_t Reserved3[33];
  __IO uint32_t PDMIC_WPMR;    /**< \brief (Pdmic Offset: 0xE4) Write Protection Mode Register */
  __I  uint32_t PDMIC_WPSR;    /**< \brief (Pdmic Offset: 0xE8) Write Protection Status Register */
  __I  uint32_t Reserved4[4];
  __I  uint32_t PDMIC_VERSION; /**< \brief (Pdmic Offset: 0xFC) Version Register */
} Pdmic;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */
/* -------- PDMIC_CR : (PDMIC Offset: 0x00) Control Register -------- */
#define PDMIC_CR_SWRST (0x1u << 0) /**< \brief (PDMIC_CR) Software Reset */
#define PDMIC_CR_ENPDM (0x1u << 4) /**< \brief (PDMIC_CR) Enable PDM */
/* -------- PDMIC_MR : (PDMIC Offset: 0x04) Mode Register -------- */
#define PDMIC_MR_PRESCAL_Pos 8
#define PDMIC_MR_PRESCAL_Msk (0x7fu << PDMIC_MR_PRESCAL_Pos) /**< \brief (PDMIC_MR) Prescaler Rate Selection */
#define PDMIC_MR_PRESCAL(value) ((PDMIC_MR_PRESCAL_Msk & ((value) << PDMIC_MR_PRESCAL_Pos)))
/* -------- PDMIC_CDR : (PDMIC Offset: 0x14) Converted Data Register -------- */
#define PDMIC_CDR_DATA_Pos 0
#define PDMIC_CDR_DATA_Msk (0xffffffffu << PDMIC_CDR_DATA_Pos) /**< \brief (PDMIC_CDR) Data Converted */
/* -------- PDMIC_IER : (PDMIC Offset: 0x18) Interrupt Enable Register -------- */
#define PDMIC_IER_DRDY (0x1u << 24) /**< \brief (PDMIC_IER) Data Ready Interrupt Enable */
#define PDMIC_IER_OVRE (0x1u << 25) /**< \brief (PDMIC_IER) Overrun Error Interrupt Enable */
/* -------- PDMIC_IDR : (PDMIC Offset: 0x1C) Interrupt Disable Register -------- */
#define PDMIC_IDR_DRDY (0x1u << 24) /**< \brief (PDMIC_IDR) Data Ready Interrupt Disable */
#define PDMIC_IDR_OVRE (0x1u << 25) /**< \brief (PDMIC_IDR) General Overrun Error Interrupt Disable */
/* -------- PDMIC_IMR : (PDMIC Offset: 0x20) Interrupt Mask Register -------- */
#define PDMIC_IMR_DRDY (0x1u << 24) /**< \brief (PDMIC_IMR) Data Ready Interrupt Mask */
#define PDMIC_IMR_OVRE (0x1u << 25) /**< \brief (PDMIC_IMR) General Overrun Error Interrupt Mask */
/* -------- PDMIC_ISR : (PDMIC Offset: 0x24) Interrupt Status Register -------- */
#define PDMIC_ISR_FIFOCNT_Pos 16
#define PDMIC_ISR_FIFOCNT_Msk (0xffu << PDMIC_ISR_FIFOCNT_Pos) /**< \brief (PDMIC_ISR) FIFO Count */
#define PDMIC_ISR_DRDY (0x1u << 24) /**< \brief (PDMIC_ISR) Data Ready (cleared by reading PDMIC_CDR) */
#define PDMIC_ISR_OVRE (0x1u << 25) /**< \brief (PDMIC_ISR) Overrun Error (cleared on read) */
/* -------- PDMIC_DSPR0 : (PDMIC Offset: 0x58) DSP Configuration Register 0 -------- */
#define PDMIC_DSPR0_HPFBYP (0x1u << 1) /**< \brief (PDMIC_DSPR0) High-Pass Filter Bypass */
#define PDMIC_DSPR0_SINBYP (0x1u << 2) /**< \brief (PDMIC_DSPR0) SINCC Filter Bypass */
#define PDMIC_DSPR0_SIZE (0x1u << 3) /**< \brief (PDMIC_DSPR0) Data Size */
#define PDMIC_DSPR0_OSR_Pos 4
#define PDMIC_DSPR0_OSR_Msk (0x7u << PDMIC_DSPR0_OSR_Pos) /**< \brief (PDMIC_DSPR0) Oversampling Ratio */
#define PDMIC_DSPR0_OSR(value) ((PDMIC_DSPR0_OSR_Msk & ((value) << PDMIC_DSPR0_OSR_Pos)))
#define   PDMIC_DSPR0_OSR_128 (0x0u << 4) /**< \brief (PDMIC_DSPR0) Oversampling ratio is 128 */
#define   PDMIC_DSPR0_OSR_64 (0x1u << 4) /**< \brief (PDMIC_DSPR0) Oversampling ratio is 64 */
#define PDMIC_DSPR0_SCALE_Pos 8
#define PDMIC_DSPR0_SCALE_Msk (0xfu << PDMIC_DSPR0_SCALE_Pos) /**< \brief (PDMIC_DSPR0) Data Scale */
#define PDMIC_DSPR0_SCALE(value) ((PDMIC_DSPR0_SCALE_Msk & ((value) << PDMIC_DSPR0_SCALE_Pos)))
#define PDMIC_DSPR0_SHIFT_Pos 12
#define PDMIC_DSPR0_SHIFT_Msk (0xfu << PDMIC_DSPR0_SHIFT_Pos) /**< \brief (PDMIC_DSPR0) Data Shift */
#define PDMIC_DSPR0_SHIFT(value) ((PDMIC_DSPR0_SHIFT_Msk & ((value) << PDMIC_DSPR0_SHIFT_Pos)))
/* -------- PDMIC_DSPR1 : (PDMIC Offset: 0x5C) DSP Configuration Register 1 -------- */
#define PDMIC_DSPR1_DGAIN_Pos 0
#define PDMIC_DSPR1_DGAIN_Msk (0x7fffu << PDMIC_DSPR1_DGAIN_Pos) /**< \brief (PDMIC_DSPR1) Gain Correction */
#define PDMIC_DSPR1_DGAIN(value) ((PDMIC_DSPR1_DGAIN_Msk & ((value) << PDMIC_DSPR1_DGAIN_Pos)))
#define PDMIC_DSPR1_OFFSET_Pos 16
#define PDMIC_DSPR1_OFFSET_Msk (0xffffu << PDMIC_DSPR1_OFFSET_Pos) /**< \brief (PDMIC_DSPR1) Offset Correction */
#define PDMIC_DSPR1_OFFSET(value) ((PDMIC_DSPR1_OFFSET_Msk & ((value) << PDMIC_DSPR1_OFFSET_Pos)))
/* -------- PDMIC_WPMR : (PDMIC Offset: 0xE4) Write Protection Mode Register -------- */
#define PDMIC_WPMR_WPEN (0x1u << 0) /**< \brief (PDMIC_WPMR) Write Protection Enable */
#define PDMIC_WPMR_WPKEY_Pos 8
#define PDMIC_WPMR_WPKEY_Msk (0xffffffu << PDMIC_WPMR_WPKEY_Pos) /**< \brief (PDMIC_WPMR) Write Protection Key */
#define PDMIC_WPMR_WPKEY(value) ((PDMIC_WPMR_WPKEY_Msk & ((value) << PDMIC_WPMR_WPKEY_Pos)))
#define   PDMIC_WPMR_WPKEY_PASSWD (0x414443u << 8) /**< \brief (PDMIC_WPMR) Writing any other value in this field aborts the write operation of the WPEN bit.Always reads as 0. */
/* -------- PDMIC_WPSR : (PDMIC Offset: 0xE8) Write Protection Status Register -------- */
#define PDMIC_WPSR_WPVS (0x1u << 0) /**< \brief (PDMIC_WPSR) Write Protection Violation Status */
#define PDMIC_WPSR_WPVSRC_Pos 8
#define PDMIC_WPSR_WPVSRC_Msk (0xffffu << PDMIC_WPSR_WPVSRC_Pos) /**< \brief (PDMIC_WPSR) Write Protection Violation Source */
/* -------- PDMIC_VERSION : (PDMIC Offset: 0xFC) Version Register -------- */
#define PDMIC_VERSION_VERSION_Pos 0
#define PDMIC_VERSION_VERSION_Msk (0xfffu << PDMIC_VERSION_VERSION_Pos) /**< \brief (PDMIC_VERSION) Version of the Hardware Module */
#define PDMIC_VERSION_MFN_Pos 16
#define PDMIC_VERSION_MFN_Msk (0x7u << PDMIC_VERSION_MFN_Pos) /**< \brief (PDMIC_VERSION) Metal Fix Number */

/*@}*/


#endif /* _SAMA5D2_PDMIC_COMPONENT_ */
