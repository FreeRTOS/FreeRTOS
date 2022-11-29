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

#ifndef _SAMA5D2_CLASSD_COMPONENT_
#define _SAMA5D2_CLASSD_COMPONENT_

/* ============================================================================= */
/**  SOFTWARE API DEFINITION FOR Audio Class D Amplifier */
/* ============================================================================= */
/** \addtogroup SAMA5D2_CLASSD Audio Class D Amplifier */
/*@{*/

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
/** \brief Classd hardware registers */
typedef struct {
  __O  uint32_t CLASSD_CR;      /**< \brief (Classd Offset: 0x00) Control Register */
  __IO uint32_t CLASSD_MR;      /**< \brief (Classd Offset: 0x04) Mode Register */
  __IO uint32_t CLASSD_INTPMR;  /**< \brief (Classd Offset: 0x08) Interpolator Mode Register */
  __I  uint32_t CLASSD_INTSR;   /**< \brief (Classd Offset: 0x0C) Interpolator Status Register */
  __IO uint32_t CLASSD_THR;     /**< \brief (Classd Offset: 0x10) Transmit Holding Register */
  __O  uint32_t CLASSD_IER;     /**< \brief (Classd Offset: 0x14) Interrupt Enable Register */
  __O  uint32_t CLASSD_IDR;     /**< \brief (Classd Offset: 0x18) Interrupt Disable Register */
  __IO uint32_t CLASSD_IMR;     /**< \brief (Classd Offset: 0x1C) Interrupt Mask Register */
  __I  uint32_t CLASSD_ISR;     /**< \brief (Classd Offset: 0x20) Interrupt Status Register */
  __I  uint32_t Reserved1[48];
  __IO uint32_t CLASSD_WPMR;    /**< \brief (Classd Offset: 0xE4) Write Protection Mode Register */
  __I  uint32_t Reserved2[5];
  __I  uint32_t CLASSD_VERSION; /**< \brief (Classd Offset: 0xFC) IP Version Register */
} Classd;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */
/* -------- CLASSD_CR : (CLASSD Offset: 0x00) Control Register -------- */
#define CLASSD_CR_SWRST (0x1u << 0) /**< \brief (CLASSD_CR) Software Reset */
/* -------- CLASSD_MR : (CLASSD Offset: 0x04) Mode Register -------- */
#define CLASSD_MR_LEN (0x1u << 0) /**< \brief (CLASSD_MR) Left Channel Enable */
#define CLASSD_MR_LMUTE (0x1u << 1) /**< \brief (CLASSD_MR) Left Channel Mute */
#define CLASSD_MR_REN (0x1u << 4) /**< \brief (CLASSD_MR) Right Channel Enable */
#define CLASSD_MR_RMUTE (0x1u << 5) /**< \brief (CLASSD_MR) Right Channel Mute */
#define CLASSD_MR_PWMTYP (0x1u << 8) /**< \brief (CLASSD_MR) PWM Modulation Type */
#define CLASSD_MR_NON_OVERLAP (0x1u << 16) /**< \brief (CLASSD_MR) Non-Overlapping Enable */
#define CLASSD_MR_NOVRVAL_Pos 20
#define CLASSD_MR_NOVRVAL_Msk (0x3u << CLASSD_MR_NOVRVAL_Pos) /**< \brief (CLASSD_MR) Non-Overlapping Value */
#define CLASSD_MR_NOVRVAL(value) ((CLASSD_MR_NOVRVAL_Msk & ((value) << CLASSD_MR_NOVRVAL_Pos)))
#define   CLASSD_MR_NOVRVAL_5NS (0x0u << 20) /**< \brief (CLASSD_MR) Non-overlapping time is 5 ns */
#define   CLASSD_MR_NOVRVAL_10NS (0x1u << 20) /**< \brief (CLASSD_MR) Non-overlapping time is 10 ns */
#define   CLASSD_MR_NOVRVAL_15NS (0x2u << 20) /**< \brief (CLASSD_MR) Non-overlapping time is 15 ns */
#define   CLASSD_MR_NOVRVAL_20NS (0x3u << 20) /**< \brief (CLASSD_MR) Non-overlapping time is 20 ns */
/* -------- CLASSD_INTPMR : (CLASSD Offset: 0x08) Interpolator Mode Register -------- */
#define CLASSD_INTPMR_ATTL_Pos 0
#define CLASSD_INTPMR_ATTL_Msk (0x7fu << CLASSD_INTPMR_ATTL_Pos) /**< \brief (CLASSD_INTPMR) Left Channel Attenuation */
#define CLASSD_INTPMR_ATTL(value) ((CLASSD_INTPMR_ATTL_Msk & ((value) << CLASSD_INTPMR_ATTL_Pos)))
#define CLASSD_INTPMR_ATTR_Pos 8
#define CLASSD_INTPMR_ATTR_Msk (0x7fu << CLASSD_INTPMR_ATTR_Pos) /**< \brief (CLASSD_INTPMR) Right Channel Attenuation */
#define CLASSD_INTPMR_ATTR(value) ((CLASSD_INTPMR_ATTR_Msk & ((value) << CLASSD_INTPMR_ATTR_Pos)))
#define CLASSD_INTPMR_DSPCLKFREQ (0x1u << 16) /**< \brief (CLASSD_INTPMR) DSP Clock Frequency */
#define   CLASSD_INTPMR_DSPCLKFREQ_12M288 (0x0u << 16) /**< \brief (CLASSD_INTPMR) DSP Clock (DSPCLK) is 12.288 MHz */
#define   CLASSD_INTPMR_DSPCLKFREQ_11M2896 (0x1u << 16) /**< \brief (CLASSD_INTPMR) DSP Clock (DSPCLK) is 11.2896 MHz */
#define CLASSD_INTPMR_DEEMP (0x1u << 18) /**< \brief (CLASSD_INTPMR) Enable De-emphasis Filter */
#define   CLASSD_INTPMR_DEEMP_DISABLED (0x0u << 18) /**< \brief (CLASSD_INTPMR) De-emphasis filter is disabled */
#define   CLASSD_INTPMR_DEEMP_ENABLED (0x1u << 18) /**< \brief (CLASSD_INTPMR) De-emphasis filter is enabled */
#define CLASSD_INTPMR_SWAP (0x1u << 19) /**< \brief (CLASSD_INTPMR) Swap Left and Right Channels */
#define   CLASSD_INTPMR_SWAP_LEFT_ON_LSB (0x0u << 19) /**< \brief (CLASSD_INTPMR) Left channel is on CLASSD_THR[15:0], right channel is on CLASSD_THR[31:16] */
#define   CLASSD_INTPMR_SWAP_RIGHT_ON_LSB (0x1u << 19) /**< \brief (CLASSD_INTPMR) Right channel is on CLASSD_THR[15:0], left channel is on CLASSD_THR[31:16] */
#define CLASSD_INTPMR_FRAME_Pos 20
#define CLASSD_INTPMR_FRAME_Msk (0x7u << CLASSD_INTPMR_FRAME_Pos) /**< \brief (CLASSD_INTPMR) CLASSD Incoming Data Sampling Frequency */
#define CLASSD_INTPMR_FRAME(value) ((CLASSD_INTPMR_FRAME_Msk & ((value) << CLASSD_INTPMR_FRAME_Pos)))
#define   CLASSD_INTPMR_FRAME_FRAME_8K (0x0u << 20) /**< \brief (CLASSD_INTPMR) 8 kHz */
#define   CLASSD_INTPMR_FRAME_FRAME_16K (0x1u << 20) /**< \brief (CLASSD_INTPMR) 16 kHz */
#define   CLASSD_INTPMR_FRAME_FRAME_32K (0x2u << 20) /**< \brief (CLASSD_INTPMR) 32 kHz */
#define   CLASSD_INTPMR_FRAME_FRAME_48K (0x3u << 20) /**< \brief (CLASSD_INTPMR) 48 kHz */
#define   CLASSD_INTPMR_FRAME_FRAME_96K (0x4u << 20) /**< \brief (CLASSD_INTPMR) 96 kHz */
#define   CLASSD_INTPMR_FRAME_FRAME_22K (0x5u << 20) /**< \brief (CLASSD_INTPMR) 22.05 kHz */
#define   CLASSD_INTPMR_FRAME_FRAME_44K (0x6u << 20) /**< \brief (CLASSD_INTPMR) 44.1 kHz */
#define   CLASSD_INTPMR_FRAME_FRAME_88K (0x7u << 20) /**< \brief (CLASSD_INTPMR) 88.2 kHz */
#define CLASSD_INTPMR_EQCFG_Pos 24
#define CLASSD_INTPMR_EQCFG_Msk (0xfu << CLASSD_INTPMR_EQCFG_Pos) /**< \brief (CLASSD_INTPMR) Equalization Selection */
#define CLASSD_INTPMR_EQCFG(value) ((CLASSD_INTPMR_EQCFG_Msk & ((value) << CLASSD_INTPMR_EQCFG_Pos)))
#define   CLASSD_INTPMR_EQCFG_FLAT (0x0u << 24) /**< \brief (CLASSD_INTPMR) Flat Response */
#define   CLASSD_INTPMR_EQCFG_BBOOST12 (0x1u << 24) /**< \brief (CLASSD_INTPMR) Bass boost +12 dB */
#define   CLASSD_INTPMR_EQCFG_BBOOST6 (0x2u << 24) /**< \brief (CLASSD_INTPMR) Bass boost +6 dB */
#define   CLASSD_INTPMR_EQCFG_BCUT12 (0x3u << 24) /**< \brief (CLASSD_INTPMR) Bass cut -12 dB */
#define   CLASSD_INTPMR_EQCFG_BCUT6 (0x4u << 24) /**< \brief (CLASSD_INTPMR) Bass cut -6 dB */
#define   CLASSD_INTPMR_EQCFG_MBOOST3 (0x5u << 24) /**< \brief (CLASSD_INTPMR) Medium boost +3 dB */
#define   CLASSD_INTPMR_EQCFG_MBOOST8 (0x6u << 24) /**< \brief (CLASSD_INTPMR) Medium boost +8 dB */
#define   CLASSD_INTPMR_EQCFG_MCUT3 (0x7u << 24) /**< \brief (CLASSD_INTPMR) Medium cut -3 dB */
#define   CLASSD_INTPMR_EQCFG_MCUT8 (0x8u << 24) /**< \brief (CLASSD_INTPMR) Medium cut -8 dB */
#define   CLASSD_INTPMR_EQCFG_TBOOST12 (0x9u << 24) /**< \brief (CLASSD_INTPMR) Treble boost +12 dB */
#define   CLASSD_INTPMR_EQCFG_TBOOST6 (0xAu << 24) /**< \brief (CLASSD_INTPMR) Treble boost +6 dB */
#define   CLASSD_INTPMR_EQCFG_TCUT12 (0xBu << 24) /**< \brief (CLASSD_INTPMR) Treble cut -12 dB */
#define   CLASSD_INTPMR_EQCFG_TCUT6 (0xCu << 24) /**< \brief (CLASSD_INTPMR) Treble cut -6 dB */
#define CLASSD_INTPMR_MONO (0x1u << 28) /**< \brief (CLASSD_INTPMR) Mono Signal */
#define   CLASSD_INTPMR_MONO_DISABLED (0x0u << 28) /**< \brief (CLASSD_INTPMR) The signal is sent stereo to the left and right channels. */
#define   CLASSD_INTPMR_MONO_ENABLED (0x1u << 28) /**< \brief (CLASSD_INTPMR) The same signal is sent on both left and right channels. The sent signal is defined by the MONOMODE field value. */
#define CLASSD_INTPMR_MONOMODE_Pos 29
#define CLASSD_INTPMR_MONOMODE_Msk (0x3u << CLASSD_INTPMR_MONOMODE_Pos) /**< \brief (CLASSD_INTPMR) Mono Mode Selection */
#define CLASSD_INTPMR_MONOMODE(value) ((CLASSD_INTPMR_MONOMODE_Msk & ((value) << CLASSD_INTPMR_MONOMODE_Pos)))
#define   CLASSD_INTPMR_MONOMODE_MONOMIX (0x0u << 29) /**< \brief (CLASSD_INTPMR) (left + right) / 2 is sent on both channels */
#define   CLASSD_INTPMR_MONOMODE_MONOSAT (0x1u << 29) /**< \brief (CLASSD_INTPMR) (left + right) is sent to both channels. If the sum is too high, the result is saturated. */
#define   CLASSD_INTPMR_MONOMODE_MONOLEFT (0x2u << 29) /**< \brief (CLASSD_INTPMR) THR[15:0] is sent on both left and right channels */
#define   CLASSD_INTPMR_MONOMODE_MONORIGHT (0x3u << 29) /**< \brief (CLASSD_INTPMR) THR[31:16] is sent on both left and right channels */
/* -------- CLASSD_INTSR : (CLASSD Offset: 0x0C) Interpolator Status Register -------- */
#define CLASSD_INTSR_CFGERR (0x1u << 0) /**< \brief (CLASSD_INTSR) Configuration Error */
/* -------- CLASSD_THR : (CLASSD Offset: 0x10) Transmit Holding Register -------- */
#define CLASSD_THR_LDATA_Pos 0
#define CLASSD_THR_LDATA_Msk (0xffffu << CLASSD_THR_LDATA_Pos) /**< \brief (CLASSD_THR) Left Channel Data */
#define CLASSD_THR_LDATA(value) ((CLASSD_THR_LDATA_Msk & ((value) << CLASSD_THR_LDATA_Pos)))
#define CLASSD_THR_RDATA_Pos 16
#define CLASSD_THR_RDATA_Msk (0xffffu << CLASSD_THR_RDATA_Pos) /**< \brief (CLASSD_THR) Right Channel Data */
#define CLASSD_THR_RDATA(value) ((CLASSD_THR_RDATA_Msk & ((value) << CLASSD_THR_RDATA_Pos)))
/* -------- CLASSD_IER : (CLASSD Offset: 0x14) Interrupt Enable Register -------- */
#define CLASSD_IER_DATRDY (0x1u << 0) /**< \brief (CLASSD_IER) Data Ready */
/* -------- CLASSD_IDR : (CLASSD Offset: 0x18) Interrupt Disable Register -------- */
#define CLASSD_IDR_DATRDY (0x1u << 0) /**< \brief (CLASSD_IDR) Data Ready */
/* -------- CLASSD_IMR : (CLASSD Offset: 0x1C) Interrupt Mask Register -------- */
#define CLASSD_IMR_DATRDY (0x1u << 0) /**< \brief (CLASSD_IMR) Data Ready */
/* -------- CLASSD_ISR : (CLASSD Offset: 0x20) Interrupt Status Register -------- */
#define CLASSD_ISR_DATRDY (0x1u << 0) /**< \brief (CLASSD_ISR) Data Ready */
/* -------- CLASSD_WPMR : (CLASSD Offset: 0xE4) Write Protection Mode Register -------- */
#define CLASSD_WPMR_WPEN (0x1u << 0) /**< \brief (CLASSD_WPMR) Write Protection Enable */
#define CLASSD_WPMR_WPKEY_Pos 8
#define CLASSD_WPMR_WPKEY_Msk (0xffffffu << CLASSD_WPMR_WPKEY_Pos) /**< \brief (CLASSD_WPMR) Write Protection Key */
#define CLASSD_WPMR_WPKEY(value) ((CLASSD_WPMR_WPKEY_Msk & ((value) << CLASSD_WPMR_WPKEY_Pos)))
#define   CLASSD_WPMR_WPKEY_PASSWD (0x434C44u << 8) /**< \brief (CLASSD_WPMR) Writing any other value in this field aborts the write operation of the WPEN bit.Always reads as 0. */
/* -------- CLASSD_VERSION : (CLASSD Offset: 0xFC) IP Version Register -------- */
#define CLASSD_VERSION_VERSION_Pos 0
#define CLASSD_VERSION_VERSION_Msk (0xfffu << CLASSD_VERSION_VERSION_Pos) /**< \brief (CLASSD_VERSION) Version of the Hardware Module */
#define CLASSD_VERSION_MFN_Pos 16
#define CLASSD_VERSION_MFN_Msk (0x7u << CLASSD_VERSION_MFN_Pos) /**< \brief (CLASSD_VERSION) Metal Fix Number */

/*@}*/


#endif /* _SAMA5D2_CLASSD_COMPONENT_ */
