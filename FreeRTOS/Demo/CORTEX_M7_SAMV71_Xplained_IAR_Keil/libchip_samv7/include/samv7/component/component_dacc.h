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

#ifndef _SAM_DACC_COMPONENT_
#define _SAM_DACC_COMPONENT_

/* ============================================================================= */
/**  SOFTWARE API DEFINITION FOR Digital-to-Analog Converter Controller */
/* ============================================================================= */
/** \addtogroup SAM_DACC Digital-to-Analog Converter Controller */
/*@{*/

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
/** \brief Dacc hardware registers */
typedef struct {
  __O  uint32_t DACC_CR;       /**< \brief (Dacc Offset: 0x00) Control Register */
  __IO uint32_t DACC_MR;       /**< \brief (Dacc Offset: 0x04) Mode Register */
  __IO uint32_t DACC_TRIGR;    /**< \brief (Dacc Offset: 0x08) Trigger Register */
  __I  uint32_t Reserved1[1];
  __O  uint32_t DACC_CHER;     /**< \brief (Dacc Offset: 0x10) Channel Enable Register */
  __O  uint32_t DACC_CHDR;     /**< \brief (Dacc Offset: 0x14) Channel Disable Register */
  __I  uint32_t DACC_CHSR;     /**< \brief (Dacc Offset: 0x18) Channel Status Register */
  __O  uint32_t DACC_CDR[2];   /**< \brief (Dacc Offset: 0x1C) Conversion Data Register */
  __O  uint32_t DACC_IER;      /**< \brief (Dacc Offset: 0x24) Interrupt Enable Register */
  __O  uint32_t DACC_IDR;      /**< \brief (Dacc Offset: 0x28) Interrupt Disable Register */
  __I  uint32_t DACC_IMR;      /**< \brief (Dacc Offset: 0x2C) Interrupt Mask Register */
  __I  uint32_t DACC_ISR;      /**< \brief (Dacc Offset: 0x30) Interrupt Status Register */
  __I  uint32_t Reserved2[24];
  __IO uint32_t DACC_ACR;      /**< \brief (Dacc Offset: 0x94) Analog Current Register */
  __I  uint32_t Reserved3[19];
  __IO uint32_t DACC_WPMR;     /**< \brief (Dacc Offset: 0xE4) Write Protection Mode register */
  __I  uint32_t DACC_WPSR;     /**< \brief (Dacc Offset: 0xE8) Write Protection Status register */
} Dacc;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */
/* -------- DACC_CR : (DACC Offset: 0x00) Control Register -------- */
#define DACC_CR_SWRST (0x1u << 0) /**< \brief (DACC_CR) Software Reset */
/* -------- DACC_MR : (DACC Offset: 0x04) Mode Register -------- */
#define DACC_MR_MAXS0 (0x1u << 0) /**< \brief (DACC_MR) Max Speed Mode for Channel 0 */
#define   DACC_MR_MAXS0_TRIG_EVENT (0x0u << 0) /**< \brief (DACC_MR) Triggered by selected event */
#define   DACC_MR_MAXS0_MAXIMUM (0x1u << 0) /**< \brief (DACC_MR) Max Speed Mode enabled */
#define DACC_MR_MAXS1 (0x1u << 1) /**< \brief (DACC_MR) Max Speed Mode for Channel 1 */
#define   DACC_MR_MAXS1_TRIG_EVENT (0x0u << 1) /**< \brief (DACC_MR) Triggered by selected event */
#define   DACC_MR_MAXS1_MAXIMUM (0x1u << 1) /**< \brief (DACC_MR) Max Speed Mode enabled */
#define DACC_MR_WORD (0x1u << 4) /**< \brief (DACC_MR) Word Transfer Mode */
#define   DACC_MR_WORD_DISABLED (0x0u << 4) /**< \brief (DACC_MR) One data to convert is written to the FIFO per access to DACC */
#define   DACC_MR_WORD_ENABLED (0x1u << 4) /**< \brief (DACC_MR) Two data to convert are written to the FIFO per access to DACC (reduces number of requests to DMA and the number of system bus accesses) */
#define DACC_MR_SLEEP (0x1u << 5) /**< \brief (DACC_MR) Sleep Mode */
#define   DACC_MR_SLEEP_DISABLED (0x0u << 5) /**< \brief (DACC_MR) The DAC Core and reference voltage circuitry are kept ON between conversions.For the first conversion, a startup time defined by the analog cell is applied. Note that in this mode, STARTUP time is only required once, at start up. */
#define   DACC_MR_SLEEP_ENABLED (0x1u << 5) /**< \brief (DACC_MR) The DAC Core and reference voltage circuitry are OFF between conversions. */
#define DACC_MR_REFRESH_Pos 8
#define DACC_MR_REFRESH_Msk (0xffu << DACC_MR_REFRESH_Pos) /**< \brief (DACC_MR) Refresh Period */
#define DACC_MR_REFRESH(value) ((DACC_MR_REFRESH_Msk & ((value) << DACC_MR_REFRESH_Pos)))
#define DACC_MR_DIFF (0x1u << 23) /**< \brief (DACC_MR) Differential Mode */
#define   DACC_MR_DIFF_DISABLED (0x0u << 23) /**< \brief (DACC_MR) DAC0 and DAC1 outputs can be separately configured */
#define   DACC_MR_DIFF_ENABLED (0x1u << 23) /**< \brief (DACC_MR) DACP and DACN outputs are configured by the channel 0 value. */
#define DACC_MR_PRESCALER_Pos 24
#define DACC_MR_PRESCALER_Msk (0xfu << DACC_MR_PRESCALER_Pos) /**< \brief (DACC_MR) Peripheral Clock to DAC Clock Ratio */
#define DACC_MR_PRESCALER(value) ((DACC_MR_PRESCALER_Msk & ((value) << DACC_MR_PRESCALER_Pos)))
/* -------- DACC_TRIGR : (DACC Offset: 0x08) Trigger Register -------- */
#define DACC_TRIGR_TRGEN0 (0x1u << 0) /**< \brief (DACC_TRIGR) Trigger Enable of Channel 0 */
#define   DACC_TRIGR_TRGEN0_DIS (0x0u << 0) /**< \brief (DACC_TRIGR) External trigger mode disabled. DAC is in free running mode. */
#define   DACC_TRIGR_TRGEN0_EN (0x1u << 0) /**< \brief (DACC_TRIGR) External trigger mode enabled. */
#define DACC_TRIGR_TRGEN1 (0x1u << 1) /**< \brief (DACC_TRIGR) Trigger Enable of Channel 1 */
#define   DACC_TRIGR_TRGEN1_DIS (0x0u << 1) /**< \brief (DACC_TRIGR) External trigger mode disabled. DAC is in free running mode. */
#define   DACC_TRIGR_TRGEN1_EN (0x1u << 1) /**< \brief (DACC_TRIGR) External trigger mode enabled. */
#define DACC_TRIGR_TRGSEL0_Pos 4
#define DACC_TRIGR_TRGSEL0_Msk (0x7u << DACC_TRIGR_TRGSEL0_Pos) /**< \brief (DACC_TRIGR) Trigger Selection of Channel 0 */
#define   DACC_TRIGR_TRGSEL0_TRGSEL0 (0x0u << 4) /**< \brief (DACC_TRIGR) TRGSEL: Trigger Selection */
#define   DACC_TRIGR_TRGSEL0_TRGSEL1 (0x1u << 4) /**< \brief (DACC_TRIGR) TRGSEL: Trigger Selection */
#define   DACC_TRIGR_TRGSEL0_TRGSEL2 (0x2u << 4) /**< \brief (DACC_TRIGR) TRGSEL: Trigger Selection */
#define   DACC_TRIGR_TRGSEL0_TRGSEL3 (0x3u << 4) /**< \brief (DACC_TRIGR) TRGSEL: Trigger Selection */
#define   DACC_TRIGR_TRGSEL0_TRGSEL4 (0x4u << 4) /**< \brief (DACC_TRIGR) TRGSEL: Trigger Selection */
#define   DACC_TRIGR_TRGSEL0_TRGSEL5 (0x5u << 4) /**< \brief (DACC_TRIGR) TRGSEL: Trigger Selection */
#define   DACC_TRIGR_TRGSEL0_TRGSEL6 (0x6u << 4) /**< \brief (DACC_TRIGR) TRGSEL: Trigger Selection */
#define DACC_TRIGR_TRGSEL1_Pos 8
#define DACC_TRIGR_TRGSEL1_Msk (0x7u << DACC_TRIGR_TRGSEL1_Pos) /**< \brief (DACC_TRIGR) Trigger Selection of Channel 1 */
#define   DACC_TRIGR_TRGSEL1_TRGSEL0 (0x0u << 8) /**< \brief (DACC_TRIGR) TRGSEL: Trigger Selection */
#define   DACC_TRIGR_TRGSEL1_TRGSEL1 (0x1u << 8) /**< \brief (DACC_TRIGR) TRGSEL: Trigger Selection */
#define   DACC_TRIGR_TRGSEL1_TRGSEL2 (0x2u << 8) /**< \brief (DACC_TRIGR) TRGSEL: Trigger Selection */
#define   DACC_TRIGR_TRGSEL1_TRGSEL3 (0x3u << 8) /**< \brief (DACC_TRIGR) TRGSEL: Trigger Selection */
#define   DACC_TRIGR_TRGSEL1_TRGSEL4 (0x4u << 8) /**< \brief (DACC_TRIGR) TRGSEL: Trigger Selection */
#define   DACC_TRIGR_TRGSEL1_TRGSEL5 (0x5u << 8) /**< \brief (DACC_TRIGR) TRGSEL: Trigger Selection */
#define   DACC_TRIGR_TRGSEL1_TRGSEL6 (0x6u << 8) /**< \brief (DACC_TRIGR) TRGSEL: Trigger Selection */
#define DACC_TRIGR_OSR0_Pos 16
#define DACC_TRIGR_OSR0_Msk (0x7u << DACC_TRIGR_OSR0_Pos) /**< \brief (DACC_TRIGR) Over Sampling Ratio of Channel 0 */
#define   DACC_TRIGR_OSR0_OSR_1 (0x0u << 16) /**< \brief (DACC_TRIGR) OSR = 1 */
#define   DACC_TRIGR_OSR0_OSR_2 (0x1u << 16) /**< \brief (DACC_TRIGR) OSR = 2 */
#define   DACC_TRIGR_OSR0_OSR_4 (0x2u << 16) /**< \brief (DACC_TRIGR) OSR = 4 */
#define   DACC_TRIGR_OSR0_OSR_8 (0x3u << 16) /**< \brief (DACC_TRIGR) OSR = 8 */
#define   DACC_TRIGR_OSR0_OSR_16 (0x4u << 16) /**< \brief (DACC_TRIGR) OSR = 16 */
#define   DACC_TRIGR_OSR0_OSR_32 (0x5u << 16) /**< \brief (DACC_TRIGR) OSR = 32 */
#define DACC_TRIGR_OSR1_Pos 20
#define DACC_TRIGR_OSR1_Msk (0x7u << DACC_TRIGR_OSR1_Pos) /**< \brief (DACC_TRIGR) Over Sampling Ratio of Channel 1 */
#define   DACC_TRIGR_OSR1_OSR_1 (0x0u << 20) /**< \brief (DACC_TRIGR) OSR = 1 */
#define   DACC_TRIGR_OSR1_OSR_2 (0x1u << 20) /**< \brief (DACC_TRIGR) OSR = 2 */
#define   DACC_TRIGR_OSR1_OSR_4 (0x2u << 20) /**< \brief (DACC_TRIGR) OSR = 4 */
#define   DACC_TRIGR_OSR1_OSR_8 (0x3u << 20) /**< \brief (DACC_TRIGR) OSR = 8 */
#define   DACC_TRIGR_OSR1_OSR_16 (0x4u << 20) /**< \brief (DACC_TRIGR) OSR = 16 */
#define   DACC_TRIGR_OSR1_OSR_32 (0x5u << 20) /**< \brief (DACC_TRIGR) OSR = 32 */
/* -------- DACC_CHER : (DACC Offset: 0x10) Channel Enable Register -------- */
#define DACC_CHER_CH0 (0x1u << 0) /**< \brief (DACC_CHER) Channel 0 Enable */
#define DACC_CHER_CH1 (0x1u << 1) /**< \brief (DACC_CHER) Channel 1 Enable */
/* -------- DACC_CHDR : (DACC Offset: 0x14) Channel Disable Register -------- */
#define DACC_CHDR_CH0 (0x1u << 0) /**< \brief (DACC_CHDR) Channel 0 Disable */
#define DACC_CHDR_CH1 (0x1u << 1) /**< \brief (DACC_CHDR) Channel 1 Disable */
/* -------- DACC_CHSR : (DACC Offset: 0x18) Channel Status Register -------- */
#define DACC_CHSR_CH0 (0x1u << 0) /**< \brief (DACC_CHSR) Channel 0 Status */
#define DACC_CHSR_CH1 (0x1u << 1) /**< \brief (DACC_CHSR) Channel 1 Status */
#define DACC_CHSR_DACRDY0 (0x1u << 8) /**< \brief (DACC_CHSR) DAC ready flag */
#define DACC_CHSR_DACRDY1 (0x1u << 9) /**< \brief (DACC_CHSR) DAC ready flag */
/* -------- DACC_CDR[2] : (DACC Offset: 0x1C) Conversion Data Register -------- */
#define DACC_CDR_DATA0_Pos 0
#define DACC_CDR_DATA0_Msk (0xffffu << DACC_CDR_DATA0_Pos) /**< \brief (DACC_CDR[2]) Data to Convert for channel 0 */
#define DACC_CDR_DATA0(value) ((DACC_CDR_DATA0_Msk & ((value) << DACC_CDR_DATA0_Pos)))
#define DACC_CDR_DATA1_Pos 16
#define DACC_CDR_DATA1_Msk (0xffffu << DACC_CDR_DATA1_Pos) /**< \brief (DACC_CDR[2]) Data to Convert for channel 1 */
#define DACC_CDR_DATA1(value) ((DACC_CDR_DATA1_Msk & ((value) << DACC_CDR_DATA1_Pos)))
/* -------- DACC_IER : (DACC Offset: 0x24) Interrupt Enable Register -------- */
#define DACC_IER_TXRDY0 (0x1u << 0) /**< \brief (DACC_IER) Transmit Ready Interrupt Enable of channel 0 */
#define DACC_IER_TXRDY1 (0x1u << 1) /**< \brief (DACC_IER) Transmit Ready Interrupt Enable of channel 1 */
#define DACC_IER_EOC0 (0x1u << 4) /**< \brief (DACC_IER) End of Conversion Interrupt Enable of channel 0 */
#define DACC_IER_EOC1 (0x1u << 5) /**< \brief (DACC_IER) End of Conversion Interrupt Enable of channel 1 */
#define DACC_IER_ENDTX0 (0x1u << 8) /**< \brief (DACC_IER) End of Transmit Buffer Interrupt Enable of channel 0 */
#define DACC_IER_ENDTX1 (0x1u << 9) /**< \brief (DACC_IER) End of Transmit Buffer Interrupt Enable of channel 1 */
#define DACC_IER_TXBUFE0 (0x1u << 12) /**< \brief (DACC_IER) Transmit Buffer Empty Interrupt Enable of channel 0 */
#define DACC_IER_TXBUFE1 (0x1u << 13) /**< \brief (DACC_IER) Transmit Buffer Empty Interrupt Enable of channel 1 */
/* -------- DACC_IDR : (DACC Offset: 0x28) Interrupt Disable Register -------- */
#define DACC_IDR_TXRDY0 (0x1u << 0) /**< \brief (DACC_IDR) Transmit Ready Interrupt Disable of channel 0 */
#define DACC_IDR_TXRDY1 (0x1u << 1) /**< \brief (DACC_IDR) Transmit Ready Interrupt Disable of channel 1 */
#define DACC_IDR_EOC0 (0x1u << 4) /**< \brief (DACC_IDR) End of Conversion Interrupt Disable of channel 0 */
#define DACC_IDR_EOC1 (0x1u << 5) /**< \brief (DACC_IDR) End of Conversion Interrupt Disable of channel 1 */
#define DACC_IDR_ENDTX0 (0x1u << 8) /**< \brief (DACC_IDR) End of Transmit Buffer Interrupt Disable of channel 0 */
#define DACC_IDR_ENDTX1 (0x1u << 9) /**< \brief (DACC_IDR) End of Transmit Buffer Interrupt Disable of channel 1 */
#define DACC_IDR_TXBUFE0 (0x1u << 12) /**< \brief (DACC_IDR) Transmit Buffer Empty Interrupt Disable of channel 0 */
#define DACC_IDR_TXBUFE1 (0x1u << 13) /**< \brief (DACC_IDR) Transmit Buffer Empty Interrupt Disable of channel 1 */
/* -------- DACC_IMR : (DACC Offset: 0x2C) Interrupt Mask Register -------- */
#define DACC_IMR_TXRDY0 (0x1u << 0) /**< \brief (DACC_IMR) Transmit Ready Interrupt Mask of channel 0 */
#define DACC_IMR_TXRDY1 (0x1u << 1) /**< \brief (DACC_IMR) Transmit Ready Interrupt Mask of channel 1 */
#define DACC_IMR_EOC0 (0x1u << 4) /**< \brief (DACC_IMR) End of Conversion Interrupt Mask of channel 0 */
#define DACC_IMR_EOC1 (0x1u << 5) /**< \brief (DACC_IMR) End of Conversion Interrupt Mask of channel 1 */
#define DACC_IMR_ENDTX0 (0x1u << 8) /**< \brief (DACC_IMR) End of Transmit Buffer Interrupt Mask of channel 0 */
#define DACC_IMR_ENDTX1 (0x1u << 9) /**< \brief (DACC_IMR) End of Transmit Buffer Interrupt Mask of channel 1 */
#define DACC_IMR_TXBUFE0 (0x1u << 12) /**< \brief (DACC_IMR) Transmit Buffer Empty Interrupt Mask of channel 0 */
#define DACC_IMR_TXBUFE1 (0x1u << 13) /**< \brief (DACC_IMR) Transmit Buffer Empty Interrupt Mask of channel 1 */
/* -------- DACC_ISR : (DACC Offset: 0x30) Interrupt Status Register -------- */
#define DACC_ISR_TXRDY0 (0x1u << 0) /**< \brief (DACC_ISR) Transmit Ready Interrupt Flag of channel 0 */
#define DACC_ISR_TXRDY1 (0x1u << 1) /**< \brief (DACC_ISR) Transmit Ready Interrupt Flag of channel 1 */
#define DACC_ISR_EOC0 (0x1u << 4) /**< \brief (DACC_ISR) End of Conversion Interrupt Flag of channel 0 */
#define DACC_ISR_EOC1 (0x1u << 5) /**< \brief (DACC_ISR) End of Conversion Interrupt Flag of channel 1 */
#define DACC_ISR_ENDTX0 (0x1u << 8) /**< \brief (DACC_ISR) End of DMA Interrupt Flag of channel 0 */
#define DACC_ISR_ENDTX1 (0x1u << 9) /**< \brief (DACC_ISR) End of DMA Interrupt Flag of channel 1 */
#define DACC_ISR_TXBUFE0 (0x1u << 12) /**< \brief (DACC_ISR) Transmit Buffer Empty of channel 0 */
#define DACC_ISR_TXBUFE1 (0x1u << 13) /**< \brief (DACC_ISR) Transmit Buffer Empty of channel 1 */
/* -------- DACC_ACR : (DACC Offset: 0x94) Analog Current Register -------- */
#define DACC_ACR_IBCTLCH0_Pos 0
#define DACC_ACR_IBCTLCH0_Msk (0x3u << DACC_ACR_IBCTLCH0_Pos) /**< \brief (DACC_ACR) Analog Output Current Control */
#define DACC_ACR_IBCTLCH0(value) ((DACC_ACR_IBCTLCH0_Msk & ((value) << DACC_ACR_IBCTLCH0_Pos)))
#define DACC_ACR_IBCTLCH1_Pos 2
#define DACC_ACR_IBCTLCH1_Msk (0x3u << DACC_ACR_IBCTLCH1_Pos) /**< \brief (DACC_ACR) Analog Output Current Control */
#define DACC_ACR_IBCTLCH1(value) ((DACC_ACR_IBCTLCH1_Msk & ((value) << DACC_ACR_IBCTLCH1_Pos)))
/* -------- DACC_WPMR : (DACC Offset: 0xE4) Write Protection Mode register -------- */
#define DACC_WPMR_WPEN (0x1u << 0) /**< \brief (DACC_WPMR) Write Protection Enable */
#define DACC_WPMR_WPKEY_Pos 8
#define DACC_WPMR_WPKEY_Msk (0xffffffu << DACC_WPMR_WPKEY_Pos) /**< \brief (DACC_WPMR) Write Protect Key */
#define   DACC_WPMR_WPKEY_PASSWD (0x444143u << 8) /**< \brief (DACC_WPMR) Writing any other value in this field aborts the write operation of bit WPEN.Always reads as 0. */
/* -------- DACC_WPSR : (DACC Offset: 0xE8) Write Protection Status register -------- */
#define DACC_WPSR_WPVS (0x1u << 0) /**< \brief (DACC_WPSR) Write Protection Violation Status */
#define DACC_WPSR_WPVSRC_Pos 8
#define DACC_WPSR_WPVSRC_Msk (0xffu << DACC_WPSR_WPVSRC_Pos) /**< \brief (DACC_WPSR) Write Protection Violation Source */

/*@}*/


#endif /* _SAM_DACC_COMPONENT_ */
