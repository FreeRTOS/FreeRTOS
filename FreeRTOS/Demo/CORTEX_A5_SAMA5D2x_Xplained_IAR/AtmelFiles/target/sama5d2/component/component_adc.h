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

#ifndef _SAMA5D2_ADC_COMPONENT_
#define _SAMA5D2_ADC_COMPONENT_

/* ============================================================================= */
/**  SOFTWARE API DEFINITION FOR Analog-to-Digital Converter */
/* ============================================================================= */
/** \addtogroup SAMA5D2_ADC Analog-to-Digital Converter */
/*@{*/

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
/** \brief Adc hardware registers */
typedef struct {
  __O  uint32_t ADC_CR;       /**< \brief (Adc Offset: 0x00) Control Register */
  __IO uint32_t ADC_MR;       /**< \brief (Adc Offset: 0x04) Mode Register */
  __IO uint32_t ADC_SEQR1;    /**< \brief (Adc Offset: 0x08) Channel Sequence Register 1 */
  __IO uint32_t ADC_SEQR2;    /**< \brief (Adc Offset: 0x0C) Channel Sequence Register 2 */
  __O  uint32_t ADC_CHER;     /**< \brief (Adc Offset: 0x10) Channel Enable Register */
  __O  uint32_t ADC_CHDR;     /**< \brief (Adc Offset: 0x14) Channel Disable Register */
  __I  uint32_t ADC_CHSR;     /**< \brief (Adc Offset: 0x18) Channel Status Register */
  __I  uint32_t Reserved1[1];
  __I  uint32_t ADC_LCDR;     /**< \brief (Adc Offset: 0x20) Last Converted Data Register */
  __O  uint32_t ADC_IER;      /**< \brief (Adc Offset: 0x24) Interrupt Enable Register */
  __O  uint32_t ADC_IDR;      /**< \brief (Adc Offset: 0x28) Interrupt Disable Register */
  __I  uint32_t ADC_IMR;      /**< \brief (Adc Offset: 0x2C) Interrupt Mask Register */
  __I  uint32_t ADC_ISR;      /**< \brief (Adc Offset: 0x30) Interrupt Status Register */
  __IO uint32_t ADC_LCTMR;    /**< \brief (Adc Offset: 0x34) Last Channel Trigger Mode Register */
  __IO uint32_t ADC_LCCWR;    /**< \brief (Adc Offset: 0x38) Last Channel Compare Window Register */
  __I  uint32_t ADC_OVER;     /**< \brief (Adc Offset: 0x3C) Overrun Status Register */
  __IO uint32_t ADC_EMR;      /**< \brief (Adc Offset: 0x40) Extended Mode Register */
  __IO uint32_t ADC_CWR;      /**< \brief (Adc Offset: 0x44) Compare Window Register */
  __IO uint32_t ADC_CGR;      /**< \brief (Adc Offset: 0x48) Channel Gain Register */
  __IO uint32_t ADC_COR;      /**< \brief (Adc Offset: 0x4C) Channel Offset Register */
  __I  uint32_t ADC_CDR[12];  /**< \brief (Adc Offset: 0x50) Channel Data Registers */
  __I  uint32_t Reserved2[5];
  __IO uint32_t ADC_ACR;      /**< \brief (Adc Offset: 0x94) Analog Control Register */
  __I  uint32_t Reserved3[6];
  __IO uint32_t ADC_TSMR;     /**< \brief (Adc Offset: 0xB0) Touchscreen Mode Register */
  __I  uint32_t ADC_XPOSR;    /**< \brief (Adc Offset: 0xB4) Touchscreen X Position Register */
  __I  uint32_t ADC_YPOSR;    /**< \brief (Adc Offset: 0xB8) Touchscreen Y Position Register */
  __I  uint32_t ADC_PRESSR;   /**< \brief (Adc Offset: 0xBC) Touchscreen Pressure Register */
  __IO uint32_t ADC_TRGR;     /**< \brief (Adc Offset: 0xC0) Trigger Register */
  __I  uint32_t Reserved4[3];
  __IO uint32_t ADC_COSR;     /**< \brief (Adc Offset: 0xD0) Correction Select Register */
  __IO uint32_t ADC_CVR;      /**< \brief (Adc Offset: 0xD4) Correction Values Register */
  __IO uint32_t ADC_CECR;     /**< \brief (Adc Offset: 0xD8) Channel Error Correction Register */
  __I  uint32_t Reserved5[2];
  __IO uint32_t ADC_WPMR;     /**< \brief (Adc Offset: 0xE4) Write Protection Mode Register */
  __I  uint32_t ADC_WPSR;     /**< \brief (Adc Offset: 0xE8) Write Protection Status Register */
  __I  uint32_t Reserved6[4];
  __I  uint32_t ADC_VERSION;  /**< \brief (Adc Offset: 0xFC) Version Register */
} Adc;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */
/* -------- ADC_CR : (ADC Offset: 0x00) Control Register -------- */
#define ADC_CR_SWRST (0x1u << 0) /**< \brief (ADC_CR) Software Reset */
#define ADC_CR_START (0x1u << 1) /**< \brief (ADC_CR) Start Conversion */
#define ADC_CR_TSCALIB (0x1u << 2) /**< \brief (ADC_CR) Touchscreen Calibration */
#define ADC_CR_CMPRST (0x1u << 4) /**< \brief (ADC_CR) Comparison Restart */
/* -------- ADC_MR : (ADC Offset: 0x04) Mode Register -------- */
#define ADC_MR_TRGSEL_Pos 1
#define ADC_MR_TRGSEL_Msk (0x7u << ADC_MR_TRGSEL_Pos) /**< \brief (ADC_MR) Trigger Selection */
#define ADC_MR_TRGSEL(value) ((ADC_MR_TRGSEL_Msk & ((value) << ADC_MR_TRGSEL_Pos)))
#define   ADC_MR_TRGSEL_ADC_TRIG0 (0x0u << 1) /**< \brief (ADC_MR) ADTRG */
#define   ADC_MR_TRGSEL_ADC_TRIG1 (0x1u << 1) /**< \brief (ADC_MR) TIOA0 */
#define   ADC_MR_TRGSEL_ADC_TRIG2 (0x2u << 1) /**< \brief (ADC_MR) TIOA1 */
#define   ADC_MR_TRGSEL_ADC_TRIG3 (0x3u << 1) /**< \brief (ADC_MR) TIOA2 */
#define   ADC_MR_TRGSEL_ADC_TRIG4 (0x4u << 1) /**< \brief (ADC_MR) PWM event line 0 */
#define   ADC_MR_TRGSEL_ADC_TRIG5 (0x5u << 1) /**< \brief (ADC_MR) PWM_even line 1 */
#define ADC_MR_SLEEP (0x1u << 5) /**< \brief (ADC_MR) Sleep Mode */
#define   ADC_MR_SLEEP_NORMAL (0x0u << 5) /**< \brief (ADC_MR) Normal Mode: The ADC core and reference voltage circuitry are kept ON between conversions. */
#define   ADC_MR_SLEEP_SLEEP (0x1u << 5) /**< \brief (ADC_MR) Sleep Mode: The wake-up time can be modified by programming FWUP bit. */
#define ADC_MR_FWUP (0x1u << 6) /**< \brief (ADC_MR) Fast Wake Up */
#define   ADC_MR_FWUP_OFF (0x0u << 6) /**< \brief (ADC_MR) If SLEEP is 1, then both ADC core and reference voltage circuitry are OFF between conversions */
#define   ADC_MR_FWUP_ON (0x1u << 6) /**< \brief (ADC_MR) If SLEEP is 1, then Fast Wake-up Sleep mode: The voltage reference is ON between conversions and ADC core is OFF */
#define ADC_MR_PRESCAL_Pos 8
#define ADC_MR_PRESCAL_Msk (0xffu << ADC_MR_PRESCAL_Pos) /**< \brief (ADC_MR) Prescaler Rate Selection */
#define ADC_MR_PRESCAL(value) ((ADC_MR_PRESCAL_Msk & ((value) << ADC_MR_PRESCAL_Pos)))
#define ADC_MR_STARTUP_Pos 16
#define ADC_MR_STARTUP_Msk (0xfu << ADC_MR_STARTUP_Pos) /**< \brief (ADC_MR) Startup Time */
#define ADC_MR_STARTUP(value) ((ADC_MR_STARTUP_Msk & ((value) << ADC_MR_STARTUP_Pos)))
#define   ADC_MR_STARTUP_SUT0 (0x0u << 16) /**< \brief (ADC_MR) 0 periods of ADCCLK */
#define   ADC_MR_STARTUP_SUT8 (0x1u << 16) /**< \brief (ADC_MR) 8 periods of ADCCLK */
#define   ADC_MR_STARTUP_SUT16 (0x2u << 16) /**< \brief (ADC_MR) 16 periods of ADCCLK */
#define   ADC_MR_STARTUP_SUT24 (0x3u << 16) /**< \brief (ADC_MR) 24 periods of ADCCLK */
#define   ADC_MR_STARTUP_SUT64 (0x4u << 16) /**< \brief (ADC_MR) 64 periods of ADCCLK */
#define   ADC_MR_STARTUP_SUT80 (0x5u << 16) /**< \brief (ADC_MR) 80 periods of ADCCLK */
#define   ADC_MR_STARTUP_SUT96 (0x6u << 16) /**< \brief (ADC_MR) 96 periods of ADCCLK */
#define   ADC_MR_STARTUP_SUT112 (0x7u << 16) /**< \brief (ADC_MR) 112 periods of ADCCLK */
#define   ADC_MR_STARTUP_SUT512 (0x8u << 16) /**< \brief (ADC_MR) 512 periods of ADCCLK */
#define   ADC_MR_STARTUP_SUT576 (0x9u << 16) /**< \brief (ADC_MR) 576 periods of ADCCLK */
#define   ADC_MR_STARTUP_SUT640 (0xAu << 16) /**< \brief (ADC_MR) 640 periods of ADCCLK */
#define   ADC_MR_STARTUP_SUT704 (0xBu << 16) /**< \brief (ADC_MR) 704 periods of ADCCLK */
#define   ADC_MR_STARTUP_SUT768 (0xCu << 16) /**< \brief (ADC_MR) 768 periods of ADCCLK */
#define   ADC_MR_STARTUP_SUT832 (0xDu << 16) /**< \brief (ADC_MR) 832 periods of ADCCLK */
#define   ADC_MR_STARTUP_SUT896 (0xEu << 16) /**< \brief (ADC_MR) 896 periods of ADCCLK */
#define   ADC_MR_STARTUP_SUT960 (0xFu << 16) /**< \brief (ADC_MR) 960 periods of ADCCLK */
#define ADC_MR_SETTLING_Pos 20
#define ADC_MR_SETTLING_Msk (0x3u << ADC_MR_SETTLING_Pos) /**< \brief (ADC_MR) Analog Settling Time */
#define ADC_MR_SETTLING(value) ((ADC_MR_SETTLING_Msk & ((value) << ADC_MR_SETTLING_Pos)))
#define   ADC_MR_SETTLING_AST3 (0x0u << 20) /**< \brief (ADC_MR) 3 periods of ADCCLK */
#define   ADC_MR_SETTLING_AST5 (0x1u << 20) /**< \brief (ADC_MR) 5 periods of ADCCLK */
#define   ADC_MR_SETTLING_AST9 (0x2u << 20) /**< \brief (ADC_MR) 9 periods of ADCCLK */
#define   ADC_MR_SETTLING_AST17 (0x3u << 20) /**< \brief (ADC_MR) 17 periods of ADCCLK */
#define ADC_MR_ANACH (0x1u << 23) /**< \brief (ADC_MR) Analog Change */
#define   ADC_MR_ANACH_NONE (0x0u << 23) /**< \brief (ADC_MR) No analog change on channel switching: DIFF0, GAIN0 and OFF0 are used for all channels. */
#define   ADC_MR_ANACH_ALLOWED (0x1u << 23) /**< \brief (ADC_MR) Allows different analog settings for each channel. See ADC_CGR and ADC_COR registers. */
#define ADC_MR_TRACKTIM_Pos 24
#define ADC_MR_TRACKTIM_Msk (0xfu << ADC_MR_TRACKTIM_Pos) /**< \brief (ADC_MR) Tracking Time */
#define ADC_MR_TRACKTIM(value) ((ADC_MR_TRACKTIM_Msk & ((value) << ADC_MR_TRACKTIM_Pos)))
#define ADC_MR_TRANSFER_Pos 28
#define ADC_MR_TRANSFER_Msk (0x3u << ADC_MR_TRANSFER_Pos) /**< \brief (ADC_MR) Hold Time */
#define ADC_MR_TRANSFER(value) ((ADC_MR_TRANSFER_Msk & ((value) << ADC_MR_TRANSFER_Pos)))
#define ADC_MR_USEQ (0x1u << 31) /**< \brief (ADC_MR) Use Sequence Enable */
#define   ADC_MR_USEQ_NUM_ORDER (0x0u << 31) /**< \brief (ADC_MR) Normal Mode: The controller converts channels in a simple numeric order depending only on the channel index. */
#define   ADC_MR_USEQ_REG_ORDER (0x1u << 31) /**< \brief (ADC_MR) User Sequence Mode: The sequence respects what is defined in ADC_SEQR1 and ADC_SEQR2 registers and can be used to convert the same channel several times. */
/* -------- ADC_SEQR1 : (ADC Offset: 0x08) Channel Sequence Register 1 -------- */
#define ADC_SEQR1_USCH1_Pos 0
#define ADC_SEQR1_USCH1_Msk (0xfu << ADC_SEQR1_USCH1_Pos) /**< \brief (ADC_SEQR1) User Sequence Number 1 */
#define ADC_SEQR1_USCH1(value) ((ADC_SEQR1_USCH1_Msk & ((value) << ADC_SEQR1_USCH1_Pos)))
#define ADC_SEQR1_USCH2_Pos 4
#define ADC_SEQR1_USCH2_Msk (0xfu << ADC_SEQR1_USCH2_Pos) /**< \brief (ADC_SEQR1) User Sequence Number 2 */
#define ADC_SEQR1_USCH2(value) ((ADC_SEQR1_USCH2_Msk & ((value) << ADC_SEQR1_USCH2_Pos)))
#define ADC_SEQR1_USCH3_Pos 8
#define ADC_SEQR1_USCH3_Msk (0xfu << ADC_SEQR1_USCH3_Pos) /**< \brief (ADC_SEQR1) User Sequence Number 3 */
#define ADC_SEQR1_USCH3(value) ((ADC_SEQR1_USCH3_Msk & ((value) << ADC_SEQR1_USCH3_Pos)))
#define ADC_SEQR1_USCH4_Pos 12
#define ADC_SEQR1_USCH4_Msk (0xfu << ADC_SEQR1_USCH4_Pos) /**< \brief (ADC_SEQR1) User Sequence Number 4 */
#define ADC_SEQR1_USCH4(value) ((ADC_SEQR1_USCH4_Msk & ((value) << ADC_SEQR1_USCH4_Pos)))
#define ADC_SEQR1_USCH5_Pos 16
#define ADC_SEQR1_USCH5_Msk (0xfu << ADC_SEQR1_USCH5_Pos) /**< \brief (ADC_SEQR1) User Sequence Number 5 */
#define ADC_SEQR1_USCH5(value) ((ADC_SEQR1_USCH5_Msk & ((value) << ADC_SEQR1_USCH5_Pos)))
#define ADC_SEQR1_USCH6_Pos 20
#define ADC_SEQR1_USCH6_Msk (0xfu << ADC_SEQR1_USCH6_Pos) /**< \brief (ADC_SEQR1) User Sequence Number 6 */
#define ADC_SEQR1_USCH6(value) ((ADC_SEQR1_USCH6_Msk & ((value) << ADC_SEQR1_USCH6_Pos)))
#define ADC_SEQR1_USCH7_Pos 24
#define ADC_SEQR1_USCH7_Msk (0xfu << ADC_SEQR1_USCH7_Pos) /**< \brief (ADC_SEQR1) User Sequence Number 7 */
#define ADC_SEQR1_USCH7(value) ((ADC_SEQR1_USCH7_Msk & ((value) << ADC_SEQR1_USCH7_Pos)))
#define ADC_SEQR1_USCH8_Pos 28
#define ADC_SEQR1_USCH8_Msk (0xfu << ADC_SEQR1_USCH8_Pos) /**< \brief (ADC_SEQR1) User Sequence Number 8 */
#define ADC_SEQR1_USCH8(value) ((ADC_SEQR1_USCH8_Msk & ((value) << ADC_SEQR1_USCH8_Pos)))
/* -------- ADC_SEQR2 : (ADC Offset: 0x0C) Channel Sequence Register 2 -------- */
#define ADC_SEQR2_USCH9_Pos 0
#define ADC_SEQR2_USCH9_Msk (0xfu << ADC_SEQR2_USCH9_Pos) /**< \brief (ADC_SEQR2) User Sequence Number 9 */
#define ADC_SEQR2_USCH9(value) ((ADC_SEQR2_USCH9_Msk & ((value) << ADC_SEQR2_USCH9_Pos)))
#define ADC_SEQR2_USCH10_Pos 4
#define ADC_SEQR2_USCH10_Msk (0xfu << ADC_SEQR2_USCH10_Pos) /**< \brief (ADC_SEQR2) User Sequence Number 10 */
#define ADC_SEQR2_USCH10(value) ((ADC_SEQR2_USCH10_Msk & ((value) << ADC_SEQR2_USCH10_Pos)))
#define ADC_SEQR2_USCH11_Pos 8
#define ADC_SEQR2_USCH11_Msk (0xfu << ADC_SEQR2_USCH11_Pos) /**< \brief (ADC_SEQR2) User Sequence Number 11 */
#define ADC_SEQR2_USCH11(value) ((ADC_SEQR2_USCH11_Msk & ((value) << ADC_SEQR2_USCH11_Pos)))
/* -------- ADC_CHER : (ADC Offset: 0x10) Channel Enable Register -------- */
#define ADC_CHER_CH0 (0x1u << 0) /**< \brief (ADC_CHER) Channel 0 Enable */
#define ADC_CHER_CH1 (0x1u << 1) /**< \brief (ADC_CHER) Channel 1 Enable */
#define ADC_CHER_CH2 (0x1u << 2) /**< \brief (ADC_CHER) Channel 2 Enable */
#define ADC_CHER_CH3 (0x1u << 3) /**< \brief (ADC_CHER) Channel 3 Enable */
#define ADC_CHER_CH4 (0x1u << 4) /**< \brief (ADC_CHER) Channel 4 Enable */
#define ADC_CHER_CH5 (0x1u << 5) /**< \brief (ADC_CHER) Channel 5 Enable */
#define ADC_CHER_CH6 (0x1u << 6) /**< \brief (ADC_CHER) Channel 6 Enable */
#define ADC_CHER_CH7 (0x1u << 7) /**< \brief (ADC_CHER) Channel 7 Enable */
#define ADC_CHER_CH8 (0x1u << 8) /**< \brief (ADC_CHER) Channel 8 Enable */
#define ADC_CHER_CH9 (0x1u << 9) /**< \brief (ADC_CHER) Channel 9 Enable */
#define ADC_CHER_CH10 (0x1u << 10) /**< \brief (ADC_CHER) Channel 10 Enable */
#define ADC_CHER_CH11 (0x1u << 11) /**< \brief (ADC_CHER) Channel 11 Enable */
/* -------- ADC_CHDR : (ADC Offset: 0x14) Channel Disable Register -------- */
#define ADC_CHDR_CH0 (0x1u << 0) /**< \brief (ADC_CHDR) Channel 0 Disable */
#define ADC_CHDR_CH1 (0x1u << 1) /**< \brief (ADC_CHDR) Channel 1 Disable */
#define ADC_CHDR_CH2 (0x1u << 2) /**< \brief (ADC_CHDR) Channel 2 Disable */
#define ADC_CHDR_CH3 (0x1u << 3) /**< \brief (ADC_CHDR) Channel 3 Disable */
#define ADC_CHDR_CH4 (0x1u << 4) /**< \brief (ADC_CHDR) Channel 4 Disable */
#define ADC_CHDR_CH5 (0x1u << 5) /**< \brief (ADC_CHDR) Channel 5 Disable */
#define ADC_CHDR_CH6 (0x1u << 6) /**< \brief (ADC_CHDR) Channel 6 Disable */
#define ADC_CHDR_CH7 (0x1u << 7) /**< \brief (ADC_CHDR) Channel 7 Disable */
#define ADC_CHDR_CH8 (0x1u << 8) /**< \brief (ADC_CHDR) Channel 8 Disable */
#define ADC_CHDR_CH9 (0x1u << 9) /**< \brief (ADC_CHDR) Channel 9 Disable */
#define ADC_CHDR_CH10 (0x1u << 10) /**< \brief (ADC_CHDR) Channel 10 Disable */
#define ADC_CHDR_CH11 (0x1u << 11) /**< \brief (ADC_CHDR) Channel 11 Disable */
/* -------- ADC_CHSR : (ADC Offset: 0x18) Channel Status Register -------- */
#define ADC_CHSR_CH0 (0x1u << 0) /**< \brief (ADC_CHSR) Channel 0 Status */
#define ADC_CHSR_CH1 (0x1u << 1) /**< \brief (ADC_CHSR) Channel 1 Status */
#define ADC_CHSR_CH2 (0x1u << 2) /**< \brief (ADC_CHSR) Channel 2 Status */
#define ADC_CHSR_CH3 (0x1u << 3) /**< \brief (ADC_CHSR) Channel 3 Status */
#define ADC_CHSR_CH4 (0x1u << 4) /**< \brief (ADC_CHSR) Channel 4 Status */
#define ADC_CHSR_CH5 (0x1u << 5) /**< \brief (ADC_CHSR) Channel 5 Status */
#define ADC_CHSR_CH6 (0x1u << 6) /**< \brief (ADC_CHSR) Channel 6 Status */
#define ADC_CHSR_CH7 (0x1u << 7) /**< \brief (ADC_CHSR) Channel 7 Status */
#define ADC_CHSR_CH8 (0x1u << 8) /**< \brief (ADC_CHSR) Channel 8 Status */
#define ADC_CHSR_CH9 (0x1u << 9) /**< \brief (ADC_CHSR) Channel 9 Status */
#define ADC_CHSR_CH10 (0x1u << 10) /**< \brief (ADC_CHSR) Channel 10 Status */
#define ADC_CHSR_CH11 (0x1u << 11) /**< \brief (ADC_CHSR) Channel 11 Status */
/* -------- ADC_LCDR : (ADC Offset: 0x20) Last Converted Data Register -------- */
#define ADC_LCDR_LDATA_Pos 0
#define ADC_LCDR_LDATA_Msk (0xfffu << ADC_LCDR_LDATA_Pos) /**< \brief (ADC_LCDR) Last Data Converted */
#define ADC_LCDR_CHNB_Pos 12
#define ADC_LCDR_CHNB_Msk (0xfu << ADC_LCDR_CHNB_Pos) /**< \brief (ADC_LCDR) Channel Number */
/* -------- ADC_IER : (ADC Offset: 0x24) Interrupt Enable Register -------- */
#define ADC_IER_EOC0 (0x1u << 0) /**< \brief (ADC_IER) End of Conversion Interrupt Enable 0 */
#define ADC_IER_EOC1 (0x1u << 1) /**< \brief (ADC_IER) End of Conversion Interrupt Enable 1 */
#define ADC_IER_EOC2 (0x1u << 2) /**< \brief (ADC_IER) End of Conversion Interrupt Enable 2 */
#define ADC_IER_EOC3 (0x1u << 3) /**< \brief (ADC_IER) End of Conversion Interrupt Enable 3 */
#define ADC_IER_EOC4 (0x1u << 4) /**< \brief (ADC_IER) End of Conversion Interrupt Enable 4 */
#define ADC_IER_EOC5 (0x1u << 5) /**< \brief (ADC_IER) End of Conversion Interrupt Enable 5 */
#define ADC_IER_EOC6 (0x1u << 6) /**< \brief (ADC_IER) End of Conversion Interrupt Enable 6 */
#define ADC_IER_EOC7 (0x1u << 7) /**< \brief (ADC_IER) End of Conversion Interrupt Enable 7 */
#define ADC_IER_EOC8 (0x1u << 8) /**< \brief (ADC_IER) End of Conversion Interrupt Enable 8 */
#define ADC_IER_EOC9 (0x1u << 9) /**< \brief (ADC_IER) End of Conversion Interrupt Enable 9 */
#define ADC_IER_EOC10 (0x1u << 10) /**< \brief (ADC_IER) End of Conversion Interrupt Enable 10 */
#define ADC_IER_EOC11 (0x1u << 11) /**< \brief (ADC_IER) End of Conversion Interrupt Enable 11 */
#define ADC_IER_VALUE_ (0x1u << 12) /**< \brief (ADC_IER)  */
#define ADC_IER_LCCHG (0x1u << 19) /**< \brief (ADC_IER) Last Channel Change Interrupt Enable */
#define ADC_IER_XRDY (0x1u << 20) /**< \brief (ADC_IER) Touchscreen Measure XPOS Ready Interrupt Enable */
#define ADC_IER_YRDY (0x1u << 21) /**< \brief (ADC_IER) Touchscreen Measure YPOS Ready Interrupt Enable */
#define ADC_IER_PRDY (0x1u << 22) /**< \brief (ADC_IER) Touchscreen Measure Pressure Ready Interrupt Enable */
#define ADC_IER_DRDY (0x1u << 24) /**< \brief (ADC_IER) Data Ready Interrupt Enable */
#define ADC_IER_GOVRE (0x1u << 25) /**< \brief (ADC_IER) General Overrun Error Interrupt Enable */
#define ADC_IER_COMPE (0x1u << 26) /**< \brief (ADC_IER) Comparison Event Interrupt Enable */
#define ADC_IER_PEN (0x1u << 29) /**< \brief (ADC_IER) Pen Contact Interrupt Enable */
#define ADC_IER_NOPEN (0x1u << 30) /**< \brief (ADC_IER) No Pen Contact Interrupt Enable */
/* -------- ADC_IDR : (ADC Offset: 0x28) Interrupt Disable Register -------- */
#define ADC_IDR_EOC0 (0x1u << 0) /**< \brief (ADC_IDR) End of Conversion Interrupt Disable 0 */
#define ADC_IDR_EOC1 (0x1u << 1) /**< \brief (ADC_IDR) End of Conversion Interrupt Disable 1 */
#define ADC_IDR_EOC2 (0x1u << 2) /**< \brief (ADC_IDR) End of Conversion Interrupt Disable 2 */
#define ADC_IDR_EOC3 (0x1u << 3) /**< \brief (ADC_IDR) End of Conversion Interrupt Disable 3 */
#define ADC_IDR_EOC4 (0x1u << 4) /**< \brief (ADC_IDR) End of Conversion Interrupt Disable 4 */
#define ADC_IDR_EOC5 (0x1u << 5) /**< \brief (ADC_IDR) End of Conversion Interrupt Disable 5 */
#define ADC_IDR_EOC6 (0x1u << 6) /**< \brief (ADC_IDR) End of Conversion Interrupt Disable 6 */
#define ADC_IDR_EOC7 (0x1u << 7) /**< \brief (ADC_IDR) End of Conversion Interrupt Disable 7 */
#define ADC_IDR_EOC8 (0x1u << 8) /**< \brief (ADC_IDR) End of Conversion Interrupt Disable 8 */
#define ADC_IDR_EOC9 (0x1u << 9) /**< \brief (ADC_IDR) End of Conversion Interrupt Disable 9 */
#define ADC_IDR_EOC10 (0x1u << 10) /**< \brief (ADC_IDR) End of Conversion Interrupt Disable 10 */
#define ADC_IDR_EOC11 (0x1u << 11) /**< \brief (ADC_IDR) End of Conversion Interrupt Disable 11 */
#define ADC_IDR_VALUE_ (0x1u << 12) /**< \brief (ADC_IDR)  */
#define ADC_IDR_LCCHG (0x1u << 19) /**< \brief (ADC_IDR) Last Channel Change Interrupt Disable */
#define ADC_IDR_XRDY (0x1u << 20) /**< \brief (ADC_IDR) Touchscreen Measure XPOS Ready Interrupt Disable */
#define ADC_IDR_YRDY (0x1u << 21) /**< \brief (ADC_IDR) Touchscreen Measure YPOS Ready Interrupt Disable */
#define ADC_IDR_PRDY (0x1u << 22) /**< \brief (ADC_IDR) Touchscreen Measure Pressure Ready Interrupt Disable */
#define ADC_IDR_DRDY (0x1u << 24) /**< \brief (ADC_IDR) Data Ready Interrupt Disable */
#define ADC_IDR_GOVRE (0x1u << 25) /**< \brief (ADC_IDR) General Overrun Error Interrupt Disable */
#define ADC_IDR_COMPE (0x1u << 26) /**< \brief (ADC_IDR) Comparison Event Interrupt Disable */
#define ADC_IDR_PEN (0x1u << 29) /**< \brief (ADC_IDR) Pen Contact Interrupt Disable */
#define ADC_IDR_NOPEN (0x1u << 30) /**< \brief (ADC_IDR) No Pen Contact Interrupt Disable */
/* -------- ADC_IMR : (ADC Offset: 0x2C) Interrupt Mask Register -------- */
#define ADC_IMR_EOC0 (0x1u << 0) /**< \brief (ADC_IMR) End of Conversion Interrupt Mask 0 */
#define ADC_IMR_EOC1 (0x1u << 1) /**< \brief (ADC_IMR) End of Conversion Interrupt Mask 1 */
#define ADC_IMR_EOC2 (0x1u << 2) /**< \brief (ADC_IMR) End of Conversion Interrupt Mask 2 */
#define ADC_IMR_EOC3 (0x1u << 3) /**< \brief (ADC_IMR) End of Conversion Interrupt Mask 3 */
#define ADC_IMR_EOC4 (0x1u << 4) /**< \brief (ADC_IMR) End of Conversion Interrupt Mask 4 */
#define ADC_IMR_EOC5 (0x1u << 5) /**< \brief (ADC_IMR) End of Conversion Interrupt Mask 5 */
#define ADC_IMR_EOC6 (0x1u << 6) /**< \brief (ADC_IMR) End of Conversion Interrupt Mask 6 */
#define ADC_IMR_EOC7 (0x1u << 7) /**< \brief (ADC_IMR) End of Conversion Interrupt Mask 7 */
#define ADC_IMR_EOC8 (0x1u << 8) /**< \brief (ADC_IMR) End of Conversion Interrupt Mask 8 */
#define ADC_IMR_EOC9 (0x1u << 9) /**< \brief (ADC_IMR) End of Conversion Interrupt Mask 9 */
#define ADC_IMR_EOC10 (0x1u << 10) /**< \brief (ADC_IMR) End of Conversion Interrupt Mask 10 */
#define ADC_IMR_EOC11 (0x1u << 11) /**< \brief (ADC_IMR) End of Conversion Interrupt Mask 11 */
#define ADC_IMR_VALUE_ (0x1u << 12) /**< \brief (ADC_IMR)  */
#define ADC_IMR_LCCHG (0x1u << 19) /**< \brief (ADC_IMR) Last Channel Change Interrupt Mask */
#define ADC_IMR_XRDY (0x1u << 20) /**< \brief (ADC_IMR) Touchscreen Measure XPOS Ready Interrupt Mask */
#define ADC_IMR_YRDY (0x1u << 21) /**< \brief (ADC_IMR) Touchscreen Measure YPOS Ready Interrupt Mask */
#define ADC_IMR_PRDY (0x1u << 22) /**< \brief (ADC_IMR) Touchscreen Measure Pressure Ready Interrupt Mask */
#define ADC_IMR_DRDY (0x1u << 24) /**< \brief (ADC_IMR) Data Ready Interrupt Mask */
#define ADC_IMR_GOVRE (0x1u << 25) /**< \brief (ADC_IMR) General Overrun Error Interrupt Mask */
#define ADC_IMR_COMPE (0x1u << 26) /**< \brief (ADC_IMR) Comparison Event Interrupt Mask */
#define ADC_IMR_PEN (0x1u << 29) /**< \brief (ADC_IMR) Pen Contact Interrupt Mask */
#define ADC_IMR_NOPEN (0x1u << 30) /**< \brief (ADC_IMR) No Pen Contact Interrupt Mask */
/* -------- ADC_ISR : (ADC Offset: 0x30) Interrupt Status Register -------- */
#define ADC_ISR_EOC0 (0x1u << 0) /**< \brief (ADC_ISR) End of Conversion 0 (automatically set / cleared) */
#define ADC_ISR_EOC1 (0x1u << 1) /**< \brief (ADC_ISR) End of Conversion 1 (automatically set / cleared) */
#define ADC_ISR_EOC2 (0x1u << 2) /**< \brief (ADC_ISR) End of Conversion 2 (automatically set / cleared) */
#define ADC_ISR_EOC3 (0x1u << 3) /**< \brief (ADC_ISR) End of Conversion 3 (automatically set / cleared) */
#define ADC_ISR_EOC4 (0x1u << 4) /**< \brief (ADC_ISR) End of Conversion 4 (automatically set / cleared) */
#define ADC_ISR_EOC5 (0x1u << 5) /**< \brief (ADC_ISR) End of Conversion 5 (automatically set / cleared) */
#define ADC_ISR_EOC6 (0x1u << 6) /**< \brief (ADC_ISR) End of Conversion 6 (automatically set / cleared) */
#define ADC_ISR_EOC7 (0x1u << 7) /**< \brief (ADC_ISR) End of Conversion 7 (automatically set / cleared) */
#define ADC_ISR_EOC8 (0x1u << 8) /**< \brief (ADC_ISR) End of Conversion 8 (automatically set / cleared) */
#define ADC_ISR_EOC9 (0x1u << 9) /**< \brief (ADC_ISR) End of Conversion 9 (automatically set / cleared) */
#define ADC_ISR_EOC10 (0x1u << 10) /**< \brief (ADC_ISR) End of Conversion 10 (automatically set / cleared) */
#define ADC_ISR_EOC11 (0x1u << 11) /**< \brief (ADC_ISR) End of Conversion 11 (automatically set / cleared) */
#define ADC_ISR_VALUE_ (0x1u << 12) /**< \brief (ADC_ISR)  */
#define ADC_ISR_LCCHG (0x1u << 19) /**< \brief (ADC_ISR) Last Channel Change (cleared on read) */
#define ADC_ISR_XRDY (0x1u << 20) /**< \brief (ADC_ISR) Touchscreen XPOS Measure Ready (cleared on read) */
#define ADC_ISR_YRDY (0x1u << 21) /**< \brief (ADC_ISR) Touchscreen YPOS Measure Ready (cleared on read) */
#define ADC_ISR_PRDY (0x1u << 22) /**< \brief (ADC_ISR) Touchscreen Pressure Measure Ready (cleared on read) */
#define ADC_ISR_DRDY (0x1u << 24) /**< \brief (ADC_ISR) Data Ready (automatically set / cleared) */
#define ADC_ISR_GOVRE (0x1u << 25) /**< \brief (ADC_ISR) General Overrun Error (cleared on read) */
#define ADC_ISR_COMPE (0x1u << 26) /**< \brief (ADC_ISR) Comparison Event (cleared on read) */
#define ADC_ISR_PEN (0x1u << 29) /**< \brief (ADC_ISR) Pen contact (cleared on read) */
#define ADC_ISR_NOPEN (0x1u << 30) /**< \brief (ADC_ISR) No Pen Contact (cleared on read) */
#define ADC_ISR_PENS (0x1u << 31) /**< \brief (ADC_ISR) Pen Detect Status */
/* -------- ADC_LCTMR : (ADC Offset: 0x34) Last Channel Trigger Mode Register -------- */
#define ADC_LCTMR_DUALTRIG (0x1u << 0) /**< \brief (ADC_LCTMR) Dual Trigger ON */
#define ADC_LCTMR_CMPMOD_Pos 4
#define ADC_LCTMR_CMPMOD_Msk (0x3u << ADC_LCTMR_CMPMOD_Pos) /**< \brief (ADC_LCTMR) Last Channel Comparison Mode */
#define ADC_LCTMR_CMPMOD(value) ((ADC_LCTMR_CMPMOD_Msk & ((value) << ADC_LCTMR_CMPMOD_Pos)))
#define   ADC_LCTMR_CMPMOD_LOW (0x0u << 4) /**< \brief (ADC_LCTMR) Generates an event when the converted data is lower than the low threshold of the window. */
#define   ADC_LCTMR_CMPMOD_HIGH (0x1u << 4) /**< \brief (ADC_LCTMR) Generates an event when the converted data is higher than the high threshold of the window. */
#define   ADC_LCTMR_CMPMOD_IN (0x2u << 4) /**< \brief (ADC_LCTMR) Generates an event when the converted data is in the comparison window. */
#define   ADC_LCTMR_CMPMOD_OUT (0x3u << 4) /**< \brief (ADC_LCTMR) Generates an event when the converted data is out of the comparison window. */
/* -------- ADC_LCCWR : (ADC Offset: 0x38) Last Channel Compare Window Register -------- */
#define ADC_LCCWR_LOWTHRES_Pos 0
#define ADC_LCCWR_LOWTHRES_Msk (0xfffu << ADC_LCCWR_LOWTHRES_Pos) /**< \brief (ADC_LCCWR) Low Threshold */
#define ADC_LCCWR_LOWTHRES(value) ((ADC_LCCWR_LOWTHRES_Msk & ((value) << ADC_LCCWR_LOWTHRES_Pos)))
#define ADC_LCCWR_HIGHTHRES_Pos 16
#define ADC_LCCWR_HIGHTHRES_Msk (0xfffu << ADC_LCCWR_HIGHTHRES_Pos) /**< \brief (ADC_LCCWR) High Threshold */
#define ADC_LCCWR_HIGHTHRES(value) ((ADC_LCCWR_HIGHTHRES_Msk & ((value) << ADC_LCCWR_HIGHTHRES_Pos)))
/* -------- ADC_OVER : (ADC Offset: 0x3C) Overrun Status Register -------- */
#define ADC_OVER_OVRE0 (0x1u << 0) /**< \brief (ADC_OVER) Overrun Error 0 */
#define ADC_OVER_OVRE1 (0x1u << 1) /**< \brief (ADC_OVER) Overrun Error 1 */
#define ADC_OVER_OVRE2 (0x1u << 2) /**< \brief (ADC_OVER) Overrun Error 2 */
#define ADC_OVER_OVRE3 (0x1u << 3) /**< \brief (ADC_OVER) Overrun Error 3 */
#define ADC_OVER_OVRE4 (0x1u << 4) /**< \brief (ADC_OVER) Overrun Error 4 */
#define ADC_OVER_OVRE5 (0x1u << 5) /**< \brief (ADC_OVER) Overrun Error 5 */
#define ADC_OVER_OVRE6 (0x1u << 6) /**< \brief (ADC_OVER) Overrun Error 6 */
#define ADC_OVER_OVRE7 (0x1u << 7) /**< \brief (ADC_OVER) Overrun Error 7 */
#define ADC_OVER_OVRE8 (0x1u << 8) /**< \brief (ADC_OVER) Overrun Error 8 */
#define ADC_OVER_OVRE9 (0x1u << 9) /**< \brief (ADC_OVER) Overrun Error 9 */
#define ADC_OVER_OVRE10 (0x1u << 10) /**< \brief (ADC_OVER) Overrun Error 10 */
#define ADC_OVER_OVRE11 (0x1u << 11) /**< \brief (ADC_OVER) Overrun Error 11 */
/* -------- ADC_EMR : (ADC Offset: 0x40) Extended Mode Register -------- */
#define ADC_EMR_CMPMODE_Pos 0
#define ADC_EMR_CMPMODE_Msk (0x3u << ADC_EMR_CMPMODE_Pos) /**< \brief (ADC_EMR) Comparison Mode */
#define ADC_EMR_CMPMODE(value) ((ADC_EMR_CMPMODE_Msk & ((value) << ADC_EMR_CMPMODE_Pos)))
#define   ADC_EMR_CMPMODE_LOW (0x0u << 0) /**< \brief (ADC_EMR) Generates an event when the converted data is lower than the low threshold of the window. */
#define   ADC_EMR_CMPMODE_HIGH (0x1u << 0) /**< \brief (ADC_EMR) Generates an event when the converted data is higher than the high threshold of the window. */
#define   ADC_EMR_CMPMODE_IN (0x2u << 0) /**< \brief (ADC_EMR) Generates an event when the converted data is in the comparison window. */
#define   ADC_EMR_CMPMODE_OUT (0x3u << 0) /**< \brief (ADC_EMR) Generates an event when the converted data is out of the comparison window. */
#define ADC_EMR_CMPTYPE (0x1u << 2) /**< \brief (ADC_EMR) Comparison Type */
#define   ADC_EMR_CMPTYPE_FLAG_ONLY (0x0u << 2) /**< \brief (ADC_EMR) Any conversion is performed and comparison function drives the COMPE flag. */
#define   ADC_EMR_CMPTYPE_START_CONDITION (0x1u << 2) /**< \brief (ADC_EMR) Comparison conditions must be met to start the storage of all conversions until the CMPRST bit is set. */
#define ADC_EMR_CMPSEL_Pos 4
#define ADC_EMR_CMPSEL_Msk (0xfu << ADC_EMR_CMPSEL_Pos) /**< \brief (ADC_EMR) Comparison Selected Channel */
#define ADC_EMR_CMPSEL(value) ((ADC_EMR_CMPSEL_Msk & ((value) << ADC_EMR_CMPSEL_Pos)))
#define ADC_EMR_CMPALL (0x1u << 9) /**< \brief (ADC_EMR) Compare All Channels */
#define ADC_EMR_CMPFILTER_Pos 12
#define ADC_EMR_CMPFILTER_Msk (0x3u << ADC_EMR_CMPFILTER_Pos) /**< \brief (ADC_EMR) Compare Event Filtering */
#define ADC_EMR_CMPFILTER(value) ((ADC_EMR_CMPFILTER_Msk & ((value) << ADC_EMR_CMPFILTER_Pos)))
#define ADC_EMR_SRCCLK (0x1u << 21) /**< \brief (ADC_EMR) External Clock Selection */
#define   ADC_EMR_SRCCLK_PERIPH_CLK (0x0u << 21) /**< \brief (ADC_EMR) The peripheral clock is the source for the ADC prescaler. */
#define   ADC_EMR_SRCCLK_PMC_PCK (0x1u << 21) /**< \brief (ADC_EMR) PMC PCKx is the source clock for the ADC prescaler, thus the ADC clock can be independent of the core/peripheral clock. */
#define ADC_EMR_TAG (0x1u << 24) /**< \brief (ADC_EMR) Tag of the ADC_LCDR */
#define ADC_EMR_ADCMODE_Pos 28
#define ADC_EMR_ADCMODE_Msk (0x3u << ADC_EMR_ADCMODE_Pos) /**< \brief (ADC_EMR) ADC Running Mode */
#define ADC_EMR_ADCMODE(value) ((ADC_EMR_ADCMODE_Msk & ((value) << ADC_EMR_ADCMODE_Pos)))
#define   ADC_EMR_ADCMODE_NORMAL (0x0u << 28) /**< \brief (ADC_EMR) Normal mode of operation. */
#define   ADC_EMR_ADCMODE_OFFSET_ERROR (0x1u << 28) /**< \brief (ADC_EMR) Offset Error mode to measure the offset error. See Table 1-8. */
#define   ADC_EMR_ADCMODE_GAIN_ERROR_HIGH (0x2u << 28) /**< \brief (ADC_EMR) Gain Error mode to measure the gain error. See Table 1-8. */
#define   ADC_EMR_ADCMODE_GAIN_ERROR_LOW (0x3u << 28) /**< \brief (ADC_EMR) Gain Error mode to measure the gain error. See Table 1-8. */
/* -------- ADC_CWR : (ADC Offset: 0x44) Compare Window Register -------- */
#define ADC_CWR_LOWTHRES_Pos 0
#define ADC_CWR_LOWTHRES_Msk (0xfffu << ADC_CWR_LOWTHRES_Pos) /**< \brief (ADC_CWR) Low Threshold */
#define ADC_CWR_LOWTHRES(value) ((ADC_CWR_LOWTHRES_Msk & ((value) << ADC_CWR_LOWTHRES_Pos)))
#define ADC_CWR_HIGHTHRES_Pos 16
#define ADC_CWR_HIGHTHRES_Msk (0xfffu << ADC_CWR_HIGHTHRES_Pos) /**< \brief (ADC_CWR) High Threshold */
#define ADC_CWR_HIGHTHRES(value) ((ADC_CWR_HIGHTHRES_Msk & ((value) << ADC_CWR_HIGHTHRES_Pos)))
/* -------- ADC_CGR : (ADC Offset: 0x48) Channel Gain Register -------- */
#define ADC_CGR_GAIN0_Pos 0
#define ADC_CGR_GAIN0_Msk (0x3u << ADC_CGR_GAIN0_Pos) /**< \brief (ADC_CGR) Gain for Channel 0 */
#define ADC_CGR_GAIN0(value) ((ADC_CGR_GAIN0_Msk & ((value) << ADC_CGR_GAIN0_Pos)))
#define   ADC_CGR_GAIN0_SE1_DIFF0_5 (0x0u << 0) /**< \brief (ADC_CGR) Single-ended gain = 1 (ADC_COR.DIFFx = 0), differential gain = 0.5 (ADC_COR.DIFFx = 1) */
#define   ADC_CGR_GAIN0_SE1_DIFF1 (0x1u << 0) /**< \brief (ADC_CGR) Single-ended gain = 1 (ADC_COR.DIFFx = 0), differential gain = 1 (ADC_COR.DIFFx = 1) */
#define   ADC_CGR_GAIN0_SE2_DIFF2 (0x2u << 0) /**< \brief (ADC_CGR) Single-ended gain = 2 (ADC_COR.DIFFx = 0), differential gain = 2 (ADC_COR.DIFFx = 1) */
#define   ADC_CGR_GAIN0_SE4_DIFF2 (0x3u << 0) /**< \brief (ADC_CGR) Single-ended gain = 4 (ADC_COR.DIFFx = 0), differential gain = 2 (ADC_COR.DIFFx = 1) */
#define ADC_CGR_GAIN1_Pos 2
#define ADC_CGR_GAIN1_Msk (0x3u << ADC_CGR_GAIN1_Pos) /**< \brief (ADC_CGR) Gain for Channel 1 */
#define ADC_CGR_GAIN1(value) ((ADC_CGR_GAIN1_Msk & ((value) << ADC_CGR_GAIN1_Pos)))
#define   ADC_CGR_GAIN1_SE1_DIFF0_5 (0x0u << 2) /**< \brief (ADC_CGR) Single-ended gain = 1 (ADC_COR.DIFFx = 0), differential gain = 0.5 (ADC_COR.DIFFx = 1) */
#define   ADC_CGR_GAIN1_SE1_DIFF1 (0x1u << 2) /**< \brief (ADC_CGR) Single-ended gain = 1 (ADC_COR.DIFFx = 0), differential gain = 1 (ADC_COR.DIFFx = 1) */
#define   ADC_CGR_GAIN1_SE2_DIFF2 (0x2u << 2) /**< \brief (ADC_CGR) Single-ended gain = 2 (ADC_COR.DIFFx = 0), differential gain = 2 (ADC_COR.DIFFx = 1) */
#define   ADC_CGR_GAIN1_SE4_DIFF2 (0x3u << 2) /**< \brief (ADC_CGR) Single-ended gain = 4 (ADC_COR.DIFFx = 0), differential gain = 2 (ADC_COR.DIFFx = 1) */
#define ADC_CGR_GAIN2_Pos 4
#define ADC_CGR_GAIN2_Msk (0x3u << ADC_CGR_GAIN2_Pos) /**< \brief (ADC_CGR) Gain for Channel 2 */
#define ADC_CGR_GAIN2(value) ((ADC_CGR_GAIN2_Msk & ((value) << ADC_CGR_GAIN2_Pos)))
#define   ADC_CGR_GAIN2_SE1_DIFF0_5 (0x0u << 4) /**< \brief (ADC_CGR) Single-ended gain = 1 (ADC_COR.DIFFx = 0), differential gain = 0.5 (ADC_COR.DIFFx = 1) */
#define   ADC_CGR_GAIN2_SE1_DIFF1 (0x1u << 4) /**< \brief (ADC_CGR) Single-ended gain = 1 (ADC_COR.DIFFx = 0), differential gain = 1 (ADC_COR.DIFFx = 1) */
#define   ADC_CGR_GAIN2_SE2_DIFF2 (0x2u << 4) /**< \brief (ADC_CGR) Single-ended gain = 2 (ADC_COR.DIFFx = 0), differential gain = 2 (ADC_COR.DIFFx = 1) */
#define   ADC_CGR_GAIN2_SE4_DIFF2 (0x3u << 4) /**< \brief (ADC_CGR) Single-ended gain = 4 (ADC_COR.DIFFx = 0), differential gain = 2 (ADC_COR.DIFFx = 1) */
#define ADC_CGR_GAIN3_Pos 6
#define ADC_CGR_GAIN3_Msk (0x3u << ADC_CGR_GAIN3_Pos) /**< \brief (ADC_CGR) Gain for Channel 3 */
#define ADC_CGR_GAIN3(value) ((ADC_CGR_GAIN3_Msk & ((value) << ADC_CGR_GAIN3_Pos)))
#define   ADC_CGR_GAIN3_SE1_DIFF0_5 (0x0u << 6) /**< \brief (ADC_CGR) Single-ended gain = 1 (ADC_COR.DIFFx = 0), differential gain = 0.5 (ADC_COR.DIFFx = 1) */
#define   ADC_CGR_GAIN3_SE1_DIFF1 (0x1u << 6) /**< \brief (ADC_CGR) Single-ended gain = 1 (ADC_COR.DIFFx = 0), differential gain = 1 (ADC_COR.DIFFx = 1) */
#define   ADC_CGR_GAIN3_SE2_DIFF2 (0x2u << 6) /**< \brief (ADC_CGR) Single-ended gain = 2 (ADC_COR.DIFFx = 0), differential gain = 2 (ADC_COR.DIFFx = 1) */
#define   ADC_CGR_GAIN3_SE4_DIFF2 (0x3u << 6) /**< \brief (ADC_CGR) Single-ended gain = 4 (ADC_COR.DIFFx = 0), differential gain = 2 (ADC_COR.DIFFx = 1) */
#define ADC_CGR_GAIN4_Pos 8
#define ADC_CGR_GAIN4_Msk (0x3u << ADC_CGR_GAIN4_Pos) /**< \brief (ADC_CGR) Gain for Channel 4 */
#define ADC_CGR_GAIN4(value) ((ADC_CGR_GAIN4_Msk & ((value) << ADC_CGR_GAIN4_Pos)))
#define   ADC_CGR_GAIN4_SE1_DIFF0_5 (0x0u << 8) /**< \brief (ADC_CGR) Single-ended gain = 1 (ADC_COR.DIFFx = 0), differential gain = 0.5 (ADC_COR.DIFFx = 1) */
#define   ADC_CGR_GAIN4_SE1_DIFF1 (0x1u << 8) /**< \brief (ADC_CGR) Single-ended gain = 1 (ADC_COR.DIFFx = 0), differential gain = 1 (ADC_COR.DIFFx = 1) */
#define   ADC_CGR_GAIN4_SE2_DIFF2 (0x2u << 8) /**< \brief (ADC_CGR) Single-ended gain = 2 (ADC_COR.DIFFx = 0), differential gain = 2 (ADC_COR.DIFFx = 1) */
#define   ADC_CGR_GAIN4_SE4_DIFF2 (0x3u << 8) /**< \brief (ADC_CGR) Single-ended gain = 4 (ADC_COR.DIFFx = 0), differential gain = 2 (ADC_COR.DIFFx = 1) */
#define ADC_CGR_GAIN5_Pos 10
#define ADC_CGR_GAIN5_Msk (0x3u << ADC_CGR_GAIN5_Pos) /**< \brief (ADC_CGR) Gain for Channel 5 */
#define ADC_CGR_GAIN5(value) ((ADC_CGR_GAIN5_Msk & ((value) << ADC_CGR_GAIN5_Pos)))
#define   ADC_CGR_GAIN5_SE1_DIFF0_5 (0x0u << 10) /**< \brief (ADC_CGR) Single-ended gain = 1 (ADC_COR.DIFFx = 0), differential gain = 0.5 (ADC_COR.DIFFx = 1) */
#define   ADC_CGR_GAIN5_SE1_DIFF1 (0x1u << 10) /**< \brief (ADC_CGR) Single-ended gain = 1 (ADC_COR.DIFFx = 0), differential gain = 1 (ADC_COR.DIFFx = 1) */
#define   ADC_CGR_GAIN5_SE2_DIFF2 (0x2u << 10) /**< \brief (ADC_CGR) Single-ended gain = 2 (ADC_COR.DIFFx = 0), differential gain = 2 (ADC_COR.DIFFx = 1) */
#define   ADC_CGR_GAIN5_SE4_DIFF2 (0x3u << 10) /**< \brief (ADC_CGR) Single-ended gain = 4 (ADC_COR.DIFFx = 0), differential gain = 2 (ADC_COR.DIFFx = 1) */
#define ADC_CGR_GAIN6_Pos 12
#define ADC_CGR_GAIN6_Msk (0x3u << ADC_CGR_GAIN6_Pos) /**< \brief (ADC_CGR) Gain for Channel 6 */
#define ADC_CGR_GAIN6(value) ((ADC_CGR_GAIN6_Msk & ((value) << ADC_CGR_GAIN6_Pos)))
#define   ADC_CGR_GAIN6_SE1_DIFF0_5 (0x0u << 12) /**< \brief (ADC_CGR) Single-ended gain = 1 (ADC_COR.DIFFx = 0), differential gain = 0.5 (ADC_COR.DIFFx = 1) */
#define   ADC_CGR_GAIN6_SE1_DIFF1 (0x1u << 12) /**< \brief (ADC_CGR) Single-ended gain = 1 (ADC_COR.DIFFx = 0), differential gain = 1 (ADC_COR.DIFFx = 1) */
#define   ADC_CGR_GAIN6_SE2_DIFF2 (0x2u << 12) /**< \brief (ADC_CGR) Single-ended gain = 2 (ADC_COR.DIFFx = 0), differential gain = 2 (ADC_COR.DIFFx = 1) */
#define   ADC_CGR_GAIN6_SE4_DIFF2 (0x3u << 12) /**< \brief (ADC_CGR) Single-ended gain = 4 (ADC_COR.DIFFx = 0), differential gain = 2 (ADC_COR.DIFFx = 1) */
#define ADC_CGR_GAIN7_Pos 14
#define ADC_CGR_GAIN7_Msk (0x3u << ADC_CGR_GAIN7_Pos) /**< \brief (ADC_CGR) Gain for Channel 7 */
#define ADC_CGR_GAIN7(value) ((ADC_CGR_GAIN7_Msk & ((value) << ADC_CGR_GAIN7_Pos)))
#define   ADC_CGR_GAIN7_SE1_DIFF0_5 (0x0u << 14) /**< \brief (ADC_CGR) Single-ended gain = 1 (ADC_COR.DIFFx = 0), differential gain = 0.5 (ADC_COR.DIFFx = 1) */
#define   ADC_CGR_GAIN7_SE1_DIFF1 (0x1u << 14) /**< \brief (ADC_CGR) Single-ended gain = 1 (ADC_COR.DIFFx = 0), differential gain = 1 (ADC_COR.DIFFx = 1) */
#define   ADC_CGR_GAIN7_SE2_DIFF2 (0x2u << 14) /**< \brief (ADC_CGR) Single-ended gain = 2 (ADC_COR.DIFFx = 0), differential gain = 2 (ADC_COR.DIFFx = 1) */
#define   ADC_CGR_GAIN7_SE4_DIFF2 (0x3u << 14) /**< \brief (ADC_CGR) Single-ended gain = 4 (ADC_COR.DIFFx = 0), differential gain = 2 (ADC_COR.DIFFx = 1) */
#define ADC_CGR_GAIN8_Pos 16
#define ADC_CGR_GAIN8_Msk (0x3u << ADC_CGR_GAIN8_Pos) /**< \brief (ADC_CGR) Gain for Channel 8 */
#define ADC_CGR_GAIN8(value) ((ADC_CGR_GAIN8_Msk & ((value) << ADC_CGR_GAIN8_Pos)))
#define   ADC_CGR_GAIN8_SE1_DIFF0_5 (0x0u << 16) /**< \brief (ADC_CGR) Single-ended gain = 1 (ADC_COR.DIFFx = 0), differential gain = 0.5 (ADC_COR.DIFFx = 1) */
#define   ADC_CGR_GAIN8_SE1_DIFF1 (0x1u << 16) /**< \brief (ADC_CGR) Single-ended gain = 1 (ADC_COR.DIFFx = 0), differential gain = 1 (ADC_COR.DIFFx = 1) */
#define   ADC_CGR_GAIN8_SE2_DIFF2 (0x2u << 16) /**< \brief (ADC_CGR) Single-ended gain = 2 (ADC_COR.DIFFx = 0), differential gain = 2 (ADC_COR.DIFFx = 1) */
#define   ADC_CGR_GAIN8_SE4_DIFF2 (0x3u << 16) /**< \brief (ADC_CGR) Single-ended gain = 4 (ADC_COR.DIFFx = 0), differential gain = 2 (ADC_COR.DIFFx = 1) */
#define ADC_CGR_GAIN9_Pos 18
#define ADC_CGR_GAIN9_Msk (0x3u << ADC_CGR_GAIN9_Pos) /**< \brief (ADC_CGR) Gain for Channel 9 */
#define ADC_CGR_GAIN9(value) ((ADC_CGR_GAIN9_Msk & ((value) << ADC_CGR_GAIN9_Pos)))
#define   ADC_CGR_GAIN9_SE1_DIFF0_5 (0x0u << 18) /**< \brief (ADC_CGR) Single-ended gain = 1 (ADC_COR.DIFFx = 0), differential gain = 0.5 (ADC_COR.DIFFx = 1) */
#define   ADC_CGR_GAIN9_SE1_DIFF1 (0x1u << 18) /**< \brief (ADC_CGR) Single-ended gain = 1 (ADC_COR.DIFFx = 0), differential gain = 1 (ADC_COR.DIFFx = 1) */
#define   ADC_CGR_GAIN9_SE2_DIFF2 (0x2u << 18) /**< \brief (ADC_CGR) Single-ended gain = 2 (ADC_COR.DIFFx = 0), differential gain = 2 (ADC_COR.DIFFx = 1) */
#define   ADC_CGR_GAIN9_SE4_DIFF2 (0x3u << 18) /**< \brief (ADC_CGR) Single-ended gain = 4 (ADC_COR.DIFFx = 0), differential gain = 2 (ADC_COR.DIFFx = 1) */
#define ADC_CGR_GAIN10_Pos 20
#define ADC_CGR_GAIN10_Msk (0x3u << ADC_CGR_GAIN10_Pos) /**< \brief (ADC_CGR) Gain for Channel 10 */
#define ADC_CGR_GAIN10(value) ((ADC_CGR_GAIN10_Msk & ((value) << ADC_CGR_GAIN10_Pos)))
#define   ADC_CGR_GAIN10_SE1_DIFF0_5 (0x0u << 20) /**< \brief (ADC_CGR) Single-ended gain = 1 (ADC_COR.DIFFx = 0), differential gain = 0.5 (ADC_COR.DIFFx = 1) */
#define   ADC_CGR_GAIN10_SE1_DIFF1 (0x1u << 20) /**< \brief (ADC_CGR) Single-ended gain = 1 (ADC_COR.DIFFx = 0), differential gain = 1 (ADC_COR.DIFFx = 1) */
#define   ADC_CGR_GAIN10_SE2_DIFF2 (0x2u << 20) /**< \brief (ADC_CGR) Single-ended gain = 2 (ADC_COR.DIFFx = 0), differential gain = 2 (ADC_COR.DIFFx = 1) */
#define   ADC_CGR_GAIN10_SE4_DIFF2 (0x3u << 20) /**< \brief (ADC_CGR) Single-ended gain = 4 (ADC_COR.DIFFx = 0), differential gain = 2 (ADC_COR.DIFFx = 1) */
#define ADC_CGR_GAIN11_Pos 22
#define ADC_CGR_GAIN11_Msk (0x3u << ADC_CGR_GAIN11_Pos) /**< \brief (ADC_CGR) Gain for Channel 11 */
#define ADC_CGR_GAIN11(value) ((ADC_CGR_GAIN11_Msk & ((value) << ADC_CGR_GAIN11_Pos)))
#define   ADC_CGR_GAIN11_SE1_DIFF0_5 (0x0u << 22) /**< \brief (ADC_CGR) Single-ended gain = 1 (ADC_COR.DIFFx = 0), differential gain = 0.5 (ADC_COR.DIFFx = 1) */
#define   ADC_CGR_GAIN11_SE1_DIFF1 (0x1u << 22) /**< \brief (ADC_CGR) Single-ended gain = 1 (ADC_COR.DIFFx = 0), differential gain = 1 (ADC_COR.DIFFx = 1) */
#define   ADC_CGR_GAIN11_SE2_DIFF2 (0x2u << 22) /**< \brief (ADC_CGR) Single-ended gain = 2 (ADC_COR.DIFFx = 0), differential gain = 2 (ADC_COR.DIFFx = 1) */
#define   ADC_CGR_GAIN11_SE4_DIFF2 (0x3u << 22) /**< \brief (ADC_CGR) Single-ended gain = 4 (ADC_COR.DIFFx = 0), differential gain = 2 (ADC_COR.DIFFx = 1) */
/* -------- ADC_COR : (ADC Offset: 0x4C) Channel Offset Register -------- */
#define ADC_COR_OFF0 (0x1u << 0) /**< \brief (ADC_COR) Offset for Channel 0 */
#define ADC_COR_OFF1 (0x1u << 1) /**< \brief (ADC_COR) Offset for Channel 1 */
#define ADC_COR_OFF2 (0x1u << 2) /**< \brief (ADC_COR) Offset for Channel 2 */
#define ADC_COR_OFF3 (0x1u << 3) /**< \brief (ADC_COR) Offset for Channel 3 */
#define ADC_COR_OFF4 (0x1u << 4) /**< \brief (ADC_COR) Offset for Channel 4 */
#define ADC_COR_OFF5 (0x1u << 5) /**< \brief (ADC_COR) Offset for Channel 5 */
#define ADC_COR_OFF6 (0x1u << 6) /**< \brief (ADC_COR) Offset for Channel 6 */
#define ADC_COR_OFF7 (0x1u << 7) /**< \brief (ADC_COR) Offset for Channel 7 */
#define ADC_COR_OFF8 (0x1u << 8) /**< \brief (ADC_COR) Offset for Channel 8 */
#define ADC_COR_OFF9 (0x1u << 9) /**< \brief (ADC_COR) Offset for Channel 9 */
#define ADC_COR_OFF10 (0x1u << 10) /**< \brief (ADC_COR) Offset for Channel 10 */
#define ADC_COR_OFF11 (0x1u << 11) /**< \brief (ADC_COR) Offset for Channel 11 */
#define ADC_COR_DIFF0 (0x1u << 16) /**< \brief (ADC_COR) Differential Inputs for Channel 0 */
#define ADC_COR_DIFF1 (0x1u << 17) /**< \brief (ADC_COR) Differential Inputs for Channel 1 */
#define ADC_COR_DIFF2 (0x1u << 18) /**< \brief (ADC_COR) Differential Inputs for Channel 2 */
#define ADC_COR_DIFF3 (0x1u << 19) /**< \brief (ADC_COR) Differential Inputs for Channel 3 */
#define ADC_COR_DIFF4 (0x1u << 20) /**< \brief (ADC_COR) Differential Inputs for Channel 4 */
#define ADC_COR_DIFF5 (0x1u << 21) /**< \brief (ADC_COR) Differential Inputs for Channel 5 */
#define ADC_COR_DIFF6 (0x1u << 22) /**< \brief (ADC_COR) Differential Inputs for Channel 6 */
#define ADC_COR_DIFF7 (0x1u << 23) /**< \brief (ADC_COR) Differential Inputs for Channel 7 */
#define ADC_COR_DIFF8 (0x1u << 24) /**< \brief (ADC_COR) Differential Inputs for Channel 8 */
#define ADC_COR_DIFF9 (0x1u << 25) /**< \brief (ADC_COR) Differential Inputs for Channel 9 */
#define ADC_COR_DIFF10 (0x1u << 26) /**< \brief (ADC_COR) Differential Inputs for Channel 10 */
#define ADC_COR_DIFF11 (0x1u << 27) /**< \brief (ADC_COR) Differential Inputs for Channel 11 */
/* -------- ADC_CDR0 : (ADC Offset: 0x50) Channel Data Register 0 -------- */
#define ADC_CDR0_DATA_Pos 0
#define ADC_CDR0_DATA_Msk (0xfffu << ADC_CDR0_DATA_Pos) /**< \brief (ADC_CDR0) Converted Data */
/* -------- ADC_CDR1 : (ADC Offset: 0x54) Channel Data Register 1 -------- */
#define ADC_CDR1_DATA_Pos 0
#define ADC_CDR1_DATA_Msk (0xfffu << ADC_CDR1_DATA_Pos) /**< \brief (ADC_CDR1) Converted Data */
/* -------- ADC_CDR2 : (ADC Offset: 0x58) Channel Data Register 2 -------- */
#define ADC_CDR2_DATA_Pos 0
#define ADC_CDR2_DATA_Msk (0xfffu << ADC_CDR2_DATA_Pos) /**< \brief (ADC_CDR2) Converted Data */
/* -------- ADC_CDR3 : (ADC Offset: 0x5C) Channel Data Register 3 -------- */
#define ADC_CDR3_DATA_Pos 0
#define ADC_CDR3_DATA_Msk (0xfffu << ADC_CDR3_DATA_Pos) /**< \brief (ADC_CDR3) Converted Data */
/* -------- ADC_CDR4 : (ADC Offset: 0x60) Channel Data Register 4 -------- */
#define ADC_CDR4_DATA_Pos 0
#define ADC_CDR4_DATA_Msk (0xfffu << ADC_CDR4_DATA_Pos) /**< \brief (ADC_CDR4) Converted Data */
/* -------- ADC_CDR5 : (ADC Offset: 0x64) Channel Data Register 5 -------- */
#define ADC_CDR5_DATA_Pos 0
#define ADC_CDR5_DATA_Msk (0xfffu << ADC_CDR5_DATA_Pos) /**< \brief (ADC_CDR5) Converted Data */
/* -------- ADC_CDR6 : (ADC Offset: 0x68) Channel Data Register 6 -------- */
#define ADC_CDR6_DATA_Pos 0
#define ADC_CDR6_DATA_Msk (0xfffu << ADC_CDR6_DATA_Pos) /**< \brief (ADC_CDR6) Converted Data */
/* -------- ADC_CDR7 : (ADC Offset: 0x6C) Channel Data Register 7 -------- */
#define ADC_CDR7_DATA_Pos 0
#define ADC_CDR7_DATA_Msk (0xfffu << ADC_CDR7_DATA_Pos) /**< \brief (ADC_CDR7) Converted Data */
/* -------- ADC_CDR8 : (ADC Offset: 0x70) Channel Data Register 8 -------- */
#define ADC_CDR8_DATA_Pos 0
#define ADC_CDR8_DATA_Msk (0xfffu << ADC_CDR8_DATA_Pos) /**< \brief (ADC_CDR8) Converted Data */
/* -------- ADC_CDR9 : (ADC Offset: 0x74) Channel Data Register 9 -------- */
#define ADC_CDR9_DATA_Pos 0
#define ADC_CDR9_DATA_Msk (0xfffu << ADC_CDR9_DATA_Pos) /**< \brief (ADC_CDR9) Converted Data */
/* -------- ADC_CDR10 : (ADC Offset: 0x78) Channel Data Register 10 -------- */
#define ADC_CDR10_DATA_Pos 0
#define ADC_CDR10_DATA_Msk (0xfffu << ADC_CDR10_DATA_Pos) /**< \brief (ADC_CDR10) Converted Data */
/* -------- ADC_CDR11 : (ADC Offset: 0x7C) Channel Data Register 11 -------- */
#define ADC_CDR11_DATA_Pos 0
#define ADC_CDR11_DATA_Msk (0xfffu << ADC_CDR11_DATA_Pos) /**< \brief (ADC_CDR11) Converted Data */
/* -------- ADC_ACR : (ADC Offset: 0x94) Analog Control Register -------- */
#define ADC_ACR_PENDETSENS_Pos 0
#define ADC_ACR_PENDETSENS_Msk (0x3u << ADC_ACR_PENDETSENS_Pos) /**< \brief (ADC_ACR) Pen Detection Sensitivity */
#define ADC_ACR_PENDETSENS(value) ((ADC_ACR_PENDETSENS_Msk & ((value) << ADC_ACR_PENDETSENS_Pos)))
/* -------- ADC_TSMR : (ADC Offset: 0xB0) Touchscreen Mode Register -------- */
#define ADC_TSMR_TSMODE_Pos 0
#define ADC_TSMR_TSMODE_Msk (0x3u << ADC_TSMR_TSMODE_Pos) /**< \brief (ADC_TSMR) Touchscreen Mode */
#define ADC_TSMR_TSMODE(value) ((ADC_TSMR_TSMODE_Msk & ((value) << ADC_TSMR_TSMODE_Pos)))
#define   ADC_TSMR_TSMODE_NONE (0x0u << 0) /**< \brief (ADC_TSMR) No Touchscreen */
#define   ADC_TSMR_TSMODE_4_WIRE_NO_PM (0x1u << 0) /**< \brief (ADC_TSMR) 4-wire Touchscreen without pressure measurement */
#define   ADC_TSMR_TSMODE_4_WIRE (0x2u << 0) /**< \brief (ADC_TSMR) 4-wire Touchscreen with pressure measurement */
#define   ADC_TSMR_TSMODE_5_WIRE (0x3u << 0) /**< \brief (ADC_TSMR) 5-wire Touchscreen */
#define ADC_TSMR_TSAV_Pos 4
#define ADC_TSMR_TSAV_Msk (0x3u << ADC_TSMR_TSAV_Pos) /**< \brief (ADC_TSMR) Touchscreen Average */
#define ADC_TSMR_TSAV(value) ((ADC_TSMR_TSAV_Msk & ((value) << ADC_TSMR_TSAV_Pos)))
#define   ADC_TSMR_TSAV_NO_FILTER (0x0u << 4) /**< \brief (ADC_TSMR) No Filtering. Only one ADC conversion per measure */
#define   ADC_TSMR_TSAV_AVG2CONV (0x1u << 4) /**< \brief (ADC_TSMR) Averages 2 ADC conversions */
#define   ADC_TSMR_TSAV_AVG4CONV (0x2u << 4) /**< \brief (ADC_TSMR) Averages 4 ADC conversions */
#define   ADC_TSMR_TSAV_AVG8CONV (0x3u << 4) /**< \brief (ADC_TSMR) Averages 8 ADC conversions */
#define ADC_TSMR_TSFREQ_Pos 8
#define ADC_TSMR_TSFREQ_Msk (0xfu << ADC_TSMR_TSFREQ_Pos) /**< \brief (ADC_TSMR) Touchscreen Frequency */
#define ADC_TSMR_TSFREQ(value) ((ADC_TSMR_TSFREQ_Msk & ((value) << ADC_TSMR_TSFREQ_Pos)))
#define ADC_TSMR_TSSCTIM_Pos 16
#define ADC_TSMR_TSSCTIM_Msk (0xfu << ADC_TSMR_TSSCTIM_Pos) /**< \brief (ADC_TSMR) Touchscreen Switches Closure Time */
#define ADC_TSMR_TSSCTIM(value) ((ADC_TSMR_TSSCTIM_Msk & ((value) << ADC_TSMR_TSSCTIM_Pos)))
#define ADC_TSMR_NOTSDMA (0x1u << 22) /**< \brief (ADC_TSMR) No TouchScreen DMA */
#define ADC_TSMR_PENDET (0x1u << 24) /**< \brief (ADC_TSMR) Pen Contact Detection Enable */
#define ADC_TSMR_PENDBC_Pos 28
#define ADC_TSMR_PENDBC_Msk (0xfu << ADC_TSMR_PENDBC_Pos) /**< \brief (ADC_TSMR) Pen Detect Debouncing Period */
#define ADC_TSMR_PENDBC(value) ((ADC_TSMR_PENDBC_Msk & ((value) << ADC_TSMR_PENDBC_Pos)))
/* -------- ADC_XPOSR : (ADC Offset: 0xB4) Touchscreen X Position Register -------- */
#define ADC_XPOSR_XPOS_Pos 0
#define ADC_XPOSR_XPOS_Msk (0xfffu << ADC_XPOSR_XPOS_Pos) /**< \brief (ADC_XPOSR) X Position */
#define ADC_XPOSR_XSCALE_Pos 16
#define ADC_XPOSR_XSCALE_Msk (0xfffu << ADC_XPOSR_XSCALE_Pos) /**< \brief (ADC_XPOSR) Scale of XPOS */
/* -------- ADC_YPOSR : (ADC Offset: 0xB8) Touchscreen Y Position Register -------- */
#define ADC_YPOSR_YPOS_Pos 0
#define ADC_YPOSR_YPOS_Msk (0xfffu << ADC_YPOSR_YPOS_Pos) /**< \brief (ADC_YPOSR) Y Position */
#define ADC_YPOSR_YSCALE_Pos 16
#define ADC_YPOSR_YSCALE_Msk (0xfffu << ADC_YPOSR_YSCALE_Pos) /**< \brief (ADC_YPOSR) Scale of YPOS */
/* -------- ADC_PRESSR : (ADC Offset: 0xBC) Touchscreen Pressure Register -------- */
#define ADC_PRESSR_Z1_Pos 0
#define ADC_PRESSR_Z1_Msk (0xfffu << ADC_PRESSR_Z1_Pos) /**< \brief (ADC_PRESSR) Data of Z1 Measurement */
#define ADC_PRESSR_Z2_Pos 16
#define ADC_PRESSR_Z2_Msk (0xfffu << ADC_PRESSR_Z2_Pos) /**< \brief (ADC_PRESSR) Data of Z2 Measurement */
/* -------- ADC_TRGR : (ADC Offset: 0xC0) Trigger Register -------- */
#define ADC_TRGR_TRGMOD_Pos 0
#define ADC_TRGR_TRGMOD_Msk (0x7u << ADC_TRGR_TRGMOD_Pos) /**< \brief (ADC_TRGR) Trigger Mode */
#define ADC_TRGR_TRGMOD(value) ((ADC_TRGR_TRGMOD_Msk & ((value) << ADC_TRGR_TRGMOD_Pos)))
#define   ADC_TRGR_TRGMOD_NO_TRIGGER (0x0u << 0) /**< \brief (ADC_TRGR) No trigger, only software trigger can start conversions */
#define   ADC_TRGR_TRGMOD_EXT_TRIG_RISE (0x1u << 0) /**< \brief (ADC_TRGR) External trigger rising edge */
#define   ADC_TRGR_TRGMOD_EXT_TRIG_FALL (0x2u << 0) /**< \brief (ADC_TRGR) External trigger falling edge */
#define   ADC_TRGR_TRGMOD_EXT_TRIG_ANY (0x3u << 0) /**< \brief (ADC_TRGR) External trigger any edge */
#define   ADC_TRGR_TRGMOD_PEN_TRIG (0x4u << 0) /**< \brief (ADC_TRGR) Pen Detect Trigger (shall be selected only if PENDET is set and TSAMOD = Touchscreen only mode) */
#define   ADC_TRGR_TRGMOD_PERIOD_TRIG (0x5u << 0) /**< \brief (ADC_TRGR) ADC internal periodic trigger (see field TRGPER) */
#define   ADC_TRGR_TRGMOD_CONTINUOUS (0x6u << 0) /**< \brief (ADC_TRGR) Continuous Mode */
#define ADC_TRGR_TRGPER_Pos 16
#define ADC_TRGR_TRGPER_Msk (0xffffu << ADC_TRGR_TRGPER_Pos) /**< \brief (ADC_TRGR) Trigger Period */
#define ADC_TRGR_TRGPER(value) ((ADC_TRGR_TRGPER_Msk & ((value) << ADC_TRGR_TRGPER_Pos)))
/* -------- ADC_COSR : (ADC Offset: 0xD0) Correction Select Register -------- */
#define ADC_COSR_CSEL_Pos 0
#define ADC_COSR_CSEL_Msk (0x1fu << ADC_COSR_CSEL_Pos) /**< \brief (ADC_COSR) CORRECTION_TYPE Correction Select */
#define ADC_COSR_CSEL(value) ((ADC_COSR_CSEL_Msk & ((value) << ADC_COSR_CSEL_Pos)))
/* -------- ADC_CVR : (ADC Offset: 0xD4) Correction Values Register -------- */
#define ADC_CVR_OFFSETCORR_Pos 0
#define ADC_CVR_OFFSETCORR_Msk (0xffffu << ADC_CVR_OFFSETCORR_Pos) /**< \brief (ADC_CVR) Offset Correction */
#define ADC_CVR_OFFSETCORR(value) ((ADC_CVR_OFFSETCORR_Msk & ((value) << ADC_CVR_OFFSETCORR_Pos)))
#define ADC_CVR_GAINCORR_Pos 16
#define ADC_CVR_GAINCORR_Msk (0xffffu << ADC_CVR_GAINCORR_Pos) /**< \brief (ADC_CVR) Gain Correction */
#define ADC_CVR_GAINCORR(value) ((ADC_CVR_GAINCORR_Msk & ((value) << ADC_CVR_GAINCORR_Pos)))
/* -------- ADC_CECR : (ADC Offset: 0xD8) Channel Error Correction Register -------- */
#define ADC_CECR_ECORR0 (0x1u << 0) /**< \brief (ADC_CECR) Error Correction Enable for channel 0 */
#define ADC_CECR_ECORR1 (0x1u << 1) /**< \brief (ADC_CECR) Error Correction Enable for channel 1 */
#define ADC_CECR_ECORR2 (0x1u << 2) /**< \brief (ADC_CECR) Error Correction Enable for channel 2 */
#define ADC_CECR_ECORR3 (0x1u << 3) /**< \brief (ADC_CECR) Error Correction Enable for channel 3 */
#define ADC_CECR_ECORR4 (0x1u << 4) /**< \brief (ADC_CECR) Error Correction Enable for channel 4 */
#define ADC_CECR_ECORR5 (0x1u << 5) /**< \brief (ADC_CECR) Error Correction Enable for channel 5 */
#define ADC_CECR_ECORR6 (0x1u << 6) /**< \brief (ADC_CECR) Error Correction Enable for channel 6 */
#define ADC_CECR_ECORR7 (0x1u << 7) /**< \brief (ADC_CECR) Error Correction Enable for channel 7 */
#define ADC_CECR_ECORR8 (0x1u << 8) /**< \brief (ADC_CECR) Error Correction Enable for channel 8 */
#define ADC_CECR_ECORR9 (0x1u << 9) /**< \brief (ADC_CECR) Error Correction Enable for channel 9 */
#define ADC_CECR_ECORR10 (0x1u << 10) /**< \brief (ADC_CECR) Error Correction Enable for channel 10 */
#define ADC_CECR_ECORR11 (0x1u << 11) /**< \brief (ADC_CECR) Error Correction Enable for channel 11 */
/* -------- ADC_WPMR : (ADC Offset: 0xE4) Write Protection Mode Register -------- */
#define ADC_WPMR_WPEN (0x1u << 0) /**< \brief (ADC_WPMR) Write Protection Enable */
#define ADC_WPMR_WPKEY_Pos 8
#define ADC_WPMR_WPKEY_Msk (0xffffffu << ADC_WPMR_WPKEY_Pos) /**< \brief (ADC_WPMR) Write Protection Key */
#define ADC_WPMR_WPKEY(value) ((ADC_WPMR_WPKEY_Msk & ((value) << ADC_WPMR_WPKEY_Pos)))
#define   ADC_WPMR_WPKEY_PASSWD (0x414443u << 8) /**< \brief (ADC_WPMR) Writing any other value in this field aborts the write operation of the WPEN bit.Always reads as 0 */
/* -------- ADC_WPSR : (ADC Offset: 0xE8) Write Protection Status Register -------- */
#define ADC_WPSR_WPVS (0x1u << 0) /**< \brief (ADC_WPSR) Write Protection Violation Status */
#define ADC_WPSR_WPVSRC_Pos 8
#define ADC_WPSR_WPVSRC_Msk (0xffffu << ADC_WPSR_WPVSRC_Pos) /**< \brief (ADC_WPSR) Write Protection Violation Source */
/* -------- ADC_VERSION : (ADC Offset: 0xFC) Version Register -------- */
#define ADC_VERSION_VERSION_Pos 0
#define ADC_VERSION_VERSION_Msk (0xfffu << ADC_VERSION_VERSION_Pos) /**< \brief (ADC_VERSION) Version of the Hardware Module */
#define ADC_VERSION_MFN_Pos 16
#define ADC_VERSION_MFN_Msk (0x7u << ADC_VERSION_MFN_Pos) /**< \brief (ADC_VERSION) Metal Fix Number */

/*@}*/


#endif /* _SAMA5D2_ADC_COMPONENT_ */
