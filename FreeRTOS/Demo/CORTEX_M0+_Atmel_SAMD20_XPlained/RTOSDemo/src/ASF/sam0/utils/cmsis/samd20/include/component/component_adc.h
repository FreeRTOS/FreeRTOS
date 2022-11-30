/**
 * \file
 *
 * \brief Component description for ADC
 *
 * Copyright (c) 2013 Atmel Corporation. All rights reserved.
 *
 * \asf_license_start
 *
 * \page License
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 *
 * 3. The name of Atmel may not be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * 4. This software may only be redistributed and used in connection with an
 *    Atmel microcontroller product.
 *
 * THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * EXPRESSLY AND SPECIFICALLY DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
 * ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *
 * \asf_license_stop
 *
 */

#ifndef _SAMD20_ADC_COMPONENT_
#define _SAMD20_ADC_COMPONENT_

/* ========================================================================== */
/**  SOFTWARE API DEFINITION FOR ADC */
/* ========================================================================== */
/** \addtogroup SAMD20_ADC Analog Digital Converter */
/*@{*/

#define REV_ADC                     0x110

/* -------- ADC_CTRLA : (ADC Offset: 0x00) (R/W  8) Control Register A -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  SWRST:1;          /*!< bit:      0  Software Reset                     */
    uint8_t  ENABLE:1;         /*!< bit:      1  Enable                             */
    uint8_t  RUNSTDBY:1;       /*!< bit:      2  Run during Standby                 */
    uint8_t  :5;               /*!< bit:  3.. 7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} ADC_CTRLA_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define ADC_CTRLA_OFFSET            0x00         /**< \brief (ADC_CTRLA offset) Control Register A */
#define ADC_CTRLA_RESETVALUE        0x00         /**< \brief (ADC_CTRLA reset_value) Control Register A */

#define ADC_CTRLA_SWRST_Pos         0            /**< \brief (ADC_CTRLA) Software Reset */
#define ADC_CTRLA_SWRST             (0x1u << ADC_CTRLA_SWRST_Pos)
#define ADC_CTRLA_ENABLE_Pos        1            /**< \brief (ADC_CTRLA) Enable */
#define ADC_CTRLA_ENABLE            (0x1u << ADC_CTRLA_ENABLE_Pos)
#define ADC_CTRLA_RUNSTDBY_Pos      2            /**< \brief (ADC_CTRLA) Run during Standby */
#define ADC_CTRLA_RUNSTDBY          (0x1u << ADC_CTRLA_RUNSTDBY_Pos)
#define ADC_CTRLA_MASK              0x07u        /**< \brief (ADC_CTRLA) MASK Register */

/* -------- ADC_REFCTRL : (ADC Offset: 0x01) (R/W  8) Reference Control Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  REFSEL:4;         /*!< bit:  0.. 3  Reference Selection                */
    uint8_t  :3;               /*!< bit:  4.. 6  Reserved                           */
    uint8_t  REFCOMP:1;        /*!< bit:      7  Reference Buffer Offset Compensation Enable */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} ADC_REFCTRL_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define ADC_REFCTRL_OFFSET          0x01         /**< \brief (ADC_REFCTRL offset) Reference Control Register */
#define ADC_REFCTRL_RESETVALUE      0x00         /**< \brief (ADC_REFCTRL reset_value) Reference Control Register */

#define ADC_REFCTRL_REFSEL_Pos      0            /**< \brief (ADC_REFCTRL) Reference Selection */
#define ADC_REFCTRL_REFSEL_Msk      (0xFu << ADC_REFCTRL_REFSEL_Pos)
#define ADC_REFCTRL_REFSEL(value)   ((ADC_REFCTRL_REFSEL_Msk & ((value) << ADC_REFCTRL_REFSEL_Pos)))
#define   ADC_REFCTRL_REFSEL_INT1V  (0x0u <<  0) /**< \brief (ADC_REFCTRL)  */
#define   ADC_REFCTRL_REFSEL_INTVCC0 (0x1u <<  0) /**< \brief (ADC_REFCTRL)  */
#define   ADC_REFCTRL_REFSEL_INTVCC1 (0x2u <<  0) /**< \brief (ADC_REFCTRL)  */
#define   ADC_REFCTRL_REFSEL_AREFA  (0x3u <<  0) /**< \brief (ADC_REFCTRL)  */
#define   ADC_REFCTRL_REFSEL_AREFB  (0x4u <<  0) /**< \brief (ADC_REFCTRL)  */
#define ADC_REFCTRL_REFCOMP_Pos     7            /**< \brief (ADC_REFCTRL) Reference Buffer Offset Compensation Enable */
#define ADC_REFCTRL_REFCOMP         (0x1u << ADC_REFCTRL_REFCOMP_Pos)
#define ADC_REFCTRL_MASK            0x8Fu        /**< \brief (ADC_REFCTRL) MASK Register */

/* -------- ADC_AVGCTRL : (ADC Offset: 0x02) (R/W  8) Average Control Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  SAMPLENUM:4;      /*!< bit:  0.. 3  Number of Samples to be Collected  */
    uint8_t  ADJRES:3;         /*!< bit:  4.. 6  Adjusting Result / Division Coefficient */
    uint8_t  :1;               /*!< bit:      7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} ADC_AVGCTRL_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define ADC_AVGCTRL_OFFSET          0x02         /**< \brief (ADC_AVGCTRL offset) Average Control Register */
#define ADC_AVGCTRL_RESETVALUE      0x00         /**< \brief (ADC_AVGCTRL reset_value) Average Control Register */

#define ADC_AVGCTRL_SAMPLENUM_Pos   0            /**< \brief (ADC_AVGCTRL) Number of Samples to be Collected */
#define ADC_AVGCTRL_SAMPLENUM_Msk   (0xFu << ADC_AVGCTRL_SAMPLENUM_Pos)
#define ADC_AVGCTRL_SAMPLENUM(value) ((ADC_AVGCTRL_SAMPLENUM_Msk & ((value) << ADC_AVGCTRL_SAMPLENUM_Pos)))
#define   ADC_AVGCTRL_SAMPLENUM_1   (0x0u <<  0) /**< \brief (ADC_AVGCTRL)  */
#define   ADC_AVGCTRL_SAMPLENUM_2   (0x1u <<  0) /**< \brief (ADC_AVGCTRL)  */
#define   ADC_AVGCTRL_SAMPLENUM_4   (0x2u <<  0) /**< \brief (ADC_AVGCTRL)  */
#define   ADC_AVGCTRL_SAMPLENUM_8   (0x3u <<  0) /**< \brief (ADC_AVGCTRL)  */
#define   ADC_AVGCTRL_SAMPLENUM_16  (0x4u <<  0) /**< \brief (ADC_AVGCTRL)  */
#define   ADC_AVGCTRL_SAMPLENUM_32  (0x5u <<  0) /**< \brief (ADC_AVGCTRL)  */
#define   ADC_AVGCTRL_SAMPLENUM_64  (0x6u <<  0) /**< \brief (ADC_AVGCTRL)  */
#define   ADC_AVGCTRL_SAMPLENUM_128 (0x7u <<  0) /**< \brief (ADC_AVGCTRL)  */
#define   ADC_AVGCTRL_SAMPLENUM_256 (0x8u <<  0) /**< \brief (ADC_AVGCTRL)  */
#define   ADC_AVGCTRL_SAMPLENUM_512 (0x9u <<  0) /**< \brief (ADC_AVGCTRL)  */
#define   ADC_AVGCTRL_SAMPLENUM_1024 (0xAu <<  0) /**< \brief (ADC_AVGCTRL)  */
#define ADC_AVGCTRL_ADJRES_Pos      4            /**< \brief (ADC_AVGCTRL) Adjusting Result / Division Coefficient */
#define ADC_AVGCTRL_ADJRES_Msk      (0x7u << ADC_AVGCTRL_ADJRES_Pos)
#define ADC_AVGCTRL_ADJRES(value)   ((ADC_AVGCTRL_ADJRES_Msk & ((value) << ADC_AVGCTRL_ADJRES_Pos)))
#define ADC_AVGCTRL_MASK            0x7Fu        /**< \brief (ADC_AVGCTRL) MASK Register */

/* -------- ADC_SAMPCTRL : (ADC Offset: 0x03) (R/W  8) Sample Time Control Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  SAMPLEN:6;        /*!< bit:  0.. 5  Sampling Time Length               */
    uint8_t  :2;               /*!< bit:  6.. 7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} ADC_SAMPCTRL_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define ADC_SAMPCTRL_OFFSET         0x03         /**< \brief (ADC_SAMPCTRL offset) Sample Time Control Register */
#define ADC_SAMPCTRL_RESETVALUE     0x00         /**< \brief (ADC_SAMPCTRL reset_value) Sample Time Control Register */

#define ADC_SAMPCTRL_SAMPLEN_Pos    0            /**< \brief (ADC_SAMPCTRL) Sampling Time Length */
#define ADC_SAMPCTRL_SAMPLEN_Msk    (0x3Fu << ADC_SAMPCTRL_SAMPLEN_Pos)
#define ADC_SAMPCTRL_SAMPLEN(value) ((ADC_SAMPCTRL_SAMPLEN_Msk & ((value) << ADC_SAMPCTRL_SAMPLEN_Pos)))
#define ADC_SAMPCTRL_MASK           0x3Fu        /**< \brief (ADC_SAMPCTRL) MASK Register */

/* -------- ADC_CTRLB : (ADC Offset: 0x04) (R/W 16) Control Register B -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint16_t DIFFMODE:1;       /*!< bit:      0  Differential Mode                  */
    uint16_t LEFTADJ:1;        /*!< bit:      1  Left-Adjusted Result               */
    uint16_t FREERUN:1;        /*!< bit:      2  Free Running Mode                  */
    uint16_t CORREN:1;         /*!< bit:      3  Digital Correction Logic Enable    */
    uint16_t RESSEL:2;         /*!< bit:  4.. 5  Conversion Result Resolution       */
    uint16_t :2;               /*!< bit:  6.. 7  Reserved                           */
    uint16_t PRESCALER:3;      /*!< bit:  8..10  Prescaler Configuration            */
    uint16_t :5;               /*!< bit: 11..15  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint16_t reg;                /*!< Type      used for register access              */
} ADC_CTRLB_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define ADC_CTRLB_OFFSET            0x04         /**< \brief (ADC_CTRLB offset) Control Register B */
#define ADC_CTRLB_RESETVALUE        0x0000       /**< \brief (ADC_CTRLB reset_value) Control Register B */

#define ADC_CTRLB_DIFFMODE_Pos      0            /**< \brief (ADC_CTRLB) Differential Mode */
#define ADC_CTRLB_DIFFMODE          (0x1u << ADC_CTRLB_DIFFMODE_Pos)
#define ADC_CTRLB_LEFTADJ_Pos       1            /**< \brief (ADC_CTRLB) Left-Adjusted Result */
#define ADC_CTRLB_LEFTADJ           (0x1u << ADC_CTRLB_LEFTADJ_Pos)
#define ADC_CTRLB_FREERUN_Pos       2            /**< \brief (ADC_CTRLB) Free Running Mode */
#define ADC_CTRLB_FREERUN           (0x1u << ADC_CTRLB_FREERUN_Pos)
#define ADC_CTRLB_CORREN_Pos        3            /**< \brief (ADC_CTRLB) Digital Correction Logic Enable */
#define ADC_CTRLB_CORREN            (0x1u << ADC_CTRLB_CORREN_Pos)
#define ADC_CTRLB_RESSEL_Pos        4            /**< \brief (ADC_CTRLB) Conversion Result Resolution */
#define ADC_CTRLB_RESSEL_Msk        (0x3u << ADC_CTRLB_RESSEL_Pos)
#define ADC_CTRLB_RESSEL(value)     ((ADC_CTRLB_RESSEL_Msk & ((value) << ADC_CTRLB_RESSEL_Pos)))
#define   ADC_CTRLB_RESSEL_12BIT    (0x0u <<  4) /**< \brief (ADC_CTRLB)  */
#define   ADC_CTRLB_RESSEL_16BIT    (0x1u <<  4) /**< \brief (ADC_CTRLB)  */
#define   ADC_CTRLB_RESSEL_10BIT    (0x2u <<  4) /**< \brief (ADC_CTRLB)  */
#define   ADC_CTRLB_RESSEL_8BIT     (0x3u <<  4) /**< \brief (ADC_CTRLB)  */
#define ADC_CTRLB_PRESCALER_Pos     8            /**< \brief (ADC_CTRLB) Prescaler Configuration */
#define ADC_CTRLB_PRESCALER_Msk     (0x7u << ADC_CTRLB_PRESCALER_Pos)
#define ADC_CTRLB_PRESCALER(value)  ((ADC_CTRLB_PRESCALER_Msk & ((value) << ADC_CTRLB_PRESCALER_Pos)))
#define   ADC_CTRLB_PRESCALER_DIV4  (0x0u <<  8) /**< \brief (ADC_CTRLB)  */
#define   ADC_CTRLB_PRESCALER_DIV8  (0x1u <<  8) /**< \brief (ADC_CTRLB)  */
#define   ADC_CTRLB_PRESCALER_DIV16 (0x2u <<  8) /**< \brief (ADC_CTRLB)  */
#define   ADC_CTRLB_PRESCALER_DIV32 (0x3u <<  8) /**< \brief (ADC_CTRLB)  */
#define   ADC_CTRLB_PRESCALER_DIV64 (0x4u <<  8) /**< \brief (ADC_CTRLB)  */
#define   ADC_CTRLB_PRESCALER_DIV128 (0x5u <<  8) /**< \brief (ADC_CTRLB)  */
#define   ADC_CTRLB_PRESCALER_DIV256 (0x6u <<  8) /**< \brief (ADC_CTRLB)  */
#define   ADC_CTRLB_PRESCALER_DIV512 (0x7u <<  8) /**< \brief (ADC_CTRLB)  */
#define ADC_CTRLB_MASK              0x073Fu      /**< \brief (ADC_CTRLB) MASK Register */

/* -------- ADC_WINCTRL : (ADC Offset: 0x08) (R/W  8) Window Monitor Control Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  WINMODE:3;        /*!< bit:  0.. 2  Window Monitor Mode                */
    uint8_t  :5;               /*!< bit:  3.. 7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} ADC_WINCTRL_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define ADC_WINCTRL_OFFSET          0x08         /**< \brief (ADC_WINCTRL offset) Window Monitor Control Register */
#define ADC_WINCTRL_RESETVALUE      0x00         /**< \brief (ADC_WINCTRL reset_value) Window Monitor Control Register */

#define ADC_WINCTRL_WINMODE_Pos     0            /**< \brief (ADC_WINCTRL) Window Monitor Mode */
#define ADC_WINCTRL_WINMODE_Msk     (0x7u << ADC_WINCTRL_WINMODE_Pos)
#define ADC_WINCTRL_WINMODE(value)  ((ADC_WINCTRL_WINMODE_Msk & ((value) << ADC_WINCTRL_WINMODE_Pos)))
#define   ADC_WINCTRL_WINMODE_DISABLE (0x0u <<  0) /**< \brief (ADC_WINCTRL)  */
#define   ADC_WINCTRL_WINMODE_MODE1 (0x1u <<  0) /**< \brief (ADC_WINCTRL)  */
#define   ADC_WINCTRL_WINMODE_MODE2 (0x2u <<  0) /**< \brief (ADC_WINCTRL)  */
#define   ADC_WINCTRL_WINMODE_MODE3 (0x3u <<  0) /**< \brief (ADC_WINCTRL)  */
#define   ADC_WINCTRL_WINMODE_MODE4 (0x4u <<  0) /**< \brief (ADC_WINCTRL)  */
#define ADC_WINCTRL_MASK            0x07u        /**< \brief (ADC_WINCTRL) MASK Register */

/* -------- ADC_SWTRIG : (ADC Offset: 0x0C) (R/W  8) Control Register B -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  FLUSH:1;          /*!< bit:      0  ADC Flush                          */
    uint8_t  START:1;          /*!< bit:      1  Start ADC Conversion               */
    uint8_t  :6;               /*!< bit:  2.. 7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} ADC_SWTRIG_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define ADC_SWTRIG_OFFSET           0x0C         /**< \brief (ADC_SWTRIG offset) Control Register B */
#define ADC_SWTRIG_RESETVALUE       0x00         /**< \brief (ADC_SWTRIG reset_value) Control Register B */

#define ADC_SWTRIG_FLUSH_Pos        0            /**< \brief (ADC_SWTRIG) ADC Flush */
#define ADC_SWTRIG_FLUSH            (0x1u << ADC_SWTRIG_FLUSH_Pos)
#define ADC_SWTRIG_START_Pos        1            /**< \brief (ADC_SWTRIG) Start ADC Conversion */
#define ADC_SWTRIG_START            (0x1u << ADC_SWTRIG_START_Pos)
#define ADC_SWTRIG_MASK             0x03u        /**< \brief (ADC_SWTRIG) MASK Register */

/* -------- ADC_INPUTCTRL : (ADC Offset: 0x10) (R/W 32) Input Control Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t MUXPOS:5;         /*!< bit:  0.. 4  Positive Mux Input Selection       */
    uint32_t :3;               /*!< bit:  5.. 7  Reserved                           */
    uint32_t MUXNEG:5;         /*!< bit:  8..12  Negative Mux Input Selection       */
    uint32_t :3;               /*!< bit: 13..15  Reserved                           */
    uint32_t INPUTSCAN:4;      /*!< bit: 16..19  Number of Input Channels Included in Scan */
    uint32_t INPUTOFFSET:4;    /*!< bit: 20..23  Positive Mux Setting Offset        */
    uint32_t GAIN:4;           /*!< bit: 24..27  Gain Value                         */
    uint32_t :4;               /*!< bit: 28..31  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} ADC_INPUTCTRL_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define ADC_INPUTCTRL_OFFSET        0x10         /**< \brief (ADC_INPUTCTRL offset) Input Control Register */
#define ADC_INPUTCTRL_RESETVALUE    0x00000000   /**< \brief (ADC_INPUTCTRL reset_value) Input Control Register */

#define ADC_INPUTCTRL_MUXPOS_Pos    0            /**< \brief (ADC_INPUTCTRL) Positive Mux Input Selection */
#define ADC_INPUTCTRL_MUXPOS_Msk    (0x1Fu << ADC_INPUTCTRL_MUXPOS_Pos)
#define ADC_INPUTCTRL_MUXPOS(value) ((ADC_INPUTCTRL_MUXPOS_Msk & ((value) << ADC_INPUTCTRL_MUXPOS_Pos)))
#define   ADC_INPUTCTRL_MUXPOS_PIN0 (0x0u <<  0) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXPOS_PIN1 (0x1u <<  0) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXPOS_PIN2 (0x2u <<  0) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXPOS_PIN3 (0x3u <<  0) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXPOS_PIN4 (0x4u <<  0) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXPOS_PIN5 (0x5u <<  0) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXPOS_PIN6 (0x6u <<  0) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXPOS_PIN7 (0x7u <<  0) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXPOS_PIN8 (0x8u <<  0) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXPOS_PIN9 (0x9u <<  0) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXPOS_PIN10 (0xAu <<  0) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXPOS_PIN11 (0xBu <<  0) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXPOS_PIN12 (0xCu <<  0) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXPOS_PIN13 (0xDu <<  0) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXPOS_PIN14 (0xEu <<  0) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXPOS_PIN15 (0xFu <<  0) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXPOS_PIN16 (0x10u <<  0) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXPOS_PIN17 (0x11u <<  0) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXPOS_PIN18 (0x12u <<  0) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXPOS_PIN19 (0x13u <<  0) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXPOS_PIN20 (0x14u <<  0) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXPOS_PIN21 (0x15u <<  0) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXPOS_PIN22 (0x16u <<  0) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXPOS_PIN23 (0x17u <<  0) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXPOS_TEMP (0x18u <<  0) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXPOS_BANDGAP (0x19u <<  0) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXPOS_SCALEDCOREVCC (0x1Au <<  0) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXPOS_SCALEDIOVCC (0x1Bu <<  0) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXPOS_DAC  (0x1Cu <<  0) /**< \brief (ADC_INPUTCTRL)  */
#define ADC_INPUTCTRL_MUXNEG_Pos    8            /**< \brief (ADC_INPUTCTRL) Negative Mux Input Selection */
#define ADC_INPUTCTRL_MUXNEG_Msk    (0x1Fu << ADC_INPUTCTRL_MUXNEG_Pos)
#define ADC_INPUTCTRL_MUXNEG(value) ((ADC_INPUTCTRL_MUXNEG_Msk & ((value) << ADC_INPUTCTRL_MUXNEG_Pos)))
#define   ADC_INPUTCTRL_MUXNEG_PIN0 (0x0u <<  8) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXNEG_PIN1 (0x1u <<  8) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXNEG_PIN2 (0x2u <<  8) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXNEG_PIN3 (0x3u <<  8) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXNEG_PIN4 (0x4u <<  8) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXNEG_PIN5 (0x5u <<  8) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXNEG_PIN6 (0x6u <<  8) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXNEG_PIN7 (0x7u <<  8) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXNEG_PIN8 (0x8u <<  8) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXNEG_PIN9 (0x9u <<  8) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXNEG_PIN10 (0xAu <<  8) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXNEG_PIN11 (0xBu <<  8) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXNEG_PIN12 (0xCu <<  8) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXNEG_PIN13 (0xDu <<  8) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXNEG_PIN14 (0xEu <<  8) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXNEG_PIN15 (0xFu <<  8) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXNEG_PIN16 (0x10u <<  8) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXNEG_PIN17 (0x11u <<  8) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXNEG_PIN18 (0x12u <<  8) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXNEG_PIN19 (0x13u <<  8) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXNEG_PIN20 (0x14u <<  8) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXNEG_PIN21 (0x15u <<  8) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXNEG_PIN22 (0x16u <<  8) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXNEG_PIN23 (0x17u <<  8) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXNEG_GND  (0x18u <<  8) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_MUXNEG_IOGND (0x19u <<  8) /**< \brief (ADC_INPUTCTRL)  */
#define ADC_INPUTCTRL_INPUTSCAN_Pos 16           /**< \brief (ADC_INPUTCTRL) Number of Input Channels Included in Scan */
#define ADC_INPUTCTRL_INPUTSCAN_Msk (0xFu << ADC_INPUTCTRL_INPUTSCAN_Pos)
#define ADC_INPUTCTRL_INPUTSCAN(value) ((ADC_INPUTCTRL_INPUTSCAN_Msk & ((value) << ADC_INPUTCTRL_INPUTSCAN_Pos)))
#define ADC_INPUTCTRL_INPUTOFFSET_Pos 20           /**< \brief (ADC_INPUTCTRL) Positive Mux Setting Offset */
#define ADC_INPUTCTRL_INPUTOFFSET_Msk (0xFu << ADC_INPUTCTRL_INPUTOFFSET_Pos)
#define ADC_INPUTCTRL_INPUTOFFSET(value) ((ADC_INPUTCTRL_INPUTOFFSET_Msk & ((value) << ADC_INPUTCTRL_INPUTOFFSET_Pos)))
#define ADC_INPUTCTRL_GAIN_Pos      24           /**< \brief (ADC_INPUTCTRL) Gain Value */
#define ADC_INPUTCTRL_GAIN_Msk      (0xFu << ADC_INPUTCTRL_GAIN_Pos)
#define ADC_INPUTCTRL_GAIN(value)   ((ADC_INPUTCTRL_GAIN_Msk & ((value) << ADC_INPUTCTRL_GAIN_Pos)))
#define   ADC_INPUTCTRL_GAIN_1X     (0x0u << 24) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_GAIN_2X     (0x1u << 24) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_GAIN_4X     (0x2u << 24) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_GAIN_8X     (0x3u << 24) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_GAIN_16X    (0x4u << 24) /**< \brief (ADC_INPUTCTRL)  */
#define   ADC_INPUTCTRL_GAIN_DIV2   (0xFu << 24) /**< \brief (ADC_INPUTCTRL)  */
#define ADC_INPUTCTRL_MASK          0x0FFF1F1Fu  /**< \brief (ADC_INPUTCTRL) MASK Register */

/* -------- ADC_EVCTRL : (ADC Offset: 0x14) (R/W  8) Event Control Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  STARTEI:1;        /*!< bit:      0  Start Conversion Event In          */
    uint8_t  SYNCEI:1;         /*!< bit:      1  Sync Event In                      */
    uint8_t  :2;               /*!< bit:  2.. 3  Reserved                           */
    uint8_t  RESRDYEO:1;       /*!< bit:      4  Result Ready Event Out             */
    uint8_t  WINMONEO:1;       /*!< bit:      5  Window Monitor Event Out           */
    uint8_t  :2;               /*!< bit:  6.. 7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} ADC_EVCTRL_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define ADC_EVCTRL_OFFSET           0x14         /**< \brief (ADC_EVCTRL offset) Event Control Register */
#define ADC_EVCTRL_RESETVALUE       0x00         /**< \brief (ADC_EVCTRL reset_value) Event Control Register */

#define ADC_EVCTRL_STARTEI_Pos      0            /**< \brief (ADC_EVCTRL) Start Conversion Event In */
#define ADC_EVCTRL_STARTEI          (0x1u << ADC_EVCTRL_STARTEI_Pos)
#define ADC_EVCTRL_SYNCEI_Pos       1            /**< \brief (ADC_EVCTRL) Sync Event In */
#define ADC_EVCTRL_SYNCEI           (0x1u << ADC_EVCTRL_SYNCEI_Pos)
#define ADC_EVCTRL_RESRDYEO_Pos     4            /**< \brief (ADC_EVCTRL) Result Ready Event Out */
#define ADC_EVCTRL_RESRDYEO         (0x1u << ADC_EVCTRL_RESRDYEO_Pos)
#define ADC_EVCTRL_WINMONEO_Pos     5            /**< \brief (ADC_EVCTRL) Window Monitor Event Out */
#define ADC_EVCTRL_WINMONEO         (0x1u << ADC_EVCTRL_WINMONEO_Pos)
#define ADC_EVCTRL_MASK             0x33u        /**< \brief (ADC_EVCTRL) MASK Register */

/* -------- ADC_INTENCLR : (ADC Offset: 0x16) (R/W  8) Interrupt Enable Clear Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  RESRDY:1;         /*!< bit:      0  Result Ready Interrupt Disable     */
    uint8_t  OVERRUN:1;        /*!< bit:      1  Overrun Interrupt Disable          */
    uint8_t  WINMON:1;         /*!< bit:      2  Window Monitor Interrupt Disable   */
    uint8_t  SYNCRDY:1;        /*!< bit:      3  Synchronisation Ready Interrupt Disable */
    uint8_t  :4;               /*!< bit:  4.. 7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} ADC_INTENCLR_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define ADC_INTENCLR_OFFSET         0x16         /**< \brief (ADC_INTENCLR offset) Interrupt Enable Clear Register */
#define ADC_INTENCLR_RESETVALUE     0x00         /**< \brief (ADC_INTENCLR reset_value) Interrupt Enable Clear Register */

#define ADC_INTENCLR_RESRDY_Pos     0            /**< \brief (ADC_INTENCLR) Result Ready Interrupt Disable */
#define ADC_INTENCLR_RESRDY         (0x1u << ADC_INTENCLR_RESRDY_Pos)
#define ADC_INTENCLR_OVERRUN_Pos    1            /**< \brief (ADC_INTENCLR) Overrun Interrupt Disable */
#define ADC_INTENCLR_OVERRUN        (0x1u << ADC_INTENCLR_OVERRUN_Pos)
#define ADC_INTENCLR_WINMON_Pos     2            /**< \brief (ADC_INTENCLR) Window Monitor Interrupt Disable */
#define ADC_INTENCLR_WINMON         (0x1u << ADC_INTENCLR_WINMON_Pos)
#define ADC_INTENCLR_SYNCRDY_Pos    3            /**< \brief (ADC_INTENCLR) Synchronisation Ready Interrupt Disable */
#define ADC_INTENCLR_SYNCRDY        (0x1u << ADC_INTENCLR_SYNCRDY_Pos)
#define ADC_INTENCLR_MASK           0x0Fu        /**< \brief (ADC_INTENCLR) MASK Register */

/* -------- ADC_INTENSET : (ADC Offset: 0x17) (R/W  8) Interrupt Enable Set Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  RESRDY:1;         /*!< bit:      0  Result Ready Interrupt Enable      */
    uint8_t  OVERRUN:1;        /*!< bit:      1  Overrun Interrupt Enable           */
    uint8_t  WINMON:1;         /*!< bit:      2  Window Monitor Interrupt Enable    */
    uint8_t  SYNCRDY:1;        /*!< bit:      3  Synchronisation Ready Interrupt Enable */
    uint8_t  :4;               /*!< bit:  4.. 7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} ADC_INTENSET_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define ADC_INTENSET_OFFSET         0x17         /**< \brief (ADC_INTENSET offset) Interrupt Enable Set Register */
#define ADC_INTENSET_RESETVALUE     0x00         /**< \brief (ADC_INTENSET reset_value) Interrupt Enable Set Register */

#define ADC_INTENSET_RESRDY_Pos     0            /**< \brief (ADC_INTENSET) Result Ready Interrupt Enable */
#define ADC_INTENSET_RESRDY         (0x1u << ADC_INTENSET_RESRDY_Pos)
#define ADC_INTENSET_OVERRUN_Pos    1            /**< \brief (ADC_INTENSET) Overrun Interrupt Enable */
#define ADC_INTENSET_OVERRUN        (0x1u << ADC_INTENSET_OVERRUN_Pos)
#define ADC_INTENSET_WINMON_Pos     2            /**< \brief (ADC_INTENSET) Window Monitor Interrupt Enable */
#define ADC_INTENSET_WINMON         (0x1u << ADC_INTENSET_WINMON_Pos)
#define ADC_INTENSET_SYNCRDY_Pos    3            /**< \brief (ADC_INTENSET) Synchronisation Ready Interrupt Enable */
#define ADC_INTENSET_SYNCRDY        (0x1u << ADC_INTENSET_SYNCRDY_Pos)
#define ADC_INTENSET_MASK           0x0Fu        /**< \brief (ADC_INTENSET) MASK Register */

/* -------- ADC_INTFLAG : (ADC Offset: 0x18) (R/W  8) Interrupt Flag Status and Clear Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  RESRDY:1;         /*!< bit:      0  Result Ready Interrupt Flag        */
    uint8_t  OVERRUN:1;        /*!< bit:      1  Overrun Interrupt Flag             */
    uint8_t  WINMON:1;         /*!< bit:      2  Window Monitor Interrupt Flag      */
    uint8_t  SYNCRDY:1;        /*!< bit:      3  Synchronisation Ready Interrupt Flag */
    uint8_t  :4;               /*!< bit:  4.. 7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} ADC_INTFLAG_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define ADC_INTFLAG_OFFSET          0x18         /**< \brief (ADC_INTFLAG offset) Interrupt Flag Status and Clear Register */
#define ADC_INTFLAG_RESETVALUE      0x00         /**< \brief (ADC_INTFLAG reset_value) Interrupt Flag Status and Clear Register */

#define ADC_INTFLAG_RESRDY_Pos      0            /**< \brief (ADC_INTFLAG) Result Ready Interrupt Flag */
#define ADC_INTFLAG_RESRDY          (0x1u << ADC_INTFLAG_RESRDY_Pos)
#define ADC_INTFLAG_OVERRUN_Pos     1            /**< \brief (ADC_INTFLAG) Overrun Interrupt Flag */
#define ADC_INTFLAG_OVERRUN         (0x1u << ADC_INTFLAG_OVERRUN_Pos)
#define ADC_INTFLAG_WINMON_Pos      2            /**< \brief (ADC_INTFLAG) Window Monitor Interrupt Flag */
#define ADC_INTFLAG_WINMON          (0x1u << ADC_INTFLAG_WINMON_Pos)
#define ADC_INTFLAG_SYNCRDY_Pos     3            /**< \brief (ADC_INTFLAG) Synchronisation Ready Interrupt Flag */
#define ADC_INTFLAG_SYNCRDY         (0x1u << ADC_INTFLAG_SYNCRDY_Pos)
#define ADC_INTFLAG_MASK            0x0Fu        /**< \brief (ADC_INTFLAG) MASK Register */

/* -------- ADC_STATUS : (ADC Offset: 0x19) (R/   8) Status Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  :7;               /*!< bit:  0.. 6  Reserved                           */
    uint8_t  SYNCBUSY:1;       /*!< bit:      7  Synchronisation Busy Status        */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} ADC_STATUS_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define ADC_STATUS_OFFSET           0x19         /**< \brief (ADC_STATUS offset) Status Register */
#define ADC_STATUS_RESETVALUE       0x00         /**< \brief (ADC_STATUS reset_value) Status Register */

#define ADC_STATUS_SYNCBUSY_Pos     7            /**< \brief (ADC_STATUS) Synchronisation Busy Status */
#define ADC_STATUS_SYNCBUSY         (0x1u << ADC_STATUS_SYNCBUSY_Pos)
#define ADC_STATUS_MASK             0x80u        /**< \brief (ADC_STATUS) MASK Register */

/* -------- ADC_RESULT : (ADC Offset: 0x1A) (R/  16) Result Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint16_t RESULT:16;        /*!< bit:  0..15  Result Value                       */
  } bit;                       /*!< Structure used for bit  access                  */
  uint16_t reg;                /*!< Type      used for register access              */
} ADC_RESULT_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define ADC_RESULT_OFFSET           0x1A         /**< \brief (ADC_RESULT offset) Result Register */
#define ADC_RESULT_RESETVALUE       0x0000       /**< \brief (ADC_RESULT reset_value) Result Register */

#define ADC_RESULT_RESULT_Pos       0            /**< \brief (ADC_RESULT) Result Value */
#define ADC_RESULT_RESULT_Msk       (0xFFFFu << ADC_RESULT_RESULT_Pos)
#define ADC_RESULT_RESULT(value)    ((ADC_RESULT_RESULT_Msk & ((value) << ADC_RESULT_RESULT_Pos)))
#define ADC_RESULT_MASK             0xFFFFu      /**< \brief (ADC_RESULT) MASK Register */

/* -------- ADC_WINLT : (ADC Offset: 0x1C) (R/W 16) Window Monitor Lower Threshold Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint16_t WINLT:16;         /*!< bit:  0..15  Window Lower Threshold             */
  } bit;                       /*!< Structure used for bit  access                  */
  uint16_t reg;                /*!< Type      used for register access              */
} ADC_WINLT_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define ADC_WINLT_OFFSET            0x1C         /**< \brief (ADC_WINLT offset) Window Monitor Lower Threshold Register */
#define ADC_WINLT_RESETVALUE        0x0000       /**< \brief (ADC_WINLT reset_value) Window Monitor Lower Threshold Register */

#define ADC_WINLT_WINLT_Pos         0            /**< \brief (ADC_WINLT) Window Lower Threshold */
#define ADC_WINLT_WINLT_Msk         (0xFFFFu << ADC_WINLT_WINLT_Pos)
#define ADC_WINLT_WINLT(value)      ((ADC_WINLT_WINLT_Msk & ((value) << ADC_WINLT_WINLT_Pos)))
#define ADC_WINLT_MASK              0xFFFFu      /**< \brief (ADC_WINLT) MASK Register */

/* -------- ADC_WINUT : (ADC Offset: 0x20) (R/W 16) Window Monitor Upper Threshold Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint16_t WINUT:16;         /*!< bit:  0..15  Window Upper Threshold             */
  } bit;                       /*!< Structure used for bit  access                  */
  uint16_t reg;                /*!< Type      used for register access              */
} ADC_WINUT_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define ADC_WINUT_OFFSET            0x20         /**< \brief (ADC_WINUT offset) Window Monitor Upper Threshold Register */
#define ADC_WINUT_RESETVALUE        0x0000       /**< \brief (ADC_WINUT reset_value) Window Monitor Upper Threshold Register */

#define ADC_WINUT_WINUT_Pos         0            /**< \brief (ADC_WINUT) Window Upper Threshold */
#define ADC_WINUT_WINUT_Msk         (0xFFFFu << ADC_WINUT_WINUT_Pos)
#define ADC_WINUT_WINUT(value)      ((ADC_WINUT_WINUT_Msk & ((value) << ADC_WINUT_WINUT_Pos)))
#define ADC_WINUT_MASK              0xFFFFu      /**< \brief (ADC_WINUT) MASK Register */

/* -------- ADC_GAINCORR : (ADC Offset: 0x24) (R/W 16) Gain Correction Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint16_t GAINCORR:12;      /*!< bit:  0..11  Gain Correction Value              */
    uint16_t :4;               /*!< bit: 12..15  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint16_t reg;                /*!< Type      used for register access              */
} ADC_GAINCORR_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define ADC_GAINCORR_OFFSET         0x24         /**< \brief (ADC_GAINCORR offset) Gain Correction Register */
#define ADC_GAINCORR_RESETVALUE     0x0000       /**< \brief (ADC_GAINCORR reset_value) Gain Correction Register */

#define ADC_GAINCORR_GAINCORR_Pos   0            /**< \brief (ADC_GAINCORR) Gain Correction Value */
#define ADC_GAINCORR_GAINCORR_Msk   (0xFFFu << ADC_GAINCORR_GAINCORR_Pos)
#define ADC_GAINCORR_GAINCORR(value) ((ADC_GAINCORR_GAINCORR_Msk & ((value) << ADC_GAINCORR_GAINCORR_Pos)))
#define ADC_GAINCORR_MASK           0x0FFFu      /**< \brief (ADC_GAINCORR) MASK Register */

/* -------- ADC_OFFSETCORR : (ADC Offset: 0x26) (R/W 16) Offset Correction Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint16_t OFFSETCORR:12;    /*!< bit:  0..11  Offset Correction Value            */
    uint16_t :4;               /*!< bit: 12..15  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint16_t reg;                /*!< Type      used for register access              */
} ADC_OFFSETCORR_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define ADC_OFFSETCORR_OFFSET       0x26         /**< \brief (ADC_OFFSETCORR offset) Offset Correction Register */
#define ADC_OFFSETCORR_RESETVALUE   0x0000       /**< \brief (ADC_OFFSETCORR reset_value) Offset Correction Register */

#define ADC_OFFSETCORR_OFFSETCORR_Pos 0            /**< \brief (ADC_OFFSETCORR) Offset Correction Value */
#define ADC_OFFSETCORR_OFFSETCORR_Msk (0xFFFu << ADC_OFFSETCORR_OFFSETCORR_Pos)
#define ADC_OFFSETCORR_OFFSETCORR(value) ((ADC_OFFSETCORR_OFFSETCORR_Msk & ((value) << ADC_OFFSETCORR_OFFSETCORR_Pos)))
#define ADC_OFFSETCORR_MASK         0x0FFFu      /**< \brief (ADC_OFFSETCORR) MASK Register */

/* -------- ADC_CALIB : (ADC Offset: 0x28) (R/W 16) Calibration Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint16_t LINEARITY_CAL:8;  /*!< bit:  0.. 7  Linearity Calibration              */
    uint16_t BIAS_CAL:3;       /*!< bit:  8..10  Bias  Configuration                */
    uint16_t :5;               /*!< bit: 11..15  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint16_t reg;                /*!< Type      used for register access              */
} ADC_CALIB_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define ADC_CALIB_OFFSET            0x28         /**< \brief (ADC_CALIB offset) Calibration Register */
#define ADC_CALIB_RESETVALUE        0x0000       /**< \brief (ADC_CALIB reset_value) Calibration Register */

#define ADC_CALIB_LINEARITY_CAL_Pos 0            /**< \brief (ADC_CALIB) Linearity Calibration */
#define ADC_CALIB_LINEARITY_CAL_Msk (0xFFu << ADC_CALIB_LINEARITY_CAL_Pos)
#define ADC_CALIB_LINEARITY_CAL(value) ((ADC_CALIB_LINEARITY_CAL_Msk & ((value) << ADC_CALIB_LINEARITY_CAL_Pos)))
#define ADC_CALIB_BIAS_CAL_Pos      8            /**< \brief (ADC_CALIB) Bias  Configuration */
#define ADC_CALIB_BIAS_CAL_Msk      (0x7u << ADC_CALIB_BIAS_CAL_Pos)
#define ADC_CALIB_BIAS_CAL(value)   ((ADC_CALIB_BIAS_CAL_Msk & ((value) << ADC_CALIB_BIAS_CAL_Pos)))
#define ADC_CALIB_MASK              0x07FFu      /**< \brief (ADC_CALIB) MASK Register */

/* -------- ADC_DBGCTRL : (ADC Offset: 0x2A) (R/W  8) Debug Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  DBGRUN:1;         /*!< bit:      0  Debug Run                          */
    uint8_t  :7;               /*!< bit:  1.. 7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} ADC_DBGCTRL_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define ADC_DBGCTRL_OFFSET          0x2A         /**< \brief (ADC_DBGCTRL offset) Debug Register */
#define ADC_DBGCTRL_RESETVALUE      0x00         /**< \brief (ADC_DBGCTRL reset_value) Debug Register */

#define ADC_DBGCTRL_DBGRUN_Pos      0            /**< \brief (ADC_DBGCTRL) Debug Run */
#define ADC_DBGCTRL_DBGRUN          (0x1u << ADC_DBGCTRL_DBGRUN_Pos)
#define ADC_DBGCTRL_MASK            0x01u        /**< \brief (ADC_DBGCTRL) MASK Register */

/* -------- ADC_TEST : (ADC Offset: 0x2B) (R/W  8) Test Modes Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  TEST_EN:1;        /*!< bit:      0  Enable Test Mode                   */
    uint8_t  REFPAD_EN:1;      /*!< bit:      1  Connect Vrefp/n to aio33testp/n    */
    uint8_t  REFINT_DIS:1;     /*!< bit:      2  Disable Internal Reference         */
    uint8_t  :5;               /*!< bit:  3.. 7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} ADC_TEST_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define ADC_TEST_OFFSET             0x2B         /**< \brief (ADC_TEST offset) Test Modes Register */
#define ADC_TEST_RESETVALUE         0x00         /**< \brief (ADC_TEST reset_value) Test Modes Register */

#define ADC_TEST_TEST_EN_Pos        0            /**< \brief (ADC_TEST) Enable Test Mode */
#define ADC_TEST_TEST_EN            (0x1u << ADC_TEST_TEST_EN_Pos)
#define ADC_TEST_REFPAD_EN_Pos      1            /**< \brief (ADC_TEST) Connect Vrefp/n to aio33testp/n */
#define ADC_TEST_REFPAD_EN          (0x1u << ADC_TEST_REFPAD_EN_Pos)
#define ADC_TEST_REFINT_DIS_Pos     2            /**< \brief (ADC_TEST) Disable Internal Reference */
#define ADC_TEST_REFINT_DIS         (0x1u << ADC_TEST_REFINT_DIS_Pos)
#define ADC_TEST_MASK               0x07u        /**< \brief (ADC_TEST) MASK Register */

/* -------- ADC_TESTRESULT : (ADC Offset: 0x2C) (R/W 32) Test Result Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t TESTRESULT:24;    /*!< bit:  0..23  Result Directly from ADC Hard Block */
    uint32_t :8;               /*!< bit: 24..31  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} ADC_TESTRESULT_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define ADC_TESTRESULT_OFFSET       0x2C         /**< \brief (ADC_TESTRESULT offset) Test Result Register */
#define ADC_TESTRESULT_RESETVALUE   0x00000000   /**< \brief (ADC_TESTRESULT reset_value) Test Result Register */

#define ADC_TESTRESULT_TESTRESULT_Pos 0            /**< \brief (ADC_TESTRESULT) Result Directly from ADC Hard Block */
#define ADC_TESTRESULT_TESTRESULT_Msk (0xFFFFFFu << ADC_TESTRESULT_TESTRESULT_Pos)
#define ADC_TESTRESULT_TESTRESULT(value) ((ADC_TESTRESULT_TESTRESULT_Msk & ((value) << ADC_TESTRESULT_TESTRESULT_Pos)))
#define ADC_TESTRESULT_MASK         0x00FFFFFFu  /**< \brief (ADC_TESTRESULT) MASK Register */

/* -------- ADC_DCFG : (ADC Offset: 0x30) (R/W  8) Device Configuration -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  CMPDELAY:1;       /*!< bit:      0  Comparator Delay Control           */
    uint8_t  BOOSTEN:1;        /*!< bit:      1  Enable the SR Booster in the Op Amp */
    uint8_t  VCMPULSE:1;       /*!< bit:      2  Enable VCM Pulse                   */
    uint8_t  BIAS_OPA:1;       /*!< bit:      3  Select PTAT Biasing for OPA        */
    uint8_t  :4;               /*!< bit:  4.. 7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} ADC_DCFG_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define ADC_DCFG_OFFSET             0x30         /**< \brief (ADC_DCFG offset) Device Configuration */
#define ADC_DCFG_RESETVALUE         0x00         /**< \brief (ADC_DCFG reset_value) Device Configuration */

#define ADC_DCFG_CMPDELAY_Pos       0            /**< \brief (ADC_DCFG) Comparator Delay Control */
#define ADC_DCFG_CMPDELAY           (0x1u << ADC_DCFG_CMPDELAY_Pos)
#define ADC_DCFG_BOOSTEN_Pos        1            /**< \brief (ADC_DCFG) Enable the SR Booster in the Op Amp */
#define ADC_DCFG_BOOSTEN            (0x1u << ADC_DCFG_BOOSTEN_Pos)
#define ADC_DCFG_VCMPULSE_Pos       2            /**< \brief (ADC_DCFG) Enable VCM Pulse */
#define ADC_DCFG_VCMPULSE           (0x1u << ADC_DCFG_VCMPULSE_Pos)
#define ADC_DCFG_BIAS_OPA_Pos       3            /**< \brief (ADC_DCFG) Select PTAT Biasing for OPA */
#define ADC_DCFG_BIAS_OPA           (0x1u << ADC_DCFG_BIAS_OPA_Pos)
#define ADC_DCFG_MASK               0x0Fu        /**< \brief (ADC_DCFG) MASK Register */

/** \brief ADC hardware registers */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef struct {
  __IO ADC_CTRLA_Type            CTRLA;       /**< \brief Offset: 0x00 (R/W  8) Control Register A */
  __IO ADC_REFCTRL_Type          REFCTRL;     /**< \brief Offset: 0x01 (R/W  8) Reference Control Register */
  __IO ADC_AVGCTRL_Type          AVGCTRL;     /**< \brief Offset: 0x02 (R/W  8) Average Control Register */
  __IO ADC_SAMPCTRL_Type         SAMPCTRL;    /**< \brief Offset: 0x03 (R/W  8) Sample Time Control Register */
  __IO ADC_CTRLB_Type            CTRLB;       /**< \brief Offset: 0x04 (R/W 16) Control Register B */
       RoReg8                    Reserved1[0x2];
  __IO ADC_WINCTRL_Type          WINCTRL;     /**< \brief Offset: 0x08 (R/W  8) Window Monitor Control Register */
       RoReg8                    Reserved2[0x3];
  __IO ADC_SWTRIG_Type           SWTRIG;      /**< \brief Offset: 0x0C (R/W  8) Control Register B */
       RoReg8                    Reserved3[0x3];
  __IO ADC_INPUTCTRL_Type        INPUTCTRL;   /**< \brief Offset: 0x10 (R/W 32) Input Control Register */
  __IO ADC_EVCTRL_Type           EVCTRL;      /**< \brief Offset: 0x14 (R/W  8) Event Control Register */
       RoReg8                    Reserved4[0x1];
  __IO ADC_INTENCLR_Type         INTENCLR;    /**< \brief Offset: 0x16 (R/W  8) Interrupt Enable Clear Register */
  __IO ADC_INTENSET_Type         INTENSET;    /**< \brief Offset: 0x17 (R/W  8) Interrupt Enable Set Register */
  __IO ADC_INTFLAG_Type          INTFLAG;     /**< \brief Offset: 0x18 (R/W  8) Interrupt Flag Status and Clear Register */
  __I  ADC_STATUS_Type           STATUS;      /**< \brief Offset: 0x19 (R/   8) Status Register */
  __I  ADC_RESULT_Type           RESULT;      /**< \brief Offset: 0x1A (R/  16) Result Register */
  __IO ADC_WINLT_Type            WINLT;       /**< \brief Offset: 0x1C (R/W 16) Window Monitor Lower Threshold Register */
       RoReg8                    Reserved5[0x2];
  __IO ADC_WINUT_Type            WINUT;       /**< \brief Offset: 0x20 (R/W 16) Window Monitor Upper Threshold Register */
       RoReg8                    Reserved6[0x2];
  __IO ADC_GAINCORR_Type         GAINCORR;    /**< \brief Offset: 0x24 (R/W 16) Gain Correction Register */
  __IO ADC_OFFSETCORR_Type       OFFSETCORR;  /**< \brief Offset: 0x26 (R/W 16) Offset Correction Register */
  __IO ADC_CALIB_Type            CALIB;       /**< \brief Offset: 0x28 (R/W 16) Calibration Register */
  __IO ADC_DBGCTRL_Type          DBGCTRL;     /**< \brief Offset: 0x2A (R/W  8) Debug Register */
  __IO ADC_TEST_Type             TEST;        /**< \brief Offset: 0x2B (R/W  8) Test Modes Register */
  __IO ADC_TESTRESULT_Type       TESTRESULT;  /**< \brief Offset: 0x2C (R/W 32) Test Result Register */
  __IO ADC_DCFG_Type             DCFG;        /**< \brief Offset: 0x30 (R/W  8) Device Configuration */
} Adc;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

/*@}*/

#endif /* _SAMD20_ADC_COMPONENT_ */
