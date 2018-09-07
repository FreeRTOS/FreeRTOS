/**
 * \file
 *
 * \brief Component description for EVSYS
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

#ifndef _SAMD20_EVSYS_COMPONENT_
#define _SAMD20_EVSYS_COMPONENT_

/* ========================================================================== */
/**  SOFTWARE API DEFINITION FOR EVSYS */
/* ========================================================================== */
/** \addtogroup SAMD20_EVSYS Event System Interface */
/*@{*/

#define REV_EVSYS                   0x100

/* -------- EVSYS_CTRL : (EVSYS Offset: 0x00) ( /W  8) Control Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  SWRST:1;          /*!< bit:      0  Software Reset                     */
    uint8_t  :3;               /*!< bit:  1.. 3  Reserved                           */
    uint8_t  GCLKREQ:1;        /*!< bit:      4  Generic Clock Request              */
    uint8_t  :3;               /*!< bit:  5.. 7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} EVSYS_CTRL_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define EVSYS_CTRL_OFFSET           0x00         /**< \brief (EVSYS_CTRL offset) Control Register */
#define EVSYS_CTRL_RESETVALUE       0x00         /**< \brief (EVSYS_CTRL reset_value) Control Register */

#define EVSYS_CTRL_SWRST_Pos        0            /**< \brief (EVSYS_CTRL) Software Reset */
#define EVSYS_CTRL_SWRST            (0x1u << EVSYS_CTRL_SWRST_Pos)
#define EVSYS_CTRL_GCLKREQ_Pos      4            /**< \brief (EVSYS_CTRL) Generic Clock Request */
#define EVSYS_CTRL_GCLKREQ          (0x1u << EVSYS_CTRL_GCLKREQ_Pos)
#define EVSYS_CTRL_MASK             0x11u        /**< \brief (EVSYS_CTRL) MASK Register */

/* -------- EVSYS_CHANNEL : (EVSYS Offset: 0x04) (R/W 32) Channel Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t CHANNEL:8;        /*!< bit:  0.. 7  Channel Selection                  */
    uint32_t SWEVT:1;          /*!< bit:      8  Software Event                     */
    uint32_t :7;               /*!< bit:  9..15  Reserved                           */
    uint32_t EVGEN:8;          /*!< bit: 16..23  Event Generator Selection          */
    uint32_t PATH:2;           /*!< bit: 24..25  Path Selection                     */
    uint32_t EDGSEL:2;         /*!< bit: 26..27  Edge Selection                     */
    uint32_t :4;               /*!< bit: 28..31  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} EVSYS_CHANNEL_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define EVSYS_CHANNEL_OFFSET        0x04         /**< \brief (EVSYS_CHANNEL offset) Channel Register */
#define EVSYS_CHANNEL_RESETVALUE    0x00000000   /**< \brief (EVSYS_CHANNEL reset_value) Channel Register */

#define EVSYS_CHANNEL_CHANNEL_Pos   0            /**< \brief (EVSYS_CHANNEL) Channel Selection */
#define EVSYS_CHANNEL_CHANNEL_Msk   (0xFFu << EVSYS_CHANNEL_CHANNEL_Pos)
#define EVSYS_CHANNEL_CHANNEL(value) ((EVSYS_CHANNEL_CHANNEL_Msk & ((value) << EVSYS_CHANNEL_CHANNEL_Pos)))
#define EVSYS_CHANNEL_SWEVT_Pos     8            /**< \brief (EVSYS_CHANNEL) Software Event */
#define EVSYS_CHANNEL_SWEVT         (0x1u << EVSYS_CHANNEL_SWEVT_Pos)
#define EVSYS_CHANNEL_EVGEN_Pos     16           /**< \brief (EVSYS_CHANNEL) Event Generator Selection */
#define EVSYS_CHANNEL_EVGEN_Msk     (0xFFu << EVSYS_CHANNEL_EVGEN_Pos)
#define EVSYS_CHANNEL_EVGEN(value)  ((EVSYS_CHANNEL_EVGEN_Msk & ((value) << EVSYS_CHANNEL_EVGEN_Pos)))
#define EVSYS_CHANNEL_PATH_Pos      24           /**< \brief (EVSYS_CHANNEL) Path Selection */
#define EVSYS_CHANNEL_PATH_Msk      (0x3u << EVSYS_CHANNEL_PATH_Pos)
#define EVSYS_CHANNEL_PATH(value)   ((EVSYS_CHANNEL_PATH_Msk & ((value) << EVSYS_CHANNEL_PATH_Pos)))
#define   EVSYS_CHANNEL_PATH_SYNCHRONOUS (0x0u << 24) /**< \brief (EVSYS_CHANNEL) Synchronous path */
#define   EVSYS_CHANNEL_PATH_RESYNCHRONIZED (0x1u << 24) /**< \brief (EVSYS_CHANNEL) Resynchronized path */
#define   EVSYS_CHANNEL_PATH_ASYNCHRONOUS (0x2u << 24) /**< \brief (EVSYS_CHANNEL) Asynchronous path */
#define EVSYS_CHANNEL_EDGSEL_Pos    26           /**< \brief (EVSYS_CHANNEL) Edge Selection */
#define EVSYS_CHANNEL_EDGSEL_Msk    (0x3u << EVSYS_CHANNEL_EDGSEL_Pos)
#define EVSYS_CHANNEL_EDGSEL(value) ((EVSYS_CHANNEL_EDGSEL_Msk & ((value) << EVSYS_CHANNEL_EDGSEL_Pos)))
#define   EVSYS_CHANNEL_EDGSEL_NO_EVT_OUTPUT (0x0u << 26) /**< \brief (EVSYS_CHANNEL) No Event Output */
#define   EVSYS_CHANNEL_EDGSEL_RISING_EDGE (0x1u << 26) /**< \brief (EVSYS_CHANNEL) Event detection on the rising edge */
#define   EVSYS_CHANNEL_EDGSEL_FALLING_EDGE (0x2u << 26) /**< \brief (EVSYS_CHANNEL) Event detection on the falling edge */
#define   EVSYS_CHANNEL_EDGSEL_BOTH_EDGE (0x3u << 26) /**< \brief (EVSYS_CHANNEL) Event detection on both rising/falling edge */
#define EVSYS_CHANNEL_MASK          0x0FFF01FFu  /**< \brief (EVSYS_CHANNEL) MASK Register */

/* -------- EVSYS_USER : (EVSYS Offset: 0x08) (R/W 16) User Mux Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint16_t USER:8;           /*!< bit:  0.. 7  User Mux Selection                 */
    uint16_t CHANNEL:8;        /*!< bit:  8..15  Channel Event Selection            */
  } bit;                       /*!< Structure used for bit  access                  */
  uint16_t reg;                /*!< Type      used for register access              */
} EVSYS_USER_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define EVSYS_USER_OFFSET           0x08         /**< \brief (EVSYS_USER offset) User Mux Register */
#define EVSYS_USER_RESETVALUE       0x0000       /**< \brief (EVSYS_USER reset_value) User Mux Register */

#define EVSYS_USER_USER_Pos         0            /**< \brief (EVSYS_USER) User Mux Selection */
#define EVSYS_USER_USER_Msk         (0xFFu << EVSYS_USER_USER_Pos)
#define EVSYS_USER_USER(value)      ((EVSYS_USER_USER_Msk & ((value) << EVSYS_USER_USER_Pos)))
#define EVSYS_USER_CHANNEL_Pos      8            /**< \brief (EVSYS_USER) Channel Event Selection */
#define EVSYS_USER_CHANNEL_Msk      (0xFFu << EVSYS_USER_CHANNEL_Pos)
#define EVSYS_USER_CHANNEL(value)   ((EVSYS_USER_CHANNEL_Msk & ((value) << EVSYS_USER_CHANNEL_Pos)))
#define EVSYS_USER_MASK             0xFFFFu      /**< \brief (EVSYS_USER) MASK Register */

/* -------- EVSYS_CHSTATUS : (EVSYS Offset: 0x0C) (R/  32) Channel Status Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t USRRDY0:8;        /*!< bit:  0.. 7  User Ready for Channels 0 to 7 (modulo 16) */
    uint32_t CHBUSY0:8;        /*!< bit:  8..15  Channels Busy 0 to 7 (modulo 16)   */
    uint32_t USRRDY1:8;        /*!< bit: 16..23  User Ready for Channels 8 to 15 (modulo 16) */
    uint32_t CHBUSY1:8;        /*!< bit: 24..31  Channels Busy 8 to 15 (modulo 16)  */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} EVSYS_CHSTATUS_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define EVSYS_CHSTATUS_OFFSET       0x0C         /**< \brief (EVSYS_CHSTATUS offset) Channel Status Register */
#define EVSYS_CHSTATUS_RESETVALUE   0x00000000   /**< \brief (EVSYS_CHSTATUS reset_value) Channel Status Register */

#define EVSYS_CHSTATUS_USRRDY0_Pos  0            /**< \brief (EVSYS_CHSTATUS) User Ready for Channels 0 to 7 (modulo 16) */
#define EVSYS_CHSTATUS_USRRDY0_Msk  (0xFFu << EVSYS_CHSTATUS_USRRDY0_Pos)
#define EVSYS_CHSTATUS_USRRDY0(value) ((EVSYS_CHSTATUS_USRRDY0_Msk & ((value) << EVSYS_CHSTATUS_USRRDY0_Pos)))
#define   EVSYS_CHSTATUS_USRRDY0_USRRDY0 (0x1u <<  0) /**< \brief (EVSYS_CHSTATUS) User ready for Channel 0 */
#define   EVSYS_CHSTATUS_USRRDY0_USRRDY1 (0x2u <<  0) /**< \brief (EVSYS_CHSTATUS) User ready for Channel 1 */
#define   EVSYS_CHSTATUS_USRRDY0_USRRDY2 (0x4u <<  0) /**< \brief (EVSYS_CHSTATUS) User ready for Channel 2 */
#define   EVSYS_CHSTATUS_USRRDY0_USRRDY3 (0x8u <<  0) /**< \brief (EVSYS_CHSTATUS) User ready for Channel 3 */
#define   EVSYS_CHSTATUS_USRRDY0_USRRDY4 (0x10u <<  0) /**< \brief (EVSYS_CHSTATUS) User ready for Channel 4 */
#define   EVSYS_CHSTATUS_USRRDY0_USRRDY5 (0x20u <<  0) /**< \brief (EVSYS_CHSTATUS) User ready for Channel 5 */
#define   EVSYS_CHSTATUS_USRRDY0_USRRDY6 (0x40u <<  0) /**< \brief (EVSYS_CHSTATUS) User ready for Channel 6 */
#define   EVSYS_CHSTATUS_USRRDY0_USRRDY7 (0x80u <<  0) /**< \brief (EVSYS_CHSTATUS) User ready for Channel 7 */
#define EVSYS_CHSTATUS_CHBUSY0_Pos  8            /**< \brief (EVSYS_CHSTATUS) Channels Busy 0 to 7 (modulo 16) */
#define EVSYS_CHSTATUS_CHBUSY0_Msk  (0xFFu << EVSYS_CHSTATUS_CHBUSY0_Pos)
#define EVSYS_CHSTATUS_CHBUSY0(value) ((EVSYS_CHSTATUS_CHBUSY0_Msk & ((value) << EVSYS_CHSTATUS_CHBUSY0_Pos)))
#define   EVSYS_CHSTATUS_CHBUSY0_CHBUSY0 (0x1u <<  8) /**< \brief (EVSYS_CHSTATUS) Channel 0 busy */
#define   EVSYS_CHSTATUS_CHBUSY0_CHBUSY1 (0x2u <<  8) /**< \brief (EVSYS_CHSTATUS) Channel 1 busy */
#define   EVSYS_CHSTATUS_CHBUSY0_CHBUSY2 (0x4u <<  8) /**< \brief (EVSYS_CHSTATUS) Channel 2 busy */
#define   EVSYS_CHSTATUS_CHBUSY0_CHBUSY3 (0x8u <<  8) /**< \brief (EVSYS_CHSTATUS) Channel 3 busy */
#define   EVSYS_CHSTATUS_CHBUSY0_CHBUSY4 (0x10u <<  8) /**< \brief (EVSYS_CHSTATUS) Channel 4 busy */
#define   EVSYS_CHSTATUS_CHBUSY0_CHBUSY5 (0x20u <<  8) /**< \brief (EVSYS_CHSTATUS) Channel 5 busy */
#define   EVSYS_CHSTATUS_CHBUSY0_CHBUSY6 (0x40u <<  8) /**< \brief (EVSYS_CHSTATUS) Channel 6 busy */
#define   EVSYS_CHSTATUS_CHBUSY0_CHBUSY7 (0x80u <<  8) /**< \brief (EVSYS_CHSTATUS) Channel 7 busy */
#define EVSYS_CHSTATUS_USRRDY1_Pos  16           /**< \brief (EVSYS_CHSTATUS) User Ready for Channels 8 to 15 (modulo 16) */
#define EVSYS_CHSTATUS_USRRDY1_Msk  (0xFFu << EVSYS_CHSTATUS_USRRDY1_Pos)
#define EVSYS_CHSTATUS_USRRDY1(value) ((EVSYS_CHSTATUS_USRRDY1_Msk & ((value) << EVSYS_CHSTATUS_USRRDY1_Pos)))
#define   EVSYS_CHSTATUS_USRRDY1_USRRDY8 (0x1u << 16) /**< \brief (EVSYS_CHSTATUS) User ready for Channel 8 */
#define   EVSYS_CHSTATUS_USRRDY1_USRRDY9 (0x2u << 16) /**< \brief (EVSYS_CHSTATUS) User ready for Channel 9 */
#define   EVSYS_CHSTATUS_USRRDY1_USRRDY10 (0x4u << 16) /**< \brief (EVSYS_CHSTATUS) User ready for Channel 10 */
#define   EVSYS_CHSTATUS_USRRDY1_USRRDY11 (0x8u << 16) /**< \brief (EVSYS_CHSTATUS) User ready for Channel 11 */
#define   EVSYS_CHSTATUS_USRRDY1_USRRDY12 (0x10u << 16) /**< \brief (EVSYS_CHSTATUS) User ready for Channel 12 */
#define   EVSYS_CHSTATUS_USRRDY1_USRRDY13 (0x20u << 16) /**< \brief (EVSYS_CHSTATUS) User ready for Channel 13 */
#define   EVSYS_CHSTATUS_USRRDY1_USRRDY14 (0x40u << 16) /**< \brief (EVSYS_CHSTATUS) User ready for Channel 14 */
#define   EVSYS_CHSTATUS_USRRDY1_USRRDY15 (0x80u << 16) /**< \brief (EVSYS_CHSTATUS) User ready for Channel 15 */
#define EVSYS_CHSTATUS_CHBUSY1_Pos  24           /**< \brief (EVSYS_CHSTATUS) Channels Busy 8 to 15 (modulo 16) */
#define EVSYS_CHSTATUS_CHBUSY1_Msk  (0xFFu << EVSYS_CHSTATUS_CHBUSY1_Pos)
#define EVSYS_CHSTATUS_CHBUSY1(value) ((EVSYS_CHSTATUS_CHBUSY1_Msk & ((value) << EVSYS_CHSTATUS_CHBUSY1_Pos)))
#define   EVSYS_CHSTATUS_CHBUSY1_CHBUSY8 (0x1u << 24) /**< \brief (EVSYS_CHSTATUS) Channel 8 busy */
#define   EVSYS_CHSTATUS_CHBUSY1_CHBUSY9 (0x2u << 24) /**< \brief (EVSYS_CHSTATUS) Channel 9 busy */
#define   EVSYS_CHSTATUS_CHBUSY1_CHBUSY10 (0x4u << 24) /**< \brief (EVSYS_CHSTATUS) Channel 10 busy */
#define   EVSYS_CHSTATUS_CHBUSY1_CHBUSY11 (0x8u << 24) /**< \brief (EVSYS_CHSTATUS) Channel 11 busy */
#define   EVSYS_CHSTATUS_CHBUSY1_CHBUSY12 (0x10u << 24) /**< \brief (EVSYS_CHSTATUS) Channel 12 busy */
#define   EVSYS_CHSTATUS_CHBUSY1_CHBUSY13 (0x20u << 24) /**< \brief (EVSYS_CHSTATUS) Channel 13 busy */
#define   EVSYS_CHSTATUS_CHBUSY1_CHBUSY14 (0x40u << 24) /**< \brief (EVSYS_CHSTATUS) Channel 14 busy */
#define   EVSYS_CHSTATUS_CHBUSY1_CHBUSY15 (0x80u << 24) /**< \brief (EVSYS_CHSTATUS) Channel 15 busy */
#define EVSYS_CHSTATUS_MASK         0xFFFFFFFFu  /**< \brief (EVSYS_CHSTATUS) MASK Register */

/* -------- EVSYS_INTENCLR : (EVSYS Offset: 0x10) (R/W 32) Interrupt Enable Clear Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t OVR0:8;           /*!< bit:  0.. 7  Overrun Interrupt Disable for Channels 0 to 7 (modulo 16) */
    uint32_t EVD0:8;           /*!< bit:  8..15  Event Detection Interrupt Disable for Channels 0 to 7 (modulo 16) */
    uint32_t OVR1:8;           /*!< bit: 16..23  Overrun Interrupt Disable for Channels 8 to 15 (modulo 16) */
    uint32_t EVD1:8;           /*!< bit: 24..31  Event Detection Interrupt Disable for Channels 8 to 15 (modulo 16) */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} EVSYS_INTENCLR_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define EVSYS_INTENCLR_OFFSET       0x10         /**< \brief (EVSYS_INTENCLR offset) Interrupt Enable Clear Register */
#define EVSYS_INTENCLR_RESETVALUE   0x00000000   /**< \brief (EVSYS_INTENCLR reset_value) Interrupt Enable Clear Register */

#define EVSYS_INTENCLR_OVR0_Pos     0            /**< \brief (EVSYS_INTENCLR) Overrun Interrupt Disable for Channels 0 to 7 (modulo 16) */
#define EVSYS_INTENCLR_OVR0_Msk     (0xFFu << EVSYS_INTENCLR_OVR0_Pos)
#define EVSYS_INTENCLR_OVR0(value)  ((EVSYS_INTENCLR_OVR0_Msk & ((value) << EVSYS_INTENCLR_OVR0_Pos)))
#define   EVSYS_INTENCLR_OVR0_OVR0  (0x1u <<  0) /**< \brief (EVSYS_INTENCLR) Overrun detected on Channel 0 */
#define   EVSYS_INTENCLR_OVR0_OVR1  (0x2u <<  0) /**< \brief (EVSYS_INTENCLR) Overrun detected on Channel 1 */
#define   EVSYS_INTENCLR_OVR0_OVR2  (0x4u <<  0) /**< \brief (EVSYS_INTENCLR) Overrun detected on Channel 2 */
#define   EVSYS_INTENCLR_OVR0_OVR3  (0x8u <<  0) /**< \brief (EVSYS_INTENCLR) Overrun detected on Channel 3 */
#define   EVSYS_INTENCLR_OVR0_OVR4  (0x10u <<  0) /**< \brief (EVSYS_INTENCLR) Overrun detected on Channel 4 */
#define   EVSYS_INTENCLR_OVR0_OVR5  (0x20u <<  0) /**< \brief (EVSYS_INTENCLR) Overrun detected on Channel 5 */
#define   EVSYS_INTENCLR_OVR0_OVR6  (0x40u <<  0) /**< \brief (EVSYS_INTENCLR) Overrun detected on Channel 6 */
#define   EVSYS_INTENCLR_OVR0_OVR7  (0x80u <<  0) /**< \brief (EVSYS_INTENCLR) Overrun detected on Channel 7 */
#define EVSYS_INTENCLR_EVD0_Pos     8            /**< \brief (EVSYS_INTENCLR) Event Detection Interrupt Disable for Channels 0 to 7 (modulo 16) */
#define EVSYS_INTENCLR_EVD0_Msk     (0xFFu << EVSYS_INTENCLR_EVD0_Pos)
#define EVSYS_INTENCLR_EVD0(value)  ((EVSYS_INTENCLR_EVD0_Msk & ((value) << EVSYS_INTENCLR_EVD0_Pos)))
#define   EVSYS_INTENCLR_EVD0_EVD0  (0x1u <<  8) /**< \brief (EVSYS_INTENCLR) Event detected on Channel 0 */
#define   EVSYS_INTENCLR_EVD0_EVD1  (0x2u <<  8) /**< \brief (EVSYS_INTENCLR) Event detected on Channel 1 */
#define   EVSYS_INTENCLR_EVD0_EVD2  (0x4u <<  8) /**< \brief (EVSYS_INTENCLR) Event detected on Channel 2 */
#define   EVSYS_INTENCLR_EVD0_EVD3  (0x8u <<  8) /**< \brief (EVSYS_INTENCLR) Event detected on Channel 3 */
#define   EVSYS_INTENCLR_EVD0_EVD4  (0x10u <<  8) /**< \brief (EVSYS_INTENCLR) Event detected on Channel 4 */
#define   EVSYS_INTENCLR_EVD0_EVD5  (0x20u <<  8) /**< \brief (EVSYS_INTENCLR) Event detected on Channel 5 */
#define   EVSYS_INTENCLR_EVD0_EVD6  (0x40u <<  8) /**< \brief (EVSYS_INTENCLR) Event detected on Channel 6 */
#define   EVSYS_INTENCLR_EVD0_EVD7  (0x80u <<  8) /**< \brief (EVSYS_INTENCLR) Event detected on Channel 7 */
#define EVSYS_INTENCLR_OVR1_Pos     16           /**< \brief (EVSYS_INTENCLR) Overrun Interrupt Disable for Channels 8 to 15 (modulo 16) */
#define EVSYS_INTENCLR_OVR1_Msk     (0xFFu << EVSYS_INTENCLR_OVR1_Pos)
#define EVSYS_INTENCLR_OVR1(value)  ((EVSYS_INTENCLR_OVR1_Msk & ((value) << EVSYS_INTENCLR_OVR1_Pos)))
#define   EVSYS_INTENCLR_OVR1_OVR8  (0x1u << 16) /**< \brief (EVSYS_INTENCLR) Overrun detected on Channel 8 */
#define   EVSYS_INTENCLR_OVR1_OVR9  (0x2u << 16) /**< \brief (EVSYS_INTENCLR) Overrun detected on Channel 9 */
#define   EVSYS_INTENCLR_OVR1_OVR10 (0x4u << 16) /**< \brief (EVSYS_INTENCLR) Overrun detected on Channel 10 */
#define   EVSYS_INTENCLR_OVR1_OVR11 (0x8u << 16) /**< \brief (EVSYS_INTENCLR) Overrun detected on Channel 11 */
#define   EVSYS_INTENCLR_OVR1_OVR12 (0x10u << 16) /**< \brief (EVSYS_INTENCLR) Overrun detected on Channel 12 */
#define   EVSYS_INTENCLR_OVR1_OVR13 (0x20u << 16) /**< \brief (EVSYS_INTENCLR) Overrun detected on Channel 13 */
#define   EVSYS_INTENCLR_OVR1_OVR14 (0x40u << 16) /**< \brief (EVSYS_INTENCLR) Overrun detected on Channel 14 */
#define   EVSYS_INTENCLR_OVR1_OVR15 (0x80u << 16) /**< \brief (EVSYS_INTENCLR) Overrun detected on Channel 15 */
#define EVSYS_INTENCLR_EVD1_Pos     24           /**< \brief (EVSYS_INTENCLR) Event Detection Interrupt Disable for Channels 8 to 15 (modulo 16) */
#define EVSYS_INTENCLR_EVD1_Msk     (0xFFu << EVSYS_INTENCLR_EVD1_Pos)
#define EVSYS_INTENCLR_EVD1(value)  ((EVSYS_INTENCLR_EVD1_Msk & ((value) << EVSYS_INTENCLR_EVD1_Pos)))
#define   EVSYS_INTENCLR_EVD1_EVD8  (0x1u << 24) /**< \brief (EVSYS_INTENCLR) Event detected on Channel 8 */
#define   EVSYS_INTENCLR_EVD1_EVD9  (0x2u << 24) /**< \brief (EVSYS_INTENCLR) Event detected on Channel 9 */
#define   EVSYS_INTENCLR_EVD1_EVD10 (0x4u << 24) /**< \brief (EVSYS_INTENCLR) Event detected on Channel 10 */
#define   EVSYS_INTENCLR_EVD1_EVD11 (0x8u << 24) /**< \brief (EVSYS_INTENCLR) Event detected on Channel 11 */
#define   EVSYS_INTENCLR_EVD1_EVD12 (0x10u << 24) /**< \brief (EVSYS_INTENCLR) Event detected on Channel 12 */
#define   EVSYS_INTENCLR_EVD1_EVD13 (0x20u << 24) /**< \brief (EVSYS_INTENCLR) Event detected on Channel 13 */
#define   EVSYS_INTENCLR_EVD1_EVD14 (0x40u << 24) /**< \brief (EVSYS_INTENCLR) Event detected on Channel 14 */
#define   EVSYS_INTENCLR_EVD1_EVD15 (0x80u << 24) /**< \brief (EVSYS_INTENCLR) Event detected on Channel 15 */
#define EVSYS_INTENCLR_MASK         0xFFFFFFFFu  /**< \brief (EVSYS_INTENCLR) MASK Register */

/* -------- EVSYS_INTENSET : (EVSYS Offset: 0x14) (R/W 32) Interrupt Enable Set Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t OVR0:8;           /*!< bit:  0.. 7  Overrun Interrupt Enable for Channels 0 to 7 (modulo 16) */
    uint32_t EVD0:8;           /*!< bit:  8..15  Event Detection Interrupt Enable for Channels 0 to 7 (modulo 16) */
    uint32_t OVR1:8;           /*!< bit: 16..23  Overrun Interrupt Enable for Channels 8 to 15 (modulo 16) */
    uint32_t EVD1:8;           /*!< bit: 24..31  Event Detection Interrupt Enable for Channels 8 to 15 (modulo 16) */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} EVSYS_INTENSET_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define EVSYS_INTENSET_OFFSET       0x14         /**< \brief (EVSYS_INTENSET offset) Interrupt Enable Set Register */
#define EVSYS_INTENSET_RESETVALUE   0x00000000   /**< \brief (EVSYS_INTENSET reset_value) Interrupt Enable Set Register */

#define EVSYS_INTENSET_OVR0_Pos     0            /**< \brief (EVSYS_INTENSET) Overrun Interrupt Enable for Channels 0 to 7 (modulo 16) */
#define EVSYS_INTENSET_OVR0_Msk     (0xFFu << EVSYS_INTENSET_OVR0_Pos)
#define EVSYS_INTENSET_OVR0(value)  ((EVSYS_INTENSET_OVR0_Msk & ((value) << EVSYS_INTENSET_OVR0_Pos)))
#define   EVSYS_INTENSET_OVR0_OVR0  (0x1u <<  0) /**< \brief (EVSYS_INTENSET) Overrun detected on Channel 0 */
#define   EVSYS_INTENSET_OVR0_OVR1  (0x2u <<  0) /**< \brief (EVSYS_INTENSET) Overrun detected on Channel 1 */
#define   EVSYS_INTENSET_OVR0_OVR2  (0x4u <<  0) /**< \brief (EVSYS_INTENSET) Overrun detected on Channel 2 */
#define   EVSYS_INTENSET_OVR0_OVR3  (0x8u <<  0) /**< \brief (EVSYS_INTENSET) Overrun detected on Channel 3 */
#define   EVSYS_INTENSET_OVR0_OVR4  (0x10u <<  0) /**< \brief (EVSYS_INTENSET) Overrun detected on Channel 4 */
#define   EVSYS_INTENSET_OVR0_OVR5  (0x20u <<  0) /**< \brief (EVSYS_INTENSET) Overrun detected on Channel 5 */
#define   EVSYS_INTENSET_OVR0_OVR6  (0x40u <<  0) /**< \brief (EVSYS_INTENSET) Overrun detected on Channel 6 */
#define   EVSYS_INTENSET_OVR0_OVR7  (0x80u <<  0) /**< \brief (EVSYS_INTENSET) Overrun detected on Channel 7 */
#define EVSYS_INTENSET_EVD0_Pos     8            /**< \brief (EVSYS_INTENSET) Event Detection Interrupt Enable for Channels 0 to 7 (modulo 16) */
#define EVSYS_INTENSET_EVD0_Msk     (0xFFu << EVSYS_INTENSET_EVD0_Pos)
#define EVSYS_INTENSET_EVD0(value)  ((EVSYS_INTENSET_EVD0_Msk & ((value) << EVSYS_INTENSET_EVD0_Pos)))
#define   EVSYS_INTENSET_EVD0_EVD0  (0x1u <<  8) /**< \brief (EVSYS_INTENSET) Event detected on Channel 0 */
#define   EVSYS_INTENSET_EVD0_EVD1  (0x2u <<  8) /**< \brief (EVSYS_INTENSET) Event detected on Channel 1 */
#define   EVSYS_INTENSET_EVD0_EVD2  (0x4u <<  8) /**< \brief (EVSYS_INTENSET) Event detected on Channel 2 */
#define   EVSYS_INTENSET_EVD0_EVD3  (0x8u <<  8) /**< \brief (EVSYS_INTENSET) Event detected on Channel 3 */
#define   EVSYS_INTENSET_EVD0_EVD4  (0x10u <<  8) /**< \brief (EVSYS_INTENSET) Event detected on Channel 4 */
#define   EVSYS_INTENSET_EVD0_EVD5  (0x20u <<  8) /**< \brief (EVSYS_INTENSET) Event detected on Channel 5 */
#define   EVSYS_INTENSET_EVD0_EVD6  (0x40u <<  8) /**< \brief (EVSYS_INTENSET) Event detected on Channel 6 */
#define   EVSYS_INTENSET_EVD0_EVD7  (0x80u <<  8) /**< \brief (EVSYS_INTENSET) Event detected on Channel 7 */
#define EVSYS_INTENSET_OVR1_Pos     16           /**< \brief (EVSYS_INTENSET) Overrun Interrupt Enable for Channels 8 to 15 (modulo 16) */
#define EVSYS_INTENSET_OVR1_Msk     (0xFFu << EVSYS_INTENSET_OVR1_Pos)
#define EVSYS_INTENSET_OVR1(value)  ((EVSYS_INTENSET_OVR1_Msk & ((value) << EVSYS_INTENSET_OVR1_Pos)))
#define   EVSYS_INTENSET_OVR1_OVR8  (0x1u << 16) /**< \brief (EVSYS_INTENSET) Overrun detected on Channel 8 */
#define   EVSYS_INTENSET_OVR1_OVR9  (0x2u << 16) /**< \brief (EVSYS_INTENSET) Overrun detected on Channel 9 */
#define   EVSYS_INTENSET_OVR1_OVR10 (0x4u << 16) /**< \brief (EVSYS_INTENSET) Overrun detected on Channel 10 */
#define   EVSYS_INTENSET_OVR1_OVR11 (0x8u << 16) /**< \brief (EVSYS_INTENSET) Overrun detected on Channel 11 */
#define   EVSYS_INTENSET_OVR1_OVR12 (0x10u << 16) /**< \brief (EVSYS_INTENSET) Overrun detected on Channel 12 */
#define   EVSYS_INTENSET_OVR1_OVR13 (0x20u << 16) /**< \brief (EVSYS_INTENSET) Overrun detected on Channel 13 */
#define   EVSYS_INTENSET_OVR1_OVR14 (0x40u << 16) /**< \brief (EVSYS_INTENSET) Overrun detected on Channel 14 */
#define   EVSYS_INTENSET_OVR1_OVR15 (0x80u << 16) /**< \brief (EVSYS_INTENSET) Overrun detected on Channel 15 */
#define EVSYS_INTENSET_EVD1_Pos     24           /**< \brief (EVSYS_INTENSET) Event Detection Interrupt Enable for Channels 8 to 15 (modulo 16) */
#define EVSYS_INTENSET_EVD1_Msk     (0xFFu << EVSYS_INTENSET_EVD1_Pos)
#define EVSYS_INTENSET_EVD1(value)  ((EVSYS_INTENSET_EVD1_Msk & ((value) << EVSYS_INTENSET_EVD1_Pos)))
#define   EVSYS_INTENSET_EVD1_EVD8  (0x1u << 24) /**< \brief (EVSYS_INTENSET) Event detected on Channel 8 */
#define   EVSYS_INTENSET_EVD1_EVD9  (0x2u << 24) /**< \brief (EVSYS_INTENSET) Event detected on Channel 9 */
#define   EVSYS_INTENSET_EVD1_EVD10 (0x4u << 24) /**< \brief (EVSYS_INTENSET) Event detected on Channel 10 */
#define   EVSYS_INTENSET_EVD1_EVD11 (0x8u << 24) /**< \brief (EVSYS_INTENSET) Event detected on Channel 11 */
#define   EVSYS_INTENSET_EVD1_EVD12 (0x10u << 24) /**< \brief (EVSYS_INTENSET) Event detected on Channel 12 */
#define   EVSYS_INTENSET_EVD1_EVD13 (0x20u << 24) /**< \brief (EVSYS_INTENSET) Event detected on Channel 13 */
#define   EVSYS_INTENSET_EVD1_EVD14 (0x40u << 24) /**< \brief (EVSYS_INTENSET) Event detected on Channel 14 */
#define   EVSYS_INTENSET_EVD1_EVD15 (0x80u << 24) /**< \brief (EVSYS_INTENSET) Event detected on Channel 15 */
#define EVSYS_INTENSET_MASK         0xFFFFFFFFu  /**< \brief (EVSYS_INTENSET) MASK Register */

/* -------- EVSYS_INTFLAG : (EVSYS Offset: 0x18) (R/W 32) Interrupt Flag Status and Clear Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t OVR0:8;           /*!< bit:  0.. 7  Overrun Interrupt Flag for Channels 0 to 7 (modulo 16) */
    uint32_t EVD0:8;           /*!< bit:  8..15  Event Detection Interrupt Flag for Channels 0 to 7 (modulo 16) */
    uint32_t OVR1:8;           /*!< bit: 16..23  Overrun Interrupt Flag for Channels 8 to 15 (modulo 16) */
    uint32_t EVD1:8;           /*!< bit: 24..31  Event Detection Interrupt Flag for Channels 8 to 15 (modulo 16) */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} EVSYS_INTFLAG_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define EVSYS_INTFLAG_OFFSET        0x18         /**< \brief (EVSYS_INTFLAG offset) Interrupt Flag Status and Clear Register */
#define EVSYS_INTFLAG_RESETVALUE    0x00000000   /**< \brief (EVSYS_INTFLAG reset_value) Interrupt Flag Status and Clear Register */

#define EVSYS_INTFLAG_OVR0_Pos      0            /**< \brief (EVSYS_INTFLAG) Overrun Interrupt Flag for Channels 0 to 7 (modulo 16) */
#define EVSYS_INTFLAG_OVR0_Msk      (0xFFu << EVSYS_INTFLAG_OVR0_Pos)
#define EVSYS_INTFLAG_OVR0(value)   ((EVSYS_INTFLAG_OVR0_Msk & ((value) << EVSYS_INTFLAG_OVR0_Pos)))
#define   EVSYS_INTFLAG_OVR0_OVR0   (0x1u <<  0) /**< \brief (EVSYS_INTFLAG) Overrun detected on Channel 0 */
#define   EVSYS_INTFLAG_OVR0_OVR1   (0x2u <<  0) /**< \brief (EVSYS_INTFLAG) Overrun detected on Channel 1 */
#define   EVSYS_INTFLAG_OVR0_OVR2   (0x4u <<  0) /**< \brief (EVSYS_INTFLAG) Overrun detected on Channel 2 */
#define   EVSYS_INTFLAG_OVR0_OVR3   (0x8u <<  0) /**< \brief (EVSYS_INTFLAG) Overrun detected on Channel 3 */
#define   EVSYS_INTFLAG_OVR0_OVR4   (0x10u <<  0) /**< \brief (EVSYS_INTFLAG) Overrun detected on Channel 4 */
#define   EVSYS_INTFLAG_OVR0_OVR5   (0x20u <<  0) /**< \brief (EVSYS_INTFLAG) Overrun detected on Channel 5 */
#define   EVSYS_INTFLAG_OVR0_OVR6   (0x40u <<  0) /**< \brief (EVSYS_INTFLAG) Overrun detected on Channel 6 */
#define   EVSYS_INTFLAG_OVR0_OVR7   (0x80u <<  0) /**< \brief (EVSYS_INTFLAG) Overrun detected on Channel 7 */
#define EVSYS_INTFLAG_EVD0_Pos      8            /**< \brief (EVSYS_INTFLAG) Event Detection Interrupt Flag for Channels 0 to 7 (modulo 16) */
#define EVSYS_INTFLAG_EVD0_Msk      (0xFFu << EVSYS_INTFLAG_EVD0_Pos)
#define EVSYS_INTFLAG_EVD0(value)   ((EVSYS_INTFLAG_EVD0_Msk & ((value) << EVSYS_INTFLAG_EVD0_Pos)))
#define   EVSYS_INTFLAG_EVD0_EVD0   (0x1u <<  8) /**< \brief (EVSYS_INTFLAG) Event detected on Channel 0 */
#define   EVSYS_INTFLAG_EVD0_EVD1   (0x2u <<  8) /**< \brief (EVSYS_INTFLAG) Event detected on Channel 1 */
#define   EVSYS_INTFLAG_EVD0_EVD2   (0x4u <<  8) /**< \brief (EVSYS_INTFLAG) Event detected on Channel 2 */
#define   EVSYS_INTFLAG_EVD0_EVD3   (0x8u <<  8) /**< \brief (EVSYS_INTFLAG) Event detected on Channel 3 */
#define   EVSYS_INTFLAG_EVD0_EVD4   (0x10u <<  8) /**< \brief (EVSYS_INTFLAG) Event detected on Channel 4 */
#define   EVSYS_INTFLAG_EVD0_EVD5   (0x20u <<  8) /**< \brief (EVSYS_INTFLAG) Event detected on Channel 5 */
#define   EVSYS_INTFLAG_EVD0_EVD6   (0x40u <<  8) /**< \brief (EVSYS_INTFLAG) Event detected on Channel 6 */
#define   EVSYS_INTFLAG_EVD0_EVD7   (0x80u <<  8) /**< \brief (EVSYS_INTFLAG) Event detected on Channel 7 */
#define EVSYS_INTFLAG_OVR1_Pos      16           /**< \brief (EVSYS_INTFLAG) Overrun Interrupt Flag for Channels 8 to 15 (modulo 16) */
#define EVSYS_INTFLAG_OVR1_Msk      (0xFFu << EVSYS_INTFLAG_OVR1_Pos)
#define EVSYS_INTFLAG_OVR1(value)   ((EVSYS_INTFLAG_OVR1_Msk & ((value) << EVSYS_INTFLAG_OVR1_Pos)))
#define   EVSYS_INTFLAG_OVR1_OVR8   (0x1u << 16) /**< \brief (EVSYS_INTFLAG) Overrun detected on Channel 8 */
#define   EVSYS_INTFLAG_OVR1_OVR9   (0x2u << 16) /**< \brief (EVSYS_INTFLAG) Overrun detected on Channel 9 */
#define   EVSYS_INTFLAG_OVR1_OVR10  (0x4u << 16) /**< \brief (EVSYS_INTFLAG) Overrun detected on Channel 10 */
#define   EVSYS_INTFLAG_OVR1_OVR11  (0x8u << 16) /**< \brief (EVSYS_INTFLAG) Overrun detected on Channel 11 */
#define   EVSYS_INTFLAG_OVR1_OVR12  (0x10u << 16) /**< \brief (EVSYS_INTFLAG) Overrun detected on Channel 12 */
#define   EVSYS_INTFLAG_OVR1_OVR13  (0x20u << 16) /**< \brief (EVSYS_INTFLAG) Overrun detected on Channel 13 */
#define   EVSYS_INTFLAG_OVR1_OVR14  (0x40u << 16) /**< \brief (EVSYS_INTFLAG) Overrun detected on Channel 14 */
#define   EVSYS_INTFLAG_OVR1_OVR15  (0x80u << 16) /**< \brief (EVSYS_INTFLAG) Overrun detected on Channel 15 */
#define EVSYS_INTFLAG_EVD1_Pos      24           /**< \brief (EVSYS_INTFLAG) Event Detection Interrupt Flag for Channels 8 to 15 (modulo 16) */
#define EVSYS_INTFLAG_EVD1_Msk      (0xFFu << EVSYS_INTFLAG_EVD1_Pos)
#define EVSYS_INTFLAG_EVD1(value)   ((EVSYS_INTFLAG_EVD1_Msk & ((value) << EVSYS_INTFLAG_EVD1_Pos)))
#define   EVSYS_INTFLAG_EVD1_EVD8   (0x1u << 24) /**< \brief (EVSYS_INTFLAG) Event detected on Channel 8 */
#define   EVSYS_INTFLAG_EVD1_EVD9   (0x2u << 24) /**< \brief (EVSYS_INTFLAG) Event detected on Channel 9 */
#define   EVSYS_INTFLAG_EVD1_EVD10  (0x4u << 24) /**< \brief (EVSYS_INTFLAG) Event detected on Channel 10 */
#define   EVSYS_INTFLAG_EVD1_EVD11  (0x8u << 24) /**< \brief (EVSYS_INTFLAG) Event detected on Channel 11 */
#define   EVSYS_INTFLAG_EVD1_EVD12  (0x10u << 24) /**< \brief (EVSYS_INTFLAG) Event detected on Channel 12 */
#define   EVSYS_INTFLAG_EVD1_EVD13  (0x20u << 24) /**< \brief (EVSYS_INTFLAG) Event detected on Channel 13 */
#define   EVSYS_INTFLAG_EVD1_EVD14  (0x40u << 24) /**< \brief (EVSYS_INTFLAG) Event detected on Channel 14 */
#define   EVSYS_INTFLAG_EVD1_EVD15  (0x80u << 24) /**< \brief (EVSYS_INTFLAG) Event detected on Channel 15 */
#define EVSYS_INTFLAG_MASK          0xFFFFFFFFu  /**< \brief (EVSYS_INTFLAG) MASK Register */

/** \brief EVSYS hardware registers */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef struct {
  __O  EVSYS_CTRL_Type           CTRL;        /**< \brief Offset: 0x00 ( /W  8) Control Register */
       RoReg8                    Reserved1[0x3];
  __IO EVSYS_CHANNEL_Type        CHANNEL;     /**< \brief Offset: 0x04 (R/W 32) Channel Register */
  __IO EVSYS_USER_Type           USER;        /**< \brief Offset: 0x08 (R/W 16) User Mux Register */
       RoReg8                    Reserved2[0x2];
  __I  EVSYS_CHSTATUS_Type       CHSTATUS;    /**< \brief Offset: 0x0C (R/  32) Channel Status Register */
  __IO EVSYS_INTENCLR_Type       INTENCLR;    /**< \brief Offset: 0x10 (R/W 32) Interrupt Enable Clear Register */
  __IO EVSYS_INTENSET_Type       INTENSET;    /**< \brief Offset: 0x14 (R/W 32) Interrupt Enable Set Register */
  __IO EVSYS_INTFLAG_Type        INTFLAG;     /**< \brief Offset: 0x18 (R/W 32) Interrupt Flag Status and Clear Register */
} Evsys;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

/*@}*/

#endif /* _SAMD20_EVSYS_COMPONENT_ */
