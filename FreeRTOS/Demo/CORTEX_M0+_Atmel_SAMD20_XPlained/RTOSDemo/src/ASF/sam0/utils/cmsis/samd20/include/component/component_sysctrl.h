/**
 * \file
 *
 * \brief Component description for SYSCTRL
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

#ifndef _SAMD20_SYSCTRL_COMPONENT_
#define _SAMD20_SYSCTRL_COMPONENT_

/* ========================================================================== */
/**  SOFTWARE API DEFINITION FOR SYSCTRL */
/* ========================================================================== */
/** \addtogroup SAMD20_SYSCTRL System Control */
/*@{*/

#define REV_SYSCTRL                 0x200

/* -------- SYSCTRL_INTENCLR : (SYSCTRL Offset: 0x00) (R/W 32) Interrupt Enable Clear Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t XOSCRDY:1;        /*!< bit:      0  XOSC Ready                         */
    uint32_t XOSC32KRDY:1;     /*!< bit:      1  XOSC32K Ready                      */
    uint32_t OSC32KRDY:1;      /*!< bit:      2  OSC32K Ready                       */
    uint32_t OSC8MRDY:1;       /*!< bit:      3  OSC8M Ready                        */
    uint32_t DFLLRDY:1;        /*!< bit:      4  DFLL Ready                         */
    uint32_t DFLLOOB:1;        /*!< bit:      5  DFLL Out Of Bounds                 */
    uint32_t DFLLLCKF:1;       /*!< bit:      6  DFLL Lock Fine                     */
    uint32_t DFLLLCKC:1;       /*!< bit:      7  DFLL Lock Coarse                   */
    uint32_t DFLLRCS:1;        /*!< bit:      8  DFLL Reference Clock Stopped       */
    uint32_t BOD33RDY:1;       /*!< bit:      9  BOD33 Ready                        */
    uint32_t BOD33DET:1;       /*!< bit:     10  BOD33 Detection                    */
    uint32_t B33SRDY:1;        /*!< bit:     11  BOD33 Synchronization Ready        */
    uint32_t BOD12RDY:1;       /*!< bit:     12  BOD12 Ready                        */
    uint32_t BOD12DET:1;       /*!< bit:     13  BOD12 Detection                    */
    uint32_t B12SRDY:1;        /*!< bit:     14  BOD12 Synchronization Ready        */
    uint32_t :17;              /*!< bit: 15..31  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} SYSCTRL_INTENCLR_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define SYSCTRL_INTENCLR_OFFSET     0x00         /**< \brief (SYSCTRL_INTENCLR offset) Interrupt Enable Clear Register */
#define SYSCTRL_INTENCLR_RESETVALUE 0x00000000   /**< \brief (SYSCTRL_INTENCLR reset_value) Interrupt Enable Clear Register */

#define SYSCTRL_INTENCLR_XOSCRDY_Pos 0            /**< \brief (SYSCTRL_INTENCLR) XOSC Ready */
#define SYSCTRL_INTENCLR_XOSCRDY    (0x1u << SYSCTRL_INTENCLR_XOSCRDY_Pos)
#define SYSCTRL_INTENCLR_XOSC32KRDY_Pos 1            /**< \brief (SYSCTRL_INTENCLR) XOSC32K Ready */
#define SYSCTRL_INTENCLR_XOSC32KRDY (0x1u << SYSCTRL_INTENCLR_XOSC32KRDY_Pos)
#define SYSCTRL_INTENCLR_OSC32KRDY_Pos 2            /**< \brief (SYSCTRL_INTENCLR) OSC32K Ready */
#define SYSCTRL_INTENCLR_OSC32KRDY  (0x1u << SYSCTRL_INTENCLR_OSC32KRDY_Pos)
#define SYSCTRL_INTENCLR_OSC8MRDY_Pos 3            /**< \brief (SYSCTRL_INTENCLR) OSC8M Ready */
#define SYSCTRL_INTENCLR_OSC8MRDY   (0x1u << SYSCTRL_INTENCLR_OSC8MRDY_Pos)
#define SYSCTRL_INTENCLR_DFLLRDY_Pos 4            /**< \brief (SYSCTRL_INTENCLR) DFLL Ready */
#define SYSCTRL_INTENCLR_DFLLRDY    (0x1u << SYSCTRL_INTENCLR_DFLLRDY_Pos)
#define SYSCTRL_INTENCLR_DFLLOOB_Pos 5            /**< \brief (SYSCTRL_INTENCLR) DFLL Out Of Bounds */
#define SYSCTRL_INTENCLR_DFLLOOB    (0x1u << SYSCTRL_INTENCLR_DFLLOOB_Pos)
#define SYSCTRL_INTENCLR_DFLLLCKF_Pos 6            /**< \brief (SYSCTRL_INTENCLR) DFLL Lock Fine */
#define SYSCTRL_INTENCLR_DFLLLCKF   (0x1u << SYSCTRL_INTENCLR_DFLLLCKF_Pos)
#define SYSCTRL_INTENCLR_DFLLLCKC_Pos 7            /**< \brief (SYSCTRL_INTENCLR) DFLL Lock Coarse */
#define SYSCTRL_INTENCLR_DFLLLCKC   (0x1u << SYSCTRL_INTENCLR_DFLLLCKC_Pos)
#define SYSCTRL_INTENCLR_DFLLRCS_Pos 8            /**< \brief (SYSCTRL_INTENCLR) DFLL Reference Clock Stopped */
#define SYSCTRL_INTENCLR_DFLLRCS    (0x1u << SYSCTRL_INTENCLR_DFLLRCS_Pos)
#define SYSCTRL_INTENCLR_BOD33RDY_Pos 9            /**< \brief (SYSCTRL_INTENCLR) BOD33 Ready */
#define SYSCTRL_INTENCLR_BOD33RDY   (0x1u << SYSCTRL_INTENCLR_BOD33RDY_Pos)
#define SYSCTRL_INTENCLR_BOD33DET_Pos 10           /**< \brief (SYSCTRL_INTENCLR) BOD33 Detection */
#define SYSCTRL_INTENCLR_BOD33DET   (0x1u << SYSCTRL_INTENCLR_BOD33DET_Pos)
#define SYSCTRL_INTENCLR_B33SRDY_Pos 11           /**< \brief (SYSCTRL_INTENCLR) BOD33 Synchronization Ready */
#define SYSCTRL_INTENCLR_B33SRDY    (0x1u << SYSCTRL_INTENCLR_B33SRDY_Pos)
#define SYSCTRL_INTENCLR_BOD12RDY_Pos 12           /**< \brief (SYSCTRL_INTENCLR) BOD12 Ready */
#define SYSCTRL_INTENCLR_BOD12RDY   (0x1u << SYSCTRL_INTENCLR_BOD12RDY_Pos)
#define SYSCTRL_INTENCLR_BOD12DET_Pos 13           /**< \brief (SYSCTRL_INTENCLR) BOD12 Detection */
#define SYSCTRL_INTENCLR_BOD12DET   (0x1u << SYSCTRL_INTENCLR_BOD12DET_Pos)
#define SYSCTRL_INTENCLR_B12SRDY_Pos 14           /**< \brief (SYSCTRL_INTENCLR) BOD12 Synchronization Ready */
#define SYSCTRL_INTENCLR_B12SRDY    (0x1u << SYSCTRL_INTENCLR_B12SRDY_Pos)
#define SYSCTRL_INTENCLR_MASK       0x00007FFFu  /**< \brief (SYSCTRL_INTENCLR) MASK Register */

/* -------- SYSCTRL_INTENSET : (SYSCTRL Offset: 0x04) (R/W 32) Interrupt Enable Set Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t XOSCRDY:1;        /*!< bit:      0  XOSC Ready                         */
    uint32_t XOSC32KRDY:1;     /*!< bit:      1  XOSC32K Ready                      */
    uint32_t OSC32KRDY:1;      /*!< bit:      2  OSC32K Ready                       */
    uint32_t OSC8MRDY:1;       /*!< bit:      3  OSC8M Ready                        */
    uint32_t DFLLRDY:1;        /*!< bit:      4  DFLL Ready                         */
    uint32_t DFLLOOB:1;        /*!< bit:      5  DFLL Out Of Bounds                 */
    uint32_t DFLLLCKF:1;       /*!< bit:      6  DFLL Lock Fine                     */
    uint32_t DFLLLCKC:1;       /*!< bit:      7  DFLL Lock Coarse                   */
    uint32_t DFLLRCS:1;        /*!< bit:      8  DFLL Reference Clock Stopped       */
    uint32_t BOD33RDY:1;       /*!< bit:      9  BOD33 Ready                        */
    uint32_t BOD33DET:1;       /*!< bit:     10  BOD33 Detection                    */
    uint32_t B33SRDY:1;        /*!< bit:     11  BOD33 Synchronization Ready        */
    uint32_t BOD12RDY:1;       /*!< bit:     12  BOD12 Ready                        */
    uint32_t BOD12DET:1;       /*!< bit:     13  BOD12 Detection                    */
    uint32_t B12SRDY:1;        /*!< bit:     14  BOD12 Synchronization Ready        */
    uint32_t :17;              /*!< bit: 15..31  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} SYSCTRL_INTENSET_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define SYSCTRL_INTENSET_OFFSET     0x04         /**< \brief (SYSCTRL_INTENSET offset) Interrupt Enable Set Register */
#define SYSCTRL_INTENSET_RESETVALUE 0x00000000   /**< \brief (SYSCTRL_INTENSET reset_value) Interrupt Enable Set Register */

#define SYSCTRL_INTENSET_XOSCRDY_Pos 0            /**< \brief (SYSCTRL_INTENSET) XOSC Ready */
#define SYSCTRL_INTENSET_XOSCRDY    (0x1u << SYSCTRL_INTENSET_XOSCRDY_Pos)
#define SYSCTRL_INTENSET_XOSC32KRDY_Pos 1            /**< \brief (SYSCTRL_INTENSET) XOSC32K Ready */
#define SYSCTRL_INTENSET_XOSC32KRDY (0x1u << SYSCTRL_INTENSET_XOSC32KRDY_Pos)
#define SYSCTRL_INTENSET_OSC32KRDY_Pos 2            /**< \brief (SYSCTRL_INTENSET) OSC32K Ready */
#define SYSCTRL_INTENSET_OSC32KRDY  (0x1u << SYSCTRL_INTENSET_OSC32KRDY_Pos)
#define SYSCTRL_INTENSET_OSC8MRDY_Pos 3            /**< \brief (SYSCTRL_INTENSET) OSC8M Ready */
#define SYSCTRL_INTENSET_OSC8MRDY   (0x1u << SYSCTRL_INTENSET_OSC8MRDY_Pos)
#define SYSCTRL_INTENSET_DFLLRDY_Pos 4            /**< \brief (SYSCTRL_INTENSET) DFLL Ready */
#define SYSCTRL_INTENSET_DFLLRDY    (0x1u << SYSCTRL_INTENSET_DFLLRDY_Pos)
#define SYSCTRL_INTENSET_DFLLOOB_Pos 5            /**< \brief (SYSCTRL_INTENSET) DFLL Out Of Bounds */
#define SYSCTRL_INTENSET_DFLLOOB    (0x1u << SYSCTRL_INTENSET_DFLLOOB_Pos)
#define SYSCTRL_INTENSET_DFLLLCKF_Pos 6            /**< \brief (SYSCTRL_INTENSET) DFLL Lock Fine */
#define SYSCTRL_INTENSET_DFLLLCKF   (0x1u << SYSCTRL_INTENSET_DFLLLCKF_Pos)
#define SYSCTRL_INTENSET_DFLLLCKC_Pos 7            /**< \brief (SYSCTRL_INTENSET) DFLL Lock Coarse */
#define SYSCTRL_INTENSET_DFLLLCKC   (0x1u << SYSCTRL_INTENSET_DFLLLCKC_Pos)
#define SYSCTRL_INTENSET_DFLLRCS_Pos 8            /**< \brief (SYSCTRL_INTENSET) DFLL Reference Clock Stopped */
#define SYSCTRL_INTENSET_DFLLRCS    (0x1u << SYSCTRL_INTENSET_DFLLRCS_Pos)
#define SYSCTRL_INTENSET_BOD33RDY_Pos 9            /**< \brief (SYSCTRL_INTENSET) BOD33 Ready */
#define SYSCTRL_INTENSET_BOD33RDY   (0x1u << SYSCTRL_INTENSET_BOD33RDY_Pos)
#define SYSCTRL_INTENSET_BOD33DET_Pos 10           /**< \brief (SYSCTRL_INTENSET) BOD33 Detection */
#define SYSCTRL_INTENSET_BOD33DET   (0x1u << SYSCTRL_INTENSET_BOD33DET_Pos)
#define SYSCTRL_INTENSET_B33SRDY_Pos 11           /**< \brief (SYSCTRL_INTENSET) BOD33 Synchronization Ready */
#define SYSCTRL_INTENSET_B33SRDY    (0x1u << SYSCTRL_INTENSET_B33SRDY_Pos)
#define SYSCTRL_INTENSET_BOD12RDY_Pos 12           /**< \brief (SYSCTRL_INTENSET) BOD12 Ready */
#define SYSCTRL_INTENSET_BOD12RDY   (0x1u << SYSCTRL_INTENSET_BOD12RDY_Pos)
#define SYSCTRL_INTENSET_BOD12DET_Pos 13           /**< \brief (SYSCTRL_INTENSET) BOD12 Detection */
#define SYSCTRL_INTENSET_BOD12DET   (0x1u << SYSCTRL_INTENSET_BOD12DET_Pos)
#define SYSCTRL_INTENSET_B12SRDY_Pos 14           /**< \brief (SYSCTRL_INTENSET) BOD12 Synchronization Ready */
#define SYSCTRL_INTENSET_B12SRDY    (0x1u << SYSCTRL_INTENSET_B12SRDY_Pos)
#define SYSCTRL_INTENSET_MASK       0x00007FFFu  /**< \brief (SYSCTRL_INTENSET) MASK Register */

/* -------- SYSCTRL_INTFLAG : (SYSCTRL Offset: 0x08) (R/W 32) Interrupt Flag Status and Clear Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t XOSCRDY:1;        /*!< bit:      0  XOSC Ready                         */
    uint32_t XOSC32KRDY:1;     /*!< bit:      1  XOSC32K Ready                      */
    uint32_t OSC32KRDY:1;      /*!< bit:      2  OSC32K Ready                       */
    uint32_t OSC8MRDY:1;       /*!< bit:      3  OSC8M Ready                        */
    uint32_t DFLLRDY:1;        /*!< bit:      4  DFLL Ready                         */
    uint32_t DFLLOOB:1;        /*!< bit:      5  DFLL Out Of Bounds                 */
    uint32_t DFLLLCKF:1;       /*!< bit:      6  DFLL Lock Fine                     */
    uint32_t DFLLLCKC:1;       /*!< bit:      7  DFLL Lock Coarse                   */
    uint32_t DFLLRCS:1;        /*!< bit:      8  DFLL Reference Clock Stopped       */
    uint32_t BOD33RDY:1;       /*!< bit:      9  BOD33 Ready                        */
    uint32_t BOD33DET:1;       /*!< bit:     10  BOD33 Detection                    */
    uint32_t B33SRDY:1;        /*!< bit:     11  BOD33 Synchronization Ready        */
    uint32_t BOD12RDY:1;       /*!< bit:     12  BOD12 Ready                        */
    uint32_t BOD12DET:1;       /*!< bit:     13  BOD12 Detection                    */
    uint32_t B12SRDY:1;        /*!< bit:     14  BOD12 Synchronization Ready        */
    uint32_t :17;              /*!< bit: 15..31  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} SYSCTRL_INTFLAG_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define SYSCTRL_INTFLAG_OFFSET      0x08         /**< \brief (SYSCTRL_INTFLAG offset) Interrupt Flag Status and Clear Register */
#define SYSCTRL_INTFLAG_RESETVALUE  0x00000000   /**< \brief (SYSCTRL_INTFLAG reset_value) Interrupt Flag Status and Clear Register */

#define SYSCTRL_INTFLAG_XOSCRDY_Pos 0            /**< \brief (SYSCTRL_INTFLAG) XOSC Ready */
#define SYSCTRL_INTFLAG_XOSCRDY     (0x1u << SYSCTRL_INTFLAG_XOSCRDY_Pos)
#define SYSCTRL_INTFLAG_XOSC32KRDY_Pos 1            /**< \brief (SYSCTRL_INTFLAG) XOSC32K Ready */
#define SYSCTRL_INTFLAG_XOSC32KRDY  (0x1u << SYSCTRL_INTFLAG_XOSC32KRDY_Pos)
#define SYSCTRL_INTFLAG_OSC32KRDY_Pos 2            /**< \brief (SYSCTRL_INTFLAG) OSC32K Ready */
#define SYSCTRL_INTFLAG_OSC32KRDY   (0x1u << SYSCTRL_INTFLAG_OSC32KRDY_Pos)
#define SYSCTRL_INTFLAG_OSC8MRDY_Pos 3            /**< \brief (SYSCTRL_INTFLAG) OSC8M Ready */
#define SYSCTRL_INTFLAG_OSC8MRDY    (0x1u << SYSCTRL_INTFLAG_OSC8MRDY_Pos)
#define SYSCTRL_INTFLAG_DFLLRDY_Pos 4            /**< \brief (SYSCTRL_INTFLAG) DFLL Ready */
#define SYSCTRL_INTFLAG_DFLLRDY     (0x1u << SYSCTRL_INTFLAG_DFLLRDY_Pos)
#define SYSCTRL_INTFLAG_DFLLOOB_Pos 5            /**< \brief (SYSCTRL_INTFLAG) DFLL Out Of Bounds */
#define SYSCTRL_INTFLAG_DFLLOOB     (0x1u << SYSCTRL_INTFLAG_DFLLOOB_Pos)
#define SYSCTRL_INTFLAG_DFLLLCKF_Pos 6            /**< \brief (SYSCTRL_INTFLAG) DFLL Lock Fine */
#define SYSCTRL_INTFLAG_DFLLLCKF    (0x1u << SYSCTRL_INTFLAG_DFLLLCKF_Pos)
#define SYSCTRL_INTFLAG_DFLLLCKC_Pos 7            /**< \brief (SYSCTRL_INTFLAG) DFLL Lock Coarse */
#define SYSCTRL_INTFLAG_DFLLLCKC    (0x1u << SYSCTRL_INTFLAG_DFLLLCKC_Pos)
#define SYSCTRL_INTFLAG_DFLLRCS_Pos 8            /**< \brief (SYSCTRL_INTFLAG) DFLL Reference Clock Stopped */
#define SYSCTRL_INTFLAG_DFLLRCS     (0x1u << SYSCTRL_INTFLAG_DFLLRCS_Pos)
#define SYSCTRL_INTFLAG_BOD33RDY_Pos 9            /**< \brief (SYSCTRL_INTFLAG) BOD33 Ready */
#define SYSCTRL_INTFLAG_BOD33RDY    (0x1u << SYSCTRL_INTFLAG_BOD33RDY_Pos)
#define SYSCTRL_INTFLAG_BOD33DET_Pos 10           /**< \brief (SYSCTRL_INTFLAG) BOD33 Detection */
#define SYSCTRL_INTFLAG_BOD33DET    (0x1u << SYSCTRL_INTFLAG_BOD33DET_Pos)
#define SYSCTRL_INTFLAG_B33SRDY_Pos 11           /**< \brief (SYSCTRL_INTFLAG) BOD33 Synchronization Ready */
#define SYSCTRL_INTFLAG_B33SRDY     (0x1u << SYSCTRL_INTFLAG_B33SRDY_Pos)
#define SYSCTRL_INTFLAG_BOD12RDY_Pos 12           /**< \brief (SYSCTRL_INTFLAG) BOD12 Ready */
#define SYSCTRL_INTFLAG_BOD12RDY    (0x1u << SYSCTRL_INTFLAG_BOD12RDY_Pos)
#define SYSCTRL_INTFLAG_BOD12DET_Pos 13           /**< \brief (SYSCTRL_INTFLAG) BOD12 Detection */
#define SYSCTRL_INTFLAG_BOD12DET    (0x1u << SYSCTRL_INTFLAG_BOD12DET_Pos)
#define SYSCTRL_INTFLAG_B12SRDY_Pos 14           /**< \brief (SYSCTRL_INTFLAG) BOD12 Synchronization Ready */
#define SYSCTRL_INTFLAG_B12SRDY     (0x1u << SYSCTRL_INTFLAG_B12SRDY_Pos)
#define SYSCTRL_INTFLAG_MASK        0x00007FFFu  /**< \brief (SYSCTRL_INTFLAG) MASK Register */

/* -------- SYSCTRL_PCLKSR : (SYSCTRL Offset: 0x0C) (R/  32) Power and Clocks Status Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t XOSCRDY:1;        /*!< bit:      0  XOSC Ready                         */
    uint32_t XOSC32KRDY:1;     /*!< bit:      1  XOSC32K Ready                      */
    uint32_t OSC32KRDY:1;      /*!< bit:      2  OSC32K Ready                       */
    uint32_t OSC8MRDY:1;       /*!< bit:      3  OSC8M Ready                        */
    uint32_t DFLLRDY:1;        /*!< bit:      4  DFLL Ready                         */
    uint32_t DFLLOOB:1;        /*!< bit:      5  DFLL Out Of Bounds                 */
    uint32_t DFLLLCKF:1;       /*!< bit:      6  DFLL Lock Fine                     */
    uint32_t DFLLLCKC:1;       /*!< bit:      7  DFLL Lock Coarse                   */
    uint32_t DFLLRCS:1;        /*!< bit:      8  DFLL Reference Clock Stopped       */
    uint32_t BOD33RDY:1;       /*!< bit:      9  BOD33 Ready                        */
    uint32_t BOD33DET:1;       /*!< bit:     10  BOD33 Detection                    */
    uint32_t B33SRDY:1;        /*!< bit:     11  BOD33 Synchronization Ready        */
    uint32_t BOD12RDY:1;       /*!< bit:     12  BOD12 Ready                        */
    uint32_t BOD12DET:1;       /*!< bit:     13  BOD12 Detection                    */
    uint32_t B12SRDY:1;        /*!< bit:     14  BOD12 Synchronization Ready        */
    uint32_t :17;              /*!< bit: 15..31  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} SYSCTRL_PCLKSR_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define SYSCTRL_PCLKSR_OFFSET       0x0C         /**< \brief (SYSCTRL_PCLKSR offset) Power and Clocks Status Register */
#define SYSCTRL_PCLKSR_RESETVALUE   0x00000000   /**< \brief (SYSCTRL_PCLKSR reset_value) Power and Clocks Status Register */

#define SYSCTRL_PCLKSR_XOSCRDY_Pos  0            /**< \brief (SYSCTRL_PCLKSR) XOSC Ready */
#define SYSCTRL_PCLKSR_XOSCRDY      (0x1u << SYSCTRL_PCLKSR_XOSCRDY_Pos)
#define SYSCTRL_PCLKSR_XOSC32KRDY_Pos 1            /**< \brief (SYSCTRL_PCLKSR) XOSC32K Ready */
#define SYSCTRL_PCLKSR_XOSC32KRDY   (0x1u << SYSCTRL_PCLKSR_XOSC32KRDY_Pos)
#define SYSCTRL_PCLKSR_OSC32KRDY_Pos 2            /**< \brief (SYSCTRL_PCLKSR) OSC32K Ready */
#define SYSCTRL_PCLKSR_OSC32KRDY    (0x1u << SYSCTRL_PCLKSR_OSC32KRDY_Pos)
#define SYSCTRL_PCLKSR_OSC8MRDY_Pos 3            /**< \brief (SYSCTRL_PCLKSR) OSC8M Ready */
#define SYSCTRL_PCLKSR_OSC8MRDY     (0x1u << SYSCTRL_PCLKSR_OSC8MRDY_Pos)
#define SYSCTRL_PCLKSR_DFLLRDY_Pos  4            /**< \brief (SYSCTRL_PCLKSR) DFLL Ready */
#define SYSCTRL_PCLKSR_DFLLRDY      (0x1u << SYSCTRL_PCLKSR_DFLLRDY_Pos)
#define SYSCTRL_PCLKSR_DFLLOOB_Pos  5            /**< \brief (SYSCTRL_PCLKSR) DFLL Out Of Bounds */
#define SYSCTRL_PCLKSR_DFLLOOB      (0x1u << SYSCTRL_PCLKSR_DFLLOOB_Pos)
#define SYSCTRL_PCLKSR_DFLLLCKF_Pos 6            /**< \brief (SYSCTRL_PCLKSR) DFLL Lock Fine */
#define SYSCTRL_PCLKSR_DFLLLCKF     (0x1u << SYSCTRL_PCLKSR_DFLLLCKF_Pos)
#define SYSCTRL_PCLKSR_DFLLLCKC_Pos 7            /**< \brief (SYSCTRL_PCLKSR) DFLL Lock Coarse */
#define SYSCTRL_PCLKSR_DFLLLCKC     (0x1u << SYSCTRL_PCLKSR_DFLLLCKC_Pos)
#define SYSCTRL_PCLKSR_DFLLRCS_Pos  8            /**< \brief (SYSCTRL_PCLKSR) DFLL Reference Clock Stopped */
#define SYSCTRL_PCLKSR_DFLLRCS      (0x1u << SYSCTRL_PCLKSR_DFLLRCS_Pos)
#define SYSCTRL_PCLKSR_BOD33RDY_Pos 9            /**< \brief (SYSCTRL_PCLKSR) BOD33 Ready */
#define SYSCTRL_PCLKSR_BOD33RDY     (0x1u << SYSCTRL_PCLKSR_BOD33RDY_Pos)
#define SYSCTRL_PCLKSR_BOD33DET_Pos 10           /**< \brief (SYSCTRL_PCLKSR) BOD33 Detection */
#define SYSCTRL_PCLKSR_BOD33DET     (0x1u << SYSCTRL_PCLKSR_BOD33DET_Pos)
#define SYSCTRL_PCLKSR_B33SRDY_Pos  11           /**< \brief (SYSCTRL_PCLKSR) BOD33 Synchronization Ready */
#define SYSCTRL_PCLKSR_B33SRDY      (0x1u << SYSCTRL_PCLKSR_B33SRDY_Pos)
#define SYSCTRL_PCLKSR_BOD12RDY_Pos 12           /**< \brief (SYSCTRL_PCLKSR) BOD12 Ready */
#define SYSCTRL_PCLKSR_BOD12RDY     (0x1u << SYSCTRL_PCLKSR_BOD12RDY_Pos)
#define SYSCTRL_PCLKSR_BOD12DET_Pos 13           /**< \brief (SYSCTRL_PCLKSR) BOD12 Detection */
#define SYSCTRL_PCLKSR_BOD12DET     (0x1u << SYSCTRL_PCLKSR_BOD12DET_Pos)
#define SYSCTRL_PCLKSR_B12SRDY_Pos  14           /**< \brief (SYSCTRL_PCLKSR) BOD12 Synchronization Ready */
#define SYSCTRL_PCLKSR_B12SRDY      (0x1u << SYSCTRL_PCLKSR_B12SRDY_Pos)
#define SYSCTRL_PCLKSR_MASK         0x00007FFFu  /**< \brief (SYSCTRL_PCLKSR) MASK Register */

/* -------- SYSCTRL_XOSC : (SYSCTRL Offset: 0x10) (R/W 16) XOSC Control Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint16_t :1;               /*!< bit:      0  Reserved                           */
    uint16_t ENABLE:1;         /*!< bit:      1  Enable                             */
    uint16_t XTALEN:1;         /*!< bit:      2  Crystal Oscillator Enable          */
    uint16_t :3;               /*!< bit:  3.. 5  Reserved                           */
    uint16_t RUNSTDBY:1;       /*!< bit:      6  Run during Standby                 */
    uint16_t ONDEMAND:1;       /*!< bit:      7  Enable on Demand                   */
    uint16_t GAIN:3;           /*!< bit:  8..10  Gain Value                         */
    uint16_t AMPGC:1;          /*!< bit:     11  Automatic Amplitude Gain Control   */
    uint16_t STARTUP:4;        /*!< bit: 12..15  Start-Up Time                      */
  } bit;                       /*!< Structure used for bit  access                  */
  uint16_t reg;                /*!< Type      used for register access              */
} SYSCTRL_XOSC_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define SYSCTRL_XOSC_OFFSET         0x10         /**< \brief (SYSCTRL_XOSC offset) XOSC Control Register */
#define SYSCTRL_XOSC_RESETVALUE     0x0080       /**< \brief (SYSCTRL_XOSC reset_value) XOSC Control Register */

#define SYSCTRL_XOSC_ENABLE_Pos     1            /**< \brief (SYSCTRL_XOSC) Enable */
#define SYSCTRL_XOSC_ENABLE         (0x1u << SYSCTRL_XOSC_ENABLE_Pos)
#define SYSCTRL_XOSC_XTALEN_Pos     2            /**< \brief (SYSCTRL_XOSC) Crystal Oscillator Enable */
#define SYSCTRL_XOSC_XTALEN         (0x1u << SYSCTRL_XOSC_XTALEN_Pos)
#define SYSCTRL_XOSC_RUNSTDBY_Pos   6            /**< \brief (SYSCTRL_XOSC) Run during Standby */
#define SYSCTRL_XOSC_RUNSTDBY       (0x1u << SYSCTRL_XOSC_RUNSTDBY_Pos)
#define SYSCTRL_XOSC_ONDEMAND_Pos   7            /**< \brief (SYSCTRL_XOSC) Enable on Demand */
#define SYSCTRL_XOSC_ONDEMAND       (0x1u << SYSCTRL_XOSC_ONDEMAND_Pos)
#define SYSCTRL_XOSC_GAIN_Pos       8            /**< \brief (SYSCTRL_XOSC) Gain Value */
#define SYSCTRL_XOSC_GAIN_Msk       (0x7u << SYSCTRL_XOSC_GAIN_Pos)
#define SYSCTRL_XOSC_GAIN(value)    ((SYSCTRL_XOSC_GAIN_Msk & ((value) << SYSCTRL_XOSC_GAIN_Pos)))
#define SYSCTRL_XOSC_AMPGC_Pos      11           /**< \brief (SYSCTRL_XOSC) Automatic Amplitude Gain Control */
#define SYSCTRL_XOSC_AMPGC          (0x1u << SYSCTRL_XOSC_AMPGC_Pos)
#define SYSCTRL_XOSC_STARTUP_Pos    12           /**< \brief (SYSCTRL_XOSC) Start-Up Time */
#define SYSCTRL_XOSC_STARTUP_Msk    (0xFu << SYSCTRL_XOSC_STARTUP_Pos)
#define SYSCTRL_XOSC_STARTUP(value) ((SYSCTRL_XOSC_STARTUP_Msk & ((value) << SYSCTRL_XOSC_STARTUP_Pos)))
#define SYSCTRL_XOSC_MASK           0xFFC6u      /**< \brief (SYSCTRL_XOSC) MASK Register */

/* -------- SYSCTRL_XOSC32K : (SYSCTRL Offset: 0x14) (R/W 16) XOSC32K Control Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint16_t :1;               /*!< bit:      0  Reserved                           */
    uint16_t ENABLE:1;         /*!< bit:      1  Enable                             */
    uint16_t XTALEN:1;         /*!< bit:      2  Crystal Oscillator Enable          */
    uint16_t EN32K:1;          /*!< bit:      3  32kHz Output Enable                */
    uint16_t EN1K:1;           /*!< bit:      4  1kHz Output Enable                 */
    uint16_t AAMPEN:1;         /*!< bit:      5  Automatic Amplitude Control Enable */
    uint16_t RUNSTDBY:1;       /*!< bit:      6  Run during Standby                 */
    uint16_t ONDEMAND:1;       /*!< bit:      7  Enable on Demand                   */
    uint16_t STARTUP:3;        /*!< bit:  8..10  Start-Up Time                      */
    uint16_t :1;               /*!< bit:     11  Reserved                           */
    uint16_t WRTLOCK:1;        /*!< bit:     12  Write Lock                         */
    uint16_t :3;               /*!< bit: 13..15  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint16_t reg;                /*!< Type      used for register access              */
} SYSCTRL_XOSC32K_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define SYSCTRL_XOSC32K_OFFSET      0x14         /**< \brief (SYSCTRL_XOSC32K offset) XOSC32K Control Register */
#define SYSCTRL_XOSC32K_RESETVALUE  0x0080       /**< \brief (SYSCTRL_XOSC32K reset_value) XOSC32K Control Register */

#define SYSCTRL_XOSC32K_ENABLE_Pos  1            /**< \brief (SYSCTRL_XOSC32K) Enable */
#define SYSCTRL_XOSC32K_ENABLE      (0x1u << SYSCTRL_XOSC32K_ENABLE_Pos)
#define SYSCTRL_XOSC32K_XTALEN_Pos  2            /**< \brief (SYSCTRL_XOSC32K) Crystal Oscillator Enable */
#define SYSCTRL_XOSC32K_XTALEN      (0x1u << SYSCTRL_XOSC32K_XTALEN_Pos)
#define SYSCTRL_XOSC32K_EN32K_Pos   3            /**< \brief (SYSCTRL_XOSC32K) 32kHz Output Enable */
#define SYSCTRL_XOSC32K_EN32K       (0x1u << SYSCTRL_XOSC32K_EN32K_Pos)
#define SYSCTRL_XOSC32K_EN1K_Pos    4            /**< \brief (SYSCTRL_XOSC32K) 1kHz Output Enable */
#define SYSCTRL_XOSC32K_EN1K        (0x1u << SYSCTRL_XOSC32K_EN1K_Pos)
#define SYSCTRL_XOSC32K_AAMPEN_Pos  5            /**< \brief (SYSCTRL_XOSC32K) Automatic Amplitude Control Enable */
#define SYSCTRL_XOSC32K_AAMPEN      (0x1u << SYSCTRL_XOSC32K_AAMPEN_Pos)
#define SYSCTRL_XOSC32K_RUNSTDBY_Pos 6            /**< \brief (SYSCTRL_XOSC32K) Run during Standby */
#define SYSCTRL_XOSC32K_RUNSTDBY    (0x1u << SYSCTRL_XOSC32K_RUNSTDBY_Pos)
#define SYSCTRL_XOSC32K_ONDEMAND_Pos 7            /**< \brief (SYSCTRL_XOSC32K) Enable on Demand */
#define SYSCTRL_XOSC32K_ONDEMAND    (0x1u << SYSCTRL_XOSC32K_ONDEMAND_Pos)
#define SYSCTRL_XOSC32K_STARTUP_Pos 8            /**< \brief (SYSCTRL_XOSC32K) Start-Up Time */
#define SYSCTRL_XOSC32K_STARTUP_Msk (0x7u << SYSCTRL_XOSC32K_STARTUP_Pos)
#define SYSCTRL_XOSC32K_STARTUP(value) ((SYSCTRL_XOSC32K_STARTUP_Msk & ((value) << SYSCTRL_XOSC32K_STARTUP_Pos)))
#define SYSCTRL_XOSC32K_WRTLOCK_Pos 12           /**< \brief (SYSCTRL_XOSC32K) Write Lock */
#define SYSCTRL_XOSC32K_WRTLOCK     (0x1u << SYSCTRL_XOSC32K_WRTLOCK_Pos)
#define SYSCTRL_XOSC32K_MASK        0x17FEu      /**< \brief (SYSCTRL_XOSC32K) MASK Register */

/* -------- SYSCTRL_OSC32K : (SYSCTRL Offset: 0x18) (R/W 32) OSC32K Control Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t :1;               /*!< bit:      0  Reserved                           */
    uint32_t ENABLE:1;         /*!< bit:      1  Enable                             */
    uint32_t EN32K:1;          /*!< bit:      2  32kHz Output Enable                */
    uint32_t EN1K:1;           /*!< bit:      3  1kHz Output Enable                 */
    uint32_t :2;               /*!< bit:  4.. 5  Reserved                           */
    uint32_t RUNSTDBY:1;       /*!< bit:      6  Run during Standby                 */
    uint32_t ONDEMAND:1;       /*!< bit:      7  Enable on Demand                   */
    uint32_t STARTUP:3;        /*!< bit:  8..10  Start-Up Time                      */
    uint32_t :1;               /*!< bit:     11  Reserved                           */
    uint32_t WRTLOCK:1;        /*!< bit:     12  Write Lock                         */
    uint32_t :3;               /*!< bit: 13..15  Reserved                           */
    uint32_t CALIB:7;          /*!< bit: 16..22  Calibration Value                  */
    uint32_t :9;               /*!< bit: 23..31  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} SYSCTRL_OSC32K_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define SYSCTRL_OSC32K_OFFSET       0x18         /**< \brief (SYSCTRL_OSC32K offset) OSC32K Control Register */
#define SYSCTRL_OSC32K_RESETVALUE   0x003F0080   /**< \brief (SYSCTRL_OSC32K reset_value) OSC32K Control Register */

#define SYSCTRL_OSC32K_ENABLE_Pos   1            /**< \brief (SYSCTRL_OSC32K) Enable */
#define SYSCTRL_OSC32K_ENABLE       (0x1u << SYSCTRL_OSC32K_ENABLE_Pos)
#define SYSCTRL_OSC32K_EN32K_Pos    2            /**< \brief (SYSCTRL_OSC32K) 32kHz Output Enable */
#define SYSCTRL_OSC32K_EN32K        (0x1u << SYSCTRL_OSC32K_EN32K_Pos)
#define SYSCTRL_OSC32K_EN1K_Pos     3            /**< \brief (SYSCTRL_OSC32K) 1kHz Output Enable */
#define SYSCTRL_OSC32K_EN1K         (0x1u << SYSCTRL_OSC32K_EN1K_Pos)
#define SYSCTRL_OSC32K_RUNSTDBY_Pos 6            /**< \brief (SYSCTRL_OSC32K) Run during Standby */
#define SYSCTRL_OSC32K_RUNSTDBY     (0x1u << SYSCTRL_OSC32K_RUNSTDBY_Pos)
#define SYSCTRL_OSC32K_ONDEMAND_Pos 7            /**< \brief (SYSCTRL_OSC32K) Enable on Demand */
#define SYSCTRL_OSC32K_ONDEMAND     (0x1u << SYSCTRL_OSC32K_ONDEMAND_Pos)
#define SYSCTRL_OSC32K_STARTUP_Pos  8            /**< \brief (SYSCTRL_OSC32K) Start-Up Time */
#define SYSCTRL_OSC32K_STARTUP_Msk  (0x7u << SYSCTRL_OSC32K_STARTUP_Pos)
#define SYSCTRL_OSC32K_STARTUP(value) ((SYSCTRL_OSC32K_STARTUP_Msk & ((value) << SYSCTRL_OSC32K_STARTUP_Pos)))
#define SYSCTRL_OSC32K_WRTLOCK_Pos  12           /**< \brief (SYSCTRL_OSC32K) Write Lock */
#define SYSCTRL_OSC32K_WRTLOCK      (0x1u << SYSCTRL_OSC32K_WRTLOCK_Pos)
#define SYSCTRL_OSC32K_CALIB_Pos    16           /**< \brief (SYSCTRL_OSC32K) Calibration Value */
#define SYSCTRL_OSC32K_CALIB_Msk    (0x7Fu << SYSCTRL_OSC32K_CALIB_Pos)
#define SYSCTRL_OSC32K_CALIB(value) ((SYSCTRL_OSC32K_CALIB_Msk & ((value) << SYSCTRL_OSC32K_CALIB_Pos)))
#define SYSCTRL_OSC32K_MASK         0x007F17CEu  /**< \brief (SYSCTRL_OSC32K) MASK Register */

/* -------- SYSCTRL_OSCULP32K : (SYSCTRL Offset: 0x1C) (R/W  8) OSCULP32K Control Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  CALIB:5;          /*!< bit:  0.. 4  Calibration Value                  */
    uint8_t  :2;               /*!< bit:  5.. 6  Reserved                           */
    uint8_t  WRTLOCK:1;        /*!< bit:      7  Write Lock                         */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} SYSCTRL_OSCULP32K_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define SYSCTRL_OSCULP32K_OFFSET    0x1C         /**< \brief (SYSCTRL_OSCULP32K offset) OSCULP32K Control Register */
#define SYSCTRL_OSCULP32K_RESETVALUE 0x0F         /**< \brief (SYSCTRL_OSCULP32K reset_value) OSCULP32K Control Register */

#define SYSCTRL_OSCULP32K_CALIB_Pos 0            /**< \brief (SYSCTRL_OSCULP32K) Calibration Value */
#define SYSCTRL_OSCULP32K_CALIB_Msk (0x1Fu << SYSCTRL_OSCULP32K_CALIB_Pos)
#define SYSCTRL_OSCULP32K_CALIB(value) ((SYSCTRL_OSCULP32K_CALIB_Msk & ((value) << SYSCTRL_OSCULP32K_CALIB_Pos)))
#define SYSCTRL_OSCULP32K_WRTLOCK_Pos 7            /**< \brief (SYSCTRL_OSCULP32K) Write Lock */
#define SYSCTRL_OSCULP32K_WRTLOCK   (0x1u << SYSCTRL_OSCULP32K_WRTLOCK_Pos)
#define SYSCTRL_OSCULP32K_MASK      0x9Fu        /**< \brief (SYSCTRL_OSCULP32K) MASK Register */

/* -------- SYSCTRL_OSC8M : (SYSCTRL Offset: 0x20) (R/W 32) OSC8M Control Register A -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t :1;               /*!< bit:      0  Reserved                           */
    uint32_t ENABLE:1;         /*!< bit:      1  Enable                             */
    uint32_t :4;               /*!< bit:  2.. 5  Reserved                           */
    uint32_t RUNSTDBY:1;       /*!< bit:      6  Run during Standby                 */
    uint32_t ONDEMAND:1;       /*!< bit:      7  Enable on Demand                   */
    uint32_t PRESC:2;          /*!< bit:  8.. 9  Prescaler Select                   */
    uint32_t :6;               /*!< bit: 10..15  Reserved                           */
    uint32_t CALIB:12;         /*!< bit: 16..27  Calibration Value                  */
    uint32_t :2;               /*!< bit: 28..29  Reserved                           */
    uint32_t FRANGE:2;         /*!< bit: 30..31  Frequency Range                    */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} SYSCTRL_OSC8M_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define SYSCTRL_OSC8M_OFFSET        0x20         /**< \brief (SYSCTRL_OSC8M offset) OSC8M Control Register A */
#define SYSCTRL_OSC8M_RESETVALUE    0x00000080   /**< \brief (SYSCTRL_OSC8M reset_value) OSC8M Control Register A */

#define SYSCTRL_OSC8M_ENABLE_Pos    1            /**< \brief (SYSCTRL_OSC8M) Enable */
#define SYSCTRL_OSC8M_ENABLE        (0x1u << SYSCTRL_OSC8M_ENABLE_Pos)
#define SYSCTRL_OSC8M_RUNSTDBY_Pos  6            /**< \brief (SYSCTRL_OSC8M) Run during Standby */
#define SYSCTRL_OSC8M_RUNSTDBY      (0x1u << SYSCTRL_OSC8M_RUNSTDBY_Pos)
#define SYSCTRL_OSC8M_ONDEMAND_Pos  7            /**< \brief (SYSCTRL_OSC8M) Enable on Demand */
#define SYSCTRL_OSC8M_ONDEMAND      (0x1u << SYSCTRL_OSC8M_ONDEMAND_Pos)
#define SYSCTRL_OSC8M_PRESC_Pos     8            /**< \brief (SYSCTRL_OSC8M) Prescaler Select */
#define SYSCTRL_OSC8M_PRESC_Msk     (0x3u << SYSCTRL_OSC8M_PRESC_Pos)
#define SYSCTRL_OSC8M_PRESC(value)  ((SYSCTRL_OSC8M_PRESC_Msk & ((value) << SYSCTRL_OSC8M_PRESC_Pos)))
#define SYSCTRL_OSC8M_CALIB_Pos     16           /**< \brief (SYSCTRL_OSC8M) Calibration Value */
#define SYSCTRL_OSC8M_CALIB_Msk     (0xFFFu << SYSCTRL_OSC8M_CALIB_Pos)
#define SYSCTRL_OSC8M_CALIB(value)  ((SYSCTRL_OSC8M_CALIB_Msk & ((value) << SYSCTRL_OSC8M_CALIB_Pos)))
#define SYSCTRL_OSC8M_FRANGE_Pos    30           /**< \brief (SYSCTRL_OSC8M) Frequency Range */
#define SYSCTRL_OSC8M_FRANGE_Msk    (0x3u << SYSCTRL_OSC8M_FRANGE_Pos)
#define SYSCTRL_OSC8M_FRANGE(value) ((SYSCTRL_OSC8M_FRANGE_Msk & ((value) << SYSCTRL_OSC8M_FRANGE_Pos)))
#define SYSCTRL_OSC8M_MASK          0xCFFF03C2u  /**< \brief (SYSCTRL_OSC8M) MASK Register */

/* -------- SYSCTRL_DFLLCTRL : (SYSCTRL Offset: 0x24) (R/W 16) DFLL Config Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint16_t :1;               /*!< bit:      0  Reserved                           */
    uint16_t ENABLE:1;         /*!< bit:      1  Enable                             */
    uint16_t MODE:1;           /*!< bit:      2  Mode Selection                     */
    uint16_t STABLE:1;         /*!< bit:      3  Stable Frequency                   */
    uint16_t LLAW:1;           /*!< bit:      4  Lose Lock After Wake               */
    uint16_t USBCRM:1;         /*!< bit:      5  USB Clock Recovery Mode            */
    uint16_t RUNSTDBY:1;       /*!< bit:      6  Run during Standby                 */
    uint16_t ONDEMAND:1;       /*!< bit:      7  Enable on Demand                   */
    uint16_t CCDIS:1;          /*!< bit:      8  Chill Cycle Disable                */
    uint16_t QLDIS:1;          /*!< bit:      9  Quick Lock Disable                 */
    uint16_t :6;               /*!< bit: 10..15  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint16_t reg;                /*!< Type      used for register access              */
} SYSCTRL_DFLLCTRL_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define SYSCTRL_DFLLCTRL_OFFSET     0x24         /**< \brief (SYSCTRL_DFLLCTRL offset) DFLL Config Register */
#define SYSCTRL_DFLLCTRL_RESETVALUE 0x0080       /**< \brief (SYSCTRL_DFLLCTRL reset_value) DFLL Config Register */

#define SYSCTRL_DFLLCTRL_ENABLE_Pos 1            /**< \brief (SYSCTRL_DFLLCTRL) Enable */
#define SYSCTRL_DFLLCTRL_ENABLE     (0x1u << SYSCTRL_DFLLCTRL_ENABLE_Pos)
#define SYSCTRL_DFLLCTRL_MODE_Pos   2            /**< \brief (SYSCTRL_DFLLCTRL) Mode Selection */
#define SYSCTRL_DFLLCTRL_MODE       (0x1u << SYSCTRL_DFLLCTRL_MODE_Pos)
#define SYSCTRL_DFLLCTRL_STABLE_Pos 3            /**< \brief (SYSCTRL_DFLLCTRL) Stable Frequency */
#define SYSCTRL_DFLLCTRL_STABLE     (0x1u << SYSCTRL_DFLLCTRL_STABLE_Pos)
#define SYSCTRL_DFLLCTRL_LLAW_Pos   4            /**< \brief (SYSCTRL_DFLLCTRL) Lose Lock After Wake */
#define SYSCTRL_DFLLCTRL_LLAW       (0x1u << SYSCTRL_DFLLCTRL_LLAW_Pos)
#define SYSCTRL_DFLLCTRL_USBCRM_Pos 5            /**< \brief (SYSCTRL_DFLLCTRL) USB Clock Recovery Mode */
#define SYSCTRL_DFLLCTRL_USBCRM     (0x1u << SYSCTRL_DFLLCTRL_USBCRM_Pos)
#define SYSCTRL_DFLLCTRL_RUNSTDBY_Pos 6            /**< \brief (SYSCTRL_DFLLCTRL) Run during Standby */
#define SYSCTRL_DFLLCTRL_RUNSTDBY   (0x1u << SYSCTRL_DFLLCTRL_RUNSTDBY_Pos)
#define SYSCTRL_DFLLCTRL_ONDEMAND_Pos 7            /**< \brief (SYSCTRL_DFLLCTRL) Enable on Demand */
#define SYSCTRL_DFLLCTRL_ONDEMAND   (0x1u << SYSCTRL_DFLLCTRL_ONDEMAND_Pos)
#define SYSCTRL_DFLLCTRL_CCDIS_Pos  8            /**< \brief (SYSCTRL_DFLLCTRL) Chill Cycle Disable */
#define SYSCTRL_DFLLCTRL_CCDIS      (0x1u << SYSCTRL_DFLLCTRL_CCDIS_Pos)
#define SYSCTRL_DFLLCTRL_QLDIS_Pos  9            /**< \brief (SYSCTRL_DFLLCTRL) Quick Lock Disable */
#define SYSCTRL_DFLLCTRL_QLDIS      (0x1u << SYSCTRL_DFLLCTRL_QLDIS_Pos)
#define SYSCTRL_DFLLCTRL_MASK       0x03FEu      /**< \brief (SYSCTRL_DFLLCTRL) MASK Register */

/* -------- SYSCTRL_DFLLVAL : (SYSCTRL Offset: 0x28) (R/W 32) DFLL Calibration Value Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t FINE:8;           /*!< bit:  0.. 7  Fine Calibration Value             */
    uint32_t COARSE:5;         /*!< bit:  8..12  Coarse Calibration Value           */
    uint32_t :3;               /*!< bit: 13..15  Reserved                           */
    uint32_t DIFF:16;          /*!< bit: 16..31  Multiplication Ratio Difference    */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} SYSCTRL_DFLLVAL_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define SYSCTRL_DFLLVAL_OFFSET      0x28         /**< \brief (SYSCTRL_DFLLVAL offset) DFLL Calibration Value Register */
#define SYSCTRL_DFLLVAL_RESETVALUE  0x00000000   /**< \brief (SYSCTRL_DFLLVAL reset_value) DFLL Calibration Value Register */

#define SYSCTRL_DFLLVAL_FINE_Pos    0            /**< \brief (SYSCTRL_DFLLVAL) Fine Calibration Value */
#define SYSCTRL_DFLLVAL_FINE_Msk    (0xFFu << SYSCTRL_DFLLVAL_FINE_Pos)
#define SYSCTRL_DFLLVAL_FINE(value) ((SYSCTRL_DFLLVAL_FINE_Msk & ((value) << SYSCTRL_DFLLVAL_FINE_Pos)))
#define SYSCTRL_DFLLVAL_COARSE_Pos  8            /**< \brief (SYSCTRL_DFLLVAL) Coarse Calibration Value */
#define SYSCTRL_DFLLVAL_COARSE_Msk  (0x1Fu << SYSCTRL_DFLLVAL_COARSE_Pos)
#define SYSCTRL_DFLLVAL_COARSE(value) ((SYSCTRL_DFLLVAL_COARSE_Msk & ((value) << SYSCTRL_DFLLVAL_COARSE_Pos)))
#define SYSCTRL_DFLLVAL_DIFF_Pos    16           /**< \brief (SYSCTRL_DFLLVAL) Multiplication Ratio Difference */
#define SYSCTRL_DFLLVAL_DIFF_Msk    (0xFFFFu << SYSCTRL_DFLLVAL_DIFF_Pos)
#define SYSCTRL_DFLLVAL_DIFF(value) ((SYSCTRL_DFLLVAL_DIFF_Msk & ((value) << SYSCTRL_DFLLVAL_DIFF_Pos)))
#define SYSCTRL_DFLLVAL_MASK        0xFFFF1FFFu  /**< \brief (SYSCTRL_DFLLVAL) MASK Register */

/* -------- SYSCTRL_DFLLMUL : (SYSCTRL Offset: 0x2C) (R/W 32) DFLL Multiplier Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t MUL:16;           /*!< bit:  0..15  Multiplication Value               */
    uint32_t FSTEP:8;          /*!< bit: 16..23  Maximum Fine Step Size             */
    uint32_t CSTEP:5;          /*!< bit: 24..28  Maximum Coarse Step Size           */
    uint32_t :3;               /*!< bit: 29..31  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} SYSCTRL_DFLLMUL_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define SYSCTRL_DFLLMUL_OFFSET      0x2C         /**< \brief (SYSCTRL_DFLLMUL offset) DFLL Multiplier Register */
#define SYSCTRL_DFLLMUL_RESETVALUE  0x00000000   /**< \brief (SYSCTRL_DFLLMUL reset_value) DFLL Multiplier Register */

#define SYSCTRL_DFLLMUL_MUL_Pos     0            /**< \brief (SYSCTRL_DFLLMUL) Multiplication Value */
#define SYSCTRL_DFLLMUL_MUL_Msk     (0xFFFFu << SYSCTRL_DFLLMUL_MUL_Pos)
#define SYSCTRL_DFLLMUL_MUL(value)  ((SYSCTRL_DFLLMUL_MUL_Msk & ((value) << SYSCTRL_DFLLMUL_MUL_Pos)))
#define SYSCTRL_DFLLMUL_FSTEP_Pos   16           /**< \brief (SYSCTRL_DFLLMUL) Maximum Fine Step Size */
#define SYSCTRL_DFLLMUL_FSTEP_Msk   (0xFFu << SYSCTRL_DFLLMUL_FSTEP_Pos)
#define SYSCTRL_DFLLMUL_FSTEP(value) ((SYSCTRL_DFLLMUL_FSTEP_Msk & ((value) << SYSCTRL_DFLLMUL_FSTEP_Pos)))
#define SYSCTRL_DFLLMUL_CSTEP_Pos   24           /**< \brief (SYSCTRL_DFLLMUL) Maximum Coarse Step Size */
#define SYSCTRL_DFLLMUL_CSTEP_Msk   (0x1Fu << SYSCTRL_DFLLMUL_CSTEP_Pos)
#define SYSCTRL_DFLLMUL_CSTEP(value) ((SYSCTRL_DFLLMUL_CSTEP_Msk & ((value) << SYSCTRL_DFLLMUL_CSTEP_Pos)))
#define SYSCTRL_DFLLMUL_MASK        0x1FFFFFFFu  /**< \brief (SYSCTRL_DFLLMUL) MASK Register */

/* -------- SYSCTRL_DFLLSYNC : (SYSCTRL Offset: 0x30) (R/W  8) DFLL Synchronization Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  :7;               /*!< bit:  0.. 6  Reserved                           */
    uint8_t  READREQ:1;        /*!< bit:      7  Read Request Synchronization       */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} SYSCTRL_DFLLSYNC_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define SYSCTRL_DFLLSYNC_OFFSET     0x30         /**< \brief (SYSCTRL_DFLLSYNC offset) DFLL Synchronization Register */
#define SYSCTRL_DFLLSYNC_RESETVALUE 0x00         /**< \brief (SYSCTRL_DFLLSYNC reset_value) DFLL Synchronization Register */

#define SYSCTRL_DFLLSYNC_READREQ_Pos 7            /**< \brief (SYSCTRL_DFLLSYNC) Read Request Synchronization */
#define SYSCTRL_DFLLSYNC_READREQ    (0x1u << SYSCTRL_DFLLSYNC_READREQ_Pos)
#define SYSCTRL_DFLLSYNC_MASK       0x80u        /**< \brief (SYSCTRL_DFLLSYNC) MASK Register */

/* -------- SYSCTRL_BOD33 : (SYSCTRL Offset: 0x34) (R/W 32) BOD33 Control Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t :1;               /*!< bit:      0  Reserved                           */
    uint32_t ENABLE:1;         /*!< bit:      1  Enable                             */
    uint32_t HYST:1;           /*!< bit:      2  Hysteresis Enable                  */
    uint32_t ACTION:2;         /*!< bit:  3.. 4  Action when Threshold Crossed      */
    uint32_t :1;               /*!< bit:      5  Reserved                           */
    uint32_t RUNSTDBY:1;       /*!< bit:      6  Run during Standby                 */
    uint32_t :1;               /*!< bit:      7  Reserved                           */
    uint32_t MODE:1;           /*!< bit:      8  Operation Modes                    */
    uint32_t CEN:1;            /*!< bit:      9  Clock Enable                       */
    uint32_t :2;               /*!< bit: 10..11  Reserved                           */
    uint32_t PSEL:4;           /*!< bit: 12..15  Prescaler Select                   */
    uint32_t LEVEL:6;          /*!< bit: 16..21  Threshold Level                    */
    uint32_t :10;              /*!< bit: 22..31  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} SYSCTRL_BOD33_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define SYSCTRL_BOD33_OFFSET        0x34         /**< \brief (SYSCTRL_BOD33 offset) BOD33 Control Register */

#define SYSCTRL_BOD33_ENABLE_Pos    1            /**< \brief (SYSCTRL_BOD33) Enable */
#define SYSCTRL_BOD33_ENABLE        (0x1u << SYSCTRL_BOD33_ENABLE_Pos)
#define SYSCTRL_BOD33_HYST_Pos      2            /**< \brief (SYSCTRL_BOD33) Hysteresis Enable */
#define SYSCTRL_BOD33_HYST          (0x1u << SYSCTRL_BOD33_HYST_Pos)
#define SYSCTRL_BOD33_ACTION_Pos    3            /**< \brief (SYSCTRL_BOD33) Action when Threshold Crossed */
#define SYSCTRL_BOD33_ACTION_Msk    (0x3u << SYSCTRL_BOD33_ACTION_Pos)
#define SYSCTRL_BOD33_ACTION(value) ((SYSCTRL_BOD33_ACTION_Msk & ((value) << SYSCTRL_BOD33_ACTION_Pos)))
#define SYSCTRL_BOD33_RUNSTDBY_Pos  6            /**< \brief (SYSCTRL_BOD33) Run during Standby */
#define SYSCTRL_BOD33_RUNSTDBY      (0x1u << SYSCTRL_BOD33_RUNSTDBY_Pos)
#define SYSCTRL_BOD33_MODE_Pos      8            /**< \brief (SYSCTRL_BOD33) Operation Modes */
#define SYSCTRL_BOD33_MODE          (0x1u << SYSCTRL_BOD33_MODE_Pos)
#define SYSCTRL_BOD33_CEN_Pos       9            /**< \brief (SYSCTRL_BOD33) Clock Enable */
#define SYSCTRL_BOD33_CEN           (0x1u << SYSCTRL_BOD33_CEN_Pos)
#define SYSCTRL_BOD33_PSEL_Pos      12           /**< \brief (SYSCTRL_BOD33) Prescaler Select */
#define SYSCTRL_BOD33_PSEL_Msk      (0xFu << SYSCTRL_BOD33_PSEL_Pos)
#define SYSCTRL_BOD33_PSEL(value)   ((SYSCTRL_BOD33_PSEL_Msk & ((value) << SYSCTRL_BOD33_PSEL_Pos)))
#define SYSCTRL_BOD33_LEVEL_Pos     16           /**< \brief (SYSCTRL_BOD33) Threshold Level */
#define SYSCTRL_BOD33_LEVEL_Msk     (0x3Fu << SYSCTRL_BOD33_LEVEL_Pos)
#define SYSCTRL_BOD33_LEVEL(value)  ((SYSCTRL_BOD33_LEVEL_Msk & ((value) << SYSCTRL_BOD33_LEVEL_Pos)))
#define SYSCTRL_BOD33_MASK          0x003FF35Eu  /**< \brief (SYSCTRL_BOD33) MASK Register */

/* -------- SYSCTRL_BOD12 : (SYSCTRL Offset: 0x38) (R/W 32) BOD12 Control Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t :1;               /*!< bit:      0  Reserved                           */
    uint32_t ENABLE:1;         /*!< bit:      1  Enable                             */
    uint32_t HYST:1;           /*!< bit:      2  Hysteresis Enable                  */
    uint32_t ACTION:2;         /*!< bit:  3.. 4  Action when Threshold Crossed      */
    uint32_t :1;               /*!< bit:      5  Reserved                           */
    uint32_t RUNSTDBY:1;       /*!< bit:      6  Run during Standby                 */
    uint32_t :1;               /*!< bit:      7  Reserved                           */
    uint32_t MODE:1;           /*!< bit:      8  Operation Modes                    */
    uint32_t CEN:1;            /*!< bit:      9  Clock Enable                       */
    uint32_t :2;               /*!< bit: 10..11  Reserved                           */
    uint32_t PSEL:4;           /*!< bit: 12..15  Prescaler Select                   */
    uint32_t LEVEL:5;          /*!< bit: 16..20  Threshold Level                    */
    uint32_t :11;              /*!< bit: 21..31  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} SYSCTRL_BOD12_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define SYSCTRL_BOD12_OFFSET        0x38         /**< \brief (SYSCTRL_BOD12 offset) BOD12 Control Register */

#define SYSCTRL_BOD12_ENABLE_Pos    1            /**< \brief (SYSCTRL_BOD12) Enable */
#define SYSCTRL_BOD12_ENABLE        (0x1u << SYSCTRL_BOD12_ENABLE_Pos)
#define SYSCTRL_BOD12_HYST_Pos      2            /**< \brief (SYSCTRL_BOD12) Hysteresis Enable */
#define SYSCTRL_BOD12_HYST          (0x1u << SYSCTRL_BOD12_HYST_Pos)
#define SYSCTRL_BOD12_ACTION_Pos    3            /**< \brief (SYSCTRL_BOD12) Action when Threshold Crossed */
#define SYSCTRL_BOD12_ACTION_Msk    (0x3u << SYSCTRL_BOD12_ACTION_Pos)
#define SYSCTRL_BOD12_ACTION(value) ((SYSCTRL_BOD12_ACTION_Msk & ((value) << SYSCTRL_BOD12_ACTION_Pos)))
#define SYSCTRL_BOD12_RUNSTDBY_Pos  6            /**< \brief (SYSCTRL_BOD12) Run during Standby */
#define SYSCTRL_BOD12_RUNSTDBY      (0x1u << SYSCTRL_BOD12_RUNSTDBY_Pos)
#define SYSCTRL_BOD12_MODE_Pos      8            /**< \brief (SYSCTRL_BOD12) Operation Modes */
#define SYSCTRL_BOD12_MODE          (0x1u << SYSCTRL_BOD12_MODE_Pos)
#define SYSCTRL_BOD12_CEN_Pos       9            /**< \brief (SYSCTRL_BOD12) Clock Enable */
#define SYSCTRL_BOD12_CEN           (0x1u << SYSCTRL_BOD12_CEN_Pos)
#define SYSCTRL_BOD12_PSEL_Pos      12           /**< \brief (SYSCTRL_BOD12) Prescaler Select */
#define SYSCTRL_BOD12_PSEL_Msk      (0xFu << SYSCTRL_BOD12_PSEL_Pos)
#define SYSCTRL_BOD12_PSEL(value)   ((SYSCTRL_BOD12_PSEL_Msk & ((value) << SYSCTRL_BOD12_PSEL_Pos)))
#define SYSCTRL_BOD12_LEVEL_Pos     16           /**< \brief (SYSCTRL_BOD12) Threshold Level */
#define SYSCTRL_BOD12_LEVEL_Msk     (0x1Fu << SYSCTRL_BOD12_LEVEL_Pos)
#define SYSCTRL_BOD12_LEVEL(value)  ((SYSCTRL_BOD12_LEVEL_Msk & ((value) << SYSCTRL_BOD12_LEVEL_Pos)))
#define SYSCTRL_BOD12_MASK          0x001FF35Eu  /**< \brief (SYSCTRL_BOD12) MASK Register */

/* -------- SYSCTRL_VREG : (SYSCTRL Offset: 0x3C) (R/W 16) VREG Control Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint16_t :1;               /*!< bit:      0  Reserved                           */
    uint16_t ENABLE:1;         /*!< bit:      1  Enable                             */
    uint16_t :2;               /*!< bit:  2.. 3  Reserved                           */
    uint16_t VDDMON:2;         /*!< bit:  4.. 5  Enable reset on core supply failure */
    uint16_t RUNSTDBY:1;       /*!< bit:      6  Run during Standby                 */
    uint16_t :1;               /*!< bit:      7  Reserved                           */
    uint16_t LEVEL:3;          /*!< bit:  8..10  Output Voltage Level               */
    uint16_t :1;               /*!< bit:     11  Reserved                           */
    uint16_t CALIB:3;          /*!< bit: 12..14  Calibration Value                  */
    uint16_t :1;               /*!< bit:     15  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint16_t reg;                /*!< Type      used for register access              */
} SYSCTRL_VREG_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define SYSCTRL_VREG_OFFSET         0x3C         /**< \brief (SYSCTRL_VREG offset) VREG Control Register */
#define SYSCTRL_VREG_RESETVALUE     0x0000       /**< \brief (SYSCTRL_VREG reset_value) VREG Control Register */

#define SYSCTRL_VREG_ENABLE_Pos     1            /**< \brief (SYSCTRL_VREG) Enable */
#define SYSCTRL_VREG_ENABLE         (0x1u << SYSCTRL_VREG_ENABLE_Pos)
#define SYSCTRL_VREG_VDDMON_Pos     4            /**< \brief (SYSCTRL_VREG) Enable reset on core supply failure */
#define SYSCTRL_VREG_VDDMON_Msk     (0x3u << SYSCTRL_VREG_VDDMON_Pos)
#define SYSCTRL_VREG_VDDMON(value)  ((SYSCTRL_VREG_VDDMON_Msk & ((value) << SYSCTRL_VREG_VDDMON_Pos)))
#define SYSCTRL_VREG_RUNSTDBY_Pos   6            /**< \brief (SYSCTRL_VREG) Run during Standby */
#define SYSCTRL_VREG_RUNSTDBY       (0x1u << SYSCTRL_VREG_RUNSTDBY_Pos)
#define SYSCTRL_VREG_LEVEL_Pos      8            /**< \brief (SYSCTRL_VREG) Output Voltage Level */
#define SYSCTRL_VREG_LEVEL_Msk      (0x7u << SYSCTRL_VREG_LEVEL_Pos)
#define SYSCTRL_VREG_LEVEL(value)   ((SYSCTRL_VREG_LEVEL_Msk & ((value) << SYSCTRL_VREG_LEVEL_Pos)))
#define SYSCTRL_VREG_CALIB_Pos      12           /**< \brief (SYSCTRL_VREG) Calibration Value */
#define SYSCTRL_VREG_CALIB_Msk      (0x7u << SYSCTRL_VREG_CALIB_Pos)
#define SYSCTRL_VREG_CALIB(value)   ((SYSCTRL_VREG_CALIB_Msk & ((value) << SYSCTRL_VREG_CALIB_Pos)))
#define SYSCTRL_VREG_MASK           0x7772u      /**< \brief (SYSCTRL_VREG) MASK Register */

/* -------- SYSCTRL_VREF : (SYSCTRL Offset: 0x40) (R/W 32) VREF Control Register A -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t :1;               /*!< bit:      0  Reserved                           */
    uint32_t TSEN:1;           /*!< bit:      1  Temperature Sensor Output Enable   */
    uint32_t BGOUTEN:1;        /*!< bit:      2  Bandgap Output Enable              */
    uint32_t :13;              /*!< bit:  3..15  Reserved                           */
    uint32_t CALIB:11;         /*!< bit: 16..26  Voltage Reference Calibration Value */
    uint32_t :5;               /*!< bit: 27..31  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} SYSCTRL_VREF_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define SYSCTRL_VREF_OFFSET         0x40         /**< \brief (SYSCTRL_VREF offset) VREF Control Register A */
#define SYSCTRL_VREF_RESETVALUE     0x00000000   /**< \brief (SYSCTRL_VREF reset_value) VREF Control Register A */

#define SYSCTRL_VREF_TSEN_Pos       1            /**< \brief (SYSCTRL_VREF) Temperature Sensor Output Enable */
#define SYSCTRL_VREF_TSEN           (0x1u << SYSCTRL_VREF_TSEN_Pos)
#define SYSCTRL_VREF_BGOUTEN_Pos    2            /**< \brief (SYSCTRL_VREF) Bandgap Output Enable */
#define SYSCTRL_VREF_BGOUTEN        (0x1u << SYSCTRL_VREF_BGOUTEN_Pos)
#define SYSCTRL_VREF_CALIB_Pos      16           /**< \brief (SYSCTRL_VREF) Voltage Reference Calibration Value */
#define SYSCTRL_VREF_CALIB_Msk      (0x7FFu << SYSCTRL_VREF_CALIB_Pos)
#define SYSCTRL_VREF_CALIB(value)   ((SYSCTRL_VREF_CALIB_Msk & ((value) << SYSCTRL_VREF_CALIB_Pos)))
#define SYSCTRL_VREF_MASK           0x07FF0006u  /**< \brief (SYSCTRL_VREF) MASK Register */

/** \brief SYSCTRL hardware registers */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef struct {
  __IO SYSCTRL_INTENCLR_Type     INTENCLR;    /**< \brief Offset: 0x00 (R/W 32) Interrupt Enable Clear Register */
  __IO SYSCTRL_INTENSET_Type     INTENSET;    /**< \brief Offset: 0x04 (R/W 32) Interrupt Enable Set Register */
  __IO SYSCTRL_INTFLAG_Type      INTFLAG;     /**< \brief Offset: 0x08 (R/W 32) Interrupt Flag Status and Clear Register */
  __I  SYSCTRL_PCLKSR_Type       PCLKSR;      /**< \brief Offset: 0x0C (R/  32) Power and Clocks Status Register */
  __IO SYSCTRL_XOSC_Type         XOSC;        /**< \brief Offset: 0x10 (R/W 16) XOSC Control Register */
       RoReg8                    Reserved1[0x2];
  __IO SYSCTRL_XOSC32K_Type      XOSC32K;     /**< \brief Offset: 0x14 (R/W 16) XOSC32K Control Register */
       RoReg8                    Reserved2[0x2];
  __IO SYSCTRL_OSC32K_Type       OSC32K;      /**< \brief Offset: 0x18 (R/W 32) OSC32K Control Register */
  __IO SYSCTRL_OSCULP32K_Type    OSCULP32K;   /**< \brief Offset: 0x1C (R/W  8) OSCULP32K Control Register */
       RoReg8                    Reserved3[0x3];
  __IO SYSCTRL_OSC8M_Type        OSC8M;       /**< \brief Offset: 0x20 (R/W 32) OSC8M Control Register A */
  __IO SYSCTRL_DFLLCTRL_Type     DFLLCTRL;    /**< \brief Offset: 0x24 (R/W 16) DFLL Config Register */
       RoReg8                    Reserved4[0x2];
  __IO SYSCTRL_DFLLVAL_Type      DFLLVAL;     /**< \brief Offset: 0x28 (R/W 32) DFLL Calibration Value Register */
  __IO SYSCTRL_DFLLMUL_Type      DFLLMUL;     /**< \brief Offset: 0x2C (R/W 32) DFLL Multiplier Register */
  __IO SYSCTRL_DFLLSYNC_Type     DFLLSYNC;    /**< \brief Offset: 0x30 (R/W  8) DFLL Synchronization Register */
       RoReg8                    Reserved5[0x3];
  __IO SYSCTRL_BOD33_Type        BOD33;       /**< \brief Offset: 0x34 (R/W 32) BOD33 Control Register */
  __IO SYSCTRL_BOD12_Type        BOD12;       /**< \brief Offset: 0x38 (R/W 32) BOD12 Control Register */
  __IO SYSCTRL_VREG_Type         VREG;        /**< \brief Offset: 0x3C (R/W 16) VREG Control Register */
       RoReg8                    Reserved6[0x2];
  __IO SYSCTRL_VREF_Type         VREF;        /**< \brief Offset: 0x40 (R/W 32) VREF Control Register A */
} Sysctrl;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

/*@}*/

#endif /* _SAMD20_SYSCTRL_COMPONENT_ */
