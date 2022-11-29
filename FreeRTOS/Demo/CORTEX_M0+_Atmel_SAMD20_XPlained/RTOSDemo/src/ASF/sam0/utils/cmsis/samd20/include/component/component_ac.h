/**
 * \file
 *
 * \brief Component description for AC
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

#ifndef _SAMD20_AC_COMPONENT_
#define _SAMD20_AC_COMPONENT_

/* ========================================================================== */
/**  SOFTWARE API DEFINITION FOR AC */
/* ========================================================================== */
/** \addtogroup SAMD20_AC Analog Comparators */
/*@{*/

#define REV_AC                      0x110

/* -------- AC_CTRLA : (AC Offset: 0x00) (R/W  8) Control A Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  SWRST:1;          /*!< bit:      0  Software Reset                     */
    uint8_t  ENABLE:1;         /*!< bit:      1  Enable                             */
    uint8_t  RUNSTDBY:1;       /*!< bit:      2  Run during Standby                 */
    uint8_t  :5;               /*!< bit:  3.. 7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} AC_CTRLA_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define AC_CTRLA_OFFSET             0x00         /**< \brief (AC_CTRLA offset) Control A Register */
#define AC_CTRLA_RESETVALUE         0x00         /**< \brief (AC_CTRLA reset_value) Control A Register */

#define AC_CTRLA_SWRST_Pos          0            /**< \brief (AC_CTRLA) Software Reset */
#define AC_CTRLA_SWRST              (0x1u << AC_CTRLA_SWRST_Pos)
#define AC_CTRLA_ENABLE_Pos         1            /**< \brief (AC_CTRLA) Enable */
#define AC_CTRLA_ENABLE             (0x1u << AC_CTRLA_ENABLE_Pos)
#define AC_CTRLA_RUNSTDBY_Pos       2            /**< \brief (AC_CTRLA) Run during Standby */
#define AC_CTRLA_RUNSTDBY_Msk       (0x1u << AC_CTRLA_RUNSTDBY_Pos)
#define AC_CTRLA_RUNSTDBY(value)    ((AC_CTRLA_RUNSTDBY_Msk & ((value) << AC_CTRLA_RUNSTDBY_Pos)))
#define AC_CTRLA_MASK               0x07u        /**< \brief (AC_CTRLA) MASK Register */

/* -------- AC_CTRLB : (AC Offset: 0x01) ( /W  8) Control B Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  START0:1;         /*!< bit:      0  Comparator 0 Start Comparison      */
    uint8_t  START1:1;         /*!< bit:      1  Comparator 1 Start Comparison      */
    uint8_t  START2:1;         /*!< bit:      2  Comparator 2 Start Comparison      */
    uint8_t  START3:1;         /*!< bit:      3  Comparator 3 Start Comparison      */
    uint8_t  :4;               /*!< bit:  4.. 7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} AC_CTRLB_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define AC_CTRLB_OFFSET             0x01         /**< \brief (AC_CTRLB offset) Control B Register */
#define AC_CTRLB_RESETVALUE         0x00         /**< \brief (AC_CTRLB reset_value) Control B Register */

#define AC_CTRLB_START0_Pos         0            /**< \brief (AC_CTRLB) Comparator 0 Start Comparison */
#define AC_CTRLB_START0             (0x1u << AC_CTRLB_START0_Pos)
#define AC_CTRLB_START1_Pos         1            /**< \brief (AC_CTRLB) Comparator 1 Start Comparison */
#define AC_CTRLB_START1             (0x1u << AC_CTRLB_START1_Pos)
#define AC_CTRLB_START2_Pos         2            /**< \brief (AC_CTRLB) Comparator 2 Start Comparison */
#define AC_CTRLB_START2             (0x1u << AC_CTRLB_START2_Pos)
#define AC_CTRLB_START3_Pos         3            /**< \brief (AC_CTRLB) Comparator 3 Start Comparison */
#define AC_CTRLB_START3             (0x1u << AC_CTRLB_START3_Pos)
#define AC_CTRLB_MASK               0x0Fu        /**< \brief (AC_CTRLB) MASK Register */

/* -------- AC_EVCTRL : (AC Offset: 0x02) (R/W 16) Event Control Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint16_t COMPEO0:1;        /*!< bit:      0  Comparator 0 Event Output Enable   */
    uint16_t COMPEO1:1;        /*!< bit:      1  Comparator 1 Event Output Enable   */
    uint16_t COMPEO2:1;        /*!< bit:      2  Comparator 2 Event Output Enable   */
    uint16_t COMPEO3:1;        /*!< bit:      3  Comparator 3 Event Output Enable   */
    uint16_t WINEO0:1;         /*!< bit:      4  Window 0 Event Output Enable       */
    uint16_t WINEO1:1;         /*!< bit:      5  Window 1 Event Output Enable       */
    uint16_t :2;               /*!< bit:  6.. 7  Reserved                           */
    uint16_t COMPEI0:1;        /*!< bit:      8  Comparator 0 Event Input Enable    */
    uint16_t COMPEI1:1;        /*!< bit:      9  Comparator 1 Event Input Enable    */
    uint16_t COMPEI2:1;        /*!< bit:     10  Comparator 2 Event Input Enable    */
    uint16_t COMPEI3:1;        /*!< bit:     11  Comparator 3 Event Input Enable    */
    uint16_t :4;               /*!< bit: 12..15  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint16_t reg;                /*!< Type      used for register access              */
} AC_EVCTRL_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define AC_EVCTRL_OFFSET            0x02         /**< \brief (AC_EVCTRL offset) Event Control Register */
#define AC_EVCTRL_RESETVALUE        0x0000       /**< \brief (AC_EVCTRL reset_value) Event Control Register */

#define AC_EVCTRL_COMPEO0_Pos       0            /**< \brief (AC_EVCTRL) Comparator 0 Event Output Enable */
#define AC_EVCTRL_COMPEO0           (0x1u << AC_EVCTRL_COMPEO0_Pos)
#define AC_EVCTRL_COMPEO1_Pos       1            /**< \brief (AC_EVCTRL) Comparator 1 Event Output Enable */
#define AC_EVCTRL_COMPEO1           (0x1u << AC_EVCTRL_COMPEO1_Pos)
#define AC_EVCTRL_COMPEO2_Pos       2            /**< \brief (AC_EVCTRL) Comparator 2 Event Output Enable */
#define AC_EVCTRL_COMPEO2           (0x1u << AC_EVCTRL_COMPEO2_Pos)
#define AC_EVCTRL_COMPEO3_Pos       3            /**< \brief (AC_EVCTRL) Comparator 3 Event Output Enable */
#define AC_EVCTRL_COMPEO3           (0x1u << AC_EVCTRL_COMPEO3_Pos)
#define AC_EVCTRL_WINEO0_Pos        4            /**< \brief (AC_EVCTRL) Window 0 Event Output Enable */
#define AC_EVCTRL_WINEO0            (0x1u << AC_EVCTRL_WINEO0_Pos)
#define AC_EVCTRL_WINEO1_Pos        5            /**< \brief (AC_EVCTRL) Window 1 Event Output Enable */
#define AC_EVCTRL_WINEO1            (0x1u << AC_EVCTRL_WINEO1_Pos)
#define AC_EVCTRL_COMPEI0_Pos       8            /**< \brief (AC_EVCTRL) Comparator 0 Event Input Enable */
#define AC_EVCTRL_COMPEI0           (0x1u << AC_EVCTRL_COMPEI0_Pos)
#define AC_EVCTRL_COMPEI1_Pos       9            /**< \brief (AC_EVCTRL) Comparator 1 Event Input Enable */
#define AC_EVCTRL_COMPEI1           (0x1u << AC_EVCTRL_COMPEI1_Pos)
#define AC_EVCTRL_COMPEI2_Pos       10           /**< \brief (AC_EVCTRL) Comparator 2 Event Input Enable */
#define AC_EVCTRL_COMPEI2           (0x1u << AC_EVCTRL_COMPEI2_Pos)
#define AC_EVCTRL_COMPEI3_Pos       11           /**< \brief (AC_EVCTRL) Comparator 3 Event Input Enable */
#define AC_EVCTRL_COMPEI3           (0x1u << AC_EVCTRL_COMPEI3_Pos)
#define AC_EVCTRL_MASK              0x0F3Fu      /**< \brief (AC_EVCTRL) MASK Register */

/* -------- AC_INTENCLR : (AC Offset: 0x04) (R/W  8) Interrupt Enable Clear Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  COMP0:1;          /*!< bit:      0  Comparator 0 Interrupt Disable     */
    uint8_t  COMP1:1;          /*!< bit:      1  Comparator 1 Interrupt Disable     */
    uint8_t  COMP2:1;          /*!< bit:      2  Comparator 2 Interrupt Disable     */
    uint8_t  COMP3:1;          /*!< bit:      3  Comparator 3 Interrupt Disable     */
    uint8_t  WIN0:1;           /*!< bit:      4  Window 0 Interrupt Disable         */
    uint8_t  WIN1:1;           /*!< bit:      5  Window 1 Interrupt Disable         */
    uint8_t  :2;               /*!< bit:  6.. 7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} AC_INTENCLR_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define AC_INTENCLR_OFFSET          0x04         /**< \brief (AC_INTENCLR offset) Interrupt Enable Clear Register */
#define AC_INTENCLR_RESETVALUE      0x00         /**< \brief (AC_INTENCLR reset_value) Interrupt Enable Clear Register */

#define AC_INTENCLR_COMP0_Pos       0            /**< \brief (AC_INTENCLR) Comparator 0 Interrupt Disable */
#define AC_INTENCLR_COMP0           (0x1u << AC_INTENCLR_COMP0_Pos)
#define AC_INTENCLR_COMP1_Pos       1            /**< \brief (AC_INTENCLR) Comparator 1 Interrupt Disable */
#define AC_INTENCLR_COMP1           (0x1u << AC_INTENCLR_COMP1_Pos)
#define AC_INTENCLR_COMP2_Pos       2            /**< \brief (AC_INTENCLR) Comparator 2 Interrupt Disable */
#define AC_INTENCLR_COMP2           (0x1u << AC_INTENCLR_COMP2_Pos)
#define AC_INTENCLR_COMP3_Pos       3            /**< \brief (AC_INTENCLR) Comparator 3 Interrupt Disable */
#define AC_INTENCLR_COMP3           (0x1u << AC_INTENCLR_COMP3_Pos)
#define AC_INTENCLR_WIN0_Pos        4            /**< \brief (AC_INTENCLR) Window 0 Interrupt Disable */
#define AC_INTENCLR_WIN0            (0x1u << AC_INTENCLR_WIN0_Pos)
#define AC_INTENCLR_WIN1_Pos        5            /**< \brief (AC_INTENCLR) Window 1 Interrupt Disable */
#define AC_INTENCLR_WIN1            (0x1u << AC_INTENCLR_WIN1_Pos)
#define AC_INTENCLR_MASK            0x3Fu        /**< \brief (AC_INTENCLR) MASK Register */

/* -------- AC_INTENSET : (AC Offset: 0x05) (R/W  8) Interrupt Enable Set Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  COMP0:1;          /*!< bit:      0  Comparator 0 Interrupt Enable      */
    uint8_t  COMP1:1;          /*!< bit:      1  Comparator 1 Interrupt Enable      */
    uint8_t  COMP2:1;          /*!< bit:      2  Comparator 2 Interrupt Enable      */
    uint8_t  COMP3:1;          /*!< bit:      3  Comparator 3 Interrupt Enable      */
    uint8_t  WIN0:1;           /*!< bit:      4  Window 0 Interrupt Enable          */
    uint8_t  WIN1:1;           /*!< bit:      5  Window 1 Interrupt Enable          */
    uint8_t  :2;               /*!< bit:  6.. 7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} AC_INTENSET_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define AC_INTENSET_OFFSET          0x05         /**< \brief (AC_INTENSET offset) Interrupt Enable Set Register */
#define AC_INTENSET_RESETVALUE      0x00         /**< \brief (AC_INTENSET reset_value) Interrupt Enable Set Register */

#define AC_INTENSET_COMP0_Pos       0            /**< \brief (AC_INTENSET) Comparator 0 Interrupt Enable */
#define AC_INTENSET_COMP0           (0x1u << AC_INTENSET_COMP0_Pos)
#define AC_INTENSET_COMP1_Pos       1            /**< \brief (AC_INTENSET) Comparator 1 Interrupt Enable */
#define AC_INTENSET_COMP1           (0x1u << AC_INTENSET_COMP1_Pos)
#define AC_INTENSET_COMP2_Pos       2            /**< \brief (AC_INTENSET) Comparator 2 Interrupt Enable */
#define AC_INTENSET_COMP2           (0x1u << AC_INTENSET_COMP2_Pos)
#define AC_INTENSET_COMP3_Pos       3            /**< \brief (AC_INTENSET) Comparator 3 Interrupt Enable */
#define AC_INTENSET_COMP3           (0x1u << AC_INTENSET_COMP3_Pos)
#define AC_INTENSET_WIN0_Pos        4            /**< \brief (AC_INTENSET) Window 0 Interrupt Enable */
#define AC_INTENSET_WIN0            (0x1u << AC_INTENSET_WIN0_Pos)
#define AC_INTENSET_WIN1_Pos        5            /**< \brief (AC_INTENSET) Window 1 Interrupt Enable */
#define AC_INTENSET_WIN1            (0x1u << AC_INTENSET_WIN1_Pos)
#define AC_INTENSET_MASK            0x3Fu        /**< \brief (AC_INTENSET) MASK Register */

/* -------- AC_INTFLAG : (AC Offset: 0x06) (R/W  8) Interrupt Flag Status and Clear Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  COMP0:1;          /*!< bit:      0  Comparator 0 Interrupt Flag        */
    uint8_t  COMP1:1;          /*!< bit:      1  Comparator 1 Interrupt Flag        */
    uint8_t  COMP2:1;          /*!< bit:      2  Comparator 2 Interrupt Flag        */
    uint8_t  COMP3:1;          /*!< bit:      3  Comparator 3 Interrupt Flag        */
    uint8_t  WIN0:1;           /*!< bit:      4  Window 0 Interrupt Flag            */
    uint8_t  WIN1:1;           /*!< bit:      5  Window 1 Interrupt Flag            */
    uint8_t  :2;               /*!< bit:  6.. 7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} AC_INTFLAG_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define AC_INTFLAG_OFFSET           0x06         /**< \brief (AC_INTFLAG offset) Interrupt Flag Status and Clear Register */
#define AC_INTFLAG_RESETVALUE       0x00         /**< \brief (AC_INTFLAG reset_value) Interrupt Flag Status and Clear Register */

#define AC_INTFLAG_COMP0_Pos        0            /**< \brief (AC_INTFLAG) Comparator 0 Interrupt Flag */
#define AC_INTFLAG_COMP0            (0x1u << AC_INTFLAG_COMP0_Pos)
#define AC_INTFLAG_COMP1_Pos        1            /**< \brief (AC_INTFLAG) Comparator 1 Interrupt Flag */
#define AC_INTFLAG_COMP1            (0x1u << AC_INTFLAG_COMP1_Pos)
#define AC_INTFLAG_COMP2_Pos        2            /**< \brief (AC_INTFLAG) Comparator 2 Interrupt Flag */
#define AC_INTFLAG_COMP2            (0x1u << AC_INTFLAG_COMP2_Pos)
#define AC_INTFLAG_COMP3_Pos        3            /**< \brief (AC_INTFLAG) Comparator 3 Interrupt Flag */
#define AC_INTFLAG_COMP3            (0x1u << AC_INTFLAG_COMP3_Pos)
#define AC_INTFLAG_WIN0_Pos         4            /**< \brief (AC_INTFLAG) Window 0 Interrupt Flag */
#define AC_INTFLAG_WIN0             (0x1u << AC_INTFLAG_WIN0_Pos)
#define AC_INTFLAG_WIN1_Pos         5            /**< \brief (AC_INTFLAG) Window 1 Interrupt Flag */
#define AC_INTFLAG_WIN1             (0x1u << AC_INTFLAG_WIN1_Pos)
#define AC_INTFLAG_MASK             0x3Fu        /**< \brief (AC_INTFLAG) MASK Register */

/* -------- AC_STATUSA : (AC Offset: 0x08) (R/   8) Status A Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  STATE0:1;         /*!< bit:      0  Comparator 0 Current State         */
    uint8_t  STATE1:1;         /*!< bit:      1  Comparator 1 Current State         */
    uint8_t  STATE2:1;         /*!< bit:      2  Comparator 2 Current State         */
    uint8_t  STATE3:1;         /*!< bit:      3  Comparator 3 Current State         */
    uint8_t  WSTATE0:2;        /*!< bit:  4.. 5  Window 0 Current State             */
    uint8_t  WSTATE1:2;        /*!< bit:  6.. 7  Window 1 Current State             */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} AC_STATUSA_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define AC_STATUSA_OFFSET           0x08         /**< \brief (AC_STATUSA offset) Status A Register */
#define AC_STATUSA_RESETVALUE       0x00         /**< \brief (AC_STATUSA reset_value) Status A Register */

#define AC_STATUSA_STATE0_Pos       0            /**< \brief (AC_STATUSA) Comparator 0 Current State */
#define AC_STATUSA_STATE0           (0x1u << AC_STATUSA_STATE0_Pos)
#define AC_STATUSA_STATE1_Pos       1            /**< \brief (AC_STATUSA) Comparator 1 Current State */
#define AC_STATUSA_STATE1           (0x1u << AC_STATUSA_STATE1_Pos)
#define AC_STATUSA_STATE2_Pos       2            /**< \brief (AC_STATUSA) Comparator 2 Current State */
#define AC_STATUSA_STATE2           (0x1u << AC_STATUSA_STATE2_Pos)
#define AC_STATUSA_STATE3_Pos       3            /**< \brief (AC_STATUSA) Comparator 3 Current State */
#define AC_STATUSA_STATE3           (0x1u << AC_STATUSA_STATE3_Pos)
#define AC_STATUSA_WSTATE0_Pos      4            /**< \brief (AC_STATUSA) Window 0 Current State */
#define AC_STATUSA_WSTATE0_Msk      (0x3u << AC_STATUSA_WSTATE0_Pos)
#define AC_STATUSA_WSTATE0(value)   ((AC_STATUSA_WSTATE0_Msk & ((value) << AC_STATUSA_WSTATE0_Pos)))
#define   AC_STATUSA_WSTATE0_ABOVE  (0x0u <<  4) /**< \brief (AC_STATUSA)  */
#define   AC_STATUSA_WSTATE0_INSIDE (0x1u <<  4) /**< \brief (AC_STATUSA)  */
#define   AC_STATUSA_WSTATE0_BELOW  (0x2u <<  4) /**< \brief (AC_STATUSA)  */
#define AC_STATUSA_WSTATE1_Pos      6            /**< \brief (AC_STATUSA) Window 1 Current State */
#define AC_STATUSA_WSTATE1_Msk      (0x3u << AC_STATUSA_WSTATE1_Pos)
#define AC_STATUSA_WSTATE1(value)   ((AC_STATUSA_WSTATE1_Msk & ((value) << AC_STATUSA_WSTATE1_Pos)))
#define   AC_STATUSA_WSTATE1_ABOVE  (0x0u <<  6) /**< \brief (AC_STATUSA)  */
#define   AC_STATUSA_WSTATE1_INSIDE (0x1u <<  6) /**< \brief (AC_STATUSA)  */
#define   AC_STATUSA_WSTATE1_BELOW  (0x2u <<  6) /**< \brief (AC_STATUSA)  */
#define AC_STATUSA_MASK             0xFFu        /**< \brief (AC_STATUSA) MASK Register */

/* -------- AC_STATUSB : (AC Offset: 0x09) (R/   8) Status B Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  READY0:1;         /*!< bit:      0  Comparator 0 Ready                 */
    uint8_t  READY1:1;         /*!< bit:      1  Comparator 1 Ready                 */
    uint8_t  READY2:1;         /*!< bit:      2  Comparator 2 Ready                 */
    uint8_t  READY3:1;         /*!< bit:      3  Comparator 3 Ready                 */
    uint8_t  :3;               /*!< bit:  4.. 6  Reserved                           */
    uint8_t  SYNCBUSY:1;       /*!< bit:      7  Synchronization Busy               */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} AC_STATUSB_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define AC_STATUSB_OFFSET           0x09         /**< \brief (AC_STATUSB offset) Status B Register */
#define AC_STATUSB_RESETVALUE       0x00         /**< \brief (AC_STATUSB reset_value) Status B Register */

#define AC_STATUSB_READY0_Pos       0            /**< \brief (AC_STATUSB) Comparator 0 Ready */
#define AC_STATUSB_READY0           (0x1u << AC_STATUSB_READY0_Pos)
#define AC_STATUSB_READY1_Pos       1            /**< \brief (AC_STATUSB) Comparator 1 Ready */
#define AC_STATUSB_READY1           (0x1u << AC_STATUSB_READY1_Pos)
#define AC_STATUSB_READY2_Pos       2            /**< \brief (AC_STATUSB) Comparator 2 Ready */
#define AC_STATUSB_READY2           (0x1u << AC_STATUSB_READY2_Pos)
#define AC_STATUSB_READY3_Pos       3            /**< \brief (AC_STATUSB) Comparator 3 Ready */
#define AC_STATUSB_READY3           (0x1u << AC_STATUSB_READY3_Pos)
#define AC_STATUSB_SYNCBUSY_Pos     7            /**< \brief (AC_STATUSB) Synchronization Busy */
#define AC_STATUSB_SYNCBUSY         (0x1u << AC_STATUSB_SYNCBUSY_Pos)
#define AC_STATUSB_MASK             0x8Fu        /**< \brief (AC_STATUSB) MASK Register */

/* -------- AC_STATUSC : (AC Offset: 0x0A) (R/   8) Status C Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  STATE0:1;         /*!< bit:      0  Comparator 0 Current State         */
    uint8_t  STATE1:1;         /*!< bit:      1  Comparator 1 Current State         */
    uint8_t  STATE2:1;         /*!< bit:      2  Comparator 2 Current State         */
    uint8_t  STATE3:1;         /*!< bit:      3  Comparator 3 Current State         */
    uint8_t  WSTATE0:2;        /*!< bit:  4.. 5  Window 0 Current State             */
    uint8_t  WSTATE1:2;        /*!< bit:  6.. 7  Window 1 Current State             */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} AC_STATUSC_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define AC_STATUSC_OFFSET           0x0A         /**< \brief (AC_STATUSC offset) Status C Register */
#define AC_STATUSC_RESETVALUE       0x00         /**< \brief (AC_STATUSC reset_value) Status C Register */

#define AC_STATUSC_STATE0_Pos       0            /**< \brief (AC_STATUSC) Comparator 0 Current State */
#define AC_STATUSC_STATE0           (0x1u << AC_STATUSC_STATE0_Pos)
#define AC_STATUSC_STATE1_Pos       1            /**< \brief (AC_STATUSC) Comparator 1 Current State */
#define AC_STATUSC_STATE1           (0x1u << AC_STATUSC_STATE1_Pos)
#define AC_STATUSC_STATE2_Pos       2            /**< \brief (AC_STATUSC) Comparator 2 Current State */
#define AC_STATUSC_STATE2           (0x1u << AC_STATUSC_STATE2_Pos)
#define AC_STATUSC_STATE3_Pos       3            /**< \brief (AC_STATUSC) Comparator 3 Current State */
#define AC_STATUSC_STATE3           (0x1u << AC_STATUSC_STATE3_Pos)
#define AC_STATUSC_WSTATE0_Pos      4            /**< \brief (AC_STATUSC) Window 0 Current State */
#define AC_STATUSC_WSTATE0_Msk      (0x3u << AC_STATUSC_WSTATE0_Pos)
#define AC_STATUSC_WSTATE0(value)   ((AC_STATUSC_WSTATE0_Msk & ((value) << AC_STATUSC_WSTATE0_Pos)))
#define   AC_STATUSC_WSTATE0_ABOVE  (0x0u <<  4) /**< \brief (AC_STATUSC)  */
#define   AC_STATUSC_WSTATE0_INSIDE (0x1u <<  4) /**< \brief (AC_STATUSC)  */
#define   AC_STATUSC_WSTATE0_BELOW  (0x2u <<  4) /**< \brief (AC_STATUSC)  */
#define AC_STATUSC_WSTATE1_Pos      6            /**< \brief (AC_STATUSC) Window 1 Current State */
#define AC_STATUSC_WSTATE1_Msk      (0x3u << AC_STATUSC_WSTATE1_Pos)
#define AC_STATUSC_WSTATE1(value)   ((AC_STATUSC_WSTATE1_Msk & ((value) << AC_STATUSC_WSTATE1_Pos)))
#define   AC_STATUSC_WSTATE1_ABOVE  (0x0u <<  6) /**< \brief (AC_STATUSC)  */
#define   AC_STATUSC_WSTATE1_INSIDE (0x1u <<  6) /**< \brief (AC_STATUSC)  */
#define   AC_STATUSC_WSTATE1_BELOW  (0x2u <<  6) /**< \brief (AC_STATUSC)  */
#define AC_STATUSC_MASK             0xFFu        /**< \brief (AC_STATUSC) MASK Register */

/* -------- AC_WINCTRL : (AC Offset: 0x0C) (R/W  8) Window Control Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  WEN0:1;           /*!< bit:      0  Window 0 Mode Enable               */
    uint8_t  WINTSEL0:2;       /*!< bit:  1.. 2  Window 0 Interrupt Selection       */
    uint8_t  :1;               /*!< bit:      3  Reserved                           */
    uint8_t  WEN1:1;           /*!< bit:      4  Window 1 Mode Enable               */
    uint8_t  WINTSEL1:2;       /*!< bit:  5.. 6  Window 1 Interrupt Selection       */
    uint8_t  :1;               /*!< bit:      7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} AC_WINCTRL_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define AC_WINCTRL_OFFSET           0x0C         /**< \brief (AC_WINCTRL offset) Window Control Register */
#define AC_WINCTRL_RESETVALUE       0x00         /**< \brief (AC_WINCTRL reset_value) Window Control Register */

#define AC_WINCTRL_WEN0_Pos         0            /**< \brief (AC_WINCTRL) Window 0 Mode Enable */
#define AC_WINCTRL_WEN0             (0x1u << AC_WINCTRL_WEN0_Pos)
#define AC_WINCTRL_WINTSEL0_Pos     1            /**< \brief (AC_WINCTRL) Window 0 Interrupt Selection */
#define AC_WINCTRL_WINTSEL0_Msk     (0x3u << AC_WINCTRL_WINTSEL0_Pos)
#define AC_WINCTRL_WINTSEL0(value)  ((AC_WINCTRL_WINTSEL0_Msk & ((value) << AC_WINCTRL_WINTSEL0_Pos)))
#define   AC_WINCTRL_WINTSEL0_ABOVE (0x0u <<  1) /**< \brief (AC_WINCTRL)  */
#define   AC_WINCTRL_WINTSEL0_INSIDE (0x1u <<  1) /**< \brief (AC_WINCTRL)  */
#define   AC_WINCTRL_WINTSEL0_BELOW (0x2u <<  1) /**< \brief (AC_WINCTRL)  */
#define   AC_WINCTRL_WINTSEL0_OUTSIDE (0x3u <<  1) /**< \brief (AC_WINCTRL)  */
#define AC_WINCTRL_WEN1_Pos         4            /**< \brief (AC_WINCTRL) Window 1 Mode Enable */
#define AC_WINCTRL_WEN1             (0x1u << AC_WINCTRL_WEN1_Pos)
#define AC_WINCTRL_WINTSEL1_Pos     5            /**< \brief (AC_WINCTRL) Window 1 Interrupt Selection */
#define AC_WINCTRL_WINTSEL1_Msk     (0x3u << AC_WINCTRL_WINTSEL1_Pos)
#define AC_WINCTRL_WINTSEL1(value)  ((AC_WINCTRL_WINTSEL1_Msk & ((value) << AC_WINCTRL_WINTSEL1_Pos)))
#define   AC_WINCTRL_WINTSEL1_ABOVE (0x0u <<  5) /**< \brief (AC_WINCTRL)  */
#define   AC_WINCTRL_WINTSEL1_INSIDE (0x1u <<  5) /**< \brief (AC_WINCTRL)  */
#define   AC_WINCTRL_WINTSEL1_BELOW (0x2u <<  5) /**< \brief (AC_WINCTRL)  */
#define   AC_WINCTRL_WINTSEL1_OUTSIDE (0x3u <<  5) /**< \brief (AC_WINCTRL)  */
#define AC_WINCTRL_MASK             0x77u        /**< \brief (AC_WINCTRL) MASK Register */

/* -------- AC_COMPCTRL : (AC Offset: 0x10) (R/W 32) Comparator Control Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t ENABLE:1;         /*!< bit:      0  Enable                             */
    uint32_t SINGLE:1;         /*!< bit:      1  Single-Shot Mode                   */
    uint32_t SPEED:2;          /*!< bit:  2.. 3  Speed Selection                    */
    uint32_t :1;               /*!< bit:      4  Reserved                           */
    uint32_t INTSEL:2;         /*!< bit:  5.. 6  Interrupt Selection                */
    uint32_t :1;               /*!< bit:      7  Reserved                           */
    uint32_t MUXNEG:3;         /*!< bit:  8..10  Negative Input Mux Selection       */
    uint32_t :1;               /*!< bit:     11  Reserved                           */
    uint32_t MUXPOS:2;         /*!< bit: 12..13  Positive Input Mux Selection       */
    uint32_t :1;               /*!< bit:     14  Reserved                           */
    uint32_t SWAP:1;           /*!< bit:     15  Swap Inputs and Invert             */
    uint32_t OUT:2;            /*!< bit: 16..17  Output Mode                        */
    uint32_t :1;               /*!< bit:     18  Reserved                           */
    uint32_t HYST:1;           /*!< bit:     19  Hysteresis Enable                  */
    uint32_t :4;               /*!< bit: 20..23  Reserved                           */
    uint32_t FLEN:3;           /*!< bit: 24..26  Filter Length                      */
    uint32_t :5;               /*!< bit: 27..31  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} AC_COMPCTRL_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define AC_COMPCTRL_OFFSET          0x10         /**< \brief (AC_COMPCTRL offset) Comparator Control Register */
#define AC_COMPCTRL_RESETVALUE      0x00000000   /**< \brief (AC_COMPCTRL reset_value) Comparator Control Register */

#define AC_COMPCTRL_ENABLE_Pos      0            /**< \brief (AC_COMPCTRL) Enable */
#define AC_COMPCTRL_ENABLE          (0x1u << AC_COMPCTRL_ENABLE_Pos)
#define AC_COMPCTRL_SINGLE_Pos      1            /**< \brief (AC_COMPCTRL) Single-Shot Mode */
#define AC_COMPCTRL_SINGLE          (0x1u << AC_COMPCTRL_SINGLE_Pos)
#define AC_COMPCTRL_SPEED_Pos       2            /**< \brief (AC_COMPCTRL) Speed Selection */
#define AC_COMPCTRL_SPEED_Msk       (0x3u << AC_COMPCTRL_SPEED_Pos)
#define AC_COMPCTRL_SPEED(value)    ((AC_COMPCTRL_SPEED_Msk & ((value) << AC_COMPCTRL_SPEED_Pos)))
#define   AC_COMPCTRL_SPEED_LOWPOWER (0x0u <<  2) /**< \brief (AC_COMPCTRL)  */
#define   AC_COMPCTRL_SPEED_FAST    (0x1u <<  2) /**< \brief (AC_COMPCTRL)  */
#define AC_COMPCTRL_INTSEL_Pos      5            /**< \brief (AC_COMPCTRL) Interrupt Selection */
#define AC_COMPCTRL_INTSEL_Msk      (0x3u << AC_COMPCTRL_INTSEL_Pos)
#define AC_COMPCTRL_INTSEL(value)   ((AC_COMPCTRL_INTSEL_Msk & ((value) << AC_COMPCTRL_INTSEL_Pos)))
#define   AC_COMPCTRL_INTSEL_TOGGLE (0x0u <<  5) /**< \brief (AC_COMPCTRL)  */
#define   AC_COMPCTRL_INTSEL_RISING (0x1u <<  5) /**< \brief (AC_COMPCTRL)  */
#define   AC_COMPCTRL_INTSEL_FALLING (0x2u <<  5) /**< \brief (AC_COMPCTRL)  */
#define   AC_COMPCTRL_INTSEL_EOC    (0x3u <<  5) /**< \brief (AC_COMPCTRL)  */
#define AC_COMPCTRL_MUXNEG_Pos      8            /**< \brief (AC_COMPCTRL) Negative Input Mux Selection */
#define AC_COMPCTRL_MUXNEG_Msk      (0x7u << AC_COMPCTRL_MUXNEG_Pos)
#define AC_COMPCTRL_MUXNEG(value)   ((AC_COMPCTRL_MUXNEG_Msk & ((value) << AC_COMPCTRL_MUXNEG_Pos)))
#define   AC_COMPCTRL_MUXNEG_PIN0   (0x0u <<  8) /**< \brief (AC_COMPCTRL)  */
#define   AC_COMPCTRL_MUXNEG_PIN1   (0x1u <<  8) /**< \brief (AC_COMPCTRL)  */
#define   AC_COMPCTRL_MUXNEG_PIN2   (0x2u <<  8) /**< \brief (AC_COMPCTRL)  */
#define   AC_COMPCTRL_MUXNEG_PIN3   (0x3u <<  8) /**< \brief (AC_COMPCTRL)  */
#define   AC_COMPCTRL_MUXNEG_GND    (0x4u <<  8) /**< \brief (AC_COMPCTRL)  */
#define   AC_COMPCTRL_MUXNEG_VSCALE (0x5u <<  8) /**< \brief (AC_COMPCTRL)  */
#define   AC_COMPCTRL_MUXNEG_BANDGAP (0x6u <<  8) /**< \brief (AC_COMPCTRL)  */
#define   AC_COMPCTRL_MUXNEG_DAC    (0x7u <<  8) /**< \brief (AC_COMPCTRL)  */
#define AC_COMPCTRL_MUXPOS_Pos      12           /**< \brief (AC_COMPCTRL) Positive Input Mux Selection */
#define AC_COMPCTRL_MUXPOS_Msk      (0x3u << AC_COMPCTRL_MUXPOS_Pos)
#define AC_COMPCTRL_MUXPOS(value)   ((AC_COMPCTRL_MUXPOS_Msk & ((value) << AC_COMPCTRL_MUXPOS_Pos)))
#define   AC_COMPCTRL_MUXPOS_PIN0   (0x0u << 12) /**< \brief (AC_COMPCTRL)  */
#define   AC_COMPCTRL_MUXPOS_PIN1   (0x1u << 12) /**< \brief (AC_COMPCTRL)  */
#define   AC_COMPCTRL_MUXPOS_PIN2   (0x2u << 12) /**< \brief (AC_COMPCTRL)  */
#define   AC_COMPCTRL_MUXPOS_PIN3   (0x3u << 12) /**< \brief (AC_COMPCTRL)  */
#define AC_COMPCTRL_SWAP_Pos        15           /**< \brief (AC_COMPCTRL) Swap Inputs and Invert */
#define AC_COMPCTRL_SWAP            (0x1u << AC_COMPCTRL_SWAP_Pos)
#define AC_COMPCTRL_OUT_Pos         16           /**< \brief (AC_COMPCTRL) Output Mode */
#define AC_COMPCTRL_OUT_Msk         (0x3u << AC_COMPCTRL_OUT_Pos)
#define AC_COMPCTRL_OUT(value)      ((AC_COMPCTRL_OUT_Msk & ((value) << AC_COMPCTRL_OUT_Pos)))
#define   AC_COMPCTRL_OUT_OFF       (0x0u << 16) /**< \brief (AC_COMPCTRL)  */
#define   AC_COMPCTRL_OUT_ASYNC     (0x1u << 16) /**< \brief (AC_COMPCTRL)  */
#define   AC_COMPCTRL_OUT_SYNC      (0x2u << 16) /**< \brief (AC_COMPCTRL)  */
#define AC_COMPCTRL_HYST_Pos        19           /**< \brief (AC_COMPCTRL) Hysteresis Enable */
#define AC_COMPCTRL_HYST            (0x1u << AC_COMPCTRL_HYST_Pos)
#define AC_COMPCTRL_FLEN_Pos        24           /**< \brief (AC_COMPCTRL) Filter Length */
#define AC_COMPCTRL_FLEN_Msk        (0x7u << AC_COMPCTRL_FLEN_Pos)
#define AC_COMPCTRL_FLEN(value)     ((AC_COMPCTRL_FLEN_Msk & ((value) << AC_COMPCTRL_FLEN_Pos)))
#define   AC_COMPCTRL_FLEN_OFF      (0x0u << 24) /**< \brief (AC_COMPCTRL)  */
#define   AC_COMPCTRL_FLEN_MAJ3     (0x1u << 24) /**< \brief (AC_COMPCTRL)  */
#define   AC_COMPCTRL_FLEN_MAJ5     (0x2u << 24) /**< \brief (AC_COMPCTRL)  */
#define AC_COMPCTRL_MASK            0x070BB76Fu  /**< \brief (AC_COMPCTRL) MASK Register */

/* -------- AC_SCALER : (AC Offset: 0x20) (R/W  8) Scaler Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  VALUE:6;          /*!< bit:  0.. 5  Scaler Value                       */
    uint8_t  :2;               /*!< bit:  6.. 7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} AC_SCALER_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define AC_SCALER_OFFSET            0x20         /**< \brief (AC_SCALER offset) Scaler Register */
#define AC_SCALER_RESETVALUE        0x00         /**< \brief (AC_SCALER reset_value) Scaler Register */

#define AC_SCALER_VALUE_Pos         0            /**< \brief (AC_SCALER) Scaler Value */
#define AC_SCALER_VALUE_Msk         (0x3Fu << AC_SCALER_VALUE_Pos)
#define AC_SCALER_VALUE(value)      ((AC_SCALER_VALUE_Msk & ((value) << AC_SCALER_VALUE_Pos)))
#define AC_SCALER_MASK              0x3Fu        /**< \brief (AC_SCALER) MASK Register */

/** \brief AC hardware registers */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef struct {
  __IO AC_CTRLA_Type             CTRLA;       /**< \brief Offset: 0x00 (R/W  8) Control A Register */
  __O  AC_CTRLB_Type             CTRLB;       /**< \brief Offset: 0x01 ( /W  8) Control B Register */
  __IO AC_EVCTRL_Type            EVCTRL;      /**< \brief Offset: 0x02 (R/W 16) Event Control Register */
  __IO AC_INTENCLR_Type          INTENCLR;    /**< \brief Offset: 0x04 (R/W  8) Interrupt Enable Clear Register */
  __IO AC_INTENSET_Type          INTENSET;    /**< \brief Offset: 0x05 (R/W  8) Interrupt Enable Set Register */
  __IO AC_INTFLAG_Type           INTFLAG;     /**< \brief Offset: 0x06 (R/W  8) Interrupt Flag Status and Clear Register */
       RoReg8                    Reserved1[0x1];
  __I  AC_STATUSA_Type           STATUSA;     /**< \brief Offset: 0x08 (R/   8) Status A Register */
  __I  AC_STATUSB_Type           STATUSB;     /**< \brief Offset: 0x09 (R/   8) Status B Register */
  __I  AC_STATUSC_Type           STATUSC;     /**< \brief Offset: 0x0A (R/   8) Status C Register */
       RoReg8                    Reserved2[0x1];
  __IO AC_WINCTRL_Type           WINCTRL;     /**< \brief Offset: 0x0C (R/W  8) Window Control Register */
       RoReg8                    Reserved3[0x3];
  __IO AC_COMPCTRL_Type          COMPCTRL[2]; /**< \brief Offset: 0x10 (R/W 32) Comparator Control Register [NUM_CMP] */
       RoReg8                    Reserved4[0x8];
  __IO AC_SCALER_Type            SCALER[2];   /**< \brief Offset: 0x20 (R/W  8) Scaler Register [NUM_CMP] */
} Ac;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

/*@}*/

#endif /* _SAMD20_AC_COMPONENT_ */
