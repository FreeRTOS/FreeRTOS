/**
 * \file
 *
 * \brief Component description for RTC
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

#ifndef _SAMD20_RTC_COMPONENT_
#define _SAMD20_RTC_COMPONENT_

/* ========================================================================== */
/**  SOFTWARE API DEFINITION FOR RTC */
/* ========================================================================== */
/** \addtogroup SAMD20_RTC Real-Time Counter */
/*@{*/

#define REV_RTC                     0x101

/* -------- RTC_MODE0_CTRL : (RTC Offset: 0x00) (R/W 16) MODE0 MODE0 Control Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint16_t SWRST:1;          /*!< bit:      0  Software Reset                     */
    uint16_t ENABLE:1;         /*!< bit:      1  Enable                             */
    uint16_t MODE:2;           /*!< bit:  2.. 3  Mode                               */
    uint16_t :3;               /*!< bit:  4.. 6  Reserved                           */
    uint16_t MATCHCLR:1;       /*!< bit:      7  Match Clears Counter               */
    uint16_t PRESCALER:4;      /*!< bit:  8..11  Prescaler                          */
    uint16_t :4;               /*!< bit: 12..15  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint16_t reg;                /*!< Type      used for register access              */
} RTC_MODE0_CTRL_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define RTC_MODE0_CTRL_OFFSET       0x00         /**< \brief (RTC_MODE0_CTRL offset) MODE0 Control Register */
#define RTC_MODE0_CTRL_RESETVALUE   0x0000       /**< \brief (RTC_MODE0_CTRL reset_value) MODE0 Control Register */

#define RTC_MODE0_CTRL_SWRST_Pos    0            /**< \brief (RTC_MODE0_CTRL) Software Reset */
#define RTC_MODE0_CTRL_SWRST        (0x1u << RTC_MODE0_CTRL_SWRST_Pos)
#define RTC_MODE0_CTRL_ENABLE_Pos   1            /**< \brief (RTC_MODE0_CTRL) Enable */
#define RTC_MODE0_CTRL_ENABLE       (0x1u << RTC_MODE0_CTRL_ENABLE_Pos)
#define RTC_MODE0_CTRL_MODE_Pos     2            /**< \brief (RTC_MODE0_CTRL) Mode */
#define RTC_MODE0_CTRL_MODE_Msk     (0x3u << RTC_MODE0_CTRL_MODE_Pos)
#define RTC_MODE0_CTRL_MODE(value)  ((RTC_MODE0_CTRL_MODE_Msk & ((value) << RTC_MODE0_CTRL_MODE_Pos)))
#define   RTC_MODE0_CTRL_MODE_COUNT32 (0x0u <<  2) /**< \brief (RTC_MODE0_CTRL) Mode 0 */
#define   RTC_MODE0_CTRL_MODE_COUNT16 (0x1u <<  2) /**< \brief (RTC_MODE0_CTRL) Mode 1 */
#define   RTC_MODE0_CTRL_MODE_CLOCK (0x2u <<  2) /**< \brief (RTC_MODE0_CTRL) Mode 2 */
#define RTC_MODE0_CTRL_MATCHCLR_Pos 7            /**< \brief (RTC_MODE0_CTRL) Match Clears Counter */
#define RTC_MODE0_CTRL_MATCHCLR     (0x1u << RTC_MODE0_CTRL_MATCHCLR_Pos)
#define RTC_MODE0_CTRL_PRESCALER_Pos 8            /**< \brief (RTC_MODE0_CTRL) Prescaler */
#define RTC_MODE0_CTRL_PRESCALER_Msk (0xFu << RTC_MODE0_CTRL_PRESCALER_Pos)
#define RTC_MODE0_CTRL_PRESCALER(value) ((RTC_MODE0_CTRL_PRESCALER_Msk & ((value) << RTC_MODE0_CTRL_PRESCALER_Pos)))
#define   RTC_MODE0_CTRL_PRESCALER_DIV1 (0x0u <<  8) /**< \brief (RTC_MODE0_CTRL)  */
#define   RTC_MODE0_CTRL_PRESCALER_DIV2 (0x1u <<  8) /**< \brief (RTC_MODE0_CTRL)  */
#define   RTC_MODE0_CTRL_PRESCALER_DIV4 (0x2u <<  8) /**< \brief (RTC_MODE0_CTRL)  */
#define   RTC_MODE0_CTRL_PRESCALER_DIV8 (0x3u <<  8) /**< \brief (RTC_MODE0_CTRL)  */
#define   RTC_MODE0_CTRL_PRESCALER_DIV16 (0x4u <<  8) /**< \brief (RTC_MODE0_CTRL)  */
#define   RTC_MODE0_CTRL_PRESCALER_DIV32 (0x5u <<  8) /**< \brief (RTC_MODE0_CTRL)  */
#define   RTC_MODE0_CTRL_PRESCALER_DIV64 (0x6u <<  8) /**< \brief (RTC_MODE0_CTRL)  */
#define   RTC_MODE0_CTRL_PRESCALER_DIV128 (0x7u <<  8) /**< \brief (RTC_MODE0_CTRL)  */
#define   RTC_MODE0_CTRL_PRESCALER_DIV256 (0x8u <<  8) /**< \brief (RTC_MODE0_CTRL)  */
#define   RTC_MODE0_CTRL_PRESCALER_DIV512 (0x9u <<  8) /**< \brief (RTC_MODE0_CTRL)  */
#define   RTC_MODE0_CTRL_PRESCALER_DIV1024 (0xAu <<  8) /**< \brief (RTC_MODE0_CTRL)  */
#define RTC_MODE0_CTRL_MASK         0x0F8Fu      /**< \brief (RTC_MODE0_CTRL) MASK Register */

/* -------- RTC_MODE1_CTRL : (RTC Offset: 0x00) (R/W 16) MODE1 MODE1 Control Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint16_t SWRST:1;          /*!< bit:      0  Software Reset                     */
    uint16_t ENABLE:1;         /*!< bit:      1  Enable                             */
    uint16_t MODE:2;           /*!< bit:  2.. 3  Mode                               */
    uint16_t :4;               /*!< bit:  4.. 7  Reserved                           */
    uint16_t PRESCALER:4;      /*!< bit:  8..11  Prescaler                          */
    uint16_t :4;               /*!< bit: 12..15  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint16_t reg;                /*!< Type      used for register access              */
} RTC_MODE1_CTRL_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define RTC_MODE1_CTRL_OFFSET       0x00         /**< \brief (RTC_MODE1_CTRL offset) MODE1 Control Register */
#define RTC_MODE1_CTRL_RESETVALUE   0x0000       /**< \brief (RTC_MODE1_CTRL reset_value) MODE1 Control Register */

#define RTC_MODE1_CTRL_SWRST_Pos    0            /**< \brief (RTC_MODE1_CTRL) Software Reset */
#define RTC_MODE1_CTRL_SWRST        (0x1u << RTC_MODE1_CTRL_SWRST_Pos)
#define RTC_MODE1_CTRL_ENABLE_Pos   1            /**< \brief (RTC_MODE1_CTRL) Enable */
#define RTC_MODE1_CTRL_ENABLE       (0x1u << RTC_MODE1_CTRL_ENABLE_Pos)
#define RTC_MODE1_CTRL_MODE_Pos     2            /**< \brief (RTC_MODE1_CTRL) Mode */
#define RTC_MODE1_CTRL_MODE_Msk     (0x3u << RTC_MODE1_CTRL_MODE_Pos)
#define RTC_MODE1_CTRL_MODE(value)  ((RTC_MODE1_CTRL_MODE_Msk & ((value) << RTC_MODE1_CTRL_MODE_Pos)))
#define   RTC_MODE1_CTRL_MODE_COUNT32 (0x0u <<  2) /**< \brief (RTC_MODE1_CTRL) Mode 0 */
#define   RTC_MODE1_CTRL_MODE_COUNT16 (0x1u <<  2) /**< \brief (RTC_MODE1_CTRL) Mode 1 */
#define   RTC_MODE1_CTRL_MODE_CLOCK (0x2u <<  2) /**< \brief (RTC_MODE1_CTRL) Mode 2 */
#define RTC_MODE1_CTRL_PRESCALER_Pos 8            /**< \brief (RTC_MODE1_CTRL) Prescaler */
#define RTC_MODE1_CTRL_PRESCALER_Msk (0xFu << RTC_MODE1_CTRL_PRESCALER_Pos)
#define RTC_MODE1_CTRL_PRESCALER(value) ((RTC_MODE1_CTRL_PRESCALER_Msk & ((value) << RTC_MODE1_CTRL_PRESCALER_Pos)))
#define   RTC_MODE1_CTRL_PRESCALER_DIV1 (0x0u <<  8) /**< \brief (RTC_MODE1_CTRL)  */
#define   RTC_MODE1_CTRL_PRESCALER_DIV2 (0x1u <<  8) /**< \brief (RTC_MODE1_CTRL)  */
#define   RTC_MODE1_CTRL_PRESCALER_DIV4 (0x2u <<  8) /**< \brief (RTC_MODE1_CTRL)  */
#define   RTC_MODE1_CTRL_PRESCALER_DIV8 (0x3u <<  8) /**< \brief (RTC_MODE1_CTRL)  */
#define   RTC_MODE1_CTRL_PRESCALER_DIV16 (0x4u <<  8) /**< \brief (RTC_MODE1_CTRL)  */
#define   RTC_MODE1_CTRL_PRESCALER_DIV32 (0x5u <<  8) /**< \brief (RTC_MODE1_CTRL)  */
#define   RTC_MODE1_CTRL_PRESCALER_DIV64 (0x6u <<  8) /**< \brief (RTC_MODE1_CTRL)  */
#define   RTC_MODE1_CTRL_PRESCALER_DIV128 (0x7u <<  8) /**< \brief (RTC_MODE1_CTRL)  */
#define   RTC_MODE1_CTRL_PRESCALER_DIV256 (0x8u <<  8) /**< \brief (RTC_MODE1_CTRL)  */
#define   RTC_MODE1_CTRL_PRESCALER_DIV512 (0x9u <<  8) /**< \brief (RTC_MODE1_CTRL)  */
#define   RTC_MODE1_CTRL_PRESCALER_DIV1024 (0xAu <<  8) /**< \brief (RTC_MODE1_CTRL)  */
#define RTC_MODE1_CTRL_MASK         0x0F0Fu      /**< \brief (RTC_MODE1_CTRL) MASK Register */

/* -------- RTC_MODE2_CTRL : (RTC Offset: 0x00) (R/W 16) MODE2 MODE2 Control Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint16_t SWRST:1;          /*!< bit:      0  Software Reset                     */
    uint16_t ENABLE:1;         /*!< bit:      1  Enable                             */
    uint16_t MODE:2;           /*!< bit:  2.. 3  Mode                               */
    uint16_t :2;               /*!< bit:  4.. 5  Reserved                           */
    uint16_t CLKREP:1;         /*!< bit:      6  Clock Representation               */
    uint16_t MATCHCLR:1;       /*!< bit:      7  Match Clears Counter               */
    uint16_t PRESCALER:4;      /*!< bit:  8..11  Prescaler                          */
    uint16_t :4;               /*!< bit: 12..15  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint16_t reg;                /*!< Type      used for register access              */
} RTC_MODE2_CTRL_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define RTC_MODE2_CTRL_OFFSET       0x00         /**< \brief (RTC_MODE2_CTRL offset) MODE2 Control Register */
#define RTC_MODE2_CTRL_RESETVALUE   0x0000       /**< \brief (RTC_MODE2_CTRL reset_value) MODE2 Control Register */

#define RTC_MODE2_CTRL_SWRST_Pos    0            /**< \brief (RTC_MODE2_CTRL) Software Reset */
#define RTC_MODE2_CTRL_SWRST        (0x1u << RTC_MODE2_CTRL_SWRST_Pos)
#define RTC_MODE2_CTRL_ENABLE_Pos   1            /**< \brief (RTC_MODE2_CTRL) Enable */
#define RTC_MODE2_CTRL_ENABLE       (0x1u << RTC_MODE2_CTRL_ENABLE_Pos)
#define RTC_MODE2_CTRL_MODE_Pos     2            /**< \brief (RTC_MODE2_CTRL) Mode */
#define RTC_MODE2_CTRL_MODE_Msk     (0x3u << RTC_MODE2_CTRL_MODE_Pos)
#define RTC_MODE2_CTRL_MODE(value)  ((RTC_MODE2_CTRL_MODE_Msk & ((value) << RTC_MODE2_CTRL_MODE_Pos)))
#define   RTC_MODE2_CTRL_MODE_COUNT32 (0x0u <<  2) /**< \brief (RTC_MODE2_CTRL) Mode 0 */
#define   RTC_MODE2_CTRL_MODE_COUNT16 (0x1u <<  2) /**< \brief (RTC_MODE2_CTRL) Mode 1 */
#define   RTC_MODE2_CTRL_MODE_CLOCK (0x2u <<  2) /**< \brief (RTC_MODE2_CTRL) Mode 2 */
#define RTC_MODE2_CTRL_CLKREP_Pos   6            /**< \brief (RTC_MODE2_CTRL) Clock Representation */
#define RTC_MODE2_CTRL_CLKREP       (0x1u << RTC_MODE2_CTRL_CLKREP_Pos)
#define RTC_MODE2_CTRL_MATCHCLR_Pos 7            /**< \brief (RTC_MODE2_CTRL) Match Clears Counter */
#define RTC_MODE2_CTRL_MATCHCLR     (0x1u << RTC_MODE2_CTRL_MATCHCLR_Pos)
#define RTC_MODE2_CTRL_PRESCALER_Pos 8            /**< \brief (RTC_MODE2_CTRL) Prescaler */
#define RTC_MODE2_CTRL_PRESCALER_Msk (0xFu << RTC_MODE2_CTRL_PRESCALER_Pos)
#define RTC_MODE2_CTRL_PRESCALER(value) ((RTC_MODE2_CTRL_PRESCALER_Msk & ((value) << RTC_MODE2_CTRL_PRESCALER_Pos)))
#define   RTC_MODE2_CTRL_PRESCALER_DIV1 (0x0u <<  8) /**< \brief (RTC_MODE2_CTRL)  */
#define   RTC_MODE2_CTRL_PRESCALER_DIV2 (0x1u <<  8) /**< \brief (RTC_MODE2_CTRL)  */
#define   RTC_MODE2_CTRL_PRESCALER_DIV4 (0x2u <<  8) /**< \brief (RTC_MODE2_CTRL)  */
#define   RTC_MODE2_CTRL_PRESCALER_DIV8 (0x3u <<  8) /**< \brief (RTC_MODE2_CTRL)  */
#define   RTC_MODE2_CTRL_PRESCALER_DIV16 (0x4u <<  8) /**< \brief (RTC_MODE2_CTRL)  */
#define   RTC_MODE2_CTRL_PRESCALER_DIV32 (0x5u <<  8) /**< \brief (RTC_MODE2_CTRL)  */
#define   RTC_MODE2_CTRL_PRESCALER_DIV64 (0x6u <<  8) /**< \brief (RTC_MODE2_CTRL)  */
#define   RTC_MODE2_CTRL_PRESCALER_DIV128 (0x7u <<  8) /**< \brief (RTC_MODE2_CTRL)  */
#define   RTC_MODE2_CTRL_PRESCALER_DIV256 (0x8u <<  8) /**< \brief (RTC_MODE2_CTRL)  */
#define   RTC_MODE2_CTRL_PRESCALER_DIV512 (0x9u <<  8) /**< \brief (RTC_MODE2_CTRL)  */
#define   RTC_MODE2_CTRL_PRESCALER_DIV1024 (0xAu <<  8) /**< \brief (RTC_MODE2_CTRL)  */
#define RTC_MODE2_CTRL_MASK         0x0FCFu      /**< \brief (RTC_MODE2_CTRL) MASK Register */

/* -------- RTC_READREQ : (RTC Offset: 0x02) (R/W 16) Read Request Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint16_t ADDR:6;           /*!< bit:  0.. 5  Read Address                       */
    uint16_t :8;               /*!< bit:  6..13  Reserved                           */
    uint16_t RCONT:1;          /*!< bit:     14  Read Continuously                  */
    uint16_t RREQ:1;           /*!< bit:     15  Read Request                       */
  } bit;                       /*!< Structure used for bit  access                  */
  uint16_t reg;                /*!< Type      used for register access              */
} RTC_READREQ_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define RTC_READREQ_OFFSET          0x02         /**< \brief (RTC_READREQ offset) Read Request Register */
#define RTC_READREQ_RESETVALUE      0x0010       /**< \brief (RTC_READREQ reset_value) Read Request Register */

#define RTC_READREQ_ADDR_Pos        0            /**< \brief (RTC_READREQ) Read Address */
#define RTC_READREQ_ADDR_Msk        (0x3Fu << RTC_READREQ_ADDR_Pos)
#define RTC_READREQ_ADDR(value)     ((RTC_READREQ_ADDR_Msk & ((value) << RTC_READREQ_ADDR_Pos)))
#define RTC_READREQ_RCONT_Pos       14           /**< \brief (RTC_READREQ) Read Continuously */
#define RTC_READREQ_RCONT           (0x1u << RTC_READREQ_RCONT_Pos)
#define RTC_READREQ_RREQ_Pos        15           /**< \brief (RTC_READREQ) Read Request */
#define RTC_READREQ_RREQ            (0x1u << RTC_READREQ_RREQ_Pos)
#define RTC_READREQ_MASK            0xC03Fu      /**< \brief (RTC_READREQ) MASK Register */

/* -------- RTC_MODE0_EVCTRL : (RTC Offset: 0x04) (R/W 16) MODE0 MODE0 Event Control Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint16_t PEREO:8;          /*!< bit:  0.. 7  Periodic Interval Event Output Enables */
    uint16_t CMPEO:1;          /*!< bit:      8  Compare Event Output Enables       */
    uint16_t :6;               /*!< bit:  9..14  Reserved                           */
    uint16_t OVFEO:1;          /*!< bit:     15  Overflow Event Output Enable       */
  } bit;                       /*!< Structure used for bit  access                  */
  uint16_t reg;                /*!< Type      used for register access              */
} RTC_MODE0_EVCTRL_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define RTC_MODE0_EVCTRL_OFFSET     0x04         /**< \brief (RTC_MODE0_EVCTRL offset) MODE0 Event Control Register */
#define RTC_MODE0_EVCTRL_RESETVALUE 0x0000       /**< \brief (RTC_MODE0_EVCTRL reset_value) MODE0 Event Control Register */

#define RTC_MODE0_EVCTRL_PEREO_Pos  0            /**< \brief (RTC_MODE0_EVCTRL) Periodic Interval Event Output Enables */
#define RTC_MODE0_EVCTRL_PEREO_Msk  (0xFFu << RTC_MODE0_EVCTRL_PEREO_Pos)
#define RTC_MODE0_EVCTRL_PEREO(value) ((RTC_MODE0_EVCTRL_PEREO_Msk & ((value) << RTC_MODE0_EVCTRL_PEREO_Pos)))
#define RTC_MODE0_EVCTRL_CMPEO_Pos  8            /**< \brief (RTC_MODE0_EVCTRL) Compare Event Output Enables */
#define RTC_MODE0_EVCTRL_CMPEO_Msk  (0x1u << RTC_MODE0_EVCTRL_CMPEO_Pos)
#define RTC_MODE0_EVCTRL_CMPEO(value) ((RTC_MODE0_EVCTRL_CMPEO_Msk & ((value) << RTC_MODE0_EVCTRL_CMPEO_Pos)))
#define RTC_MODE0_EVCTRL_OVFEO_Pos  15           /**< \brief (RTC_MODE0_EVCTRL) Overflow Event Output Enable */
#define RTC_MODE0_EVCTRL_OVFEO      (0x1u << RTC_MODE0_EVCTRL_OVFEO_Pos)
#define RTC_MODE0_EVCTRL_MASK       0x81FFu      /**< \brief (RTC_MODE0_EVCTRL) MASK Register */

/* -------- RTC_MODE1_EVCTRL : (RTC Offset: 0x04) (R/W 16) MODE1 MODE1 Event Control Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint16_t PEREO:8;          /*!< bit:  0.. 7  Periodic Interval Event Output Enables */
    uint16_t CMPEO:2;          /*!< bit:  8.. 9  Compare Event Output Enables       */
    uint16_t :5;               /*!< bit: 10..14  Reserved                           */
    uint16_t OVFEO:1;          /*!< bit:     15  Overflow Event Output Enable       */
  } bit;                       /*!< Structure used for bit  access                  */
  uint16_t reg;                /*!< Type      used for register access              */
} RTC_MODE1_EVCTRL_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define RTC_MODE1_EVCTRL_OFFSET     0x04         /**< \brief (RTC_MODE1_EVCTRL offset) MODE1 Event Control Register */
#define RTC_MODE1_EVCTRL_RESETVALUE 0x0000       /**< \brief (RTC_MODE1_EVCTRL reset_value) MODE1 Event Control Register */

#define RTC_MODE1_EVCTRL_PEREO_Pos  0            /**< \brief (RTC_MODE1_EVCTRL) Periodic Interval Event Output Enables */
#define RTC_MODE1_EVCTRL_PEREO_Msk  (0xFFu << RTC_MODE1_EVCTRL_PEREO_Pos)
#define RTC_MODE1_EVCTRL_PEREO(value) ((RTC_MODE1_EVCTRL_PEREO_Msk & ((value) << RTC_MODE1_EVCTRL_PEREO_Pos)))
#define RTC_MODE1_EVCTRL_CMPEO_Pos  8            /**< \brief (RTC_MODE1_EVCTRL) Compare Event Output Enables */
#define RTC_MODE1_EVCTRL_CMPEO_Msk  (0x3u << RTC_MODE1_EVCTRL_CMPEO_Pos)
#define RTC_MODE1_EVCTRL_CMPEO(value) ((RTC_MODE1_EVCTRL_CMPEO_Msk & ((value) << RTC_MODE1_EVCTRL_CMPEO_Pos)))
#define RTC_MODE1_EVCTRL_OVFEO_Pos  15           /**< \brief (RTC_MODE1_EVCTRL) Overflow Event Output Enable */
#define RTC_MODE1_EVCTRL_OVFEO      (0x1u << RTC_MODE1_EVCTRL_OVFEO_Pos)
#define RTC_MODE1_EVCTRL_MASK       0x83FFu      /**< \brief (RTC_MODE1_EVCTRL) MASK Register */

/* -------- RTC_MODE2_EVCTRL : (RTC Offset: 0x04) (R/W 16) MODE2 MODE2 Event Control Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint16_t PEREO:8;          /*!< bit:  0.. 7  Periodic Interval Event Output Enables */
    uint16_t ALARMEO:1;        /*!< bit:      8  Alarm 0Event Output Enables        */
    uint16_t :6;               /*!< bit:  9..14  Reserved                           */
    uint16_t OVFEO:1;          /*!< bit:     15  Overflow Event Output Enable       */
  } bit;                       /*!< Structure used for bit  access                  */
  uint16_t reg;                /*!< Type      used for register access              */
} RTC_MODE2_EVCTRL_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define RTC_MODE2_EVCTRL_OFFSET     0x04         /**< \brief (RTC_MODE2_EVCTRL offset) MODE2 Event Control Register */
#define RTC_MODE2_EVCTRL_RESETVALUE 0x0000       /**< \brief (RTC_MODE2_EVCTRL reset_value) MODE2 Event Control Register */

#define RTC_MODE2_EVCTRL_PEREO_Pos  0            /**< \brief (RTC_MODE2_EVCTRL) Periodic Interval Event Output Enables */
#define RTC_MODE2_EVCTRL_PEREO_Msk  (0xFFu << RTC_MODE2_EVCTRL_PEREO_Pos)
#define RTC_MODE2_EVCTRL_PEREO(value) ((RTC_MODE2_EVCTRL_PEREO_Msk & ((value) << RTC_MODE2_EVCTRL_PEREO_Pos)))
#define RTC_MODE2_EVCTRL_ALARMEO_Pos 8            /**< \brief (RTC_MODE2_EVCTRL) Alarm 0Event Output Enables */
#define RTC_MODE2_EVCTRL_ALARMEO_Msk (0x1u << RTC_MODE2_EVCTRL_ALARMEO_Pos)
#define RTC_MODE2_EVCTRL_ALARMEO(value) ((RTC_MODE2_EVCTRL_ALARMEO_Msk & ((value) << RTC_MODE2_EVCTRL_ALARMEO_Pos)))
#define RTC_MODE2_EVCTRL_OVFEO_Pos  15           /**< \brief (RTC_MODE2_EVCTRL) Overflow Event Output Enable */
#define RTC_MODE2_EVCTRL_OVFEO      (0x1u << RTC_MODE2_EVCTRL_OVFEO_Pos)
#define RTC_MODE2_EVCTRL_MASK       0x81FFu      /**< \brief (RTC_MODE2_EVCTRL) MASK Register */

/* -------- RTC_MODE0_INTENCLR : (RTC Offset: 0x06) (R/W  8) MODE0 MODE0 Interrupt Enable Clear Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  CMP:1;            /*!< bit:      0  Comparator Interrupt Disables      */
    uint8_t  :5;               /*!< bit:  1.. 5  Reserved                           */
    uint8_t  SYNCRDY:1;        /*!< bit:      6  Synchronization Ready Interrupt Disable */
    uint8_t  OVF:1;            /*!< bit:      7  Overflow Interrupt Disable         */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} RTC_MODE0_INTENCLR_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define RTC_MODE0_INTENCLR_OFFSET   0x06         /**< \brief (RTC_MODE0_INTENCLR offset) MODE0 Interrupt Enable Clear Register */
#define RTC_MODE0_INTENCLR_RESETVALUE 0x00         /**< \brief (RTC_MODE0_INTENCLR reset_value) MODE0 Interrupt Enable Clear Register */

#define RTC_MODE0_INTENCLR_CMP_Pos  0            /**< \brief (RTC_MODE0_INTENCLR) Comparator Interrupt Disables */
#define RTC_MODE0_INTENCLR_CMP_Msk  (0x1u << RTC_MODE0_INTENCLR_CMP_Pos)
#define RTC_MODE0_INTENCLR_CMP(value) ((RTC_MODE0_INTENCLR_CMP_Msk & ((value) << RTC_MODE0_INTENCLR_CMP_Pos)))
#define RTC_MODE0_INTENCLR_SYNCRDY_Pos 6            /**< \brief (RTC_MODE0_INTENCLR) Synchronization Ready Interrupt Disable */
#define RTC_MODE0_INTENCLR_SYNCRDY  (0x1u << RTC_MODE0_INTENCLR_SYNCRDY_Pos)
#define RTC_MODE0_INTENCLR_OVF_Pos  7            /**< \brief (RTC_MODE0_INTENCLR) Overflow Interrupt Disable */
#define RTC_MODE0_INTENCLR_OVF      (0x1u << RTC_MODE0_INTENCLR_OVF_Pos)
#define RTC_MODE0_INTENCLR_MASK     0xC1u        /**< \brief (RTC_MODE0_INTENCLR) MASK Register */

/* -------- RTC_MODE1_INTENCLR : (RTC Offset: 0x06) (R/W  8) MODE1 MODE1 Interrupt Enable Clear Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  CMP:2;            /*!< bit:  0.. 1  Comparator Interrupt Disables      */
    uint8_t  :4;               /*!< bit:  2.. 5  Reserved                           */
    uint8_t  SYNCRDY:1;        /*!< bit:      6  Synchronization Ready Interrupt Disable */
    uint8_t  OVF:1;            /*!< bit:      7  Overflow Interrupt Disable         */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} RTC_MODE1_INTENCLR_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define RTC_MODE1_INTENCLR_OFFSET   0x06         /**< \brief (RTC_MODE1_INTENCLR offset) MODE1 Interrupt Enable Clear Register */
#define RTC_MODE1_INTENCLR_RESETVALUE 0x00         /**< \brief (RTC_MODE1_INTENCLR reset_value) MODE1 Interrupt Enable Clear Register */

#define RTC_MODE1_INTENCLR_CMP_Pos  0            /**< \brief (RTC_MODE1_INTENCLR) Comparator Interrupt Disables */
#define RTC_MODE1_INTENCLR_CMP_Msk  (0x3u << RTC_MODE1_INTENCLR_CMP_Pos)
#define RTC_MODE1_INTENCLR_CMP(value) ((RTC_MODE1_INTENCLR_CMP_Msk & ((value) << RTC_MODE1_INTENCLR_CMP_Pos)))
#define RTC_MODE1_INTENCLR_SYNCRDY_Pos 6            /**< \brief (RTC_MODE1_INTENCLR) Synchronization Ready Interrupt Disable */
#define RTC_MODE1_INTENCLR_SYNCRDY  (0x1u << RTC_MODE1_INTENCLR_SYNCRDY_Pos)
#define RTC_MODE1_INTENCLR_OVF_Pos  7            /**< \brief (RTC_MODE1_INTENCLR) Overflow Interrupt Disable */
#define RTC_MODE1_INTENCLR_OVF      (0x1u << RTC_MODE1_INTENCLR_OVF_Pos)
#define RTC_MODE1_INTENCLR_MASK     0xC3u        /**< \brief (RTC_MODE1_INTENCLR) MASK Register */

/* -------- RTC_MODE2_INTENCLR : (RTC Offset: 0x06) (R/W  8) MODE2 MODE2 Interrupt Enable Clear Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  ALARM:1;          /*!< bit:      0  Alarm Interrupt Disables           */
    uint8_t  :5;               /*!< bit:  1.. 5  Reserved                           */
    uint8_t  SYNCRDY:1;        /*!< bit:      6  Synchronization Ready Interrupt Disable */
    uint8_t  OVF:1;            /*!< bit:      7  Overflow Interrupt Disable         */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} RTC_MODE2_INTENCLR_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define RTC_MODE2_INTENCLR_OFFSET   0x06         /**< \brief (RTC_MODE2_INTENCLR offset) MODE2 Interrupt Enable Clear Register */
#define RTC_MODE2_INTENCLR_RESETVALUE 0x00         /**< \brief (RTC_MODE2_INTENCLR reset_value) MODE2 Interrupt Enable Clear Register */

#define RTC_MODE2_INTENCLR_ALARM_Pos 0            /**< \brief (RTC_MODE2_INTENCLR) Alarm Interrupt Disables */
#define RTC_MODE2_INTENCLR_ALARM_Msk (0x1u << RTC_MODE2_INTENCLR_ALARM_Pos)
#define RTC_MODE2_INTENCLR_ALARM(value) ((RTC_MODE2_INTENCLR_ALARM_Msk & ((value) << RTC_MODE2_INTENCLR_ALARM_Pos)))
#define RTC_MODE2_INTENCLR_SYNCRDY_Pos 6            /**< \brief (RTC_MODE2_INTENCLR) Synchronization Ready Interrupt Disable */
#define RTC_MODE2_INTENCLR_SYNCRDY  (0x1u << RTC_MODE2_INTENCLR_SYNCRDY_Pos)
#define RTC_MODE2_INTENCLR_OVF_Pos  7            /**< \brief (RTC_MODE2_INTENCLR) Overflow Interrupt Disable */
#define RTC_MODE2_INTENCLR_OVF      (0x1u << RTC_MODE2_INTENCLR_OVF_Pos)
#define RTC_MODE2_INTENCLR_MASK     0xC1u        /**< \brief (RTC_MODE2_INTENCLR) MASK Register */

/* -------- RTC_MODE0_INTENSET : (RTC Offset: 0x07) (R/W  8) MODE0 MODE0 Interrupt Enable Set Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  CMP:1;            /*!< bit:      0  Comparator Interrupt Enables       */
    uint8_t  :5;               /*!< bit:  1.. 5  Reserved                           */
    uint8_t  SYNCRDY:1;        /*!< bit:      6  Synchronization Ready Interrupt Enable */
    uint8_t  OVF:1;            /*!< bit:      7  Overflow Interrupt Enable          */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} RTC_MODE0_INTENSET_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define RTC_MODE0_INTENSET_OFFSET   0x07         /**< \brief (RTC_MODE0_INTENSET offset) MODE0 Interrupt Enable Set Register */
#define RTC_MODE0_INTENSET_RESETVALUE 0x00         /**< \brief (RTC_MODE0_INTENSET reset_value) MODE0 Interrupt Enable Set Register */

#define RTC_MODE0_INTENSET_CMP_Pos  0            /**< \brief (RTC_MODE0_INTENSET) Comparator Interrupt Enables */
#define RTC_MODE0_INTENSET_CMP_Msk  (0x1u << RTC_MODE0_INTENSET_CMP_Pos)
#define RTC_MODE0_INTENSET_CMP(value) ((RTC_MODE0_INTENSET_CMP_Msk & ((value) << RTC_MODE0_INTENSET_CMP_Pos)))
#define RTC_MODE0_INTENSET_SYNCRDY_Pos 6            /**< \brief (RTC_MODE0_INTENSET) Synchronization Ready Interrupt Enable */
#define RTC_MODE0_INTENSET_SYNCRDY  (0x1u << RTC_MODE0_INTENSET_SYNCRDY_Pos)
#define RTC_MODE0_INTENSET_OVF_Pos  7            /**< \brief (RTC_MODE0_INTENSET) Overflow Interrupt Enable */
#define RTC_MODE0_INTENSET_OVF      (0x1u << RTC_MODE0_INTENSET_OVF_Pos)
#define RTC_MODE0_INTENSET_MASK     0xC1u        /**< \brief (RTC_MODE0_INTENSET) MASK Register */

/* -------- RTC_MODE1_INTENSET : (RTC Offset: 0x07) (R/W  8) MODE1 MODE1 Interrupt Enable Set Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  CMP:2;            /*!< bit:  0.. 1  Comparator Interrupt Enables       */
    uint8_t  :4;               /*!< bit:  2.. 5  Reserved                           */
    uint8_t  SYNCRDY:1;        /*!< bit:      6  Synchronization Ready Interrupt Enable */
    uint8_t  OVF:1;            /*!< bit:      7  Overflow Interrupt Enable          */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} RTC_MODE1_INTENSET_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define RTC_MODE1_INTENSET_OFFSET   0x07         /**< \brief (RTC_MODE1_INTENSET offset) MODE1 Interrupt Enable Set Register */
#define RTC_MODE1_INTENSET_RESETVALUE 0x00         /**< \brief (RTC_MODE1_INTENSET reset_value) MODE1 Interrupt Enable Set Register */

#define RTC_MODE1_INTENSET_CMP_Pos  0            /**< \brief (RTC_MODE1_INTENSET) Comparator Interrupt Enables */
#define RTC_MODE1_INTENSET_CMP_Msk  (0x3u << RTC_MODE1_INTENSET_CMP_Pos)
#define RTC_MODE1_INTENSET_CMP(value) ((RTC_MODE1_INTENSET_CMP_Msk & ((value) << RTC_MODE1_INTENSET_CMP_Pos)))
#define RTC_MODE1_INTENSET_SYNCRDY_Pos 6            /**< \brief (RTC_MODE1_INTENSET) Synchronization Ready Interrupt Enable */
#define RTC_MODE1_INTENSET_SYNCRDY  (0x1u << RTC_MODE1_INTENSET_SYNCRDY_Pos)
#define RTC_MODE1_INTENSET_OVF_Pos  7            /**< \brief (RTC_MODE1_INTENSET) Overflow Interrupt Enable */
#define RTC_MODE1_INTENSET_OVF      (0x1u << RTC_MODE1_INTENSET_OVF_Pos)
#define RTC_MODE1_INTENSET_MASK     0xC3u        /**< \brief (RTC_MODE1_INTENSET) MASK Register */

/* -------- RTC_MODE2_INTENSET : (RTC Offset: 0x07) (R/W  8) MODE2 MODE2 Interrupt Enable Set Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  ALARM:1;          /*!< bit:      0  Alarm Interrupt Enables            */
    uint8_t  :5;               /*!< bit:  1.. 5  Reserved                           */
    uint8_t  SYNCRDY:1;        /*!< bit:      6  Synchronization Ready Interrupt Enable */
    uint8_t  OVF:1;            /*!< bit:      7  Overflow Interrupt Enable          */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} RTC_MODE2_INTENSET_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define RTC_MODE2_INTENSET_OFFSET   0x07         /**< \brief (RTC_MODE2_INTENSET offset) MODE2 Interrupt Enable Set Register */
#define RTC_MODE2_INTENSET_RESETVALUE 0x00         /**< \brief (RTC_MODE2_INTENSET reset_value) MODE2 Interrupt Enable Set Register */

#define RTC_MODE2_INTENSET_ALARM_Pos 0            /**< \brief (RTC_MODE2_INTENSET) Alarm Interrupt Enables */
#define RTC_MODE2_INTENSET_ALARM_Msk (0x1u << RTC_MODE2_INTENSET_ALARM_Pos)
#define RTC_MODE2_INTENSET_ALARM(value) ((RTC_MODE2_INTENSET_ALARM_Msk & ((value) << RTC_MODE2_INTENSET_ALARM_Pos)))
#define RTC_MODE2_INTENSET_SYNCRDY_Pos 6            /**< \brief (RTC_MODE2_INTENSET) Synchronization Ready Interrupt Enable */
#define RTC_MODE2_INTENSET_SYNCRDY  (0x1u << RTC_MODE2_INTENSET_SYNCRDY_Pos)
#define RTC_MODE2_INTENSET_OVF_Pos  7            /**< \brief (RTC_MODE2_INTENSET) Overflow Interrupt Enable */
#define RTC_MODE2_INTENSET_OVF      (0x1u << RTC_MODE2_INTENSET_OVF_Pos)
#define RTC_MODE2_INTENSET_MASK     0xC1u        /**< \brief (RTC_MODE2_INTENSET) MASK Register */

/* -------- RTC_MODE0_INTFLAG : (RTC Offset: 0x08) (R/W  8) MODE0 MODE0 Interrupt Flag Status and Clear Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  CMP:1;            /*!< bit:      0  Comparator Interrupt Flags         */
    uint8_t  :5;               /*!< bit:  1.. 5  Reserved                           */
    uint8_t  SYNCRDY:1;        /*!< bit:      6  Synchronization Ready Interrupt Flag */
    uint8_t  OVF:1;            /*!< bit:      7  Overflow Interrupt Flag            */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} RTC_MODE0_INTFLAG_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define RTC_MODE0_INTFLAG_OFFSET    0x08         /**< \brief (RTC_MODE0_INTFLAG offset) MODE0 Interrupt Flag Status and Clear Register */
#define RTC_MODE0_INTFLAG_RESETVALUE 0x00         /**< \brief (RTC_MODE0_INTFLAG reset_value) MODE0 Interrupt Flag Status and Clear Register */

#define RTC_MODE0_INTFLAG_CMP_Pos   0            /**< \brief (RTC_MODE0_INTFLAG) Comparator Interrupt Flags */
#define RTC_MODE0_INTFLAG_CMP_Msk   (0x1u << RTC_MODE0_INTFLAG_CMP_Pos)
#define RTC_MODE0_INTFLAG_CMP(value) ((RTC_MODE0_INTFLAG_CMP_Msk & ((value) << RTC_MODE0_INTFLAG_CMP_Pos)))
#define RTC_MODE0_INTFLAG_SYNCRDY_Pos 6            /**< \brief (RTC_MODE0_INTFLAG) Synchronization Ready Interrupt Flag */
#define RTC_MODE0_INTFLAG_SYNCRDY   (0x1u << RTC_MODE0_INTFLAG_SYNCRDY_Pos)
#define RTC_MODE0_INTFLAG_OVF_Pos   7            /**< \brief (RTC_MODE0_INTFLAG) Overflow Interrupt Flag */
#define RTC_MODE0_INTFLAG_OVF       (0x1u << RTC_MODE0_INTFLAG_OVF_Pos)
#define RTC_MODE0_INTFLAG_MASK      0xC1u        /**< \brief (RTC_MODE0_INTFLAG) MASK Register */

/* -------- RTC_MODE1_INTFLAG : (RTC Offset: 0x08) (R/W  8) MODE1 MODE1 Interrupt Flag Status and Clear Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  CMP:2;            /*!< bit:  0.. 1  Comparator Interrupt Flags         */
    uint8_t  :4;               /*!< bit:  2.. 5  Reserved                           */
    uint8_t  SYNCRDY:1;        /*!< bit:      6  Synchronization Ready Interrupt Flag */
    uint8_t  OVF:1;            /*!< bit:      7  Overflow Interrupt Flag            */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} RTC_MODE1_INTFLAG_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define RTC_MODE1_INTFLAG_OFFSET    0x08         /**< \brief (RTC_MODE1_INTFLAG offset) MODE1 Interrupt Flag Status and Clear Register */
#define RTC_MODE1_INTFLAG_RESETVALUE 0x00         /**< \brief (RTC_MODE1_INTFLAG reset_value) MODE1 Interrupt Flag Status and Clear Register */

#define RTC_MODE1_INTFLAG_CMP_Pos   0            /**< \brief (RTC_MODE1_INTFLAG) Comparator Interrupt Flags */
#define RTC_MODE1_INTFLAG_CMP_Msk   (0x3u << RTC_MODE1_INTFLAG_CMP_Pos)
#define RTC_MODE1_INTFLAG_CMP(value) ((RTC_MODE1_INTFLAG_CMP_Msk & ((value) << RTC_MODE1_INTFLAG_CMP_Pos)))
#define RTC_MODE1_INTFLAG_SYNCRDY_Pos 6            /**< \brief (RTC_MODE1_INTFLAG) Synchronization Ready Interrupt Flag */
#define RTC_MODE1_INTFLAG_SYNCRDY   (0x1u << RTC_MODE1_INTFLAG_SYNCRDY_Pos)
#define RTC_MODE1_INTFLAG_OVF_Pos   7            /**< \brief (RTC_MODE1_INTFLAG) Overflow Interrupt Flag */
#define RTC_MODE1_INTFLAG_OVF       (0x1u << RTC_MODE1_INTFLAG_OVF_Pos)
#define RTC_MODE1_INTFLAG_MASK      0xC3u        /**< \brief (RTC_MODE1_INTFLAG) MASK Register */

/* -------- RTC_MODE2_INTFLAG : (RTC Offset: 0x08) (R/W  8) MODE2 MODE2 Interrupt Flag Status and Clear Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  ALARM:1;          /*!< bit:      0  Alarm Interrupt Flags              */
    uint8_t  :5;               /*!< bit:  1.. 5  Reserved                           */
    uint8_t  SYNCRDY:1;        /*!< bit:      6  Synchronization Ready Interrupt Flag */
    uint8_t  OVF:1;            /*!< bit:      7  Overflow Interrupt Flag            */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} RTC_MODE2_INTFLAG_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define RTC_MODE2_INTFLAG_OFFSET    0x08         /**< \brief (RTC_MODE2_INTFLAG offset) MODE2 Interrupt Flag Status and Clear Register */
#define RTC_MODE2_INTFLAG_RESETVALUE 0x00         /**< \brief (RTC_MODE2_INTFLAG reset_value) MODE2 Interrupt Flag Status and Clear Register */

#define RTC_MODE2_INTFLAG_ALARM_Pos 0            /**< \brief (RTC_MODE2_INTFLAG) Alarm Interrupt Flags */
#define RTC_MODE2_INTFLAG_ALARM_Msk (0x1u << RTC_MODE2_INTFLAG_ALARM_Pos)
#define RTC_MODE2_INTFLAG_ALARM(value) ((RTC_MODE2_INTFLAG_ALARM_Msk & ((value) << RTC_MODE2_INTFLAG_ALARM_Pos)))
#define RTC_MODE2_INTFLAG_SYNCRDY_Pos 6            /**< \brief (RTC_MODE2_INTFLAG) Synchronization Ready Interrupt Flag */
#define RTC_MODE2_INTFLAG_SYNCRDY   (0x1u << RTC_MODE2_INTFLAG_SYNCRDY_Pos)
#define RTC_MODE2_INTFLAG_OVF_Pos   7            /**< \brief (RTC_MODE2_INTFLAG) Overflow Interrupt Flag */
#define RTC_MODE2_INTFLAG_OVF       (0x1u << RTC_MODE2_INTFLAG_OVF_Pos)
#define RTC_MODE2_INTFLAG_MASK      0xC1u        /**< \brief (RTC_MODE2_INTFLAG) MASK Register */

/* -------- RTC_STATUS : (RTC Offset: 0x0A) (R/W  8) Status Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  :7;               /*!< bit:  0.. 6  Reserved                           */
    uint8_t  SYNCBUSY:1;       /*!< bit:      7  Synchronization Busy Status        */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} RTC_STATUS_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define RTC_STATUS_OFFSET           0x0A         /**< \brief (RTC_STATUS offset) Status Register */
#define RTC_STATUS_RESETVALUE       0x00         /**< \brief (RTC_STATUS reset_value) Status Register */

#define RTC_STATUS_SYNCBUSY_Pos     7            /**< \brief (RTC_STATUS) Synchronization Busy Status */
#define RTC_STATUS_SYNCBUSY         (0x1u << RTC_STATUS_SYNCBUSY_Pos)
#define RTC_STATUS_MASK             0x80u        /**< \brief (RTC_STATUS) MASK Register */

/* -------- RTC_DBGCTRL : (RTC Offset: 0x0B) (R/W  8) Debug Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  DBGRUN:1;         /*!< bit:      0  Run During Debug                   */
    uint8_t  :7;               /*!< bit:  1.. 7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} RTC_DBGCTRL_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define RTC_DBGCTRL_OFFSET          0x0B         /**< \brief (RTC_DBGCTRL offset) Debug Register */
#define RTC_DBGCTRL_RESETVALUE      0x00         /**< \brief (RTC_DBGCTRL reset_value) Debug Register */

#define RTC_DBGCTRL_DBGRUN_Pos      0            /**< \brief (RTC_DBGCTRL) Run During Debug */
#define RTC_DBGCTRL_DBGRUN          (0x1u << RTC_DBGCTRL_DBGRUN_Pos)
#define RTC_DBGCTRL_MASK            0x01u        /**< \brief (RTC_DBGCTRL) MASK Register */

/* -------- RTC_FREQCORR : (RTC Offset: 0x0C) (R/W  8) Frequency Correction Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  VALUE:7;          /*!< bit:  0.. 6  Correction Value                   */
    uint8_t  SIGN:1;           /*!< bit:      7  Correction Sign                    */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} RTC_FREQCORR_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define RTC_FREQCORR_OFFSET         0x0C         /**< \brief (RTC_FREQCORR offset) Frequency Correction Register */
#define RTC_FREQCORR_RESETVALUE     0x00         /**< \brief (RTC_FREQCORR reset_value) Frequency Correction Register */

#define RTC_FREQCORR_VALUE_Pos      0            /**< \brief (RTC_FREQCORR) Correction Value */
#define RTC_FREQCORR_VALUE_Msk      (0x7Fu << RTC_FREQCORR_VALUE_Pos)
#define RTC_FREQCORR_VALUE(value)   ((RTC_FREQCORR_VALUE_Msk & ((value) << RTC_FREQCORR_VALUE_Pos)))
#define RTC_FREQCORR_SIGN_Pos       7            /**< \brief (RTC_FREQCORR) Correction Sign */
#define RTC_FREQCORR_SIGN           (0x1u << RTC_FREQCORR_SIGN_Pos)
#define RTC_FREQCORR_MASK           0xFFu        /**< \brief (RTC_FREQCORR) MASK Register */

/* -------- RTC_MODE0_COUNT : (RTC Offset: 0x10) (R/W 32) MODE0 MODE0 Count Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t COUNT:32;         /*!< bit:  0..31  Counter Value                      */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} RTC_MODE0_COUNT_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define RTC_MODE0_COUNT_OFFSET      0x10         /**< \brief (RTC_MODE0_COUNT offset) MODE0 Count Register */
#define RTC_MODE0_COUNT_RESETVALUE  0x00000000   /**< \brief (RTC_MODE0_COUNT reset_value) MODE0 Count Register */

#define RTC_MODE0_COUNT_COUNT_Pos   0            /**< \brief (RTC_MODE0_COUNT) Counter Value */
#define RTC_MODE0_COUNT_COUNT_Msk   (0xFFFFFFFFu << RTC_MODE0_COUNT_COUNT_Pos)
#define RTC_MODE0_COUNT_COUNT(value) ((RTC_MODE0_COUNT_COUNT_Msk & ((value) << RTC_MODE0_COUNT_COUNT_Pos)))
#define RTC_MODE0_COUNT_MASK        0xFFFFFFFFu  /**< \brief (RTC_MODE0_COUNT) MASK Register */

/* -------- RTC_MODE1_COUNT : (RTC Offset: 0x10) (R/W 16) MODE1 MODE1 Count Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint16_t COUNT:16;         /*!< bit:  0..15  Counter Value                      */
  } bit;                       /*!< Structure used for bit  access                  */
  uint16_t reg;                /*!< Type      used for register access              */
} RTC_MODE1_COUNT_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define RTC_MODE1_COUNT_OFFSET      0x10         /**< \brief (RTC_MODE1_COUNT offset) MODE1 Count Register */
#define RTC_MODE1_COUNT_RESETVALUE  0x0000       /**< \brief (RTC_MODE1_COUNT reset_value) MODE1 Count Register */

#define RTC_MODE1_COUNT_COUNT_Pos   0            /**< \brief (RTC_MODE1_COUNT) Counter Value */
#define RTC_MODE1_COUNT_COUNT_Msk   (0xFFFFu << RTC_MODE1_COUNT_COUNT_Pos)
#define RTC_MODE1_COUNT_COUNT(value) ((RTC_MODE1_COUNT_COUNT_Msk & ((value) << RTC_MODE1_COUNT_COUNT_Pos)))
#define RTC_MODE1_COUNT_MASK        0xFFFFu      /**< \brief (RTC_MODE1_COUNT) MASK Register */

/* -------- RTC_MODE2_CLOCK : (RTC Offset: 0x10) (R/W 32) MODE2 MODE2 Clock Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t SECOND:6;         /*!< bit:  0.. 5  Current Second                     */
    uint32_t MINUTE:6;         /*!< bit:  6..11  Current Minute                     */
    uint32_t HOUR:5;           /*!< bit: 12..16  Current Hour                       */
    uint32_t DAY:5;            /*!< bit: 17..21  Current Day                        */
    uint32_t MONTH:4;          /*!< bit: 22..25  Current Month                      */
    uint32_t YEAR:6;           /*!< bit: 26..31  Current Year                       */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} RTC_MODE2_CLOCK_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define RTC_MODE2_CLOCK_OFFSET      0x10         /**< \brief (RTC_MODE2_CLOCK offset) MODE2 Clock Register */
#define RTC_MODE2_CLOCK_RESETVALUE  0x00000000   /**< \brief (RTC_MODE2_CLOCK reset_value) MODE2 Clock Register */

#define RTC_MODE2_CLOCK_SECOND_Pos  0            /**< \brief (RTC_MODE2_CLOCK) Current Second */
#define RTC_MODE2_CLOCK_SECOND_Msk  (0x3Fu << RTC_MODE2_CLOCK_SECOND_Pos)
#define RTC_MODE2_CLOCK_SECOND(value) ((RTC_MODE2_CLOCK_SECOND_Msk & ((value) << RTC_MODE2_CLOCK_SECOND_Pos)))
#define RTC_MODE2_CLOCK_MINUTE_Pos  6            /**< \brief (RTC_MODE2_CLOCK) Current Minute */
#define RTC_MODE2_CLOCK_MINUTE_Msk  (0x3Fu << RTC_MODE2_CLOCK_MINUTE_Pos)
#define RTC_MODE2_CLOCK_MINUTE(value) ((RTC_MODE2_CLOCK_MINUTE_Msk & ((value) << RTC_MODE2_CLOCK_MINUTE_Pos)))
#define RTC_MODE2_CLOCK_HOUR_Pos    12           /**< \brief (RTC_MODE2_CLOCK) Current Hour */
#define RTC_MODE2_CLOCK_HOUR_Msk    (0x1Fu << RTC_MODE2_CLOCK_HOUR_Pos)
#define RTC_MODE2_CLOCK_HOUR(value) ((RTC_MODE2_CLOCK_HOUR_Msk & ((value) << RTC_MODE2_CLOCK_HOUR_Pos)))
#define   RTC_MODE2_CLOCK_HOUR_PM   (0x10u << 12) /**< \brief (RTC_MODE2_CLOCK)  */
#define RTC_MODE2_CLOCK_DAY_Pos     17           /**< \brief (RTC_MODE2_CLOCK) Current Day */
#define RTC_MODE2_CLOCK_DAY_Msk     (0x1Fu << RTC_MODE2_CLOCK_DAY_Pos)
#define RTC_MODE2_CLOCK_DAY(value)  ((RTC_MODE2_CLOCK_DAY_Msk & ((value) << RTC_MODE2_CLOCK_DAY_Pos)))
#define RTC_MODE2_CLOCK_MONTH_Pos   22           /**< \brief (RTC_MODE2_CLOCK) Current Month */
#define RTC_MODE2_CLOCK_MONTH_Msk   (0xFu << RTC_MODE2_CLOCK_MONTH_Pos)
#define RTC_MODE2_CLOCK_MONTH(value) ((RTC_MODE2_CLOCK_MONTH_Msk & ((value) << RTC_MODE2_CLOCK_MONTH_Pos)))
#define RTC_MODE2_CLOCK_YEAR_Pos    26           /**< \brief (RTC_MODE2_CLOCK) Current Year */
#define RTC_MODE2_CLOCK_YEAR_Msk    (0x3Fu << RTC_MODE2_CLOCK_YEAR_Pos)
#define RTC_MODE2_CLOCK_YEAR(value) ((RTC_MODE2_CLOCK_YEAR_Msk & ((value) << RTC_MODE2_CLOCK_YEAR_Pos)))
#define RTC_MODE2_CLOCK_MASK        0xFFFFFFFFu  /**< \brief (RTC_MODE2_CLOCK) MASK Register */

/* -------- RTC_MODE1_PER : (RTC Offset: 0x14) (R/W 16) MODE1 MODE1 Period Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint16_t PER:16;           /*!< bit:  0..15  Counter Period                     */
  } bit;                       /*!< Structure used for bit  access                  */
  uint16_t reg;                /*!< Type      used for register access              */
} RTC_MODE1_PER_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define RTC_MODE1_PER_OFFSET        0x14         /**< \brief (RTC_MODE1_PER offset) MODE1 Period Register */
#define RTC_MODE1_PER_RESETVALUE    0x0000       /**< \brief (RTC_MODE1_PER reset_value) MODE1 Period Register */

#define RTC_MODE1_PER_PER_Pos       0            /**< \brief (RTC_MODE1_PER) Counter Period */
#define RTC_MODE1_PER_PER_Msk       (0xFFFFu << RTC_MODE1_PER_PER_Pos)
#define RTC_MODE1_PER_PER(value)    ((RTC_MODE1_PER_PER_Msk & ((value) << RTC_MODE1_PER_PER_Pos)))
#define RTC_MODE1_PER_MASK          0xFFFFu      /**< \brief (RTC_MODE1_PER) MASK Register */

/* -------- RTC_MODE0_COMP : (RTC Offset: 0x18) (R/W 32) MODE0 MODE0 Compare Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t COMP:32;          /*!< bit:  0..31  Compare Value                      */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} RTC_MODE0_COMP_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define RTC_MODE0_COMP_OFFSET       0x18         /**< \brief (RTC_MODE0_COMP offset) MODE0 Compare Register */
#define RTC_MODE0_COMP_RESETVALUE   0x00000000   /**< \brief (RTC_MODE0_COMP reset_value) MODE0 Compare Register */

#define RTC_MODE0_COMP_COMP_Pos     0            /**< \brief (RTC_MODE0_COMP) Compare Value */
#define RTC_MODE0_COMP_COMP_Msk     (0xFFFFFFFFu << RTC_MODE0_COMP_COMP_Pos)
#define RTC_MODE0_COMP_COMP(value)  ((RTC_MODE0_COMP_COMP_Msk & ((value) << RTC_MODE0_COMP_COMP_Pos)))
#define RTC_MODE0_COMP_MASK         0xFFFFFFFFu  /**< \brief (RTC_MODE0_COMP) MASK Register */

/* -------- RTC_MODE1_COMP : (RTC Offset: 0x18) (R/W 16) MODE1 MODE1 Compare Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint16_t COMP:16;          /*!< bit:  0..15  Compare Value                      */
  } bit;                       /*!< Structure used for bit  access                  */
  uint16_t reg;                /*!< Type      used for register access              */
} RTC_MODE1_COMP_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define RTC_MODE1_COMP_OFFSET       0x18         /**< \brief (RTC_MODE1_COMP offset) MODE1 Compare Register */
#define RTC_MODE1_COMP_RESETVALUE   0x0000       /**< \brief (RTC_MODE1_COMP reset_value) MODE1 Compare Register */

#define RTC_MODE1_COMP_COMP_Pos     0            /**< \brief (RTC_MODE1_COMP) Compare Value */
#define RTC_MODE1_COMP_COMP_Msk     (0xFFFFu << RTC_MODE1_COMP_COMP_Pos)
#define RTC_MODE1_COMP_COMP(value)  ((RTC_MODE1_COMP_COMP_Msk & ((value) << RTC_MODE1_COMP_COMP_Pos)))
#define RTC_MODE1_COMP_MASK         0xFFFFu      /**< \brief (RTC_MODE1_COMP) MASK Register */

/* -------- RTC_MODE2_ALARM : (RTC Offset: 0x18) (R/W 32) MODE2 MODE2_ALARM Alarm Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t SECOND:6;         /*!< bit:  0.. 5  Alarm Second                       */
    uint32_t MINUTE:6;         /*!< bit:  6..11  Alarm Minute                       */
    uint32_t HOUR:5;           /*!< bit: 12..16  Alarm Hour                         */
    uint32_t DAY:5;            /*!< bit: 17..21  Alarm Day                          */
    uint32_t MONTH:4;          /*!< bit: 22..25  Alarm Month                        */
    uint32_t YEAR:6;           /*!< bit: 26..31  Alarm Year                         */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} RTC_MODE2_ALARM_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define RTC_MODE2_ALARM_OFFSET      0x18         /**< \brief (RTC_MODE2_ALARM offset) MODE2_ALARM Alarm Register */
#define RTC_MODE2_ALARM_RESETVALUE  0x00000000   /**< \brief (RTC_MODE2_ALARM reset_value) MODE2_ALARM Alarm Register */

#define RTC_MODE2_ALARM_SECOND_Pos  0            /**< \brief (RTC_MODE2_ALARM) Alarm Second */
#define RTC_MODE2_ALARM_SECOND_Msk  (0x3Fu << RTC_MODE2_ALARM_SECOND_Pos)
#define RTC_MODE2_ALARM_SECOND(value) ((RTC_MODE2_ALARM_SECOND_Msk & ((value) << RTC_MODE2_ALARM_SECOND_Pos)))
#define RTC_MODE2_ALARM_MINUTE_Pos  6            /**< \brief (RTC_MODE2_ALARM) Alarm Minute */
#define RTC_MODE2_ALARM_MINUTE_Msk  (0x3Fu << RTC_MODE2_ALARM_MINUTE_Pos)
#define RTC_MODE2_ALARM_MINUTE(value) ((RTC_MODE2_ALARM_MINUTE_Msk & ((value) << RTC_MODE2_ALARM_MINUTE_Pos)))
#define RTC_MODE2_ALARM_HOUR_Pos    12           /**< \brief (RTC_MODE2_ALARM) Alarm Hour */
#define RTC_MODE2_ALARM_HOUR_Msk    (0x1Fu << RTC_MODE2_ALARM_HOUR_Pos)
#define RTC_MODE2_ALARM_HOUR(value) ((RTC_MODE2_ALARM_HOUR_Msk & ((value) << RTC_MODE2_ALARM_HOUR_Pos)))
#define RTC_MODE2_ALARM_DAY_Pos     17           /**< \brief (RTC_MODE2_ALARM) Alarm Day */
#define RTC_MODE2_ALARM_DAY_Msk     (0x1Fu << RTC_MODE2_ALARM_DAY_Pos)
#define RTC_MODE2_ALARM_DAY(value)  ((RTC_MODE2_ALARM_DAY_Msk & ((value) << RTC_MODE2_ALARM_DAY_Pos)))
#define RTC_MODE2_ALARM_MONTH_Pos   22           /**< \brief (RTC_MODE2_ALARM) Alarm Month */
#define RTC_MODE2_ALARM_MONTH_Msk   (0xFu << RTC_MODE2_ALARM_MONTH_Pos)
#define RTC_MODE2_ALARM_MONTH(value) ((RTC_MODE2_ALARM_MONTH_Msk & ((value) << RTC_MODE2_ALARM_MONTH_Pos)))
#define RTC_MODE2_ALARM_YEAR_Pos    26           /**< \brief (RTC_MODE2_ALARM) Alarm Year */
#define RTC_MODE2_ALARM_YEAR_Msk    (0x3Fu << RTC_MODE2_ALARM_YEAR_Pos)
#define RTC_MODE2_ALARM_YEAR(value) ((RTC_MODE2_ALARM_YEAR_Msk & ((value) << RTC_MODE2_ALARM_YEAR_Pos)))
#define RTC_MODE2_ALARM_MASK        0xFFFFFFFFu  /**< \brief (RTC_MODE2_ALARM) MASK Register */

/* -------- RTC_MODE2_MASK : (RTC Offset: 0x1C) (R/W  8) MODE2 MODE2_ALARM Alarm Mask Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  SEL:3;            /*!< bit:  0.. 2  Alarm Mask Selection               */
    uint8_t  :5;               /*!< bit:  3.. 7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} RTC_MODE2_MASK_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define RTC_MODE2_MASK_OFFSET       0x1C         /**< \brief (RTC_MODE2_MASK offset) MODE2_ALARM Alarm Mask Register */
#define RTC_MODE2_MASK_RESETVALUE   0x00         /**< \brief (RTC_MODE2_MASK reset_value) MODE2_ALARM Alarm Mask Register */

#define RTC_MODE2_MASK_SEL_Pos      0            /**< \brief (RTC_MODE2_MASK) Alarm Mask Selection */
#define RTC_MODE2_MASK_SEL_Msk      (0x7u << RTC_MODE2_MASK_SEL_Pos)
#define RTC_MODE2_MASK_SEL(value)   ((RTC_MODE2_MASK_SEL_Msk & ((value) << RTC_MODE2_MASK_SEL_Pos)))
#define   RTC_MODE2_MASK_SEL_OFF    (0x0u <<  0) /**< \brief (RTC_MODE2_MASK)  */
#define   RTC_MODE2_MASK_SEL_SS     (0x1u <<  0) /**< \brief (RTC_MODE2_MASK)  */
#define   RTC_MODE2_MASK_SEL_MMSS   (0x2u <<  0) /**< \brief (RTC_MODE2_MASK)  */
#define   RTC_MODE2_MASK_SEL_HHMMSS (0x3u <<  0) /**< \brief (RTC_MODE2_MASK)  */
#define   RTC_MODE2_MASK_SEL_DDHHMMSS (0x4u <<  0) /**< \brief (RTC_MODE2_MASK)  */
#define   RTC_MODE2_MASK_SEL_MMDDHHMMSS (0x5u <<  0) /**< \brief (RTC_MODE2_MASK)  */
#define   RTC_MODE2_MASK_SEL_YYMMDDHHMMSS (0x6u <<  0) /**< \brief (RTC_MODE2_MASK)  */
#define RTC_MODE2_MASK_MASK         0x07u        /**< \brief (RTC_MODE2_MASK) MASK Register */

/** \brief RtcMode2Alarm hardware registers */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef struct {
  __IO RTC_MODE2_ALARM_Type      ALARM;       /**< \brief Offset: 0x00 (R/W 32) MODE2_ALARM Alarm Register */
  __IO RTC_MODE2_MASK_Type       MASK;        /**< \brief Offset: 0x04 (R/W  8) MODE2_ALARM Alarm Mask Register */
       RoReg8                    Reserved1[0x3];
} RtcMode2Alarm;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

/** \brief RTC_MODE0 hardware registers */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef struct { /* 32-bit Counter with Single 32-bit Compare */
  __IO RTC_MODE0_CTRL_Type       CTRL;        /**< \brief Offset: 0x00 (R/W 16) MODE0 Control Register */
  __IO RTC_READREQ_Type          READREQ;     /**< \brief Offset: 0x02 (R/W 16) Read Request Register */
  __IO RTC_MODE0_EVCTRL_Type     EVCTRL;      /**< \brief Offset: 0x04 (R/W 16) MODE0 Event Control Register */
  __IO RTC_MODE0_INTENCLR_Type   INTENCLR;    /**< \brief Offset: 0x06 (R/W  8) MODE0 Interrupt Enable Clear Register */
  __IO RTC_MODE0_INTENSET_Type   INTENSET;    /**< \brief Offset: 0x07 (R/W  8) MODE0 Interrupt Enable Set Register */
  __IO RTC_MODE0_INTFLAG_Type    INTFLAG;     /**< \brief Offset: 0x08 (R/W  8) MODE0 Interrupt Flag Status and Clear Register */
       RoReg8                    Reserved1[0x1];
  __IO RTC_STATUS_Type           STATUS;      /**< \brief Offset: 0x0A (R/W  8) Status Register */
  __IO RTC_DBGCTRL_Type          DBGCTRL;     /**< \brief Offset: 0x0B (R/W  8) Debug Register */
  __IO RTC_FREQCORR_Type         FREQCORR;    /**< \brief Offset: 0x0C (R/W  8) Frequency Correction Register */
       RoReg8                    Reserved2[0x3];
  __IO RTC_MODE0_COUNT_Type      COUNT;       /**< \brief Offset: 0x10 (R/W 32) MODE0 Count Register */
       RoReg8                    Reserved3[0x4];
  __IO RTC_MODE0_COMP_Type       COMP[1];     /**< \brief Offset: 0x18 (R/W 32) MODE0 Compare Register [NUM_OF_COMP32] */
} RtcMode0;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

/** \brief RTC_MODE1 hardware registers */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef struct { /* 16-bit Counter with Two 16-bit Compares */
  __IO RTC_MODE1_CTRL_Type       CTRL;        /**< \brief Offset: 0x00 (R/W 16) MODE1 Control Register */
  __IO RTC_READREQ_Type          READREQ;     /**< \brief Offset: 0x02 (R/W 16) Read Request Register */
  __IO RTC_MODE1_EVCTRL_Type     EVCTRL;      /**< \brief Offset: 0x04 (R/W 16) MODE1 Event Control Register */
  __IO RTC_MODE1_INTENCLR_Type   INTENCLR;    /**< \brief Offset: 0x06 (R/W  8) MODE1 Interrupt Enable Clear Register */
  __IO RTC_MODE1_INTENSET_Type   INTENSET;    /**< \brief Offset: 0x07 (R/W  8) MODE1 Interrupt Enable Set Register */
  __IO RTC_MODE1_INTFLAG_Type    INTFLAG;     /**< \brief Offset: 0x08 (R/W  8) MODE1 Interrupt Flag Status and Clear Register */
       RoReg8                    Reserved1[0x1];
  __IO RTC_STATUS_Type           STATUS;      /**< \brief Offset: 0x0A (R/W  8) Status Register */
  __IO RTC_DBGCTRL_Type          DBGCTRL;     /**< \brief Offset: 0x0B (R/W  8) Debug Register */
  __IO RTC_FREQCORR_Type         FREQCORR;    /**< \brief Offset: 0x0C (R/W  8) Frequency Correction Register */
       RoReg8                    Reserved2[0x3];
  __IO RTC_MODE1_COUNT_Type      COUNT;       /**< \brief Offset: 0x10 (R/W 16) MODE1 Count Register */
       RoReg8                    Reserved3[0x2];
  __IO RTC_MODE1_PER_Type        PER;         /**< \brief Offset: 0x14 (R/W 16) MODE1 Period Register */
       RoReg8                    Reserved4[0x2];
  __IO RTC_MODE1_COMP_Type       COMP[2];     /**< \brief Offset: 0x18 (R/W 16) MODE1 Compare Register [NUM_OF_COMP16] */
} RtcMode1;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

/** \brief RTC_MODE2 hardware registers */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef struct { /* Clock/Calendar with Alarm */
  __IO RTC_MODE2_CTRL_Type       CTRL;        /**< \brief Offset: 0x00 (R/W 16) MODE2 Control Register */
  __IO RTC_READREQ_Type          READREQ;     /**< \brief Offset: 0x02 (R/W 16) Read Request Register */
  __IO RTC_MODE2_EVCTRL_Type     EVCTRL;      /**< \brief Offset: 0x04 (R/W 16) MODE2 Event Control Register */
  __IO RTC_MODE2_INTENCLR_Type   INTENCLR;    /**< \brief Offset: 0x06 (R/W  8) MODE2 Interrupt Enable Clear Register */
  __IO RTC_MODE2_INTENSET_Type   INTENSET;    /**< \brief Offset: 0x07 (R/W  8) MODE2 Interrupt Enable Set Register */
  __IO RTC_MODE2_INTFLAG_Type    INTFLAG;     /**< \brief Offset: 0x08 (R/W  8) MODE2 Interrupt Flag Status and Clear Register */
       RoReg8                    Reserved1[0x1];
  __IO RTC_STATUS_Type           STATUS;      /**< \brief Offset: 0x0A (R/W  8) Status Register */
  __IO RTC_DBGCTRL_Type          DBGCTRL;     /**< \brief Offset: 0x0B (R/W  8) Debug Register */
  __IO RTC_FREQCORR_Type         FREQCORR;    /**< \brief Offset: 0x0C (R/W  8) Frequency Correction Register */
       RoReg8                    Reserved2[0x3];
  __IO RTC_MODE2_CLOCK_Type      CLOCK;       /**< \brief Offset: 0x10 (R/W 32) MODE2 Clock Register */
       RoReg8                    Reserved3[0x4];
       RtcMode2Alarm             Mode2Alarm[1]; /**< \brief Offset: 0x18 RtcMode2Alarm groups [NUM_OF_ALARMS] */
} RtcMode2;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
       RtcMode0                  MODE0;       /**< \brief Offset: 0x00 32-bit Counter with Single 32-bit Compare */
       RtcMode1                  MODE1;       /**< \brief Offset: 0x00 16-bit Counter with Two 16-bit Compares */
       RtcMode2                  MODE2;       /**< \brief Offset: 0x00 Clock/Calendar with Alarm */
} Rtc;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

/*@}*/

#endif /* _SAMD20_RTC_COMPONENT_ */
