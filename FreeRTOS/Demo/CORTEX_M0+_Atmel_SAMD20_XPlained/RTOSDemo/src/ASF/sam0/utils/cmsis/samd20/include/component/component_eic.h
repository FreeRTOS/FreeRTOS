/**
 * \file
 *
 * \brief Component description for EIC
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

#ifndef _SAMD20_EIC_COMPONENT_
#define _SAMD20_EIC_COMPONENT_

/* ========================================================================== */
/**  SOFTWARE API DEFINITION FOR EIC */
/* ========================================================================== */
/** \addtogroup SAMD20_EIC External Interrupt Controller */
/*@{*/

#define REV_EIC                     0x101

/* -------- EIC_CTRL : (EIC Offset: 0x00) (R/W  8) Control Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  SWRST:1;          /*!< bit:      0  Software Reset                     */
    uint8_t  ENABLE:1;         /*!< bit:      1  Enable                             */
    uint8_t  :6;               /*!< bit:  2.. 7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} EIC_CTRL_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define EIC_CTRL_OFFSET             0x00         /**< \brief (EIC_CTRL offset) Control Register */
#define EIC_CTRL_RESETVALUE         0x00         /**< \brief (EIC_CTRL reset_value) Control Register */

#define EIC_CTRL_SWRST_Pos          0            /**< \brief (EIC_CTRL) Software Reset */
#define EIC_CTRL_SWRST              (0x1u << EIC_CTRL_SWRST_Pos)
#define EIC_CTRL_ENABLE_Pos         1            /**< \brief (EIC_CTRL) Enable */
#define EIC_CTRL_ENABLE             (0x1u << EIC_CTRL_ENABLE_Pos)
#define EIC_CTRL_MASK               0x03u        /**< \brief (EIC_CTRL) MASK Register */

/* -------- EIC_STATUS : (EIC Offset: 0x01) (R/   8) Status Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  :7;               /*!< bit:  0.. 6  Reserved                           */
    uint8_t  SYNCBUSY:1;       /*!< bit:      7  Sync Busy                          */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} EIC_STATUS_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define EIC_STATUS_OFFSET           0x01         /**< \brief (EIC_STATUS offset) Status Register */
#define EIC_STATUS_RESETVALUE       0x00         /**< \brief (EIC_STATUS reset_value) Status Register */

#define EIC_STATUS_SYNCBUSY_Pos     7            /**< \brief (EIC_STATUS) Sync Busy */
#define EIC_STATUS_SYNCBUSY         (0x1u << EIC_STATUS_SYNCBUSY_Pos)
#define EIC_STATUS_MASK             0x80u        /**< \brief (EIC_STATUS) MASK Register */

/* -------- EIC_NMICTRL : (EIC Offset: 0x02) (R/W  8) NMI Control Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  NMISENSE:3;       /*!< bit:  0.. 2  NMI Input Sense Configuration      */
    uint8_t  NMIFILTEN:1;      /*!< bit:      3  NMI Filter Enable                  */
    uint8_t  :4;               /*!< bit:  4.. 7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} EIC_NMICTRL_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define EIC_NMICTRL_OFFSET          0x02         /**< \brief (EIC_NMICTRL offset) NMI Control Register */
#define EIC_NMICTRL_RESETVALUE      0x00         /**< \brief (EIC_NMICTRL reset_value) NMI Control Register */

#define EIC_NMICTRL_NMISENSE_Pos    0            /**< \brief (EIC_NMICTRL) NMI Input Sense Configuration */
#define EIC_NMICTRL_NMISENSE_Msk    (0x7u << EIC_NMICTRL_NMISENSE_Pos)
#define EIC_NMICTRL_NMISENSE(value) ((EIC_NMICTRL_NMISENSE_Msk & ((value) << EIC_NMICTRL_NMISENSE_Pos)))
#define   EIC_NMICTRL_NMISENSE_NONE (0x0u <<  0) /**< \brief (EIC_NMICTRL) No detection */
#define   EIC_NMICTRL_NMISENSE_RISE (0x1u <<  0) /**< \brief (EIC_NMICTRL) Rising edge detection */
#define   EIC_NMICTRL_NMISENSE_FALL (0x2u <<  0) /**< \brief (EIC_NMICTRL) Falling edge detection */
#define   EIC_NMICTRL_NMISENSE_BOTH (0x3u <<  0) /**< \brief (EIC_NMICTRL) Both edges detection */
#define   EIC_NMICTRL_NMISENSE_HIGH (0x4u <<  0) /**< \brief (EIC_NMICTRL) High level detection */
#define   EIC_NMICTRL_NMISENSE_LOW  (0x5u <<  0) /**< \brief (EIC_NMICTRL) Low level detection */
#define EIC_NMICTRL_NMIFILTEN_Pos   3            /**< \brief (EIC_NMICTRL) NMI Filter Enable */
#define EIC_NMICTRL_NMIFILTEN       (0x1u << EIC_NMICTRL_NMIFILTEN_Pos)
#define EIC_NMICTRL_MASK            0x0Fu        /**< \brief (EIC_NMICTRL) MASK Register */

/* -------- EIC_NMIFLAG : (EIC Offset: 0x03) (R/W  8) NMI Interrupt Flag Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  NMI:1;            /*!< bit:      0  NMI Interrupt Flag                 */
    uint8_t  :7;               /*!< bit:  1.. 7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} EIC_NMIFLAG_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define EIC_NMIFLAG_OFFSET          0x03         /**< \brief (EIC_NMIFLAG offset) NMI Interrupt Flag Register */
#define EIC_NMIFLAG_RESETVALUE      0x00         /**< \brief (EIC_NMIFLAG reset_value) NMI Interrupt Flag Register */

#define EIC_NMIFLAG_NMI_Pos         0            /**< \brief (EIC_NMIFLAG) NMI Interrupt Flag */
#define EIC_NMIFLAG_NMI             (0x1u << EIC_NMIFLAG_NMI_Pos)
#define EIC_NMIFLAG_MASK            0x01u        /**< \brief (EIC_NMIFLAG) MASK Register */

/* -------- EIC_EVCTRL : (EIC Offset: 0x04) (R/W 32) Event Control Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t EXTINTEO:32;      /*!< bit:  0..31  External Interrupt Event Output Enable */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} EIC_EVCTRL_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define EIC_EVCTRL_OFFSET           0x04         /**< \brief (EIC_EVCTRL offset) Event Control Register */
#define EIC_EVCTRL_RESETVALUE       0x00000000   /**< \brief (EIC_EVCTRL reset_value) Event Control Register */

#define EIC_EVCTRL_EXTINTEO_Pos     0            /**< \brief (EIC_EVCTRL) External Interrupt Event Output Enable */
#define EIC_EVCTRL_EXTINTEO_Msk     (0xFFFFFFFFu << EIC_EVCTRL_EXTINTEO_Pos)
#define EIC_EVCTRL_EXTINTEO(value)  ((EIC_EVCTRL_EXTINTEO_Msk & ((value) << EIC_EVCTRL_EXTINTEO_Pos)))
#define EIC_EVCTRL_MASK             0xFFFFFFFFu  /**< \brief (EIC_EVCTRL) MASK Register */

/* -------- EIC_INTENCLR : (EIC Offset: 0x08) (R/W 32) Interrupt Enable Clear Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t EXTINT:16;        /*!< bit:  0..15  External Interrupt Disable         */
    uint32_t :16;              /*!< bit: 16..31  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} EIC_INTENCLR_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define EIC_INTENCLR_OFFSET         0x08         /**< \brief (EIC_INTENCLR offset) Interrupt Enable Clear Register */
#define EIC_INTENCLR_RESETVALUE     0x00000000   /**< \brief (EIC_INTENCLR reset_value) Interrupt Enable Clear Register */

#define EIC_INTENCLR_EXTINT_Pos     0            /**< \brief (EIC_INTENCLR) External Interrupt Disable */
#define EIC_INTENCLR_EXTINT_Msk     (0xFFFFu << EIC_INTENCLR_EXTINT_Pos)
#define EIC_INTENCLR_EXTINT(value)  ((EIC_INTENCLR_EXTINT_Msk & ((value) << EIC_INTENCLR_EXTINT_Pos)))
#define EIC_INTENCLR_MASK           0x0000FFFFu  /**< \brief (EIC_INTENCLR) MASK Register */

/* -------- EIC_INTENSET : (EIC Offset: 0x0C) (R/W 32) Interrupt Enable Set Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t EXTINT:16;        /*!< bit:  0..15  External Interrupt Disable         */
    uint32_t :16;              /*!< bit: 16..31  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} EIC_INTENSET_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define EIC_INTENSET_OFFSET         0x0C         /**< \brief (EIC_INTENSET offset) Interrupt Enable Set Register */
#define EIC_INTENSET_RESETVALUE     0x00000000   /**< \brief (EIC_INTENSET reset_value) Interrupt Enable Set Register */

#define EIC_INTENSET_EXTINT_Pos     0            /**< \brief (EIC_INTENSET) External Interrupt Disable */
#define EIC_INTENSET_EXTINT_Msk     (0xFFFFu << EIC_INTENSET_EXTINT_Pos)
#define EIC_INTENSET_EXTINT(value)  ((EIC_INTENSET_EXTINT_Msk & ((value) << EIC_INTENSET_EXTINT_Pos)))
#define EIC_INTENSET_MASK           0x0000FFFFu  /**< \brief (EIC_INTENSET) MASK Register */

/* -------- EIC_INTFLAG : (EIC Offset: 0x10) (R/W 32) Interrupt Flag Status and Clear Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t EXTINT:16;        /*!< bit:  0..15  External Interrupt Flag            */
    uint32_t :16;              /*!< bit: 16..31  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} EIC_INTFLAG_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define EIC_INTFLAG_OFFSET          0x10         /**< \brief (EIC_INTFLAG offset) Interrupt Flag Status and Clear Register */
#define EIC_INTFLAG_RESETVALUE      0x00000000   /**< \brief (EIC_INTFLAG reset_value) Interrupt Flag Status and Clear Register */

#define EIC_INTFLAG_EXTINT_Pos      0            /**< \brief (EIC_INTFLAG) External Interrupt Flag */
#define EIC_INTFLAG_EXTINT_Msk      (0xFFFFu << EIC_INTFLAG_EXTINT_Pos)
#define EIC_INTFLAG_EXTINT(value)   ((EIC_INTFLAG_EXTINT_Msk & ((value) << EIC_INTFLAG_EXTINT_Pos)))
#define EIC_INTFLAG_MASK            0x0000FFFFu  /**< \brief (EIC_INTFLAG) MASK Register */

/* -------- EIC_WAKEUP : (EIC Offset: 0x14) (R/W 32) Wake-up Enable Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t WAKEUPEN:16;      /*!< bit:  0..15  External Interrupt Wake-Up Enable  */
    uint32_t :16;              /*!< bit: 16..31  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} EIC_WAKEUP_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define EIC_WAKEUP_OFFSET           0x14         /**< \brief (EIC_WAKEUP offset) Wake-up Enable Register */
#define EIC_WAKEUP_RESETVALUE       0x00000000   /**< \brief (EIC_WAKEUP reset_value) Wake-up Enable Register */

#define EIC_WAKEUP_WAKEUPEN_Pos     0            /**< \brief (EIC_WAKEUP) External Interrupt Wake-Up Enable */
#define EIC_WAKEUP_WAKEUPEN_Msk     (0xFFFFu << EIC_WAKEUP_WAKEUPEN_Pos)
#define EIC_WAKEUP_WAKEUPEN(value)  ((EIC_WAKEUP_WAKEUPEN_Msk & ((value) << EIC_WAKEUP_WAKEUPEN_Pos)))
#define EIC_WAKEUP_MASK             0x0000FFFFu  /**< \brief (EIC_WAKEUP) MASK Register */

/* -------- EIC_CONFIG : (EIC Offset: 0x18) (R/W 32) Config Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t SENSE0:3;         /*!< bit:  0.. 2  Input Sense Configuration 0        */
    uint32_t FILTEN0:1;        /*!< bit:      3  Filter Enable 0                    */
    uint32_t SENSE1:3;         /*!< bit:  4.. 6  Input Sense Configuration 1        */
    uint32_t FILTEN1:1;        /*!< bit:      7  Filter Enable 1                    */
    uint32_t SENSE2:3;         /*!< bit:  8..10  Input Sense Configuration 2        */
    uint32_t FILTEN2:1;        /*!< bit:     11  Filter Enable 2                    */
    uint32_t SENSE3:3;         /*!< bit: 12..14  Input Sense Configuration 3        */
    uint32_t FILTEN3:1;        /*!< bit:     15  Filter Enable 3                    */
    uint32_t SENSE4:3;         /*!< bit: 16..18  Input Sense Configuration 4        */
    uint32_t FILTEN4:1;        /*!< bit:     19  Filter Enable 4                    */
    uint32_t SENSE5:3;         /*!< bit: 20..22  Input Sense Configuration 5        */
    uint32_t FILTEN5:1;        /*!< bit:     23  Filter Enable 5                    */
    uint32_t SENSE6:3;         /*!< bit: 24..26  Input Sense Configuration 6        */
    uint32_t FILTEN6:1;        /*!< bit:     27  Filter Enable 6                    */
    uint32_t SENSE7:3;         /*!< bit: 28..30  Input Sense Configuration 7        */
    uint32_t FILTEN7:1;        /*!< bit:     31  Filter Enable 7                    */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} EIC_CONFIG_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define EIC_CONFIG_OFFSET           0x18         /**< \brief (EIC_CONFIG offset) Config Register */
#define EIC_CONFIG_RESETVALUE       0x00000000   /**< \brief (EIC_CONFIG reset_value) Config Register */

#define EIC_CONFIG_SENSE0_Pos       0            /**< \brief (EIC_CONFIG) Input Sense Configuration 0 */
#define EIC_CONFIG_SENSE0_Msk       (0x7u << EIC_CONFIG_SENSE0_Pos)
#define EIC_CONFIG_SENSE0(value)    ((EIC_CONFIG_SENSE0_Msk & ((value) << EIC_CONFIG_SENSE0_Pos)))
#define   EIC_CONFIG_SENSE0_NONE    (0x0u <<  0) /**< \brief (EIC_CONFIG) No detection */
#define   EIC_CONFIG_SENSE0_RISE    (0x1u <<  0) /**< \brief (EIC_CONFIG) Rising edge detection */
#define   EIC_CONFIG_SENSE0_FALL    (0x2u <<  0) /**< \brief (EIC_CONFIG) Falling edge detection */
#define   EIC_CONFIG_SENSE0_BOTH    (0x3u <<  0) /**< \brief (EIC_CONFIG) Both edges detection */
#define   EIC_CONFIG_SENSE0_HIGH    (0x4u <<  0) /**< \brief (EIC_CONFIG) High level detection */
#define   EIC_CONFIG_SENSE0_LOW     (0x5u <<  0) /**< \brief (EIC_CONFIG) Low level detection */
#define EIC_CONFIG_FILTEN0_Pos      3            /**< \brief (EIC_CONFIG) Filter Enable 0 */
#define EIC_CONFIG_FILTEN0          (0x1u << EIC_CONFIG_FILTEN0_Pos)
#define EIC_CONFIG_SENSE1_Pos       4            /**< \brief (EIC_CONFIG) Input Sense Configuration 1 */
#define EIC_CONFIG_SENSE1_Msk       (0x7u << EIC_CONFIG_SENSE1_Pos)
#define EIC_CONFIG_SENSE1(value)    ((EIC_CONFIG_SENSE1_Msk & ((value) << EIC_CONFIG_SENSE1_Pos)))
#define   EIC_CONFIG_SENSE1_NONE    (0x0u <<  4) /**< \brief (EIC_CONFIG) No detection */
#define   EIC_CONFIG_SENSE1_RISE    (0x1u <<  4) /**< \brief (EIC_CONFIG) Rising edge detection */
#define   EIC_CONFIG_SENSE1_FALL    (0x2u <<  4) /**< \brief (EIC_CONFIG) Falling edge detection */
#define   EIC_CONFIG_SENSE1_BOTH    (0x3u <<  4) /**< \brief (EIC_CONFIG) Both edges detection */
#define   EIC_CONFIG_SENSE1_HIGH    (0x4u <<  4) /**< \brief (EIC_CONFIG) High level detection */
#define   EIC_CONFIG_SENSE1_LOW     (0x5u <<  4) /**< \brief (EIC_CONFIG) Low level detection */
#define EIC_CONFIG_FILTEN1_Pos      7            /**< \brief (EIC_CONFIG) Filter Enable 1 */
#define EIC_CONFIG_FILTEN1          (0x1u << EIC_CONFIG_FILTEN1_Pos)
#define EIC_CONFIG_SENSE2_Pos       8            /**< \brief (EIC_CONFIG) Input Sense Configuration 2 */
#define EIC_CONFIG_SENSE2_Msk       (0x7u << EIC_CONFIG_SENSE2_Pos)
#define EIC_CONFIG_SENSE2(value)    ((EIC_CONFIG_SENSE2_Msk & ((value) << EIC_CONFIG_SENSE2_Pos)))
#define   EIC_CONFIG_SENSE2_NONE    (0x0u <<  8) /**< \brief (EIC_CONFIG) No detection */
#define   EIC_CONFIG_SENSE2_RISE    (0x1u <<  8) /**< \brief (EIC_CONFIG) Rising edge detection */
#define   EIC_CONFIG_SENSE2_FALL    (0x2u <<  8) /**< \brief (EIC_CONFIG) Falling edge detection */
#define   EIC_CONFIG_SENSE2_BOTH    (0x3u <<  8) /**< \brief (EIC_CONFIG) Both edges detection */
#define   EIC_CONFIG_SENSE2_HIGH    (0x4u <<  8) /**< \brief (EIC_CONFIG) High level detection */
#define   EIC_CONFIG_SENSE2_LOW     (0x5u <<  8) /**< \brief (EIC_CONFIG) Low level detection */
#define EIC_CONFIG_FILTEN2_Pos      11           /**< \brief (EIC_CONFIG) Filter Enable 2 */
#define EIC_CONFIG_FILTEN2          (0x1u << EIC_CONFIG_FILTEN2_Pos)
#define EIC_CONFIG_SENSE3_Pos       12           /**< \brief (EIC_CONFIG) Input Sense Configuration 3 */
#define EIC_CONFIG_SENSE3_Msk       (0x7u << EIC_CONFIG_SENSE3_Pos)
#define EIC_CONFIG_SENSE3(value)    ((EIC_CONFIG_SENSE3_Msk & ((value) << EIC_CONFIG_SENSE3_Pos)))
#define   EIC_CONFIG_SENSE3_NONE    (0x0u << 12) /**< \brief (EIC_CONFIG) No detection */
#define   EIC_CONFIG_SENSE3_RISE    (0x1u << 12) /**< \brief (EIC_CONFIG) Rising edge detection */
#define   EIC_CONFIG_SENSE3_FALL    (0x2u << 12) /**< \brief (EIC_CONFIG) Falling edge detection */
#define   EIC_CONFIG_SENSE3_BOTH    (0x3u << 12) /**< \brief (EIC_CONFIG) Both edges detection */
#define   EIC_CONFIG_SENSE3_HIGH    (0x4u << 12) /**< \brief (EIC_CONFIG) High level detection */
#define   EIC_CONFIG_SENSE3_LOW     (0x5u << 12) /**< \brief (EIC_CONFIG) Low level detection */
#define EIC_CONFIG_FILTEN3_Pos      15           /**< \brief (EIC_CONFIG) Filter Enable 3 */
#define EIC_CONFIG_FILTEN3          (0x1u << EIC_CONFIG_FILTEN3_Pos)
#define EIC_CONFIG_SENSE4_Pos       16           /**< \brief (EIC_CONFIG) Input Sense Configuration 4 */
#define EIC_CONFIG_SENSE4_Msk       (0x7u << EIC_CONFIG_SENSE4_Pos)
#define EIC_CONFIG_SENSE4(value)    ((EIC_CONFIG_SENSE4_Msk & ((value) << EIC_CONFIG_SENSE4_Pos)))
#define   EIC_CONFIG_SENSE4_NONE    (0x0u << 16) /**< \brief (EIC_CONFIG) No detection */
#define   EIC_CONFIG_SENSE4_RISE    (0x1u << 16) /**< \brief (EIC_CONFIG) Rising edge detection */
#define   EIC_CONFIG_SENSE4_FALL    (0x2u << 16) /**< \brief (EIC_CONFIG) Falling edge detection */
#define   EIC_CONFIG_SENSE4_BOTH    (0x3u << 16) /**< \brief (EIC_CONFIG) Both edges detection */
#define   EIC_CONFIG_SENSE4_HIGH    (0x4u << 16) /**< \brief (EIC_CONFIG) High level detection */
#define   EIC_CONFIG_SENSE4_LOW     (0x5u << 16) /**< \brief (EIC_CONFIG) Low level detection */
#define EIC_CONFIG_FILTEN4_Pos      19           /**< \brief (EIC_CONFIG) Filter Enable 4 */
#define EIC_CONFIG_FILTEN4          (0x1u << EIC_CONFIG_FILTEN4_Pos)
#define EIC_CONFIG_SENSE5_Pos       20           /**< \brief (EIC_CONFIG) Input Sense Configuration 5 */
#define EIC_CONFIG_SENSE5_Msk       (0x7u << EIC_CONFIG_SENSE5_Pos)
#define EIC_CONFIG_SENSE5(value)    ((EIC_CONFIG_SENSE5_Msk & ((value) << EIC_CONFIG_SENSE5_Pos)))
#define   EIC_CONFIG_SENSE5_NONE    (0x0u << 20) /**< \brief (EIC_CONFIG) No detection */
#define   EIC_CONFIG_SENSE5_RISE    (0x1u << 20) /**< \brief (EIC_CONFIG) Rising edge detection */
#define   EIC_CONFIG_SENSE5_FALL    (0x2u << 20) /**< \brief (EIC_CONFIG) Falling edge detection */
#define   EIC_CONFIG_SENSE5_BOTH    (0x3u << 20) /**< \brief (EIC_CONFIG) Both edges detection */
#define   EIC_CONFIG_SENSE5_HIGH    (0x4u << 20) /**< \brief (EIC_CONFIG) High level detection */
#define   EIC_CONFIG_SENSE5_LOW     (0x5u << 20) /**< \brief (EIC_CONFIG) Low level detection */
#define EIC_CONFIG_FILTEN5_Pos      23           /**< \brief (EIC_CONFIG) Filter Enable 5 */
#define EIC_CONFIG_FILTEN5          (0x1u << EIC_CONFIG_FILTEN5_Pos)
#define EIC_CONFIG_SENSE6_Pos       24           /**< \brief (EIC_CONFIG) Input Sense Configuration 6 */
#define EIC_CONFIG_SENSE6_Msk       (0x7u << EIC_CONFIG_SENSE6_Pos)
#define EIC_CONFIG_SENSE6(value)    ((EIC_CONFIG_SENSE6_Msk & ((value) << EIC_CONFIG_SENSE6_Pos)))
#define   EIC_CONFIG_SENSE6_NONE    (0x0u << 24) /**< \brief (EIC_CONFIG) No detection */
#define   EIC_CONFIG_SENSE6_RISE    (0x1u << 24) /**< \brief (EIC_CONFIG) Rising edge detection */
#define   EIC_CONFIG_SENSE6_FALL    (0x2u << 24) /**< \brief (EIC_CONFIG) Falling edge detection */
#define   EIC_CONFIG_SENSE6_BOTH    (0x3u << 24) /**< \brief (EIC_CONFIG) Both edges detection */
#define   EIC_CONFIG_SENSE6_HIGH    (0x4u << 24) /**< \brief (EIC_CONFIG) High level detection */
#define   EIC_CONFIG_SENSE6_LOW     (0x5u << 24) /**< \brief (EIC_CONFIG) Low level detection */
#define EIC_CONFIG_FILTEN6_Pos      27           /**< \brief (EIC_CONFIG) Filter Enable 6 */
#define EIC_CONFIG_FILTEN6          (0x1u << EIC_CONFIG_FILTEN6_Pos)
#define EIC_CONFIG_SENSE7_Pos       28           /**< \brief (EIC_CONFIG) Input Sense Configuration 7 */
#define EIC_CONFIG_SENSE7_Msk       (0x7u << EIC_CONFIG_SENSE7_Pos)
#define EIC_CONFIG_SENSE7(value)    ((EIC_CONFIG_SENSE7_Msk & ((value) << EIC_CONFIG_SENSE7_Pos)))
#define   EIC_CONFIG_SENSE7_NONE    (0x0u << 28) /**< \brief (EIC_CONFIG) No detection */
#define   EIC_CONFIG_SENSE7_RISE    (0x1u << 28) /**< \brief (EIC_CONFIG) Rising edge detection */
#define   EIC_CONFIG_SENSE7_FALL    (0x2u << 28) /**< \brief (EIC_CONFIG) Falling edge detection */
#define   EIC_CONFIG_SENSE7_BOTH    (0x3u << 28) /**< \brief (EIC_CONFIG) Both edges detection */
#define   EIC_CONFIG_SENSE7_HIGH    (0x4u << 28) /**< \brief (EIC_CONFIG) High level detection */
#define   EIC_CONFIG_SENSE7_LOW     (0x5u << 28) /**< \brief (EIC_CONFIG) Low level detection */
#define EIC_CONFIG_FILTEN7_Pos      31           /**< \brief (EIC_CONFIG) Filter Enable 7 */
#define EIC_CONFIG_FILTEN7          (0x1u << EIC_CONFIG_FILTEN7_Pos)
#define EIC_CONFIG_MASK             0xFFFFFFFFu  /**< \brief (EIC_CONFIG) MASK Register */

/** \brief EIC hardware registers */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef struct {
  __IO EIC_CTRL_Type             CTRL;        /**< \brief Offset: 0x00 (R/W  8) Control Register */
  __I  EIC_STATUS_Type           STATUS;      /**< \brief Offset: 0x01 (R/   8) Status Register */
  __IO EIC_NMICTRL_Type          NMICTRL;     /**< \brief Offset: 0x02 (R/W  8) NMI Control Register */
  __IO EIC_NMIFLAG_Type          NMIFLAG;     /**< \brief Offset: 0x03 (R/W  8) NMI Interrupt Flag Register */
  __IO EIC_EVCTRL_Type           EVCTRL;      /**< \brief Offset: 0x04 (R/W 32) Event Control Register */
  __IO EIC_INTENCLR_Type         INTENCLR;    /**< \brief Offset: 0x08 (R/W 32) Interrupt Enable Clear Register */
  __IO EIC_INTENSET_Type         INTENSET;    /**< \brief Offset: 0x0C (R/W 32) Interrupt Enable Set Register */
  __IO EIC_INTFLAG_Type          INTFLAG;     /**< \brief Offset: 0x10 (R/W 32) Interrupt Flag Status and Clear Register */
  __IO EIC_WAKEUP_Type           WAKEUP;      /**< \brief Offset: 0x14 (R/W 32) Wake-up Enable Register */
  __IO EIC_CONFIG_Type           CONFIG[2];   /**< \brief Offset: 0x18 (R/W 32) Config Register [NUMBER_OF_CONFIG_REGS] */
} Eic;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

/*@}*/

#endif /* _SAMD20_EIC_COMPONENT_ */
