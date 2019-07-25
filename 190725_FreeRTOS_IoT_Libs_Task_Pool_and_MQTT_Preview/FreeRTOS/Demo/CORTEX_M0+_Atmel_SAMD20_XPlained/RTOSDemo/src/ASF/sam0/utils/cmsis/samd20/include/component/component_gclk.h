/**
 * \file
 *
 * \brief Component description for GCLK
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

#ifndef _SAMD20_GCLK_COMPONENT_
#define _SAMD20_GCLK_COMPONENT_

/* ========================================================================== */
/**  SOFTWARE API DEFINITION FOR GCLK */
/* ========================================================================== */
/** \addtogroup SAMD20_GCLK Generic Clock Generator */
/*@{*/

#define REV_GCLK                    0x200

/* -------- GCLK_CTRL : (GCLK Offset: 0x0) (R/W  8) Control Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  SWRST:1;          /*!< bit:      0  Software Reset                     */
    uint8_t  :7;               /*!< bit:  1.. 7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} GCLK_CTRL_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define GCLK_CTRL_OFFSET            0x0          /**< \brief (GCLK_CTRL offset) Control Register */
#define GCLK_CTRL_RESETVALUE        0x00         /**< \brief (GCLK_CTRL reset_value) Control Register */

#define GCLK_CTRL_SWRST_Pos         0            /**< \brief (GCLK_CTRL) Software Reset */
#define GCLK_CTRL_SWRST             (0x1u << GCLK_CTRL_SWRST_Pos)
#define GCLK_CTRL_MASK              0x01u        /**< \brief (GCLK_CTRL) MASK Register */

/* -------- GCLK_STATUS : (GCLK Offset: 0x1) (R/   8) Status Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  :7;               /*!< bit:  0.. 6  Reserved                           */
    uint8_t  SYNCBUSY:1;       /*!< bit:      7  Synchronization Busy               */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} GCLK_STATUS_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define GCLK_STATUS_OFFSET          0x1          /**< \brief (GCLK_STATUS offset) Status Register */
#define GCLK_STATUS_RESETVALUE      0x00         /**< \brief (GCLK_STATUS reset_value) Status Register */

#define GCLK_STATUS_SYNCBUSY_Pos    7            /**< \brief (GCLK_STATUS) Synchronization Busy */
#define GCLK_STATUS_SYNCBUSY        (0x1u << GCLK_STATUS_SYNCBUSY_Pos)
#define GCLK_STATUS_MASK            0x80u        /**< \brief (GCLK_STATUS) MASK Register */

/* -------- GCLK_CLKCTRL : (GCLK Offset: 0x2) (R/W 16) Generic Clock Control Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint16_t ID:6;             /*!< bit:  0.. 5  Generic Clock Selection            */
    uint16_t :2;               /*!< bit:  6.. 7  Reserved                           */
    uint16_t GEN:4;            /*!< bit:  8..11  Generic Clock Generator Select     */
    uint16_t :2;               /*!< bit: 12..13  Reserved                           */
    uint16_t CLKEN:1;          /*!< bit:     14  Clock Enable                       */
    uint16_t WRTLOCK:1;        /*!< bit:     15  Write Lock                         */
  } bit;                       /*!< Structure used for bit  access                  */
  uint16_t reg;                /*!< Type      used for register access              */
} GCLK_CLKCTRL_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define GCLK_CLKCTRL_OFFSET         0x2          /**< \brief (GCLK_CLKCTRL offset) Generic Clock Control Register */
#define GCLK_CLKCTRL_RESETVALUE     0x0000       /**< \brief (GCLK_CLKCTRL reset_value) Generic Clock Control Register */

#define GCLK_CLKCTRL_ID_Pos         0            /**< \brief (GCLK_CLKCTRL) Generic Clock Selection */
#define GCLK_CLKCTRL_ID_Msk         (0x3Fu << GCLK_CLKCTRL_ID_Pos)
#define GCLK_CLKCTRL_ID(value)      ((GCLK_CLKCTRL_ID_Msk & ((value) << GCLK_CLKCTRL_ID_Pos)))
#define GCLK_CLKCTRL_GEN_Pos        8            /**< \brief (GCLK_CLKCTRL) Generic Clock Generator Select */
#define GCLK_CLKCTRL_GEN_Msk        (0xFu << GCLK_CLKCTRL_GEN_Pos)
#define GCLK_CLKCTRL_GEN(value)     ((GCLK_CLKCTRL_GEN_Msk & ((value) << GCLK_CLKCTRL_GEN_Pos)))
#define GCLK_CLKCTRL_CLKEN_Pos      14           /**< \brief (GCLK_CLKCTRL) Clock Enable */
#define GCLK_CLKCTRL_CLKEN          (0x1u << GCLK_CLKCTRL_CLKEN_Pos)
#define GCLK_CLKCTRL_WRTLOCK_Pos    15           /**< \brief (GCLK_CLKCTRL) Write Lock */
#define GCLK_CLKCTRL_WRTLOCK        (0x1u << GCLK_CLKCTRL_WRTLOCK_Pos)
#define GCLK_CLKCTRL_MASK           0xCF3Fu      /**< \brief (GCLK_CLKCTRL) MASK Register */

/* -------- GCLK_GENCTRL : (GCLK Offset: 0x4) (R/W 32) Generic Clock Generator Control Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t ID:4;             /*!< bit:  0.. 3  Generic Clock Generator Selection  */
    uint32_t :4;               /*!< bit:  4.. 7  Reserved                           */
    uint32_t SRC:5;            /*!< bit:  8..12  Clock Source Select                */
    uint32_t :3;               /*!< bit: 13..15  Reserved                           */
    uint32_t GENEN:1;          /*!< bit:     16  Generic Clock Generator Enable     */
    uint32_t IDC:1;            /*!< bit:     17  Improve Duty Cycle                 */
    uint32_t OOV:1;            /*!< bit:     18  Output Off Value                   */
    uint32_t OE:1;             /*!< bit:     19  Output Enable                      */
    uint32_t DIVSEL:1;         /*!< bit:     20  Divide Selection                   */
    uint32_t RUNSTDBY:1;       /*!< bit:     21  Run during Standby                 */
    uint32_t :10;              /*!< bit: 22..31  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} GCLK_GENCTRL_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define GCLK_GENCTRL_OFFSET         0x4          /**< \brief (GCLK_GENCTRL offset) Generic Clock Generator Control Register */
#define GCLK_GENCTRL_RESETVALUE     0x00000000   /**< \brief (GCLK_GENCTRL reset_value) Generic Clock Generator Control Register */

#define GCLK_GENCTRL_ID_Pos         0            /**< \brief (GCLK_GENCTRL) Generic Clock Generator Selection */
#define GCLK_GENCTRL_ID_Msk         (0xFu << GCLK_GENCTRL_ID_Pos)
#define GCLK_GENCTRL_ID(value)      ((GCLK_GENCTRL_ID_Msk & ((value) << GCLK_GENCTRL_ID_Pos)))
#define GCLK_GENCTRL_SRC_Pos        8            /**< \brief (GCLK_GENCTRL) Clock Source Select */
#define GCLK_GENCTRL_SRC_Msk        (0x1Fu << GCLK_GENCTRL_SRC_Pos)
#define GCLK_GENCTRL_SRC(value)     ((GCLK_GENCTRL_SRC_Msk & ((value) << GCLK_GENCTRL_SRC_Pos)))
#define GCLK_GENCTRL_GENEN_Pos      16           /**< \brief (GCLK_GENCTRL) Generic Clock Generator Enable */
#define GCLK_GENCTRL_GENEN          (0x1u << GCLK_GENCTRL_GENEN_Pos)
#define GCLK_GENCTRL_IDC_Pos        17           /**< \brief (GCLK_GENCTRL) Improve Duty Cycle */
#define GCLK_GENCTRL_IDC            (0x1u << GCLK_GENCTRL_IDC_Pos)
#define GCLK_GENCTRL_OOV_Pos        18           /**< \brief (GCLK_GENCTRL) Output Off Value */
#define GCLK_GENCTRL_OOV            (0x1u << GCLK_GENCTRL_OOV_Pos)
#define GCLK_GENCTRL_OE_Pos         19           /**< \brief (GCLK_GENCTRL) Output Enable */
#define GCLK_GENCTRL_OE             (0x1u << GCLK_GENCTRL_OE_Pos)
#define GCLK_GENCTRL_DIVSEL_Pos     20           /**< \brief (GCLK_GENCTRL) Divide Selection */
#define GCLK_GENCTRL_DIVSEL         (0x1u << GCLK_GENCTRL_DIVSEL_Pos)
#define GCLK_GENCTRL_RUNSTDBY_Pos   21           /**< \brief (GCLK_GENCTRL) Run during Standby */
#define GCLK_GENCTRL_RUNSTDBY       (0x1u << GCLK_GENCTRL_RUNSTDBY_Pos)
#define GCLK_GENCTRL_MASK           0x003F1F0Fu  /**< \brief (GCLK_GENCTRL) MASK Register */

/* -------- GCLK_GENDIV : (GCLK Offset: 0x8) (R/W 32) Generic Clock Generator Division Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t ID:4;             /*!< bit:  0.. 3  Generic Clock Generator Selection  */
    uint32_t :4;               /*!< bit:  4.. 7  Reserved                           */
    uint32_t DIV:16;           /*!< bit:  8..23  Division Factor                    */
    uint32_t :8;               /*!< bit: 24..31  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} GCLK_GENDIV_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define GCLK_GENDIV_OFFSET          0x8          /**< \brief (GCLK_GENDIV offset) Generic Clock Generator Division Register */
#define GCLK_GENDIV_RESETVALUE      0x00000000   /**< \brief (GCLK_GENDIV reset_value) Generic Clock Generator Division Register */

#define GCLK_GENDIV_ID_Pos          0            /**< \brief (GCLK_GENDIV) Generic Clock Generator Selection */
#define GCLK_GENDIV_ID_Msk          (0xFu << GCLK_GENDIV_ID_Pos)
#define GCLK_GENDIV_ID(value)       ((GCLK_GENDIV_ID_Msk & ((value) << GCLK_GENDIV_ID_Pos)))
#define GCLK_GENDIV_DIV_Pos         8            /**< \brief (GCLK_GENDIV) Division Factor */
#define GCLK_GENDIV_DIV_Msk         (0xFFFFu << GCLK_GENDIV_DIV_Pos)
#define GCLK_GENDIV_DIV(value)      ((GCLK_GENDIV_DIV_Msk & ((value) << GCLK_GENDIV_DIV_Pos)))
#define GCLK_GENDIV_MASK            0x00FFFF0Fu  /**< \brief (GCLK_GENDIV) MASK Register */

/** \brief GCLK hardware registers */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef struct {
  __IO GCLK_CTRL_Type            CTRL;        /**< \brief Offset: 0x0 (R/W  8) Control Register */
  __I  GCLK_STATUS_Type          STATUS;      /**< \brief Offset: 0x1 (R/   8) Status Register */
  __IO GCLK_CLKCTRL_Type         CLKCTRL;     /**< \brief Offset: 0x2 (R/W 16) Generic Clock Control Register */
  __IO GCLK_GENCTRL_Type         GENCTRL;     /**< \brief Offset: 0x4 (R/W 32) Generic Clock Generator Control Register */
  __IO GCLK_GENDIV_Type          GENDIV;      /**< \brief Offset: 0x8 (R/W 32) Generic Clock Generator Division Register */
} Gclk;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

/*@}*/

#endif /* _SAMD20_GCLK_COMPONENT_ */
