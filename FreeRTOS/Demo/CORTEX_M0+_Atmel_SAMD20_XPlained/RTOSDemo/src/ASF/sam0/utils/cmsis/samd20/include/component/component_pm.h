/**
 * \file
 *
 * \brief Component description for PM
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

#ifndef _SAMD20_PM_COMPONENT_
#define _SAMD20_PM_COMPONENT_

/* ========================================================================== */
/**  SOFTWARE API DEFINITION FOR PM */
/* ========================================================================== */
/** \addtogroup SAMD20_PM Power Manager */
/*@{*/

#define REV_PM                      0x200

/* -------- PM_CTRL : (PM Offset: 0x00) (R/W  8) Control Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  :2;               /*!< bit:  0.. 1  Reserved                           */
    uint8_t  CFDEN:1;          /*!< bit:      2  Clock Failure Detector Enable      */
    uint8_t  :1;               /*!< bit:      3  Reserved                           */
    uint8_t  BKUPCLK:1;        /*!< bit:      4  Backup Clock Select                */
    uint8_t  :3;               /*!< bit:  5.. 7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} PM_CTRL_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define PM_CTRL_OFFSET              0x00         /**< \brief (PM_CTRL offset) Control Register */
#define PM_CTRL_RESETVALUE          0x00         /**< \brief (PM_CTRL reset_value) Control Register */

#define PM_CTRL_CFDEN_Pos           2            /**< \brief (PM_CTRL) Clock Failure Detector Enable */
#define PM_CTRL_CFDEN               (0x1u << PM_CTRL_CFDEN_Pos)
#define PM_CTRL_BKUPCLK_Pos         4            /**< \brief (PM_CTRL) Backup Clock Select */
#define PM_CTRL_BKUPCLK             (0x1u << PM_CTRL_BKUPCLK_Pos)
#define PM_CTRL_MASK                0x14u        /**< \brief (PM_CTRL) MASK Register */

/* -------- PM_SLEEP : (PM Offset: 0x01) (R/W  8) Sleep Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  IDLE:2;           /*!< bit:  0.. 1  Idle Level                         */
    uint8_t  :6;               /*!< bit:  2.. 7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} PM_SLEEP_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define PM_SLEEP_OFFSET             0x01         /**< \brief (PM_SLEEP offset) Sleep Register */
#define PM_SLEEP_RESETVALUE         0x00         /**< \brief (PM_SLEEP reset_value) Sleep Register */

#define PM_SLEEP_IDLE_Pos           0            /**< \brief (PM_SLEEP) Idle Level */
#define PM_SLEEP_IDLE_Msk           (0x3u << PM_SLEEP_IDLE_Pos)
#define PM_SLEEP_IDLE(value)        ((PM_SLEEP_IDLE_Msk & ((value) << PM_SLEEP_IDLE_Pos)))
#define PM_SLEEP_MASK               0x03u        /**< \brief (PM_SLEEP) MASK Register */

/* -------- PM_CPUSEL : (PM Offset: 0x08) (R/W  8) CPU Clock Select -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  CPUDIV:3;         /*!< bit:  0.. 2  CPU Clock Select                   */
    uint8_t  :5;               /*!< bit:  3.. 7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} PM_CPUSEL_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define PM_CPUSEL_OFFSET            0x08         /**< \brief (PM_CPUSEL offset) CPU Clock Select */
#define PM_CPUSEL_RESETVALUE        0x00         /**< \brief (PM_CPUSEL reset_value) CPU Clock Select */

#define PM_CPUSEL_CPUDIV_Pos        0            /**< \brief (PM_CPUSEL) CPU Clock Select */
#define PM_CPUSEL_CPUDIV_Msk        (0x7u << PM_CPUSEL_CPUDIV_Pos)
#define PM_CPUSEL_CPUDIV(value)     ((PM_CPUSEL_CPUDIV_Msk & ((value) << PM_CPUSEL_CPUDIV_Pos)))
#define PM_CPUSEL_MASK              0x07u        /**< \brief (PM_CPUSEL) MASK Register */

/* -------- PM_APBASEL : (PM Offset: 0x09) (R/W  8) APBA Clock Select -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  APBADIV:3;        /*!< bit:  0.. 2  APBA Clock Select                  */
    uint8_t  :5;               /*!< bit:  3.. 7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} PM_APBASEL_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define PM_APBASEL_OFFSET           0x09         /**< \brief (PM_APBASEL offset) APBA Clock Select */
#define PM_APBASEL_RESETVALUE       0x00         /**< \brief (PM_APBASEL reset_value) APBA Clock Select */

#define PM_APBASEL_APBADIV_Pos      0            /**< \brief (PM_APBASEL) APBA Clock Select */
#define PM_APBASEL_APBADIV_Msk      (0x7u << PM_APBASEL_APBADIV_Pos)
#define PM_APBASEL_APBADIV(value)   ((PM_APBASEL_APBADIV_Msk & ((value) << PM_APBASEL_APBADIV_Pos)))
#define PM_APBASEL_MASK             0x07u        /**< \brief (PM_APBASEL) MASK Register */

/* -------- PM_APBBSEL : (PM Offset: 0x0A) (R/W  8) APBB Clock Select -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  APBBDIV:3;        /*!< bit:  0.. 2  PB Clock Select                    */
    uint8_t  :5;               /*!< bit:  3.. 7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} PM_APBBSEL_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define PM_APBBSEL_OFFSET           0x0A         /**< \brief (PM_APBBSEL offset) APBB Clock Select */
#define PM_APBBSEL_RESETVALUE       0x00         /**< \brief (PM_APBBSEL reset_value) APBB Clock Select */

#define PM_APBBSEL_APBBDIV_Pos      0            /**< \brief (PM_APBBSEL) PB Clock Select */
#define PM_APBBSEL_APBBDIV_Msk      (0x7u << PM_APBBSEL_APBBDIV_Pos)
#define PM_APBBSEL_APBBDIV(value)   ((PM_APBBSEL_APBBDIV_Msk & ((value) << PM_APBBSEL_APBBDIV_Pos)))
#define PM_APBBSEL_MASK             0x07u        /**< \brief (PM_APBBSEL) MASK Register */

/* -------- PM_APBCSEL : (PM Offset: 0x0B) (R/W  8) APBC Clock Select -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  APBCDIV:3;        /*!< bit:  0.. 2  APBC Clock Select                  */
    uint8_t  :5;               /*!< bit:  3.. 7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} PM_APBCSEL_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define PM_APBCSEL_OFFSET           0x0B         /**< \brief (PM_APBCSEL offset) APBC Clock Select */
#define PM_APBCSEL_RESETVALUE       0x00         /**< \brief (PM_APBCSEL reset_value) APBC Clock Select */

#define PM_APBCSEL_APBCDIV_Pos      0            /**< \brief (PM_APBCSEL) APBC Clock Select */
#define PM_APBCSEL_APBCDIV_Msk      (0x7u << PM_APBCSEL_APBCDIV_Pos)
#define PM_APBCSEL_APBCDIV(value)   ((PM_APBCSEL_APBCDIV_Msk & ((value) << PM_APBCSEL_APBCDIV_Pos)))
#define PM_APBCSEL_MASK             0x07u        /**< \brief (PM_APBCSEL) MASK Register */

/* -------- PM_AHBMASK : (PM Offset: 0x14) (R/W 32) AHB Mask -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t HPB0:1;           /*!< bit:      0  HPB0 AHB Clock Mask                */
    uint32_t HPB1:1;           /*!< bit:      1  HPB1 AHB Clock Mask                */
    uint32_t HPB2:1;           /*!< bit:      2  HPB2 AHB Clock Mask                */
    uint32_t DSU:1;            /*!< bit:      3  DSU AHB Clock Mask                 */
    uint32_t NVMCTRL:1;        /*!< bit:      4  NVMCTRL AHB Clock Mask             */
    uint32_t :27;              /*!< bit:  5..31  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} PM_AHBMASK_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define PM_AHBMASK_OFFSET           0x14         /**< \brief (PM_AHBMASK offset) AHB Mask */
#define PM_AHBMASK_RESETVALUE       0x0000001F   /**< \brief (PM_AHBMASK reset_value) AHB Mask */

#define PM_AHBMASK_HPB0_Pos         0            /**< \brief (PM_AHBMASK) HPB0 AHB Clock Mask */
#define PM_AHBMASK_HPB0             (0x1u << PM_AHBMASK_HPB0_Pos)
#define PM_AHBMASK_HPB1_Pos         1            /**< \brief (PM_AHBMASK) HPB1 AHB Clock Mask */
#define PM_AHBMASK_HPB1             (0x1u << PM_AHBMASK_HPB1_Pos)
#define PM_AHBMASK_HPB2_Pos         2            /**< \brief (PM_AHBMASK) HPB2 AHB Clock Mask */
#define PM_AHBMASK_HPB2             (0x1u << PM_AHBMASK_HPB2_Pos)
#define PM_AHBMASK_DSU_Pos          3            /**< \brief (PM_AHBMASK) DSU AHB Clock Mask */
#define PM_AHBMASK_DSU              (0x1u << PM_AHBMASK_DSU_Pos)
#define PM_AHBMASK_NVMCTRL_Pos      4            /**< \brief (PM_AHBMASK) NVMCTRL AHB Clock Mask */
#define PM_AHBMASK_NVMCTRL          (0x1u << PM_AHBMASK_NVMCTRL_Pos)
#define PM_AHBMASK_MASK             0x0000001Fu  /**< \brief (PM_AHBMASK) MASK Register */

/* -------- PM_APBAMASK : (PM Offset: 0x18) (R/W 32) APBA Mask -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t PAC0:1;           /*!< bit:      0  PAC0 APB Clock Mask                */
    uint32_t PM:1;             /*!< bit:      1  PM APB Clock Mask                  */
    uint32_t SYSCTRL:1;        /*!< bit:      2  SYSCTRL APB Clock Mask             */
    uint32_t GCLK:1;           /*!< bit:      3  GCLK APB Clock Mask                */
    uint32_t WDT:1;            /*!< bit:      4  WDT APB Clock Mask                 */
    uint32_t RTC:1;            /*!< bit:      5  RTC APB Clock Mask                 */
    uint32_t EIC:1;            /*!< bit:      6  EIC APB Clock Mask                 */
    uint32_t :25;              /*!< bit:  7..31  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} PM_APBAMASK_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define PM_APBAMASK_OFFSET          0x18         /**< \brief (PM_APBAMASK offset) APBA Mask */
#define PM_APBAMASK_RESETVALUE      0x0000007F   /**< \brief (PM_APBAMASK reset_value) APBA Mask */

#define PM_APBAMASK_PAC0_Pos        0            /**< \brief (PM_APBAMASK) PAC0 APB Clock Mask */
#define PM_APBAMASK_PAC0            (0x1u << PM_APBAMASK_PAC0_Pos)
#define PM_APBAMASK_PM_Pos          1            /**< \brief (PM_APBAMASK) PM APB Clock Mask */
#define PM_APBAMASK_PM              (0x1u << PM_APBAMASK_PM_Pos)
#define PM_APBAMASK_SYSCTRL_Pos     2            /**< \brief (PM_APBAMASK) SYSCTRL APB Clock Mask */
#define PM_APBAMASK_SYSCTRL         (0x1u << PM_APBAMASK_SYSCTRL_Pos)
#define PM_APBAMASK_GCLK_Pos        3            /**< \brief (PM_APBAMASK) GCLK APB Clock Mask */
#define PM_APBAMASK_GCLK            (0x1u << PM_APBAMASK_GCLK_Pos)
#define PM_APBAMASK_WDT_Pos         4            /**< \brief (PM_APBAMASK) WDT APB Clock Mask */
#define PM_APBAMASK_WDT             (0x1u << PM_APBAMASK_WDT_Pos)
#define PM_APBAMASK_RTC_Pos         5            /**< \brief (PM_APBAMASK) RTC APB Clock Mask */
#define PM_APBAMASK_RTC             (0x1u << PM_APBAMASK_RTC_Pos)
#define PM_APBAMASK_EIC_Pos         6            /**< \brief (PM_APBAMASK) EIC APB Clock Mask */
#define PM_APBAMASK_EIC             (0x1u << PM_APBAMASK_EIC_Pos)
#define PM_APBAMASK_MASK            0x0000007Fu  /**< \brief (PM_APBAMASK) MASK Register */

/* -------- PM_APBBMASK : (PM Offset: 0x1C) (R/W 32) APBB Mask -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t PAC1:1;           /*!< bit:      0  PAC1 APB Clock Mask                */
    uint32_t DSU:1;            /*!< bit:      1  DSU APB Clock Mask                 */
    uint32_t NVMCTRL:1;        /*!< bit:      2  NVMCTRL APB Clock Mask             */
    uint32_t PORT:1;           /*!< bit:      3  PORT APB Clock Mask                */
    uint32_t :28;              /*!< bit:  4..31  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} PM_APBBMASK_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define PM_APBBMASK_OFFSET          0x1C         /**< \brief (PM_APBBMASK offset) APBB Mask */
#define PM_APBBMASK_RESETVALUE      0x0000001F   /**< \brief (PM_APBBMASK reset_value) APBB Mask */

#define PM_APBBMASK_PAC1_Pos        0            /**< \brief (PM_APBBMASK) PAC1 APB Clock Mask */
#define PM_APBBMASK_PAC1            (0x1u << PM_APBBMASK_PAC1_Pos)
#define PM_APBBMASK_DSU_Pos         1            /**< \brief (PM_APBBMASK) DSU APB Clock Mask */
#define PM_APBBMASK_DSU             (0x1u << PM_APBBMASK_DSU_Pos)
#define PM_APBBMASK_NVMCTRL_Pos     2            /**< \brief (PM_APBBMASK) NVMCTRL APB Clock Mask */
#define PM_APBBMASK_NVMCTRL         (0x1u << PM_APBBMASK_NVMCTRL_Pos)
#define PM_APBBMASK_PORT_Pos        3            /**< \brief (PM_APBBMASK) PORT APB Clock Mask */
#define PM_APBBMASK_PORT            (0x1u << PM_APBBMASK_PORT_Pos)
#define PM_APBBMASK_MASK            0x0000000Fu  /**< \brief (PM_APBBMASK) MASK Register */

/* -------- PM_APBCMASK : (PM Offset: 0x20) (R/W 32) APBC Mask -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t PAC2:1;           /*!< bit:      0  PAC2 APB Clock Mask                */
    uint32_t EVSYS:1;          /*!< bit:      1  EVSYS APB Clock Mask               */
    uint32_t SERCOM0:1;        /*!< bit:      2  SERCOM0 APB Clock Mask             */
    uint32_t SERCOM1:1;        /*!< bit:      3  SERCOM1 APB Clock Mask             */
    uint32_t SERCOM2:1;        /*!< bit:      4  SERCOM2 APB Clock Mask             */
    uint32_t SERCOM3:1;        /*!< bit:      5  SERCOM3 APB Clock Mask             */
    uint32_t SERCOM4:1;        /*!< bit:      6  SERCOM4 APB Clock Mask             */
    uint32_t SERCOM5:1;        /*!< bit:      7  SERCOM5 APB Clock Mask             */
    uint32_t TC0:1;            /*!< bit:      8  TC0 APB Clock Mask                 */
    uint32_t TC1:1;            /*!< bit:      9  TC1 APB Clock Mask                 */
    uint32_t TC2:1;            /*!< bit:     10  TC2 APB Clock Mask                 */
    uint32_t TC3:1;            /*!< bit:     11  TC3 APB Clock Mask                 */
    uint32_t TC4:1;            /*!< bit:     12  TC4 APB Clock Mask                 */
    uint32_t TC5:1;            /*!< bit:     13  TC5 APB Clock Mask                 */
    uint32_t TC6:1;            /*!< bit:     14  TC6 APB Clock Mask                 */
    uint32_t TC7:1;            /*!< bit:     15  TC7 APB Clock Mask                 */
    uint32_t ADC:1;            /*!< bit:     16  ADC APB Clock Mask                 */
    uint32_t AC:1;             /*!< bit:     17  AC APB Clock Mask                  */
    uint32_t DAC:1;            /*!< bit:     18  DAC APB Clock Mask                 */
    uint32_t :13;              /*!< bit: 19..31  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} PM_APBCMASK_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define PM_APBCMASK_OFFSET          0x20         /**< \brief (PM_APBCMASK offset) APBC Mask */
#define PM_APBCMASK_RESETVALUE      0x00010000   /**< \brief (PM_APBCMASK reset_value) APBC Mask */

#define PM_APBCMASK_PAC2_Pos        0            /**< \brief (PM_APBCMASK) PAC2 APB Clock Mask */
#define PM_APBCMASK_PAC2            (0x1u << PM_APBCMASK_PAC2_Pos)
#define PM_APBCMASK_EVSYS_Pos       1            /**< \brief (PM_APBCMASK) EVSYS APB Clock Mask */
#define PM_APBCMASK_EVSYS           (0x1u << PM_APBCMASK_EVSYS_Pos)
#define PM_APBCMASK_SERCOM0_Pos     2            /**< \brief (PM_APBCMASK) SERCOM0 APB Clock Mask */
#define PM_APBCMASK_SERCOM0         (0x1u << PM_APBCMASK_SERCOM0_Pos)
#define PM_APBCMASK_SERCOM1_Pos     3            /**< \brief (PM_APBCMASK) SERCOM1 APB Clock Mask */
#define PM_APBCMASK_SERCOM1         (0x1u << PM_APBCMASK_SERCOM1_Pos)
#define PM_APBCMASK_SERCOM2_Pos     4            /**< \brief (PM_APBCMASK) SERCOM2 APB Clock Mask */
#define PM_APBCMASK_SERCOM2         (0x1u << PM_APBCMASK_SERCOM2_Pos)
#define PM_APBCMASK_SERCOM3_Pos     5            /**< \brief (PM_APBCMASK) SERCOM3 APB Clock Mask */
#define PM_APBCMASK_SERCOM3         (0x1u << PM_APBCMASK_SERCOM3_Pos)
#define PM_APBCMASK_SERCOM4_Pos     6            /**< \brief (PM_APBCMASK) SERCOM4 APB Clock Mask */
#define PM_APBCMASK_SERCOM4         (0x1u << PM_APBCMASK_SERCOM4_Pos)
#define PM_APBCMASK_SERCOM5_Pos     7            /**< \brief (PM_APBCMASK) SERCOM5 APB Clock Mask */
#define PM_APBCMASK_SERCOM5         (0x1u << PM_APBCMASK_SERCOM5_Pos)
#define PM_APBCMASK_TC0_Pos         8            /**< \brief (PM_APBCMASK) TC0 APB Clock Mask */
#define PM_APBCMASK_TC0             (0x1u << PM_APBCMASK_TC0_Pos)
#define PM_APBCMASK_TC1_Pos         9            /**< \brief (PM_APBCMASK) TC1 APB Clock Mask */
#define PM_APBCMASK_TC1             (0x1u << PM_APBCMASK_TC1_Pos)
#define PM_APBCMASK_TC2_Pos         10           /**< \brief (PM_APBCMASK) TC2 APB Clock Mask */
#define PM_APBCMASK_TC2             (0x1u << PM_APBCMASK_TC2_Pos)
#define PM_APBCMASK_TC3_Pos         11           /**< \brief (PM_APBCMASK) TC3 APB Clock Mask */
#define PM_APBCMASK_TC3             (0x1u << PM_APBCMASK_TC3_Pos)
#define PM_APBCMASK_TC4_Pos         12           /**< \brief (PM_APBCMASK) TC4 APB Clock Mask */
#define PM_APBCMASK_TC4             (0x1u << PM_APBCMASK_TC4_Pos)
#define PM_APBCMASK_TC5_Pos         13           /**< \brief (PM_APBCMASK) TC5 APB Clock Mask */
#define PM_APBCMASK_TC5             (0x1u << PM_APBCMASK_TC5_Pos)
#define PM_APBCMASK_TC6_Pos         14           /**< \brief (PM_APBCMASK) TC6 APB Clock Mask */
#define PM_APBCMASK_TC6             (0x1u << PM_APBCMASK_TC6_Pos)
#define PM_APBCMASK_TC7_Pos         15           /**< \brief (PM_APBCMASK) TC7 APB Clock Mask */
#define PM_APBCMASK_TC7             (0x1u << PM_APBCMASK_TC7_Pos)
#define PM_APBCMASK_ADC_Pos         16           /**< \brief (PM_APBCMASK) ADC APB Clock Mask */
#define PM_APBCMASK_ADC             (0x1u << PM_APBCMASK_ADC_Pos)
#define PM_APBCMASK_AC_Pos          17           /**< \brief (PM_APBCMASK) AC APB Clock Mask */
#define PM_APBCMASK_AC              (0x1u << PM_APBCMASK_AC_Pos)
#define PM_APBCMASK_DAC_Pos         18           /**< \brief (PM_APBCMASK) DAC APB Clock Mask */
#define PM_APBCMASK_DAC             (0x1u << PM_APBCMASK_DAC_Pos)
#define PM_APBCMASK_MASK            0x0007FFFFu  /**< \brief (PM_APBCMASK) MASK Register */

/* -------- PM_INTENCLR : (PM Offset: 0x34) (R/W  8) Interrupt Enable Clear Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  CKRDY:1;          /*!< bit:      0  Clock Ready Interrupt Enable Clear */
    uint8_t  CFD:1;            /*!< bit:      1  Clock Failure Detector Enable Clear */
    uint8_t  :6;               /*!< bit:  2.. 7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} PM_INTENCLR_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define PM_INTENCLR_OFFSET          0x34         /**< \brief (PM_INTENCLR offset) Interrupt Enable Clear Register */
#define PM_INTENCLR_RESETVALUE      0x00         /**< \brief (PM_INTENCLR reset_value) Interrupt Enable Clear Register */

#define PM_INTENCLR_CKRDY_Pos       0            /**< \brief (PM_INTENCLR) Clock Ready Interrupt Enable Clear */
#define PM_INTENCLR_CKRDY           (0x1u << PM_INTENCLR_CKRDY_Pos)
#define PM_INTENCLR_CFD_Pos         1            /**< \brief (PM_INTENCLR) Clock Failure Detector Enable Clear */
#define PM_INTENCLR_CFD             (0x1u << PM_INTENCLR_CFD_Pos)
#define PM_INTENCLR_MASK            0x03u        /**< \brief (PM_INTENCLR) MASK Register */

/* -------- PM_INTENSET : (PM Offset: 0x35) (R/W  8) Interrupt Enable Set Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  CKRDY:1;          /*!< bit:      0  Clock Ready Interrupt Enable Set   */
    uint8_t  CFD:1;            /*!< bit:      1  Clock Failure Detector Enable Set  */
    uint8_t  :6;               /*!< bit:  2.. 7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} PM_INTENSET_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define PM_INTENSET_OFFSET          0x35         /**< \brief (PM_INTENSET offset) Interrupt Enable Set Register */
#define PM_INTENSET_RESETVALUE      0x00         /**< \brief (PM_INTENSET reset_value) Interrupt Enable Set Register */

#define PM_INTENSET_CKRDY_Pos       0            /**< \brief (PM_INTENSET) Clock Ready Interrupt Enable Set */
#define PM_INTENSET_CKRDY           (0x1u << PM_INTENSET_CKRDY_Pos)
#define PM_INTENSET_CFD_Pos         1            /**< \brief (PM_INTENSET) Clock Failure Detector Enable Set */
#define PM_INTENSET_CFD             (0x1u << PM_INTENSET_CFD_Pos)
#define PM_INTENSET_MASK            0x03u        /**< \brief (PM_INTENSET) MASK Register */

/* -------- PM_INTFLAG : (PM Offset: 0x36) (R/W  8) Interrupt Flag Status and Clear Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  CKRDY:1;          /*!< bit:      0  Clock Ready Interrupt              */
    uint8_t  CFD:1;            /*!< bit:      1  Clock Failure Detectore Interrupt  */
    uint8_t  :6;               /*!< bit:  2.. 7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} PM_INTFLAG_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define PM_INTFLAG_OFFSET           0x36         /**< \brief (PM_INTFLAG offset) Interrupt Flag Status and Clear Register */
#define PM_INTFLAG_RESETVALUE       0x00         /**< \brief (PM_INTFLAG reset_value) Interrupt Flag Status and Clear Register */

#define PM_INTFLAG_CKRDY_Pos        0            /**< \brief (PM_INTFLAG) Clock Ready Interrupt */
#define PM_INTFLAG_CKRDY            (0x1u << PM_INTFLAG_CKRDY_Pos)
#define PM_INTFLAG_CFD_Pos          1            /**< \brief (PM_INTFLAG) Clock Failure Detectore Interrupt */
#define PM_INTFLAG_CFD              (0x1u << PM_INTFLAG_CFD_Pos)
#define PM_INTFLAG_MASK             0x03u        /**< \brief (PM_INTFLAG) MASK Register */

/* -------- PM_RCAUSE : (PM Offset: 0x38) (R/   8) Reset Cause Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  POR:1;            /*!< bit:      0  Power-on Reset                     */
    uint8_t  BOD12:1;          /*!< bit:      1  Brown-out 1.2V Reset               */
    uint8_t  BOD33:1;          /*!< bit:      2  Brown-out 3.3V Reset               */
    uint8_t  :1;               /*!< bit:      3  Reserved                           */
    uint8_t  EXT:1;            /*!< bit:      4  External Reset Pin                 */
    uint8_t  WDT:1;            /*!< bit:      5  Watchdog Reset                     */
    uint8_t  SYST:1;           /*!< bit:      6  System Reset Request               */
    uint8_t  :1;               /*!< bit:      7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} PM_RCAUSE_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define PM_RCAUSE_OFFSET            0x38         /**< \brief (PM_RCAUSE offset) Reset Cause Register */
#define PM_RCAUSE_RESETVALUE        0x01         /**< \brief (PM_RCAUSE reset_value) Reset Cause Register */

#define PM_RCAUSE_POR_Pos           0            /**< \brief (PM_RCAUSE) Power-on Reset */
#define PM_RCAUSE_POR               (0x1u << PM_RCAUSE_POR_Pos)
#define PM_RCAUSE_BOD12_Pos         1            /**< \brief (PM_RCAUSE) Brown-out 1.2V Reset */
#define PM_RCAUSE_BOD12             (0x1u << PM_RCAUSE_BOD12_Pos)
#define PM_RCAUSE_BOD33_Pos         2            /**< \brief (PM_RCAUSE) Brown-out 3.3V Reset */
#define PM_RCAUSE_BOD33             (0x1u << PM_RCAUSE_BOD33_Pos)
#define PM_RCAUSE_EXT_Pos           4            /**< \brief (PM_RCAUSE) External Reset Pin */
#define PM_RCAUSE_EXT               (0x1u << PM_RCAUSE_EXT_Pos)
#define PM_RCAUSE_WDT_Pos           5            /**< \brief (PM_RCAUSE) Watchdog Reset */
#define PM_RCAUSE_WDT               (0x1u << PM_RCAUSE_WDT_Pos)
#define PM_RCAUSE_SYST_Pos          6            /**< \brief (PM_RCAUSE) System Reset Request */
#define PM_RCAUSE_SYST              (0x1u << PM_RCAUSE_SYST_Pos)
#define PM_RCAUSE_MASK              0x77u        /**< \brief (PM_RCAUSE) MASK Register */

/** \brief PM hardware registers */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef struct {
  __IO PM_CTRL_Type              CTRL;        /**< \brief Offset: 0x00 (R/W  8) Control Register */
  __IO PM_SLEEP_Type             SLEEP;       /**< \brief Offset: 0x01 (R/W  8) Sleep Register */
       RoReg8                    Reserved1[0x6];
  __IO PM_CPUSEL_Type            CPUSEL;      /**< \brief Offset: 0x08 (R/W  8) CPU Clock Select */
  __IO PM_APBASEL_Type           APBASEL;     /**< \brief Offset: 0x09 (R/W  8) APBA Clock Select */
  __IO PM_APBBSEL_Type           APBBSEL;     /**< \brief Offset: 0x0A (R/W  8) APBB Clock Select */
  __IO PM_APBCSEL_Type           APBCSEL;     /**< \brief Offset: 0x0B (R/W  8) APBC Clock Select */
       RoReg8                    Reserved2[0x8];
  __IO PM_AHBMASK_Type           AHBMASK;     /**< \brief Offset: 0x14 (R/W 32) AHB Mask */
  __IO PM_APBAMASK_Type          APBAMASK;    /**< \brief Offset: 0x18 (R/W 32) APBA Mask */
  __IO PM_APBBMASK_Type          APBBMASK;    /**< \brief Offset: 0x1C (R/W 32) APBB Mask */
  __IO PM_APBCMASK_Type          APBCMASK;    /**< \brief Offset: 0x20 (R/W 32) APBC Mask */
       RoReg8                    Reserved3[0x10];
  __IO PM_INTENCLR_Type          INTENCLR;    /**< \brief Offset: 0x34 (R/W  8) Interrupt Enable Clear Register */
  __IO PM_INTENSET_Type          INTENSET;    /**< \brief Offset: 0x35 (R/W  8) Interrupt Enable Set Register */
  __IO PM_INTFLAG_Type           INTFLAG;     /**< \brief Offset: 0x36 (R/W  8) Interrupt Flag Status and Clear Register */
       RoReg8                    Reserved4[0x1];
  __I  PM_RCAUSE_Type            RCAUSE;      /**< \brief Offset: 0x38 (R/   8) Reset Cause Register */
} Pm;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

/*@}*/

#endif /* _SAMD20_PM_COMPONENT_ */
