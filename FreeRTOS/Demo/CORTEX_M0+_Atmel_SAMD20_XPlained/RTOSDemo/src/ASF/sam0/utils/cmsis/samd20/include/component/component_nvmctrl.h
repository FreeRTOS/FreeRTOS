/**
 * \file
 *
 * \brief Component description for NVMCTRL
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

#ifndef _SAMD20_NVMCTRL_COMPONENT_
#define _SAMD20_NVMCTRL_COMPONENT_

/* ========================================================================== */
/**  SOFTWARE API DEFINITION FOR NVMCTRL */
/* ========================================================================== */
/** \addtogroup SAMD20_NVMCTRL Non-Volatile Memory Controller */
/*@{*/

#define REV_NVMCTRL                 0x102

/* -------- NVMCTRL_CTRLA : (NVMCTRL Offset: 0x00) (R/W 16) NVM Control Register A -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint16_t CMD:7;            /*!< bit:  0.. 6  Command                            */
    uint16_t :1;               /*!< bit:      7  Reserved                           */
    uint16_t CMDEX:8;          /*!< bit:  8..15  Command Execution                  */
  } bit;                       /*!< Structure used for bit  access                  */
  uint16_t reg;                /*!< Type      used for register access              */
} NVMCTRL_CTRLA_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define NVMCTRL_CTRLA_OFFSET        0x00         /**< \brief (NVMCTRL_CTRLA offset) NVM Control Register A */
#define NVMCTRL_CTRLA_RESETVALUE    0x0000       /**< \brief (NVMCTRL_CTRLA reset_value) NVM Control Register A */

#define NVMCTRL_CTRLA_CMD_Pos       0            /**< \brief (NVMCTRL_CTRLA) Command */
#define NVMCTRL_CTRLA_CMD_Msk       (0x7Fu << NVMCTRL_CTRLA_CMD_Pos)
#define NVMCTRL_CTRLA_CMD(value)    ((NVMCTRL_CTRLA_CMD_Msk & ((value) << NVMCTRL_CTRLA_CMD_Pos)))
#define   NVMCTRL_CTRLA_CMD_ER      (0x2u <<  0) /**< \brief (NVMCTRL_CTRLA) Erase Row */
#define   NVMCTRL_CTRLA_CMD_WP      (0x4u <<  0) /**< \brief (NVMCTRL_CTRLA) Write Page */
#define   NVMCTRL_CTRLA_CMD_EAR     (0x5u <<  0) /**< \brief (NVMCTRL_CTRLA) Erase Auxiliary Row */
#define   NVMCTRL_CTRLA_CMD_WAP     (0x6u <<  0) /**< \brief (NVMCTRL_CTRLA) Write  Auxiliary Row */
#define   NVMCTRL_CTRLA_CMD_SF      (0xAu <<  0) /**< \brief (NVMCTRL_CTRLA) Security Flow Command */
#define   NVMCTRL_CTRLA_CMD_WL      (0xFu <<  0) /**< \brief (NVMCTRL_CTRLA) Write lockbits */
#define   NVMCTRL_CTRLA_CMD_LR      (0x40u <<  0) /**< \brief (NVMCTRL_CTRLA) Lock Region */
#define   NVMCTRL_CTRLA_CMD_UR      (0x41u <<  0) /**< \brief (NVMCTRL_CTRLA) Unlock Region */
#define   NVMCTRL_CTRLA_CMD_SPRM    (0x42u <<  0) /**< \brief (NVMCTRL_CTRLA) Set Power Reduction Mode */
#define   NVMCTRL_CTRLA_CMD_CPRM    (0x43u <<  0) /**< \brief (NVMCTRL_CTRLA) Clear Power Reduction Mode */
#define   NVMCTRL_CTRLA_CMD_PBC     (0x44u <<  0) /**< \brief (NVMCTRL_CTRLA) Page Buffer Clear */
#define   NVMCTRL_CTRLA_CMD_SSB     (0x45u <<  0) /**< \brief (NVMCTRL_CTRLA) Set Security Bit */
#define   NVMCTRL_CTRLA_CMD_SMR     (0x54u <<  0) /**< \brief (NVMCTRL_CTRLA) State Machine Reset */
#define NVMCTRL_CTRLA_CMDEX_Pos     8            /**< \brief (NVMCTRL_CTRLA) Command Execution */
#define NVMCTRL_CTRLA_CMDEX_Msk     (0xFFu << NVMCTRL_CTRLA_CMDEX_Pos)
#define NVMCTRL_CTRLA_CMDEX(value)  ((NVMCTRL_CTRLA_CMDEX_Msk & ((value) << NVMCTRL_CTRLA_CMDEX_Pos)))
#define   NVMCTRL_CTRLA_CMDEX_KEY   (0xA5u <<  8) /**< \brief (NVMCTRL_CTRLA) Execution Key */
#define NVMCTRL_CTRLA_MASK          0xFF7Fu      /**< \brief (NVMCTRL_CTRLA) MASK Register */

/* -------- NVMCTRL_CTRLB : (NVMCTRL Offset: 0x04) (R/W 32) NVM Control Register B -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t :1;               /*!< bit:      0  Reserved                           */
    uint32_t RWS:4;            /*!< bit:  1.. 4  NVM Read Wait States               */
    uint32_t :2;               /*!< bit:  5.. 6  Reserved                           */
    uint32_t MANW:1;           /*!< bit:      7  Manual Write                       */
    uint32_t SLEEPPRM:2;       /*!< bit:  8.. 9  Power Reduction Mode during Sleep  */
    uint32_t :6;               /*!< bit: 10..15  Reserved                           */
    uint32_t READMODE:2;       /*!< bit: 16..17  NVMCTRL Read Mode                  */
    uint32_t CACHEDIS:1;       /*!< bit:     18  Cache Disable                      */
    uint32_t :13;              /*!< bit: 19..31  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} NVMCTRL_CTRLB_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define NVMCTRL_CTRLB_OFFSET        0x04         /**< \brief (NVMCTRL_CTRLB offset) NVM Control Register B */
#define NVMCTRL_CTRLB_RESETVALUE    0x00000000   /**< \brief (NVMCTRL_CTRLB reset_value) NVM Control Register B */

#define NVMCTRL_CTRLB_RWS_Pos       1            /**< \brief (NVMCTRL_CTRLB) NVM Read Wait States */
#define NVMCTRL_CTRLB_RWS_Msk       (0xFu << NVMCTRL_CTRLB_RWS_Pos)
#define NVMCTRL_CTRLB_RWS(value)    ((NVMCTRL_CTRLB_RWS_Msk & ((value) << NVMCTRL_CTRLB_RWS_Pos)))
#define   NVMCTRL_CTRLB_RWS_SINGLE  (0x0u <<  1) /**< \brief (NVMCTRL_CTRLB) Single Auto Wait State */
#define   NVMCTRL_CTRLB_RWS_HALF    (0x1u <<  1) /**< \brief (NVMCTRL_CTRLB) Half Auto Wait State */
#define   NVMCTRL_CTRLB_RWS_DUAL    (0x2u <<  1) /**< \brief (NVMCTRL_CTRLB) Dual Auto Wait State */
#define NVMCTRL_CTRLB_MANW_Pos      7            /**< \brief (NVMCTRL_CTRLB) Manual Write */
#define NVMCTRL_CTRLB_MANW          (0x1u << NVMCTRL_CTRLB_MANW_Pos)
#define NVMCTRL_CTRLB_SLEEPPRM_Pos  8            /**< \brief (NVMCTRL_CTRLB) Power Reduction Mode during Sleep */
#define NVMCTRL_CTRLB_SLEEPPRM_Msk  (0x3u << NVMCTRL_CTRLB_SLEEPPRM_Pos)
#define NVMCTRL_CTRLB_SLEEPPRM(value) ((NVMCTRL_CTRLB_SLEEPPRM_Msk & ((value) << NVMCTRL_CTRLB_SLEEPPRM_Pos)))
#define   NVMCTRL_CTRLB_SLEEPPRM_WAKEONACCESS (0x0u <<  8) /**< \brief (NVMCTRL_CTRLB) Wake on first access. */
#define   NVMCTRL_CTRLB_SLEEPPRM_WAKEUPINSTANT (0x1u <<  8) /**< \brief (NVMCTRL_CTRLB) Wake on sleep exit. */
#define   NVMCTRL_CTRLB_SLEEPPRM_DISABLED (0x3u <<  8) /**< \brief (NVMCTRL_CTRLB) Auto power reduction disabled. */
#define NVMCTRL_CTRLB_READMODE_Pos  16           /**< \brief (NVMCTRL_CTRLB) NVMCTRL Read Mode */
#define NVMCTRL_CTRLB_READMODE_Msk  (0x3u << NVMCTRL_CTRLB_READMODE_Pos)
#define NVMCTRL_CTRLB_READMODE(value) ((NVMCTRL_CTRLB_READMODE_Msk & ((value) << NVMCTRL_CTRLB_READMODE_Pos)))
#define NVMCTRL_CTRLB_CACHEDIS_Pos  18           /**< \brief (NVMCTRL_CTRLB) Cache Disable */
#define NVMCTRL_CTRLB_CACHEDIS      (0x1u << NVMCTRL_CTRLB_CACHEDIS_Pos)
#define NVMCTRL_CTRLB_MASK          0x0007039Eu  /**< \brief (NVMCTRL_CTRLB) MASK Register */

/* -------- NVMCTRL_PARAM : (NVMCTRL Offset: 0x08) (R/W 32) Parameter Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t NVMP:16;          /*!< bit:  0..15  NVM Pages                          */
    uint32_t PSZ:3;            /*!< bit: 16..18  Page Size                          */
    uint32_t :13;              /*!< bit: 19..31  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} NVMCTRL_PARAM_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define NVMCTRL_PARAM_OFFSET        0x08         /**< \brief (NVMCTRL_PARAM offset) Parameter Register */
#define NVMCTRL_PARAM_RESETVALUE    0x00000000   /**< \brief (NVMCTRL_PARAM reset_value) Parameter Register */

#define NVMCTRL_PARAM_NVMP_Pos      0            /**< \brief (NVMCTRL_PARAM) NVM Pages */
#define NVMCTRL_PARAM_NVMP_Msk      (0xFFFFu << NVMCTRL_PARAM_NVMP_Pos)
#define NVMCTRL_PARAM_NVMP(value)   ((NVMCTRL_PARAM_NVMP_Msk & ((value) << NVMCTRL_PARAM_NVMP_Pos)))
#define NVMCTRL_PARAM_PSZ_Pos       16           /**< \brief (NVMCTRL_PARAM) Page Size */
#define NVMCTRL_PARAM_PSZ_Msk       (0x7u << NVMCTRL_PARAM_PSZ_Pos)
#define NVMCTRL_PARAM_PSZ(value)    ((NVMCTRL_PARAM_PSZ_Msk & ((value) << NVMCTRL_PARAM_PSZ_Pos)))
#define NVMCTRL_PARAM_MASK          0x0007FFFFu  /**< \brief (NVMCTRL_PARAM) MASK Register */

/* -------- NVMCTRL_INTENCLR : (NVMCTRL Offset: 0x0C) (R/W  8) Interrupt Enable Clear Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  READY:1;          /*!< bit:      0  NVM Ready Interrupt Disable        */
    uint8_t  ERROR:1;          /*!< bit:      1  Error Interrupt Disable            */
    uint8_t  :6;               /*!< bit:  2.. 7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} NVMCTRL_INTENCLR_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define NVMCTRL_INTENCLR_OFFSET     0x0C         /**< \brief (NVMCTRL_INTENCLR offset) Interrupt Enable Clear Register */
#define NVMCTRL_INTENCLR_RESETVALUE 0x00         /**< \brief (NVMCTRL_INTENCLR reset_value) Interrupt Enable Clear Register */

#define NVMCTRL_INTENCLR_READY_Pos  0            /**< \brief (NVMCTRL_INTENCLR) NVM Ready Interrupt Disable */
#define NVMCTRL_INTENCLR_READY      (0x1u << NVMCTRL_INTENCLR_READY_Pos)
#define NVMCTRL_INTENCLR_ERROR_Pos  1            /**< \brief (NVMCTRL_INTENCLR) Error Interrupt Disable */
#define NVMCTRL_INTENCLR_ERROR      (0x1u << NVMCTRL_INTENCLR_ERROR_Pos)
#define NVMCTRL_INTENCLR_MASK       0x03u        /**< \brief (NVMCTRL_INTENCLR) MASK Register */

/* -------- NVMCTRL_INTENSET : (NVMCTRL Offset: 0x10) (R/W  8) Interrupt Enable Set Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  READY:1;          /*!< bit:      0  NVM Ready Interrupt Enable         */
    uint8_t  ERROR:1;          /*!< bit:      1  Error Interrupt Enable             */
    uint8_t  :6;               /*!< bit:  2.. 7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} NVMCTRL_INTENSET_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define NVMCTRL_INTENSET_OFFSET     0x10         /**< \brief (NVMCTRL_INTENSET offset) Interrupt Enable Set Register */
#define NVMCTRL_INTENSET_RESETVALUE 0x00         /**< \brief (NVMCTRL_INTENSET reset_value) Interrupt Enable Set Register */

#define NVMCTRL_INTENSET_READY_Pos  0            /**< \brief (NVMCTRL_INTENSET) NVM Ready Interrupt Enable */
#define NVMCTRL_INTENSET_READY      (0x1u << NVMCTRL_INTENSET_READY_Pos)
#define NVMCTRL_INTENSET_ERROR_Pos  1            /**< \brief (NVMCTRL_INTENSET) Error Interrupt Enable */
#define NVMCTRL_INTENSET_ERROR      (0x1u << NVMCTRL_INTENSET_ERROR_Pos)
#define NVMCTRL_INTENSET_MASK       0x03u        /**< \brief (NVMCTRL_INTENSET) MASK Register */

/* -------- NVMCTRL_INTFLAG : (NVMCTRL Offset: 0x14) (R/W  8) Interrupt Flag Status and Clear Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  READY:1;          /*!< bit:      0  NVM Ready Interrupt Flag           */
    uint8_t  ERROR:1;          /*!< bit:      1  Error Interrupt Flag               */
    uint8_t  :6;               /*!< bit:  2.. 7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} NVMCTRL_INTFLAG_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define NVMCTRL_INTFLAG_OFFSET      0x14         /**< \brief (NVMCTRL_INTFLAG offset) Interrupt Flag Status and Clear Register */
#define NVMCTRL_INTFLAG_RESETVALUE  0x00         /**< \brief (NVMCTRL_INTFLAG reset_value) Interrupt Flag Status and Clear Register */

#define NVMCTRL_INTFLAG_READY_Pos   0            /**< \brief (NVMCTRL_INTFLAG) NVM Ready Interrupt Flag */
#define NVMCTRL_INTFLAG_READY       (0x1u << NVMCTRL_INTFLAG_READY_Pos)
#define NVMCTRL_INTFLAG_ERROR_Pos   1            /**< \brief (NVMCTRL_INTFLAG) Error Interrupt Flag */
#define NVMCTRL_INTFLAG_ERROR       (0x1u << NVMCTRL_INTFLAG_ERROR_Pos)
#define NVMCTRL_INTFLAG_MASK        0x03u        /**< \brief (NVMCTRL_INTFLAG) MASK Register */

/* -------- NVMCTRL_STATUS : (NVMCTRL Offset: 0x18) (R/W 16) Status Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint16_t PRM:1;            /*!< bit:      0  Power Reduction Mode               */
    uint16_t LOAD:1;           /*!< bit:      1  NVM Page Buffer Active Loading     */
    uint16_t PROGE:1;          /*!< bit:      2  Programming Error Status           */
    uint16_t LOCKE:1;          /*!< bit:      3  Lock Error Status                  */
    uint16_t NVME:1;           /*!< bit:      4  NVM Error                          */
    uint16_t :3;               /*!< bit:  5.. 7  Reserved                           */
    uint16_t SB:1;             /*!< bit:      8  Security Bit Status                */
    uint16_t :7;               /*!< bit:  9..15  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint16_t reg;                /*!< Type      used for register access              */
} NVMCTRL_STATUS_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define NVMCTRL_STATUS_OFFSET       0x18         /**< \brief (NVMCTRL_STATUS offset) Status Register */
#define NVMCTRL_STATUS_RESETVALUE   0x0000       /**< \brief (NVMCTRL_STATUS reset_value) Status Register */

#define NVMCTRL_STATUS_PRM_Pos      0            /**< \brief (NVMCTRL_STATUS) Power Reduction Mode */
#define NVMCTRL_STATUS_PRM          (0x1u << NVMCTRL_STATUS_PRM_Pos)
#define NVMCTRL_STATUS_LOAD_Pos     1            /**< \brief (NVMCTRL_STATUS) NVM Page Buffer Active Loading */
#define NVMCTRL_STATUS_LOAD         (0x1u << NVMCTRL_STATUS_LOAD_Pos)
#define NVMCTRL_STATUS_PROGE_Pos    2            /**< \brief (NVMCTRL_STATUS) Programming Error Status */
#define NVMCTRL_STATUS_PROGE        (0x1u << NVMCTRL_STATUS_PROGE_Pos)
#define NVMCTRL_STATUS_LOCKE_Pos    3            /**< \brief (NVMCTRL_STATUS) Lock Error Status */
#define NVMCTRL_STATUS_LOCKE        (0x1u << NVMCTRL_STATUS_LOCKE_Pos)
#define NVMCTRL_STATUS_NVME_Pos     4            /**< \brief (NVMCTRL_STATUS) NVM Error */
#define NVMCTRL_STATUS_NVME         (0x1u << NVMCTRL_STATUS_NVME_Pos)
#define NVMCTRL_STATUS_SB_Pos       8            /**< \brief (NVMCTRL_STATUS) Security Bit Status */
#define NVMCTRL_STATUS_SB           (0x1u << NVMCTRL_STATUS_SB_Pos)
#define NVMCTRL_STATUS_MASK         0x011Fu      /**< \brief (NVMCTRL_STATUS) MASK Register */

/* -------- NVMCTRL_ADDR : (NVMCTRL Offset: 0x1C) (R/W 32) Address Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t ADDR:22;          /*!< bit:  0..21  NVM Address                        */
    uint32_t :10;              /*!< bit: 22..31  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} NVMCTRL_ADDR_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define NVMCTRL_ADDR_OFFSET         0x1C         /**< \brief (NVMCTRL_ADDR offset) Address Register */
#define NVMCTRL_ADDR_RESETVALUE     0x00000000   /**< \brief (NVMCTRL_ADDR reset_value) Address Register */

#define NVMCTRL_ADDR_ADDR_Pos       0            /**< \brief (NVMCTRL_ADDR) NVM Address */
#define NVMCTRL_ADDR_ADDR_Msk       (0x3FFFFFu << NVMCTRL_ADDR_ADDR_Pos)
#define NVMCTRL_ADDR_ADDR(value)    ((NVMCTRL_ADDR_ADDR_Msk & ((value) << NVMCTRL_ADDR_ADDR_Pos)))
#define NVMCTRL_ADDR_MASK           0x003FFFFFu  /**< \brief (NVMCTRL_ADDR) MASK Register */

/* -------- NVMCTRL_LOCK : (NVMCTRL Offset: 0x20) (R/W 16) Lock Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint16_t LOCK:16;          /*!< bit:  0..15  Region Lock Bits                   */
  } bit;                       /*!< Structure used for bit  access                  */
  uint16_t reg;                /*!< Type      used for register access              */
} NVMCTRL_LOCK_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define NVMCTRL_LOCK_OFFSET         0x20         /**< \brief (NVMCTRL_LOCK offset) Lock Register */
#define NVMCTRL_LOCK_RESETVALUE     0x0000       /**< \brief (NVMCTRL_LOCK reset_value) Lock Register */

#define NVMCTRL_LOCK_LOCK_Pos       0            /**< \brief (NVMCTRL_LOCK) Region Lock Bits */
#define NVMCTRL_LOCK_LOCK_Msk       (0xFFFFu << NVMCTRL_LOCK_LOCK_Pos)
#define NVMCTRL_LOCK_LOCK(value)    ((NVMCTRL_LOCK_LOCK_Msk & ((value) << NVMCTRL_LOCK_LOCK_Pos)))
#define NVMCTRL_LOCK_MASK           0xFFFFu      /**< \brief (NVMCTRL_LOCK) MASK Register */

/** \brief NVMCTRL hardware registers */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef struct {
  __IO NVMCTRL_CTRLA_Type        CTRLA;       /**< \brief Offset: 0x00 (R/W 16) NVM Control Register A */
       RoReg8                    Reserved1[0x2];
  __IO NVMCTRL_CTRLB_Type        CTRLB;       /**< \brief Offset: 0x04 (R/W 32) NVM Control Register B */
  __IO NVMCTRL_PARAM_Type        PARAM;       /**< \brief Offset: 0x08 (R/W 32) Parameter Register */
  __IO NVMCTRL_INTENCLR_Type     INTENCLR;    /**< \brief Offset: 0x0C (R/W  8) Interrupt Enable Clear Register */
       RoReg8                    Reserved2[0x3];
  __IO NVMCTRL_INTENSET_Type     INTENSET;    /**< \brief Offset: 0x10 (R/W  8) Interrupt Enable Set Register */
       RoReg8                    Reserved3[0x3];
  __IO NVMCTRL_INTFLAG_Type      INTFLAG;     /**< \brief Offset: 0x14 (R/W  8) Interrupt Flag Status and Clear Register */
       RoReg8                    Reserved4[0x3];
  __IO NVMCTRL_STATUS_Type       STATUS;      /**< \brief Offset: 0x18 (R/W 16) Status Register */
       RoReg8                    Reserved5[0x2];
  __IO NVMCTRL_ADDR_Type         ADDR;        /**< \brief Offset: 0x1C (R/W 32) Address Register */
  __IO NVMCTRL_LOCK_Type         LOCK;        /**< \brief Offset: 0x20 (R/W 16) Lock Register */
} Nvmctrl;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

/*@}*/

/* ************************************************************************** */
/**  SOFTWARE PERIPHERAL API DEFINITION FOR NON-VOLATILE FUSES */
/* ************************************************************************** */
/** \addtogroup fuses_api Peripheral Software API */
/*@{*/


#define ADC_FUSES_BIASCAL_ADDR      (NVMCTRL_OTP4 + 4)
#define ADC_FUSES_BIASCAL_Pos       3            /**< \brief (NVMCTRL_OTP4) ADC Bias Calibration */
#define ADC_FUSES_BIASCAL_Msk       (0x7u << ADC_FUSES_BIASCAL_Pos)
#define ADC_FUSES_BIASCAL(value)    ((ADC_FUSES_BIASCAL_Msk & ((value) << ADC_FUSES_BIASCAL_Pos)))

#define ADC_FUSES_BIAS_OPA_ADDR     (NVMCTRL_OTP2 + 4)
#define ADC_FUSES_BIAS_OPA_Pos      19           /**< \brief (NVMCTRL_OTP2) ADC OPA Bias */
#define ADC_FUSES_BIAS_OPA_Msk      (0x1u << ADC_FUSES_BIAS_OPA_Pos)

#define ADC_FUSES_BOOSTEN_ADDR      (NVMCTRL_OTP2 + 4)
#define ADC_FUSES_BOOSTEN_Pos       17           /**< \brief (NVMCTRL_OTP2) ADC Boost Enable */
#define ADC_FUSES_BOOSTEN_Msk       (0x1u << ADC_FUSES_BOOSTEN_Pos)

#define ADC_FUSES_CMPDELAY_ADDR     (NVMCTRL_OTP2 + 4)
#define ADC_FUSES_CMPDELAY_Pos      16           /**< \brief (NVMCTRL_OTP2) ADC Comparator Delay */
#define ADC_FUSES_CMPDELAY_Msk      (0x1u << ADC_FUSES_CMPDELAY_Pos)

#define ADC_FUSES_DCFG_ADDR         (NVMCTRL_OTP2 + 4)
#define ADC_FUSES_DCFG_Pos          16           /**< \brief (NVMCTRL_OTP2) ADC Device Configuration */
#define ADC_FUSES_DCFG_Msk          (0xFu << ADC_FUSES_DCFG_Pos)
#define ADC_FUSES_DCFG(value)       ((ADC_FUSES_DCFG_Msk & ((value) << ADC_FUSES_DCFG_Pos)))

#define ADC_FUSES_GAINCORR_ADDR     NVMCTRL_OTP4
#define ADC_FUSES_GAINCORR_Pos      3            /**< \brief (NVMCTRL_OTP4) ADC Gain Correction */
#define ADC_FUSES_GAINCORR_Msk      (0xFFFu << ADC_FUSES_GAINCORR_Pos)
#define ADC_FUSES_GAINCORR(value)   ((ADC_FUSES_GAINCORR_Msk & ((value) << ADC_FUSES_GAINCORR_Pos)))

#define ADC_FUSES_LINEARITY_0_ADDR  NVMCTRL_OTP4
#define ADC_FUSES_LINEARITY_0_Pos   27           /**< \brief (NVMCTRL_OTP4) ADC Linearity bits 4:0 */
#define ADC_FUSES_LINEARITY_0_Msk   (0x1Fu << ADC_FUSES_LINEARITY_0_Pos)
#define ADC_FUSES_LINEARITY_0(value) ((ADC_FUSES_LINEARITY_0_Msk & ((value) << ADC_FUSES_LINEARITY_0_Pos)))

#define ADC_FUSES_LINEARITY_1_ADDR  (NVMCTRL_OTP4 + 4)
#define ADC_FUSES_LINEARITY_1_Pos   0            /**< \brief (NVMCTRL_OTP4) ADC Linearity bits 7:5 */
#define ADC_FUSES_LINEARITY_1_Msk   (0x7u << ADC_FUSES_LINEARITY_1_Pos)
#define ADC_FUSES_LINEARITY_1(value) ((ADC_FUSES_LINEARITY_1_Msk & ((value) << ADC_FUSES_LINEARITY_1_Pos)))

#define ADC_FUSES_OFFSETCORR_ADDR   NVMCTRL_OTP4
#define ADC_FUSES_OFFSETCORR_Pos    15           /**< \brief (NVMCTRL_OTP4) ADC Offset Correction */
#define ADC_FUSES_OFFSETCORR_Msk    (0xFFFu << ADC_FUSES_OFFSETCORR_Pos)
#define ADC_FUSES_OFFSETCORR(value) ((ADC_FUSES_OFFSETCORR_Msk & ((value) << ADC_FUSES_OFFSETCORR_Pos)))

#define ADC_FUSES_VCMPULSE_ADDR     (NVMCTRL_OTP2 + 4)
#define ADC_FUSES_VCMPULSE_Pos      18           /**< \brief (NVMCTRL_OTP2) ADC VCM Pulse */
#define ADC_FUSES_VCMPULSE_Msk      (0x1u << ADC_FUSES_VCMPULSE_Pos)

#define DSU_FUSES_DCFG0_ADDR        NVMCTRL_OTP2
#define DSU_FUSES_DCFG0_Pos         0            /**< \brief (NVMCTRL_OTP2) Device Configuration 0 */
#define DSU_FUSES_DCFG0_Msk         (0xFFFFFFFFu << DSU_FUSES_DCFG0_Pos)
#define DSU_FUSES_DCFG0(value)      ((DSU_FUSES_DCFG0_Msk & ((value) << DSU_FUSES_DCFG0_Pos)))

#define DSU_FUSES_DCFG1_ADDR        (NVMCTRL_OTP2 + 4)
#define DSU_FUSES_DCFG1_Pos         0            /**< \brief (NVMCTRL_OTP2) Device Configuration 1 */
#define DSU_FUSES_DCFG1_Msk         (0xFFFFFFFFu << DSU_FUSES_DCFG1_Pos)
#define DSU_FUSES_DCFG1(value)      ((DSU_FUSES_DCFG1_Msk & ((value) << DSU_FUSES_DCFG1_Pos)))

#define DSU_FUSES_DEV_FAMILY_CFG_0_ADDR NVMCTRL_OTP2
#define DSU_FUSES_DEV_FAMILY_CFG_0_Pos 5            /**< \brief (NVMCTRL_OTP2) Device Family Configuration bits 26:0 */
#define DSU_FUSES_DEV_FAMILY_CFG_0_Msk (0x7FFFFFFu << DSU_FUSES_DEV_FAMILY_CFG_0_Pos)
#define DSU_FUSES_DEV_FAMILY_CFG_0(value) ((DSU_FUSES_DEV_FAMILY_CFG_0_Msk & ((value) << DSU_FUSES_DEV_FAMILY_CFG_0_Pos)))

#define DSU_FUSES_DEV_FAMILY_CFG_1_ADDR (NVMCTRL_OTP2 + 4)
#define DSU_FUSES_DEV_FAMILY_CFG_1_Pos 0            /**< \brief (NVMCTRL_OTP2) Device Family Configuration bits 42:27 */
#define DSU_FUSES_DEV_FAMILY_CFG_1_Msk (0xFFFFu << DSU_FUSES_DEV_FAMILY_CFG_1_Pos)
#define DSU_FUSES_DEV_FAMILY_CFG_1(value) ((DSU_FUSES_DEV_FAMILY_CFG_1_Msk & ((value) << DSU_FUSES_DEV_FAMILY_CFG_1_Pos)))

#define DSU_FUSES_DID_DEVSEL_ADDR   NVMCTRL_OTP2
#define DSU_FUSES_DID_DEVSEL_Pos    0            /**< \brief (NVMCTRL_OTP2) Device Number */
#define DSU_FUSES_DID_DEVSEL_Msk    (0x1Fu << DSU_FUSES_DID_DEVSEL_Pos)
#define DSU_FUSES_DID_DEVSEL(value) ((DSU_FUSES_DID_DEVSEL_Msk & ((value) << DSU_FUSES_DID_DEVSEL_Pos)))

#define DSU_FUSES_RAM_BIAS_ADDR     (NVMCTRL_OTP2 + 4)
#define DSU_FUSES_RAM_BIAS_Pos      20           /**< \brief (NVMCTRL_OTP2) RAM Bias */
#define DSU_FUSES_RAM_BIAS_Msk      (0x3u << DSU_FUSES_RAM_BIAS_Pos)
#define DSU_FUSES_RAM_BIAS(value)   ((DSU_FUSES_RAM_BIAS_Msk & ((value) << DSU_FUSES_RAM_BIAS_Pos)))

#define DSU_FUSES_RAM_READ_MARGIN_ADDR (NVMCTRL_OTP2 + 4)
#define DSU_FUSES_RAM_READ_MARGIN_Pos 22           /**< \brief (NVMCTRL_OTP2) RAM Read Margin */
#define DSU_FUSES_RAM_READ_MARGIN_Msk (0xFu << DSU_FUSES_RAM_READ_MARGIN_Pos)
#define DSU_FUSES_RAM_READ_MARGIN(value) ((DSU_FUSES_RAM_READ_MARGIN_Msk & ((value) << DSU_FUSES_RAM_READ_MARGIN_Pos)))

#define NVMCTRL_FUSES_BOOTPROT_ADDR NVMCTRL_USER
#define NVMCTRL_FUSES_BOOTPROT_Pos  0            /**< \brief (NVMCTRL_USER) Bootloader Size */
#define NVMCTRL_FUSES_BOOTPROT_Msk  (0x7u << NVMCTRL_FUSES_BOOTPROT_Pos)
#define NVMCTRL_FUSES_BOOTPROT(value) ((NVMCTRL_FUSES_BOOTPROT_Msk & ((value) << NVMCTRL_FUSES_BOOTPROT_Pos)))

#define NVMCTRL_FUSES_EEPROM_SIZE_ADDR NVMCTRL_USER
#define NVMCTRL_FUSES_EEPROM_SIZE_Pos 4            /**< \brief (NVMCTRL_USER) EEPROM Size */
#define NVMCTRL_FUSES_EEPROM_SIZE_Msk (0x7u << NVMCTRL_FUSES_EEPROM_SIZE_Pos)
#define NVMCTRL_FUSES_EEPROM_SIZE(value) ((NVMCTRL_FUSES_EEPROM_SIZE_Msk & ((value) << NVMCTRL_FUSES_EEPROM_SIZE_Pos)))

#define NVMCTRL_FUSES_LOCKFIELD_ADDR NVMCTRL_LOCKBIT
#define NVMCTRL_FUSES_LOCKFIELD_Pos 0            /**< \brief (NVMCTRL_LOCKBIT) LOCK Region */
#define NVMCTRL_FUSES_LOCKFIELD_Msk (0xFFu << NVMCTRL_FUSES_LOCKFIELD_Pos)
#define NVMCTRL_FUSES_LOCKFIELD(value) ((NVMCTRL_FUSES_LOCKFIELD_Msk & ((value) << NVMCTRL_FUSES_LOCKFIELD_Pos)))

#define NVMCTRL_FUSES_NVMP_ADDR     NVMCTRL_OTP1
#define NVMCTRL_FUSES_NVMP_Pos      16           /**< \brief (NVMCTRL_OTP1) Number of NVM Pages */
#define NVMCTRL_FUSES_NVMP_Msk      (0xFFFFu << NVMCTRL_FUSES_NVMP_Pos)
#define NVMCTRL_FUSES_NVMP(value)   ((NVMCTRL_FUSES_NVMP_Msk & ((value) << NVMCTRL_FUSES_NVMP_Pos)))

#define NVMCTRL_FUSES_NVM_LOCK_ADDR NVMCTRL_OTP1
#define NVMCTRL_FUSES_NVM_LOCK_Pos  0            /**< \brief (NVMCTRL_OTP1) NVM Lock */
#define NVMCTRL_FUSES_NVM_LOCK_Msk  (0xFFu << NVMCTRL_FUSES_NVM_LOCK_Pos)
#define NVMCTRL_FUSES_NVM_LOCK(value) ((NVMCTRL_FUSES_NVM_LOCK_Msk & ((value) << NVMCTRL_FUSES_NVM_LOCK_Pos)))

#define NVMCTRL_FUSES_PSZ_ADDR      NVMCTRL_OTP1
#define NVMCTRL_FUSES_PSZ_Pos       8            /**< \brief (NVMCTRL_OTP1) NVM Page Size */
#define NVMCTRL_FUSES_PSZ_Msk       (0xFu << NVMCTRL_FUSES_PSZ_Pos)
#define NVMCTRL_FUSES_PSZ(value)    ((NVMCTRL_FUSES_PSZ_Msk & ((value) << NVMCTRL_FUSES_PSZ_Pos)))

#define NVMCTRL_FUSES_REGION_LOCKS_ADDR (NVMCTRL_USER + 4)
#define NVMCTRL_FUSES_REGION_LOCKS_Pos 16           /**< \brief (NVMCTRL_USER) NVM Region Locks */
#define NVMCTRL_FUSES_REGION_LOCKS_Msk (0xFFFFu << NVMCTRL_FUSES_REGION_LOCKS_Pos)
#define NVMCTRL_FUSES_REGION_LOCKS(value) ((NVMCTRL_FUSES_REGION_LOCKS_Msk & ((value) << NVMCTRL_FUSES_REGION_LOCKS_Pos)))

#define SYSCTRL_FUSES_OSC32KCAL_ADDR   (NVMCTRL_OTP4 + 4)
#define SYSCTRL_FUSES_OSC32KCAL_Pos    6            /**< \brief (NVMCTRL_OTP4) OSC32K Calibration */
#define SYSCTRL_FUSES_OSC32KCAL_Msk    (0x7Fu << SYSCTRL_FUSES_OSC32KCAL_Pos)
#define SYSCTRL_FUSES_OSC32KCAL(value) ((SYSCTRL_FUSES_OSC32KCAL_Msk & ((value) << SYSCTRL_FUSES_OSC32KCAL_Pos)))

#define SYSCTRL_FUSES_BOD12USERLEVEL_ADDR NVMCTRL_USER
#define SYSCTRL_FUSES_BOD12USERLEVEL_Pos 17           /**< \brief (NVMCTRL_USER) BOD12 User Level */
#define SYSCTRL_FUSES_BOD12USERLEVEL_Msk (0x1Fu << SYSCTRL_FUSES_BOD12USERLEVEL_Pos)
#define SYSCTRL_FUSES_BOD12USERLEVEL(value) ((SYSCTRL_FUSES_BOD12USERLEVEL_Msk & ((value) << SYSCTRL_FUSES_BOD12USERLEVEL_Pos)))

#define SYSCTRL_FUSES_BOD12_ACTION_ADDR NVMCTRL_USER
#define SYSCTRL_FUSES_BOD12_ACTION_Pos 23           /**< \brief (NVMCTRL_USER) BOD12 Action */
#define SYSCTRL_FUSES_BOD12_ACTION_Msk (0x3u << SYSCTRL_FUSES_BOD12_ACTION_Pos)
#define SYSCTRL_FUSES_BOD12_ACTION(value) ((SYSCTRL_FUSES_BOD12_ACTION_Msk & ((value) << SYSCTRL_FUSES_BOD12_ACTION_Pos)))

#define SYSCTRL_FUSES_BOD12_EN_ADDR NVMCTRL_USER
#define SYSCTRL_FUSES_BOD12_EN_Pos  22           /**< \brief (NVMCTRL_USER) BOD12 Enable */
#define SYSCTRL_FUSES_BOD12_EN_Msk  (0x1u << SYSCTRL_FUSES_BOD12_EN_Pos)

#define SYSCTRL_FUSES_BOD33USERLEVEL_ADDR NVMCTRL_USER
#define SYSCTRL_FUSES_BOD33USERLEVEL_Pos 8            /**< \brief (NVMCTRL_USER) BOD33 User Level */
#define SYSCTRL_FUSES_BOD33USERLEVEL_Msk (0x3Fu << SYSCTRL_FUSES_BOD33USERLEVEL_Pos)
#define SYSCTRL_FUSES_BOD33USERLEVEL(value) ((SYSCTRL_FUSES_BOD33USERLEVEL_Msk & ((value) << SYSCTRL_FUSES_BOD33USERLEVEL_Pos)))

#define SYSCTRL_FUSES_BOD33_ACTION_ADDR NVMCTRL_USER
#define SYSCTRL_FUSES_BOD33_ACTION_Pos 15           /**< \brief (NVMCTRL_USER) BOD33 Action */
#define SYSCTRL_FUSES_BOD33_ACTION_Msk (0x3u << SYSCTRL_FUSES_BOD33_ACTION_Pos)
#define SYSCTRL_FUSES_BOD33_ACTION(value) ((SYSCTRL_FUSES_BOD33_ACTION_Msk & ((value) << SYSCTRL_FUSES_BOD33_ACTION_Pos)))

#define SYSCTRL_FUSES_BOD33_EN_ADDR NVMCTRL_USER
#define SYSCTRL_FUSES_BOD33_EN_Pos  14           /**< \brief (NVMCTRL_USER) BOD33 Enable */
#define SYSCTRL_FUSES_BOD33_EN_Msk  (0x1u << SYSCTRL_FUSES_BOD33_EN_Pos)

#define SYSCTRL_FUSES_ULPVREG_ADDR  NVMCTRL_OTP4
#define SYSCTRL_FUSES_ULPVREG_Pos   0            /**< \brief (NVMCTRL_OTP4) ULP Regulator Fallback Mode */
#define SYSCTRL_FUSES_ULPVREG_Msk   (0x7u << SYSCTRL_FUSES_ULPVREG_Pos)
#define SYSCTRL_FUSES_ULPVREG(value) ((SYSCTRL_FUSES_ULPVREG_Msk & ((value) << SYSCTRL_FUSES_ULPVREG_Pos)))

#define WDT_FUSES_ALWAYSON_ADDR     NVMCTRL_USER
#define WDT_FUSES_ALWAYSON_Pos      26           /**< \brief (NVMCTRL_USER) WDT Always On */
#define WDT_FUSES_ALWAYSON_Msk      (0x1u << WDT_FUSES_ALWAYSON_Pos)

#define WDT_FUSES_ENABLE_ADDR       NVMCTRL_USER
#define WDT_FUSES_ENABLE_Pos        25           /**< \brief (NVMCTRL_USER) WDT Enable */
#define WDT_FUSES_ENABLE_Msk        (0x1u << WDT_FUSES_ENABLE_Pos)

#define WDT_FUSES_EWOFFSET_ADDR     (NVMCTRL_USER + 4)
#define WDT_FUSES_EWOFFSET_Pos      3            /**< \brief (NVMCTRL_USER) WDT Early Warning Offset */
#define WDT_FUSES_EWOFFSET_Msk      (0xFu << WDT_FUSES_EWOFFSET_Pos)
#define WDT_FUSES_EWOFFSET(value)   ((WDT_FUSES_EWOFFSET_Msk & ((value) << WDT_FUSES_EWOFFSET_Pos)))

#define WDT_FUSES_PER_ADDR          NVMCTRL_USER
#define WDT_FUSES_PER_Pos           27           /**< \brief (NVMCTRL_USER) WDT Period */
#define WDT_FUSES_PER_Msk           (0xFu << WDT_FUSES_PER_Pos)
#define WDT_FUSES_PER(value)        ((WDT_FUSES_PER_Msk & ((value) << WDT_FUSES_PER_Pos)))

#define WDT_FUSES_WEN_ADDR          (NVMCTRL_USER + 4)
#define WDT_FUSES_WEN_Pos           7            /**< \brief (NVMCTRL_USER) WDT Window Mode Enable */
#define WDT_FUSES_WEN_Msk           (0x1u << WDT_FUSES_WEN_Pos)

#define WDT_FUSES_WINDOW_0_ADDR     NVMCTRL_USER
#define WDT_FUSES_WINDOW_0_Pos      31           /**< \brief (NVMCTRL_USER) WDT Window bit 0 */
#define WDT_FUSES_WINDOW_0_Msk      (0x1u << WDT_FUSES_WINDOW_0_Pos)

#define WDT_FUSES_WINDOW_1_ADDR     (NVMCTRL_USER + 4)
#define WDT_FUSES_WINDOW_1_Pos      0            /**< \brief (NVMCTRL_USER) WDT Window bits 3:1 */
#define WDT_FUSES_WINDOW_1_Msk      (0x7u << WDT_FUSES_WINDOW_1_Pos)
#define WDT_FUSES_WINDOW_1(value)   ((WDT_FUSES_WINDOW_1_Msk & ((value) << WDT_FUSES_WINDOW_1_Pos)))

/*@}*/

#endif /* _SAMD20_NVMCTRL_COMPONENT_ */
