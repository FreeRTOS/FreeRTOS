/**
 * \file
 *
 * \brief Component description for DSU
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

#ifndef _SAMD20_DSU_COMPONENT_
#define _SAMD20_DSU_COMPONENT_

/* ========================================================================== */
/**  SOFTWARE API DEFINITION FOR DSU */
/* ========================================================================== */
/** \addtogroup SAMD20_DSU Device Service Unit */
/*@{*/

#define REV_DSU                     0x101

/* -------- DSU_CTRL : (DSU Offset: 0x0000) ( /W  8) Control Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  SWRST:1;          /*!< bit:      0  Software Reset                     */
    uint8_t  :1;               /*!< bit:      1  Reserved                           */
    uint8_t  CRC:1;            /*!< bit:      2  Cyclic Redundancy Check            */
    uint8_t  MBIST:1;          /*!< bit:      3  Memory BIST                        */
    uint8_t  CE:1;             /*!< bit:      4  Chip Erase                         */
    uint8_t  :1;               /*!< bit:      5  Reserved                           */
    uint8_t  ARR:1;            /*!< bit:      6  Auxiliary Row Read                 */
    uint8_t  SMSA:1;           /*!< bit:      7  Start Memory Stream Access         */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} DSU_CTRL_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define DSU_CTRL_OFFSET             0x0000       /**< \brief (DSU_CTRL offset) Control Register */

#define DSU_CTRL_SWRST_Pos          0            /**< \brief (DSU_CTRL) Software Reset */
#define DSU_CTRL_SWRST              (0x1u << DSU_CTRL_SWRST_Pos)
#define DSU_CTRL_CRC_Pos            2            /**< \brief (DSU_CTRL) Cyclic Redundancy Check */
#define DSU_CTRL_CRC                (0x1u << DSU_CTRL_CRC_Pos)
#define DSU_CTRL_MBIST_Pos          3            /**< \brief (DSU_CTRL) Memory BIST */
#define DSU_CTRL_MBIST              (0x1u << DSU_CTRL_MBIST_Pos)
#define DSU_CTRL_CE_Pos             4            /**< \brief (DSU_CTRL) Chip Erase */
#define DSU_CTRL_CE                 (0x1u << DSU_CTRL_CE_Pos)
#define DSU_CTRL_ARR_Pos            6            /**< \brief (DSU_CTRL) Auxiliary Row Read */
#define DSU_CTRL_ARR                (0x1u << DSU_CTRL_ARR_Pos)
#define DSU_CTRL_SMSA_Pos           7            /**< \brief (DSU_CTRL) Start Memory Stream Access */
#define DSU_CTRL_SMSA               (0x1u << DSU_CTRL_SMSA_Pos)
#define DSU_CTRL_MASK               0xDDu        /**< \brief (DSU_CTRL) MASK Register */

/* -------- DSU_STATUSA : (DSU Offset: 0x0001) (R/W  8) Status Register A -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  DONE:1;           /*!< bit:      0  Done                               */
    uint8_t  CRSTEXT:1;        /*!< bit:      1  CPU Reset Phase Extension          */
    uint8_t  BERR:1;           /*!< bit:      2  Bus Error                          */
    uint8_t  FAIL:1;           /*!< bit:      3  Failure                            */
    uint8_t  PERR:1;           /*!< bit:      4  Protection Error                   */
    uint8_t  :3;               /*!< bit:  5.. 7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} DSU_STATUSA_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define DSU_STATUSA_OFFSET          0x0001       /**< \brief (DSU_STATUSA offset) Status Register A */

#define DSU_STATUSA_DONE_Pos        0            /**< \brief (DSU_STATUSA) Done */
#define DSU_STATUSA_DONE            (0x1u << DSU_STATUSA_DONE_Pos)
#define DSU_STATUSA_CRSTEXT_Pos     1            /**< \brief (DSU_STATUSA) CPU Reset Phase Extension */
#define DSU_STATUSA_CRSTEXT         (0x1u << DSU_STATUSA_CRSTEXT_Pos)
#define DSU_STATUSA_BERR_Pos        2            /**< \brief (DSU_STATUSA) Bus Error */
#define DSU_STATUSA_BERR            (0x1u << DSU_STATUSA_BERR_Pos)
#define DSU_STATUSA_FAIL_Pos        3            /**< \brief (DSU_STATUSA) Failure */
#define DSU_STATUSA_FAIL            (0x1u << DSU_STATUSA_FAIL_Pos)
#define DSU_STATUSA_PERR_Pos        4            /**< \brief (DSU_STATUSA) Protection Error */
#define DSU_STATUSA_PERR            (0x1u << DSU_STATUSA_PERR_Pos)
#define DSU_STATUSA_MASK            0x1Fu        /**< \brief (DSU_STATUSA) MASK Register */

/* -------- DSU_STATUSB : (DSU Offset: 0x0002) (R/   8) Status Register B -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint8_t  PROT:1;           /*!< bit:      0  Protected                          */
    uint8_t  DBGPRES:1;        /*!< bit:      1  Debugger Present                   */
    uint8_t  DCCD:2;           /*!< bit:  2.. 3  Debug Communication Channel Dirty  */
    uint8_t  HPE:1;            /*!< bit:      4  Hot-Plugging Enable                */
    uint8_t  :3;               /*!< bit:  5.. 7  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint8_t reg;                 /*!< Type      used for register access              */
} DSU_STATUSB_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define DSU_STATUSB_OFFSET          0x0002       /**< \brief (DSU_STATUSB offset) Status Register B */
#define DSU_STATUSB_RESETVALUE      0x00         /**< \brief (DSU_STATUSB reset_value) Status Register B */

#define DSU_STATUSB_PROT_Pos        0            /**< \brief (DSU_STATUSB) Protected */
#define DSU_STATUSB_PROT            (0x1u << DSU_STATUSB_PROT_Pos)
#define DSU_STATUSB_DBGPRES_Pos     1            /**< \brief (DSU_STATUSB) Debugger Present */
#define DSU_STATUSB_DBGPRES         (0x1u << DSU_STATUSB_DBGPRES_Pos)
#define DSU_STATUSB_DCCD_Pos        2            /**< \brief (DSU_STATUSB) Debug Communication Channel Dirty */
#define DSU_STATUSB_DCCD_Msk        (0x3u << DSU_STATUSB_DCCD_Pos)
#define DSU_STATUSB_DCCD(value)     ((DSU_STATUSB_DCCD_Msk & ((value) << DSU_STATUSB_DCCD_Pos)))
#define DSU_STATUSB_HPE_Pos         4            /**< \brief (DSU_STATUSB) Hot-Plugging Enable */
#define DSU_STATUSB_HPE             (0x1u << DSU_STATUSB_HPE_Pos)
#define DSU_STATUSB_MASK            0x1Fu        /**< \brief (DSU_STATUSB) MASK Register */

/* -------- DSU_ADDR : (DSU Offset: 0x0004) (R/W 32) Address Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t AMOD:2;           /*!< bit:  0.. 1  Access Mode                        */
    uint32_t ADDR:30;          /*!< bit:  2..31  Address                            */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} DSU_ADDR_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define DSU_ADDR_OFFSET             0x0004       /**< \brief (DSU_ADDR offset) Address Register */
#define DSU_ADDR_RESETVALUE         0x00000000   /**< \brief (DSU_ADDR reset_value) Address Register */

#define DSU_ADDR_AMOD_Pos           0            /**< \brief (DSU_ADDR) Access Mode */
#define DSU_ADDR_AMOD_Msk           (0x3u << DSU_ADDR_AMOD_Pos)
#define DSU_ADDR_AMOD(value)        ((DSU_ADDR_AMOD_Msk & ((value) << DSU_ADDR_AMOD_Pos)))
#define DSU_ADDR_ADDR_Pos           2            /**< \brief (DSU_ADDR) Address */
#define DSU_ADDR_ADDR_Msk           (0x3FFFFFFFu << DSU_ADDR_ADDR_Pos)
#define DSU_ADDR_ADDR(value)        ((DSU_ADDR_ADDR_Msk & ((value) << DSU_ADDR_ADDR_Pos)))
#define DSU_ADDR_MASK               0xFFFFFFFFu  /**< \brief (DSU_ADDR) MASK Register */

/* -------- DSU_LENGTH : (DSU Offset: 0x0008) (R/W 32) Length Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t :2;               /*!< bit:  0.. 1  Reserved                           */
    uint32_t LENGTH:30;        /*!< bit:  2..31  Length                             */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} DSU_LENGTH_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define DSU_LENGTH_OFFSET           0x0008       /**< \brief (DSU_LENGTH offset) Length Register */
#define DSU_LENGTH_RESETVALUE       0x00000000   /**< \brief (DSU_LENGTH reset_value) Length Register */

#define DSU_LENGTH_LENGTH_Pos       2            /**< \brief (DSU_LENGTH) Length */
#define DSU_LENGTH_LENGTH_Msk       (0x3FFFFFFFu << DSU_LENGTH_LENGTH_Pos)
#define DSU_LENGTH_LENGTH(value)    ((DSU_LENGTH_LENGTH_Msk & ((value) << DSU_LENGTH_LENGTH_Pos)))
#define DSU_LENGTH_MASK             0xFFFFFFFCu  /**< \brief (DSU_LENGTH) MASK Register */

/* -------- DSU_DATA : (DSU Offset: 0x000C) (R/W 32) Data Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t DATA:32;          /*!< bit:  0..31  Data                               */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} DSU_DATA_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define DSU_DATA_OFFSET             0x000C       /**< \brief (DSU_DATA offset) Data Register */

#define DSU_DATA_DATA_Pos           0            /**< \brief (DSU_DATA) Data */
#define DSU_DATA_DATA_Msk           (0xFFFFFFFFu << DSU_DATA_DATA_Pos)
#define DSU_DATA_DATA(value)        ((DSU_DATA_DATA_Msk & ((value) << DSU_DATA_DATA_Pos)))
#define DSU_DATA_MASK               0xFFFFFFFFu  /**< \brief (DSU_DATA) MASK Register */

/* -------- DSU_DCC : (DSU Offset: 0x0010) (R/W 32) Debug Communication Channel Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t DATA:32;          /*!< bit:  0..31  Data                               */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} DSU_DCC_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define DSU_DCC_OFFSET              0x0010       /**< \brief (DSU_DCC offset) Debug Communication Channel Register */
#define DSU_DCC_RESETVALUE          0x00000000   /**< \brief (DSU_DCC reset_value) Debug Communication Channel Register */

#define DSU_DCC_DATA_Pos            0            /**< \brief (DSU_DCC) Data */
#define DSU_DCC_DATA_Msk            (0xFFFFFFFFu << DSU_DCC_DATA_Pos)
#define DSU_DCC_DATA(value)         ((DSU_DCC_DATA_Msk & ((value) << DSU_DCC_DATA_Pos)))
#define DSU_DCC_MASK                0xFFFFFFFFu  /**< \brief (DSU_DCC) MASK Register */

/* -------- DSU_DID : (DSU Offset: 0x0018) (R/  32) Device Identification Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t DEVSEL:8;         /*!< bit:  0.. 7  Device Select                      */
    uint32_t REVISION:4;       /*!< bit:  8..11  Revision Number                    */
    uint32_t DIE:4;            /*!< bit: 12..15  Die Number                         */
    uint32_t SUBFAMILY:8;      /*!< bit: 16..23  Sub-Family                         */
    uint32_t FAMILY:4;         /*!< bit: 24..27  Family                             */
    uint32_t PROCESSOR:4;      /*!< bit: 28..31  Processor                          */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} DSU_DID_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define DSU_DID_OFFSET              0x0018       /**< \brief (DSU_DID offset) Device Identification Register */
#define DSU_DID_RESETVALUE          0x00000000   /**< \brief (DSU_DID reset_value) Device Identification Register */

#define DSU_DID_DEVSEL_Pos          0            /**< \brief (DSU_DID) Device Select */
#define DSU_DID_DEVSEL_Msk          (0xFFu << DSU_DID_DEVSEL_Pos)
#define DSU_DID_DEVSEL(value)       ((DSU_DID_DEVSEL_Msk & ((value) << DSU_DID_DEVSEL_Pos)))
#define DSU_DID_REVISION_Pos        8            /**< \brief (DSU_DID) Revision Number */
#define DSU_DID_REVISION_Msk        (0xFu << DSU_DID_REVISION_Pos)
#define DSU_DID_REVISION(value)     ((DSU_DID_REVISION_Msk & ((value) << DSU_DID_REVISION_Pos)))
#define DSU_DID_DIE_Pos             12           /**< \brief (DSU_DID) Die Number */
#define DSU_DID_DIE_Msk             (0xFu << DSU_DID_DIE_Pos)
#define DSU_DID_DIE(value)          ((DSU_DID_DIE_Msk & ((value) << DSU_DID_DIE_Pos)))
#define DSU_DID_SUBFAMILY_Pos       16           /**< \brief (DSU_DID) Sub-Family */
#define DSU_DID_SUBFAMILY_Msk       (0xFFu << DSU_DID_SUBFAMILY_Pos)
#define DSU_DID_SUBFAMILY(value)    ((DSU_DID_SUBFAMILY_Msk & ((value) << DSU_DID_SUBFAMILY_Pos)))
#define DSU_DID_FAMILY_Pos          24           /**< \brief (DSU_DID) Family */
#define DSU_DID_FAMILY_Msk          (0xFu << DSU_DID_FAMILY_Pos)
#define DSU_DID_FAMILY(value)       ((DSU_DID_FAMILY_Msk & ((value) << DSU_DID_FAMILY_Pos)))
#define DSU_DID_PROCESSOR_Pos       28           /**< \brief (DSU_DID) Processor */
#define DSU_DID_PROCESSOR_Msk       (0xFu << DSU_DID_PROCESSOR_Pos)
#define DSU_DID_PROCESSOR(value)    ((DSU_DID_PROCESSOR_Msk & ((value) << DSU_DID_PROCESSOR_Pos)))
#define DSU_DID_MASK                0xFFFFFFFFu  /**< \brief (DSU_DID) MASK Register */

/* -------- DSU_DCFG : (DSU Offset: 0x00F0) (R/W 32) Device Configuration Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t DCFG:32;          /*!< bit:  0..31  Device Configuration               */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} DSU_DCFG_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define DSU_DCFG_OFFSET             0x00F0       /**< \brief (DSU_DCFG offset) Device Configuration Register */
#define DSU_DCFG_RESETVALUE         0x00000000   /**< \brief (DSU_DCFG reset_value) Device Configuration Register */

#define DSU_DCFG_DCFG_Pos           0            /**< \brief (DSU_DCFG) Device Configuration */
#define DSU_DCFG_DCFG_Msk           (0xFFFFFFFFu << DSU_DCFG_DCFG_Pos)
#define DSU_DCFG_DCFG(value)        ((DSU_DCFG_DCFG_Msk & ((value) << DSU_DCFG_DCFG_Pos)))
#define DSU_DCFG_MASK               0xFFFFFFFFu  /**< \brief (DSU_DCFG) MASK Register */

/* -------- DSU_UPTM : (DSU Offset: 0x00F8) (R/W 32) UnProtected Test Mode Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t UPTM:32;          /*!< bit:  0..31  Un-Protected Test Mode             */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} DSU_UPTM_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define DSU_UPTM_OFFSET             0x00F8       /**< \brief (DSU_UPTM offset) UnProtected Test Mode Register */
#define DSU_UPTM_RESETVALUE         0x00000000   /**< \brief (DSU_UPTM reset_value) UnProtected Test Mode Register */

#define DSU_UPTM_UPTM_Pos           0            /**< \brief (DSU_UPTM) Un-Protected Test Mode */
#define DSU_UPTM_UPTM_Msk           (0xFFFFFFFFu << DSU_UPTM_UPTM_Pos)
#define DSU_UPTM_UPTM(value)        ((DSU_UPTM_UPTM_Msk & ((value) << DSU_UPTM_UPTM_Pos)))
#define DSU_UPTM_MASK               0xFFFFFFFFu  /**< \brief (DSU_UPTM) MASK Register */

/* -------- DSU_TESTMODE : (DSU Offset: 0x00FC) (R/W 32) Test Mode Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t TESTMODE:32;      /*!< bit:  0..31  Test Mode                          */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} DSU_TESTMODE_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define DSU_TESTMODE_OFFSET         0x00FC       /**< \brief (DSU_TESTMODE offset) Test Mode Register */
#define DSU_TESTMODE_RESETVALUE     0x00000000   /**< \brief (DSU_TESTMODE reset_value) Test Mode Register */

#define DSU_TESTMODE_TESTMODE_Pos   0            /**< \brief (DSU_TESTMODE) Test Mode */
#define DSU_TESTMODE_TESTMODE_Msk   (0xFFFFFFFFu << DSU_TESTMODE_TESTMODE_Pos)
#define DSU_TESTMODE_TESTMODE(value) ((DSU_TESTMODE_TESTMODE_Msk & ((value) << DSU_TESTMODE_TESTMODE_Pos)))
#define DSU_TESTMODE_MASK           0xFFFFFFFFu  /**< \brief (DSU_TESTMODE) MASK Register */

/* -------- DSU_ENTRY : (DSU Offset: 0x1000) (R/  32) CoreSight ROM Table Entry Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t EPRES:1;          /*!< bit:      0  Entry Present                      */
    uint32_t FMT:1;            /*!< bit:      1  Format                             */
    uint32_t :10;              /*!< bit:  2..11  Reserved                           */
    uint32_t ADDOFF:20;        /*!< bit: 12..31  Address Offset                     */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} DSU_ENTRY_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define DSU_ENTRY_OFFSET            0x1000       /**< \brief (DSU_ENTRY offset) CoreSight ROM Table Entry Register */

#define DSU_ENTRY_EPRES_Pos         0            /**< \brief (DSU_ENTRY) Entry Present */
#define DSU_ENTRY_EPRES             (0x1u << DSU_ENTRY_EPRES_Pos)
#define DSU_ENTRY_FMT_Pos           1            /**< \brief (DSU_ENTRY) Format */
#define DSU_ENTRY_FMT               (0x1u << DSU_ENTRY_FMT_Pos)
#define DSU_ENTRY_ADDOFF_Pos        12           /**< \brief (DSU_ENTRY) Address Offset */
#define DSU_ENTRY_ADDOFF_Msk        (0xFFFFFu << DSU_ENTRY_ADDOFF_Pos)
#define DSU_ENTRY_ADDOFF(value)     ((DSU_ENTRY_ADDOFF_Msk & ((value) << DSU_ENTRY_ADDOFF_Pos)))
#define DSU_ENTRY_MASK              0xFFFFF003u  /**< \brief (DSU_ENTRY) MASK Register */

/* -------- DSU_END : (DSU Offset: 0x1008) (R/  32) CoreSight ROM Table End Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t END:32;           /*!< bit:  0..31  End Marker                         */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} DSU_END_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define DSU_END_OFFSET              0x1008       /**< \brief (DSU_END offset) CoreSight ROM Table End Register */
#define DSU_END_RESETVALUE          0x00000000   /**< \brief (DSU_END reset_value) CoreSight ROM Table End Register */

#define DSU_END_END_Pos             0            /**< \brief (DSU_END) End Marker */
#define DSU_END_END_Msk             (0xFFFFFFFFu << DSU_END_END_Pos)
#define DSU_END_END(value)          ((DSU_END_END_Msk & ((value) << DSU_END_END_Pos)))
#define DSU_END_MASK                0xFFFFFFFFu  /**< \brief (DSU_END) MASK Register */

/* -------- DSU_MEMTYPE : (DSU Offset: 0x1FCC) (R/  32) CoreSight ROM Table Memory Type Register -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t SMEMP:1;          /*!< bit:      0  System Memory Present              */
    uint32_t :31;              /*!< bit:  1..31  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} DSU_MEMTYPE_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define DSU_MEMTYPE_OFFSET          0x1FCC       /**< \brief (DSU_MEMTYPE offset) CoreSight ROM Table Memory Type Register */

#define DSU_MEMTYPE_SMEMP_Pos       0            /**< \brief (DSU_MEMTYPE) System Memory Present */
#define DSU_MEMTYPE_SMEMP           (0x1u << DSU_MEMTYPE_SMEMP_Pos)
#define DSU_MEMTYPE_MASK            0x00000001u  /**< \brief (DSU_MEMTYPE) MASK Register */

/* -------- DSU_PID4 : (DSU Offset: 0x1FD0) (R/  32) Peripheral Identification Register 4 -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t JEPCC:4;          /*!< bit:  0.. 3  JEP-106 Continuation Code          */
    uint32_t FKBC:4;           /*!< bit:  4.. 7  4kB Count                          */
    uint32_t :24;              /*!< bit:  8..31  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} DSU_PID4_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define DSU_PID4_OFFSET             0x1FD0       /**< \brief (DSU_PID4 offset) Peripheral Identification Register 4 */

#define DSU_PID4_JEPCC_Pos          0            /**< \brief (DSU_PID4) JEP-106 Continuation Code */
#define DSU_PID4_JEPCC_Msk          (0xFu << DSU_PID4_JEPCC_Pos)
#define DSU_PID4_JEPCC(value)       ((DSU_PID4_JEPCC_Msk & ((value) << DSU_PID4_JEPCC_Pos)))
#define DSU_PID4_FKBC_Pos           4            /**< \brief (DSU_PID4) 4kB Count */
#define DSU_PID4_FKBC_Msk           (0xFu << DSU_PID4_FKBC_Pos)
#define DSU_PID4_FKBC(value)        ((DSU_PID4_FKBC_Msk & ((value) << DSU_PID4_FKBC_Pos)))
#define DSU_PID4_MASK               0x000000FFu  /**< \brief (DSU_PID4) MASK Register */

/* -------- DSU_PID5 : (DSU Offset: 0x1FD4) (R/  32) Peripheral Identification Register 5 -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  uint32_t reg;                /*!< Type      used for register access              */
} DSU_PID5_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define DSU_PID5_OFFSET             0x1FD4       /**< \brief (DSU_PID5 offset) Peripheral Identification Register 5 */
#define DSU_PID5_MASK               0x00000000u  /**< \brief (DSU_PID5) MASK Register */

/* -------- DSU_PID6 : (DSU Offset: 0x1FD8) (R/  32) Peripheral Identification Register 6 -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  uint32_t reg;                /*!< Type      used for register access              */
} DSU_PID6_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define DSU_PID6_OFFSET             0x1FD8       /**< \brief (DSU_PID6 offset) Peripheral Identification Register 6 */
#define DSU_PID6_MASK               0x00000000u  /**< \brief (DSU_PID6) MASK Register */

/* -------- DSU_PID7 : (DSU Offset: 0x1FDC) (R/  32) Peripheral Identification Register 7 -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  uint32_t reg;                /*!< Type      used for register access              */
} DSU_PID7_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define DSU_PID7_OFFSET             0x1FDC       /**< \brief (DSU_PID7 offset) Peripheral Identification Register 7 */
#define DSU_PID7_MASK               0x00000000u  /**< \brief (DSU_PID7) MASK Register */

/* -------- DSU_PID0 : (DSU Offset: 0x1FE0) (R/  32) Peripheral Identification Register 0 -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t PARTNBL:8;        /*!< bit:  0.. 7  Part Number Low                    */
    uint32_t :24;              /*!< bit:  8..31  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} DSU_PID0_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define DSU_PID0_OFFSET             0x1FE0       /**< \brief (DSU_PID0 offset) Peripheral Identification Register 0 */

#define DSU_PID0_PARTNBL_Pos        0            /**< \brief (DSU_PID0) Part Number Low */
#define DSU_PID0_PARTNBL_Msk        (0xFFu << DSU_PID0_PARTNBL_Pos)
#define DSU_PID0_PARTNBL(value)     ((DSU_PID0_PARTNBL_Msk & ((value) << DSU_PID0_PARTNBL_Pos)))
#define DSU_PID0_MASK               0x000000FFu  /**< \brief (DSU_PID0) MASK Register */

/* -------- DSU_PID1 : (DSU Offset: 0x1FE4) (R/  32) Peripheral Identification Register 1 -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t PARTNBH:4;        /*!< bit:  0.. 3  Part Number High                   */
    uint32_t JEPIDCL:4;        /*!< bit:  4.. 7  JEP-106 Identity Code Low          */
    uint32_t :24;              /*!< bit:  8..31  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} DSU_PID1_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define DSU_PID1_OFFSET             0x1FE4       /**< \brief (DSU_PID1 offset) Peripheral Identification Register 1 */

#define DSU_PID1_PARTNBH_Pos        0            /**< \brief (DSU_PID1) Part Number High */
#define DSU_PID1_PARTNBH_Msk        (0xFu << DSU_PID1_PARTNBH_Pos)
#define DSU_PID1_PARTNBH(value)     ((DSU_PID1_PARTNBH_Msk & ((value) << DSU_PID1_PARTNBH_Pos)))
#define DSU_PID1_JEPIDCL_Pos        4            /**< \brief (DSU_PID1) JEP-106 Identity Code Low */
#define DSU_PID1_JEPIDCL_Msk        (0xFu << DSU_PID1_JEPIDCL_Pos)
#define DSU_PID1_JEPIDCL(value)     ((DSU_PID1_JEPIDCL_Msk & ((value) << DSU_PID1_JEPIDCL_Pos)))
#define DSU_PID1_MASK               0x000000FFu  /**< \brief (DSU_PID1) MASK Register */

/* -------- DSU_PID2 : (DSU Offset: 0x1FE8) (R/  32) Peripheral Identification Register 2 -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t JEPIDCH:3;        /*!< bit:  0.. 2  JEP-106 Identity Code High         */
    uint32_t JEPU:1;           /*!< bit:      3  JEP-106 Identity Code is Used      */
    uint32_t REVISION:4;       /*!< bit:  4.. 7  Revision Number                    */
    uint32_t :24;              /*!< bit:  8..31  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} DSU_PID2_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define DSU_PID2_OFFSET             0x1FE8       /**< \brief (DSU_PID2 offset) Peripheral Identification Register 2 */

#define DSU_PID2_JEPIDCH_Pos        0            /**< \brief (DSU_PID2) JEP-106 Identity Code High */
#define DSU_PID2_JEPIDCH_Msk        (0x7u << DSU_PID2_JEPIDCH_Pos)
#define DSU_PID2_JEPIDCH(value)     ((DSU_PID2_JEPIDCH_Msk & ((value) << DSU_PID2_JEPIDCH_Pos)))
#define DSU_PID2_JEPU_Pos           3            /**< \brief (DSU_PID2) JEP-106 Identity Code is Used */
#define DSU_PID2_JEPU               (0x1u << DSU_PID2_JEPU_Pos)
#define DSU_PID2_REVISION_Pos       4            /**< \brief (DSU_PID2) Revision Number */
#define DSU_PID2_REVISION_Msk       (0xFu << DSU_PID2_REVISION_Pos)
#define DSU_PID2_REVISION(value)    ((DSU_PID2_REVISION_Msk & ((value) << DSU_PID2_REVISION_Pos)))
#define DSU_PID2_MASK               0x000000FFu  /**< \brief (DSU_PID2) MASK Register */

/* -------- DSU_PID3 : (DSU Offset: 0x1FEC) (R/  32) Peripheral Identification Register 3 -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t CUSMOD:4;         /*!< bit:  0.. 3  Customer Mode                      */
    uint32_t REVAND:4;         /*!< bit:  4.. 7  Revision Number                    */
    uint32_t :24;              /*!< bit:  8..31  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} DSU_PID3_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define DSU_PID3_OFFSET             0x1FEC       /**< \brief (DSU_PID3 offset) Peripheral Identification Register 3 */

#define DSU_PID3_CUSMOD_Pos         0            /**< \brief (DSU_PID3) Customer Mode */
#define DSU_PID3_CUSMOD_Msk         (0xFu << DSU_PID3_CUSMOD_Pos)
#define DSU_PID3_CUSMOD(value)      ((DSU_PID3_CUSMOD_Msk & ((value) << DSU_PID3_CUSMOD_Pos)))
#define DSU_PID3_REVAND_Pos         4            /**< \brief (DSU_PID3) Revision Number */
#define DSU_PID3_REVAND_Msk         (0xFu << DSU_PID3_REVAND_Pos)
#define DSU_PID3_REVAND(value)      ((DSU_PID3_REVAND_Msk & ((value) << DSU_PID3_REVAND_Pos)))
#define DSU_PID3_MASK               0x000000FFu  /**< \brief (DSU_PID3) MASK Register */

/* -------- DSU_CID0 : (DSU Offset: 0x1FF0) (R/  32) Component Identification Register 0 -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t PREAMBLEB0:8;     /*!< bit:  0.. 7  Preamble Byte 0                    */
    uint32_t :24;              /*!< bit:  8..31  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} DSU_CID0_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define DSU_CID0_OFFSET             0x1FF0       /**< \brief (DSU_CID0 offset) Component Identification Register 0 */
#define DSU_CID0_RESETVALUE         0x00000000   /**< \brief (DSU_CID0 reset_value) Component Identification Register 0 */

#define DSU_CID0_PREAMBLEB0_Pos     0            /**< \brief (DSU_CID0) Preamble Byte 0 */
#define DSU_CID0_PREAMBLEB0_Msk     (0xFFu << DSU_CID0_PREAMBLEB0_Pos)
#define DSU_CID0_PREAMBLEB0(value)  ((DSU_CID0_PREAMBLEB0_Msk & ((value) << DSU_CID0_PREAMBLEB0_Pos)))
#define DSU_CID0_MASK               0x000000FFu  /**< \brief (DSU_CID0) MASK Register */

/* -------- DSU_CID1 : (DSU Offset: 0x1FF4) (R/  32) Component Identification Register 1 -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t PREAMBLE:4;       /*!< bit:  0.. 3  Preamble Byte 1                    */
    uint32_t CCLASS:4;         /*!< bit:  4.. 7  Component Class                    */
    uint32_t :24;              /*!< bit:  8..31  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} DSU_CID1_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define DSU_CID1_OFFSET             0x1FF4       /**< \brief (DSU_CID1 offset) Component Identification Register 1 */
#define DSU_CID1_RESETVALUE         0x00000000   /**< \brief (DSU_CID1 reset_value) Component Identification Register 1 */

#define DSU_CID1_PREAMBLE_Pos       0            /**< \brief (DSU_CID1) Preamble Byte 1 */
#define DSU_CID1_PREAMBLE_Msk       (0xFu << DSU_CID1_PREAMBLE_Pos)
#define DSU_CID1_PREAMBLE(value)    ((DSU_CID1_PREAMBLE_Msk & ((value) << DSU_CID1_PREAMBLE_Pos)))
#define DSU_CID1_CCLASS_Pos         4            /**< \brief (DSU_CID1) Component Class */
#define DSU_CID1_CCLASS_Msk         (0xFu << DSU_CID1_CCLASS_Pos)
#define DSU_CID1_CCLASS(value)      ((DSU_CID1_CCLASS_Msk & ((value) << DSU_CID1_CCLASS_Pos)))
#define DSU_CID1_MASK               0x000000FFu  /**< \brief (DSU_CID1) MASK Register */

/* -------- DSU_CID2 : (DSU Offset: 0x1FF8) (R/  32) Component Identification Register 2 -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t PREAMBLEB2:8;     /*!< bit:  0.. 7  Preamble Byte 2                    */
    uint32_t :24;              /*!< bit:  8..31  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} DSU_CID2_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define DSU_CID2_OFFSET             0x1FF8       /**< \brief (DSU_CID2 offset) Component Identification Register 2 */
#define DSU_CID2_RESETVALUE         0x00000000   /**< \brief (DSU_CID2 reset_value) Component Identification Register 2 */

#define DSU_CID2_PREAMBLEB2_Pos     0            /**< \brief (DSU_CID2) Preamble Byte 2 */
#define DSU_CID2_PREAMBLEB2_Msk     (0xFFu << DSU_CID2_PREAMBLEB2_Pos)
#define DSU_CID2_PREAMBLEB2(value)  ((DSU_CID2_PREAMBLEB2_Msk & ((value) << DSU_CID2_PREAMBLEB2_Pos)))
#define DSU_CID2_MASK               0x000000FFu  /**< \brief (DSU_CID2) MASK Register */

/* -------- DSU_CID3 : (DSU Offset: 0x1FFC) (R/  32) Component Identification Register 3 -------- */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef union {
  struct {
    uint32_t PREAMBLEB3:8;     /*!< bit:  0.. 7  Preamble Byte 3                    */
    uint32_t :24;              /*!< bit:  8..31  Reserved                           */
  } bit;                       /*!< Structure used for bit  access                  */
  uint32_t reg;                /*!< Type      used for register access              */
} DSU_CID3_Type;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#define DSU_CID3_OFFSET             0x1FFC       /**< \brief (DSU_CID3 offset) Component Identification Register 3 */
#define DSU_CID3_RESETVALUE         0x00000000   /**< \brief (DSU_CID3 reset_value) Component Identification Register 3 */

#define DSU_CID3_PREAMBLEB3_Pos     0            /**< \brief (DSU_CID3) Preamble Byte 3 */
#define DSU_CID3_PREAMBLEB3_Msk     (0xFFu << DSU_CID3_PREAMBLEB3_Pos)
#define DSU_CID3_PREAMBLEB3(value)  ((DSU_CID3_PREAMBLEB3_Msk & ((value) << DSU_CID3_PREAMBLEB3_Pos)))
#define DSU_CID3_MASK               0x000000FFu  /**< \brief (DSU_CID3) MASK Register */

/** \brief DSU hardware registers */
#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
typedef struct {
  __O  DSU_CTRL_Type             CTRL;        /**< \brief Offset: 0x0000 ( /W  8) Control Register */
  __IO DSU_STATUSA_Type          STATUSA;     /**< \brief Offset: 0x0001 (R/W  8) Status Register A */
  __I  DSU_STATUSB_Type          STATUSB;     /**< \brief Offset: 0x0002 (R/   8) Status Register B */
       RoReg8                    Reserved1[0x1];
  __IO DSU_ADDR_Type             ADDR;        /**< \brief Offset: 0x0004 (R/W 32) Address Register */
  __IO DSU_LENGTH_Type           LENGTH;      /**< \brief Offset: 0x0008 (R/W 32) Length Register */
  __IO DSU_DATA_Type             DATA;        /**< \brief Offset: 0x000C (R/W 32) Data Register */
  __IO DSU_DCC_Type              DCC[2];      /**< \brief Offset: 0x0010 (R/W 32) Debug Communication Channel Register */
  __I  DSU_DID_Type              DID;         /**< \brief Offset: 0x0018 (R/  32) Device Identification Register */
       RoReg8                    Reserved2[0xD4];
  __IO DSU_DCFG_Type             DCFG[2];     /**< \brief Offset: 0x00F0 (R/W 32) Device Configuration Register */
  __IO DSU_UPTM_Type             UPTM;        /**< \brief Offset: 0x00F8 (R/W 32) UnProtected Test Mode Register */
  __IO DSU_TESTMODE_Type         TESTMODE;    /**< \brief Offset: 0x00FC (R/W 32) Test Mode Register */
       RoReg8                    Reserved3[0xF00];
  __I  DSU_ENTRY_Type            ENTRY[2];    /**< \brief Offset: 0x1000 (R/  32) CoreSight ROM Table Entry Register */
  __I  DSU_END_Type              END;         /**< \brief Offset: 0x1008 (R/  32) CoreSight ROM Table End Register */
       RoReg8                    Reserved4[0xFC0];
  __I  DSU_MEMTYPE_Type          MEMTYPE;     /**< \brief Offset: 0x1FCC (R/  32) CoreSight ROM Table Memory Type Register */
  __I  DSU_PID4_Type             PID4;        /**< \brief Offset: 0x1FD0 (R/  32) Peripheral Identification Register 4 */
  __I  DSU_PID5_Type             PID5;        /**< \brief Offset: 0x1FD4 (R/  32) Peripheral Identification Register 5 */
  __I  DSU_PID6_Type             PID6;        /**< \brief Offset: 0x1FD8 (R/  32) Peripheral Identification Register 6 */
  __I  DSU_PID7_Type             PID7;        /**< \brief Offset: 0x1FDC (R/  32) Peripheral Identification Register 7 */
  __I  DSU_PID0_Type             PID0;        /**< \brief Offset: 0x1FE0 (R/  32) Peripheral Identification Register 0 */
  __I  DSU_PID1_Type             PID1;        /**< \brief Offset: 0x1FE4 (R/  32) Peripheral Identification Register 1 */
  __I  DSU_PID2_Type             PID2;        /**< \brief Offset: 0x1FE8 (R/  32) Peripheral Identification Register 2 */
  __I  DSU_PID3_Type             PID3;        /**< \brief Offset: 0x1FEC (R/  32) Peripheral Identification Register 3 */
  __I  DSU_CID0_Type             CID0;        /**< \brief Offset: 0x1FF0 (R/  32) Component Identification Register 0 */
  __I  DSU_CID1_Type             CID1;        /**< \brief Offset: 0x1FF4 (R/  32) Component Identification Register 1 */
  __I  DSU_CID2_Type             CID2;        /**< \brief Offset: 0x1FF8 (R/  32) Component Identification Register 2 */
  __I  DSU_CID3_Type             CID3;        /**< \brief Offset: 0x1FFC (R/  32) Component Identification Register 3 */
} Dsu;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

/*@}*/

#endif /* _SAMD20_DSU_COMPONENT_ */
